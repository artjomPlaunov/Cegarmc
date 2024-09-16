(*************************************************************************)
(*                                                                       *)
(* This file is intended to be used with Frama-C and a CEGAR model       *)
(* checker (currently, SATABS or CPA Checker).                           *)
(*                                                                       *)
(* Copyright (C) [2016]  Subash Shankar                                  *)
(*                                                                       *)
(* This program is free software: you can redistribute it and/or         *)
(* modify it under the terms of the GNU General Public License           *)
(* as published by the Free Software, either version 3 of the License,   *)
(* or (at your option) any later version.                                *)
(* Foundation, version 2.1.                                              *)
(*                                                                       *)
(* This program is distributed in the hope that it will be useful,       *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(* GNU General Public License for more details.                          *)
(*                                                                       *)
(* You should have received a copy of the GNU General Public License     *)
(* along with this program. If not, see <http://www.gnu.org/licenses/.>  *)
(*                                                                       *)
(* Contributors:                                                         *)
(*   Subash Shankar (subash.shankar@hunter.cuny.edu)                     *)
(*   Zachary Hutchinson                                                  *)
(*   Gilbert Pajela                                                      *)
(*************************************************************************)

(*
 * This is a plugin that attempts to prove statement contracts using  
 * CEGAR. The basic approach is to convert the statement contract to
 * a format usable by CEGAR backends (SATABS, CPAChecker).
 *
 * History:
 *   0.7  Reasonably complete coverage of C constructs
 *   0.5  First version on webpage
 *   0.3  Many fixes
 *   0.2  Initial released version (complete rewrite of 0.1)
 *   0.1  Initial version (proof of concept)
 *
 * Please report bugs/questions/comments to Subash Shankar
 * (subash.shankar@hunter.cuny.edu)
*)

(* TODO
 * CLEANER
 * Literate programming for ocaml comments
 * Separate out gui code into separate file (plugin manual 2.3.5)
 * Get rid of unneeded open/includes
 * Register state with mc results to avoid recomputation (Plugin 2.3.9)
 * Use logging services (plugin manual 4.8)
 * More information about dependences on value results (if mc-context)
 * Empty elses are printed right now (since cil alludes to a case
 *   where it is needed to avoid compiler bugs). Check if this affects
 *   cegar performance, and update code if so.
 * Change lvalset to also be a set for array (and struc?)
 *   references. Right now, it creates multiple elements since, for
 *   example, two instances of arr[5] are deemed different
 * Add support for bool (currently translated to int)
 * Replace raises with warnings for anything not a mc bug
 * Legalpred is executed multiple times; dont.
 * Add support for periodicity information (if mc-context)
 * Add cegar.maxIterations for cpa maxiterations
 * Get rid of large max constant
 * Dont insert function body if contract is present and abstractCalls
 *
 * CORRECTNESS/SOUNDNESS
 * Think about when mc can prove false (zach's email on satabs output)
 *   (probably an issue with both satabs and cpa). Note this unsupported
 *   constructs (eg, functions, in ACSL) currently might also be
 *   "proven false", since we let the cegar checker handle these.
 * Check Satabs output for multiple asserts (and update code accordingly)
 * Distinguish cil breaks from source breaks in mcpp
 * Check that mcpp is consistent with C99 grammar (esp, wrt
 *   semicolons)
 * Check whether any ACSL constructs ignored by mc affect soundness
 *   of contract proofs.
 * We are making [confirmed] assumptions about what CPAChecker prints
 *   in its output file. These need to be documented.
 * What if contract refers to a variable not in statement?
 * Check that CMCBADEND, CMCUNSUPPORTED return correct results
 * Check whether frama-c/wp does array bounds as RTEs, and be consistent
 * Match all bitwidths with those of SATABS and CPA (in varDecl,
 *   elsewhere?)
 * Might need to order declarations for arrays and comps that refer to
 *   each other (lvalset is ordered, but dumped arrays/comps first
 *   currently)
 * The semantics of multiple statement contracts is not clear in the
 *   ACSL docs (V1.8 S2.3.5 is for multiple function contracts but
 *   unclear even there; this needs to be clarified with appropriate
 *   error checks. Currently, MC treats them independently.
 * When there are multiple statement contracts MC might be getting
 *   the wrong one. Check/fix (see prog0.frama.c)
 * Add base variable assertions for pointers
 * Document interaction between context and requires (does one supercede?)
 *   esp. in regard to vacuous truths
 * Different emitters for memory models?
 * ACSL operators need to be translated or errored. Ex: ==> is an ACSL
 *   construct that results in errors in CEGAR checkers
 * Interprocedural verification doesn't work if the callee has 2
 *   requires clauses
 * Certain ACSL expressions, e.g. compound expressions such as those
 *   of the form x > y && y > z, get prettified by Frama-C into x > y >
 *   z. This shortened form has a different meaning in C, but it is
 *   still valid C, so when it is passed on to the backends, currently
 *   no errors are generated, potentially leading to unsound results.
  *
 * FEATURES (including efficiency)
 * Dont do mc if its already been done successfully (and add force option)
 * Make postconditions support other acsl constructs and add error
 *   checking for unsupported constructs. Abrupt clauses, \result,
 *   etc. might be particulary nice to support (some might be
 *   applicable only to function contracts). In particular, \is_finite is
 *   needed to support fmod() (in math.h).
 * Support attributes on declarations/types
 * Support all datatypes (enums, nested structs, typedefs, anything else?)
 * Handle function calls in statements (conditional on fct contracts)
 *   Note that we might need to also support storage classes for
 *   this. Might not be possible, needs thought.
 * Function contracts
 * Slicing
 * Consider breaking down non-atomic pre/postconditions into multiple
 *   cegar calls. But would it differ by pre/postcondition then?
 * Handle UnspecifiedSequence: see cil_types.mli
 * Check how -simplify-cfg (remove break/continue/switch) affects
 *   results
 * See if we can exploit assigns clause
 * Add selector for cegar backends (w/ automatic selection of backend?)
 * Support multiple and named behaviors (affects dumpStmtPre, checkFC)
 * Interpret CPA's counterexample to help Frama-C user try mc/etc again
 * CPAChecker version needs to use mc-numiter option (or document
 *   otherwise if not possible)
 * Use value analysis to provide array bounds for CPA (need to
 *   investigate whether this makes sense first since CIL converts
 *   variable dim arrays to pointers)
 * For pointers resulting from arrays, change to array after checking
 *   if/how CEGAR checkers treat them differently.
 * Make context work with arrays/structs/pointers
 *
 * NOTES FOR POINTERS
 * - Need to support multiple memory models (see wp pp 11-12, and
 *   ACSL). Q: what happens if inconsistent results by memory model?
 *   A: Be consistent with what wp does
 * - Value defines a separate base address for each variable, and does
 *   not allow pointer arithmetic to go from one base to another
 *   (sodium pp 47). Alarms are generated to ensure this hyp.
 *   So, mc needs to do the same?
 * - Wp: multiple memory models.
 * - Should getval also support undefined/defined pointers? Check if
 *   satabs/cpa can use this before implementing
*)

open Locations
open Cil_types
open Abstract_interp
open CilE
open Set
open Printer
include Location_Bytes

let help_msg = "Model check statement contract using CEGAR"
module Self = Plugin.Register
    (struct
      let name = "CEGAR model checking"
      let shortname = "mc"
      let help = help_msg ^ "(experimental)"
    end)

module Enabled = Self.True
    (struct
      let option_name = "-mc"
      let help = "when on (off by default), " ^ help_msg
    end)

module Diagnostics = Self.False
    (struct
      let option_name = "-mc-diag"
      let help = "output diagnostic information " ^
                 "(internal use only)."
    end)

module MaxIterations = Self.Int
    (struct
      let option_name = "-mc-numiter"
      let default = 20
      let arg_name = "n"
      let help = "max # cegar iterations for SatAbs to try\n" ^
                 "Ignored if -mc-checker is not set to 'satabs'."
    end)

module TimeLimit = Self.Int
    (struct
      let option_name = "-mc-timelimit"
      let default = 10
      let arg_name = "timelimit"
      let help = "max time (in secs) for checker to attempt verification.\n"
    end)

module Iteration = Self.String
    (struct
      let option_name = "-mc-iter"
      let default = ""
      let arg_name = "f"
      let help = "Do only one CEGAR iteration, with predicates in file <f>" ^
                 "\nNOT IMPLEMENTED YET"
    end)

module OutputFile = Self.String
    (struct
      let option_name = "-mc-output"
      let default = "mcFile31416.c"
      let arg_name = "output-file"
      let help = "File where the initial generated C program is output"
    end)

module AbstractCalls = Self.True
    (struct
      let option_name = "-mc-abstractCalls"
      let help = "Replace called function bodies with contracts " ^
                 "(ignored if only body or contract exists)"
    end)

module Context = Self.False
    (struct
      let option_name = "-mc-context"
      let help = "Context sensitive " ^
                 "(i.e., use value analysis to constrain initial state)"
    end)

module MaxContext = Self.Int
    (struct
      let option_name = "-mc-maxcontext"
      let default = 2
      let arg_name = "n"
      let help = "Maximum number of values to enumerate in context" ^
                 " (interval used otherwise)"
    end)

module Slice = Self.False
    (struct
      let option_name = "-mc-slice"
      let help = "Slice program before model checking " ^
                 "\nNOT IMPLEMENTED YET"
    end)

module Checker = Self.String
    (struct
      let option_name = "-mc-checker"
      let default = "satabs"
      let arg_name = "checker"
      let help = "Model checker used by mc " ^
                 "(cpa or satabs)"
    end)

module ConstrainVals = Self.False
    (struct
      let option_name = "-mc-constrainVals"
      let help = "Constrain Loop Body Values based on EVA (experimental)"
    end)

exception MC_Unsupported_Construct of string
exception MC_Internal_Bug of string
exception MC_Debug of string*int
exception MC_Unsupported_Argument of string

let mcStmtPrf =
  Emitter.create "MC"
    [Emitter.Property_status]
    ~correctness:[]
    ~tuning:[]

(*************************************************************************)
(* Utilities for traversing AST                                          *)
(*************************************************************************)
(* Lvalset is compatible with the following output order only:
 *   struc defs
 *   main() {
 *     array decls
 *     struct decls
 *     non-pointer scalar decls (in order of appearance)
 *     pointer decls (in order of LvalStructEq.compare)
 *     code corresponding to statement
 *     }
 * Note that this order might have to change if array/struct base types
 * can be more complicated (eg, each other, typedefs).
*)
module LvalSet = Make (
  struct
    (* ordered by position, with pointer > pointee *)
    let compare =
      (fun v1 v2 ->
         match (v1,v2) with
         | ((Var(vi1),off1),(Var(vi2),off2)) ->
           if ((Pervasives.compare vi1.vdecl vi2.vdecl) = 0) then (
             if ((Pervasives.compare vi1.vid vi2.vid) = 0) then
               (Cil_datatype.Offset.compare off1 off2)
             else (Pervasives.compare vi1.vid vi2.vid)
           )
           else (Pervasives.compare vi1.vdecl vi2.vdecl)
         | ((Var(vi1),_),(Mem(_),_)) -> -1
         | ((Mem(_),_),(Var(vi2),_)) -> 1
         | _ ->
           Cil_datatype.LvalStructEq.compare v1 v2
      )
    type t = Cil_types.lval
  end
  )

module TLvalSet = Make (
  struct
    let compare =
      (fun v1 v2 ->
         let name1 = ref ((Pretty_utils.to_string Printer.pp_term_lval)
                            v1) in
         let name2 = ref ((Pretty_utils.to_string Printer.pp_term_lval)
                            v2) in
         if (!name1 = !name2) then 0
         else Pervasives.compare v1 v2
      )
    type t = Cil_types.term_lval
  end
  )

module VarinfoSet = Make (
  struct
    let compare = Pervasives.compare
    type t = Cil_types.varinfo
  end
  )

module CompSet = Make (
  struct
    let compare = Pervasives.compare
    type t = Cil_types.varinfo
  end
  )

module CompinfoSet = Make (
  struct
    let compare = Pervasives.compare
    type t = Cil_types.compinfo
  end
  )

module EmitterSet = Make (
  struct
    let compare =
      (fun em1 em2 ->
         if ((Emitter.get_name em1) = (Emitter.get_name em2)) then 0
         else Pervasives.compare em1 em2
      )
    type t = Emitter.emitter
  end
  )

module StringSet = Make(String)

(* This is a list of the vid's of the varinfos of variables that
   were initialized locally. This is necessary to handle Frama-C's
   Local_init type of instruction. *)
let local_init : int list ref = ref []

let rec isLvalGlobal = function
  | (Var(vi), off) -> vi.vglob || isOffsetGlobal off
  | (Mem(expr), off) ->
    isExprGlobal expr.enode || isOffsetGlobal off

and isOffsetGlobal = function
  | NoOffset -> false
  | Field(_,off) -> isOffsetGlobal off
  | Index(expr,off) -> isExprGlobal expr.enode || isOffsetGlobal off

and isExprGlobal = function
  | Lval(lval)
  | AddrOf(lval)
  | StartOf(lval) ->
    isLvalGlobal lval
  | SizeOfE(expr)
  | AlignOfE(expr)
  | UnOp(_,expr,_)
  | CastE(_,expr)
  | Info(expr,_) ->
    isExprGlobal expr.enode
  | BinOp(_,expr1,expr2,_) ->
    isExprGlobal expr1.enode || isExprGlobal expr2.enode
  | Const(_)
  | SizeOf(_)
  | SizeOfStr(_)
  | AlignOf(_) ->
    false

let rec
  lvalsInLval lval assignedTo inStmt isFnName =
  let lvalstr = ((Pretty_utils.to_string Printer.pp_lval) lval) in
  let lvalSet =
    if inStmt || isFnName || (isLvalGlobal lval) then (
      LvalSet.add
        lval
        (match lval with
         | (Var(_),off) ->
           lvalsInOffset off assignedTo inStmt isFnName;
         | (Mem(expr),off) ->
           LvalSet.union (lvalsInExpr expr assignedTo inStmt isFnName)
             (lvalsInOffset off assignedTo inStmt isFnName)
        )
    ) else LvalSet.empty in
  lvalSet

and
  lvalsInOffset off assignedTo inStmt isFnName =
  (match off with
   | NoOffset ->
     LvalSet.empty;
   | Field(_,foff) ->
     lvalsInOffset foff assignedTo inStmt isFnName;
   | Index(expr,ioff) ->
     LvalSet.union (lvalsInExpr expr assignedTo inStmt isFnName)
       (lvalsInOffset ioff assignedTo inStmt isFnName)
  )

and
  lvalsInExpr expr assignedTo inStmt isFnName =
  match expr.enode with
  | Const(_) ->
    LvalSet.empty
  | Lval(lval)
  | AddrOf(lval)
  | StartOf(lval) ->
    lvalsInLval lval assignedTo inStmt isFnName
  | SizeOfE(expr)
  | AlignOfE(expr)
  | UnOp(_,expr,_)
  | CastE(_,expr)
  | Info(expr,_) ->
    lvalsInExpr expr assignedTo inStmt isFnName
  | BinOp(_,expr1,expr2,_) ->
    let t1 = lvalsInExpr expr1 assignedTo inStmt isFnName in
    let t2 = lvalsInExpr expr2 assignedTo inStmt isFnName in
    let t3 = LvalSet.union t1 t2 in
    t3
  | SizeOf(_)
  | SizeOfStr(_)
  | AlignOf(_) ->
    LvalSet.empty

and
  lvalsInExprs exprs assignedTo inStmt isFnName =
  match exprs with
  | [] -> LvalSet.empty
  | expr::exprs ->
    LvalSet.union (lvalsInExpr expr assignedTo inStmt isFnName)
      (lvalsInExprs exprs assignedTo inStmt isFnName)

and
  lvalsInInit init assignedTo inStmt isFnName =
  match init with
  | SingleInit expr ->   (** A single initializer *)
    lvalsInExpr expr assignedTo inStmt isFnName
  | CompoundInit(_,l) ->
    lvalsInCompoundInit l assignedTo inStmt isFnName

and
  lvalsInCompoundInit ci assignedTo inStmt isFnName =
  match ci with
  | [] -> LvalSet.empty
  | (off, init)::t ->
    let l1 = lvalsInOffset off assignedTo inStmt isFnName in
    let l2 = lvalsInInit init assignedTo inStmt isFnName in
    let l3 = lvalsInCompoundInit t assignedTo inStmt isFnName in
    LvalSet.union l1 (LvalSet.union l2 l3)

and
  lvalsInBlock blk assignedTo inStmt isFnName =
  (* not using blk.blocals since that won't get globals/formals *)
  lvalsInStmts blk.bstmts assignedTo inStmt isFnName

and
  lvalsInStmts stmts assignedTo inStmt isFnName =
  match stmts with
  | [] -> LvalSet.empty
  | stmt::stmts ->
    LvalSet.union (lvalsInStmt stmt assignedTo inStmt isFnName)
      (lvalsInStmts stmts assignedTo inStmt isFnName)

(*
 * This could also be done from the slocals/sformals of the enclosing
 * function, but that is potentially a huge overapproximation and
 * still wouldn't get globals (for which we would have to access Vars
 * in kernel/globals resulting in an even bigger overapproximation).
*)
and
  lvalsInStmt stmt assignedTo inStmt isFnName =
  if assignedTo then (
    match stmt.skind with
    | Instr Set(lval,expr,_) ->
      lvalsInLval lval assignedTo inStmt isFnName
    | Instr Call(Some lval,expr,exprs,_) ->
      let l1 = lvalsInLval lval assignedTo inStmt isFnName in
      (* expr has the name of the called function *)
      let l2 = lvalsInExpr expr assignedTo inStmt true in
      let lv = try LvalSet.choose l2 with Not_found ->
        raise (MC_Internal_Bug 
               "No lvals in expr (assignedTo, Instr Call Some)")
      in
      let l3 = match lv with
        | (Var vi,_) ->
          (try (
             let kf = Globals.Functions.get vi in
             match kf.fundec with
             | Definition(fundec2,_) ->
               lvalsInBlock fundec2.sbody assignedTo false isFnName
             | Declaration _ ->
               LvalSet.empty
           ) with Not_found -> LvalSet.empty
          )
        | _ -> (* This shouldn't happen *)
          raise (MC_Unsupported_Construct "Unsupported use of pointers")
      in
      LvalSet.union l1 (LvalSet.union l2 l3)
    | Instr Call(None,expr,exprs,_) ->
      let l2 = lvalsInExpr expr assignedTo inStmt true in
      let lv = try LvalSet.choose l2 with Not_found ->
        raise (MC_Internal_Bug 
               "No lvals in expr (assignedTo, Instr Call None)")
      in
      let l3 = match lv with
        | (Var vi,_) ->
          (try (
             let kf = Globals.Functions.get vi in
             match kf.fundec with
             | Definition(fundec2,_) ->
               lvalsInBlock fundec2.sbody assignedTo false isFnName
             | Declaration _ ->
               LvalSet.empty
           ) with Not_found -> LvalSet.empty
          )
        | _ -> (* This shouldn't happen *)
          raise (MC_Unsupported_Construct "Unsupported use of pointers")
      in
      LvalSet.union l2 l3
    | Instr Local_init(vi,li,_) ->
      let l1 = lvalsInLval (Var vi, NoOffset) assignedTo inStmt isFnName in
      if inStmt then local_init := vi.vid::!local_init;
      (match li with
       | ConsInit(f,args,_) ->
         let l2 = lvalsInLval (Var f, NoOffset) assignedTo inStmt true in
         let l3 = try (
           let kf = Globals.Functions.get f in
           match kf.fundec with
           | Definition(fundec2,_) ->
             lvalsInBlock fundec2.sbody assignedTo false isFnName
           | Declaration _ ->
             LvalSet.empty
         ) with Not_found -> LvalSet.empty
         in
         LvalSet.union l1 (LvalSet.union l2 l3)
       | AssignInit init ->
         let l2 = lvalsInInit init assignedTo inStmt isFnName in
         LvalSet.union l1 l2
      )
    | Return (Some expr,_) ->
      LvalSet.empty
    | Switch (expr,blk,_,_) ->
      lvalsInBlock blk assignedTo inStmt isFnName
    | If(expr,blk1,blk2,_) ->
      LvalSet.union
        (lvalsInBlock blk1 assignedTo inStmt isFnName)
        (lvalsInBlock blk2 assignedTo inStmt isFnName)
    | Loop (_,blk,_,_,_) (* note CIL represents condition as separate test *)
    | Block (blk) ->
      lvalsInBlock blk assignedTo inStmt isFnName
    | UnspecifiedSequence us ->
      lvalsInBlock (Cil.block_from_unspecified_sequence us)
        assignedTo inStmt isFnName
    | Instr _
    | Return (None,_)
    | Goto _
    | Break _
    | Continue _ ->
      LvalSet.empty
    (* Handled using catch all case since Fluorine/Neon have just
     * TryFinally and TryExcept, but Sodium also has Throw and
     * TryCatch.
    *)
    | _ ->
      raise (MC_Unsupported_Construct "Try/Throw statements")
  ) else (
    match stmt.skind with
    | Instr Set(lval,expr,_) ->
      let t1 = lvalsInLval lval assignedTo inStmt isFnName in
      let t2 = lvalsInExpr expr assignedTo inStmt isFnName in
      LvalSet.union t1 t2
    | Instr Call(Some lval,expr,exprs,_) ->
      let l1 = lvalsInLval lval assignedTo inStmt isFnName in
      let l2 = lvalsInExpr expr assignedTo inStmt true in
      let lv = try LvalSet.choose l2 with Not_found ->
        raise (MC_Internal_Bug "No lvals in expr (Instr Call Some)")
      in (
        match lv with
        | (Var vi,_) ->
          let l4 = try (
            let kf = Globals.Functions.get vi in
            match kf.fundec with
            | Definition(fundec2,_) ->
              lvalsInBlock fundec2.sbody assignedTo false isFnName
            | Declaration _ ->
              LvalSet.empty
          ) with Not_found -> LvalSet.empty
          in
          let l3 = lvalsInExprs exprs assignedTo inStmt isFnName in
          LvalSet.union l1 (LvalSet.union l2 (LvalSet.union l3 l4))
        | _ -> (* This shouldn't happen *)
          raise (MC_Unsupported_Construct "Unsupported use of pointers")
      )
    | Instr Call(None,expr,exprs,_) ->
      let l2 = lvalsInExpr expr assignedTo inStmt true in
      let lv = try LvalSet.choose l2 with Not_found ->
        raise (MC_Internal_Bug "No lvals in expr (Instr Call None)")
      in (
        match lv with
        | (Var vi,_) ->
          let l4 = try (
            let kf = Globals.Functions.get vi in
            match kf.fundec with
            | Definition(fundec2,_) ->
              lvalsInBlock fundec2.sbody assignedTo false isFnName
            | Declaration _ ->
              LvalSet.empty
          ) with Not_found -> LvalSet.empty
          in
          let l3 = lvalsInExprs exprs assignedTo inStmt isFnName in
          LvalSet.union l2 (LvalSet.union l3 l4)
        | _ -> (* This shouldn't happen *)
          raise (MC_Unsupported_Construct "Unsupported use of pointers")
      )
    | Instr Local_init(vi,li,_) ->
      let l1 = lvalsInLval (Var vi, NoOffset) assignedTo inStmt isFnName in
      if inStmt then local_init := vi.vid::!local_init;
      (match li with
       | ConsInit(f,args,_) ->
         let l2 = lvalsInLval (Var f, NoOffset) assignedTo inStmt true in
         let l4 = try (
           let kf = Globals.Functions.get f in
           match kf.fundec with
           | Definition(fundec2,_) ->
             lvalsInBlock fundec2.sbody assignedTo false isFnName
           | Declaration _ ->
             LvalSet.empty
         ) with Not_found -> LvalSet.empty
         in
         let l3 = lvalsInExprs args assignedTo inStmt isFnName in
         LvalSet.union l1 (LvalSet.union l2 (LvalSet.union l3 l4))
       | AssignInit init ->
         let l2 = lvalsInInit init assignedTo inStmt isFnName in
         LvalSet.union l1 l2
      )

    | Return (Some expr,_) ->
      lvalsInExpr expr assignedTo inStmt isFnName

    | Switch (expr,blk,_,_) ->
      lvalsInBlock blk assignedTo inStmt isFnName

    | If(expr,blk1,blk2,_) ->
      LvalSet.union
        (lvalsInExpr expr assignedTo inStmt isFnName)
        (LvalSet.union
           (lvalsInBlock blk1 assignedTo inStmt isFnName)
           (lvalsInBlock blk2 assignedTo inStmt isFnName))

    | Loop (_,blk,_,_,_)
    | Block (blk) ->
      lvalsInBlock blk assignedTo inStmt isFnName

    | UnspecifiedSequence us ->
      lvalsInBlock (Cil.block_from_unspecified_sequence us)
        assignedTo inStmt isFnName
    | Instr _
    | Return (None,_)
    | Goto _
    | Break _
    | Continue _ ->
      LvalSet.empty
    | _ ->
      raise (MC_Unsupported_Construct "Try/Throw statements")
  )

(* This is a similar set for term lvals. It is necessary for parsing
 * annotations, i.e. terms and predicates.
*)
let rec
  tlvalsInTLval tlval = TLvalSet.add
    tlval
    (match tlval with
     | (TVar(_),off)
     | (TResult(_),off) ->
       tlvalsInTOffset off
     | (TMem(term),off) ->
       TLvalSet.union (tlvalsInTerm term) (tlvalsInTOffset off)
    )

and
  tlvalsInTOffset toff =
  (match toff with
   | TNoOffset -> TLvalSet.empty;
   | TModel(_,foff)
   | TField(_,foff) -> tlvalsInTOffset foff;
   | TIndex(term,ioff) ->
     TLvalSet.union (tlvalsInTerm term) (tlvalsInTOffset ioff)
  )

and
  tlvalsInTerm t =
  match t.term_node with
  | TConst(_) ->
    TLvalSet.empty
  | TLval(tlval)
  | TAddrOf(tlval)
  | TStartOf(tlval) ->
    tlvalsInTLval tlval
  | TSizeOfE(t1)
  | TAlignOfE(t1)
  | TUnOp(_,t1)
  | TCastE(_,t1)
  | Tlambda(_,t1)
  | Tat(t1,_)
  | Tbase_addr(_,t1)
  | Toffset(_,t1)
  | Tblock_length(_,t1)
  | TLogic_coerce(_,t1)
  | Ttypeof(t1)
  | Tcomprehension(t1,_,_)
  | Tlet(_,t1) ->
    tlvalsInTerm t1
  | TSizeOf(_)
  | TSizeOfStr(_)
  | TAlignOf(_)
  | Tapp(_,_,_)
  | TDataCons(_,_)
  | Tnull
  | Ttype(_)
  | Tempty_set
  | Tunion(_)
  | Tinter(_)
  | Trange(_,_) ->
    TLvalSet.empty
  | TBinOp(_,t1,t2)
  | TUpdate(t1,_,t2) ->
    TLvalSet.union (tlvalsInTerm t1) (tlvalsInTerm t2)
  | Tif(t1,t2,t3) ->
    TLvalSet.union
      (tlvalsInTerm t1)
      (TLvalSet.union
         (tlvalsInTerm t2)
         (tlvalsInTerm t3))

and
  tlvalsInPred pred =
  match pred with
  | Prel(_,t1,t2) ->
    TLvalSet.union (tlvalsInTerm t1) (tlvalsInTerm t2)
  | Pnot(np) ->
    (tlvalsInPred np.pred_content)
  | Pand(np1,np2)
  | Por(np1,np2)
  | Pxor(np1,np2)
  | Pimplies(np1,np2)
  | Piff(np1,np2) ->
    TLvalSet.union (tlvalsInPred np1.pred_content)
      (tlvalsInPred np2.pred_content)
  | Pif(t,np1,np2) ->
    TLvalSet.union
      (tlvalsInTerm t)
      (TLvalSet.union
         (tlvalsInPred np1.pred_content)
         (tlvalsInPred np2.pred_content))
  | Pforall(_,np) ->
    (tlvalsInPred np.pred_content)
  | Pfalse
  | Ptrue
  | Papp(_,_,_)
  | Pseparated(_)
  | Plet(_,_)
  | Pexists(_,_)
  | Pat(_,_)
  | Pvalid_read(_,_)
  | Pvalid(_,_)
  | Pinitialized(_,_)
  | Pallocable(_,_)
  | Pfreeable(_,_)
  | Pfresh(_,_,_,_)
  (* Handled using catch all case since Fluorine/Neon have just
   * Psubtype(_,_), but Sodium also has Pdangling.
  *)
  | _ ->
    TLvalSet.empty

(* Type for holding assigns locations *)
type assignstype = {
  name: string;
  (** Name of the function to whose assigns clause this belongs. If the
      assigns clause belongs to the statement being checked, then this
      contains "CMCstmt". *)
  locs: StringSet.t
  (** Set of variable names in the assigns clause. *)
}

type stmtorblock =
  | Stmt of Cil_types.stmt
  | Blk of Cil_types.block
  | NoBody

(* Type to support assert *)
type bhvOrPred =
  | Bhv of Cil_types.behavior
  | Pred of Cil_types.predicate

(* Types for handling function calls in stmt *)
type fntype = {
  mutable count: int;
  (** Number of times the function is called. Used to distinguish the
      names of variables that hold the result of the function call,
      where the naming convention is CMC<function name><count>. For
      example, the name of the variable used to hold the result of the
      third call to function foo() would be CMCfoo3. *)
  vinfo: Cil_types.varinfo; (** The function's varinfo. *)
  funspec: Cil_types.funspec
  (** The entire function contract. *)
}

type currfntype = {
  idx: int; (** Index of the function in fnList. *)
  args: Cil_types.exp list (** List of actual arguments. *)
}

(*
 * This is a list of globals that have already been printed to the
 * output file.
*)
let globalsDumped : string list ref = ref []

(* Whether or not to prove assuming independence *)
let emitter = ref mcStmtPrf
let emitterName = ref "MC"
let emitters = ref (EmitterSet.add !emitter EmitterSet.empty)

(* Whether side effects of a function affect stmt *)
let hasSideEffects = ref false

(* This is a list of variables that are initialized globally *)
let globalDefs = ref VarinfoSet.empty

(* This is a list of all sids in the sliced program *)
let slicedSids : int list ref = ref []

let warn fmt str1 str2 =
  Self.warning "%s" str1;
  Format.fprintf fmt "@.%s@." str2

let regWarn fmt =
  let str = "MC_UNSUPPORTED CONSTRUCT ERROR: register storage " ^
            "class;" in
  Self.warning "Register storage class not supported";
  Format.fprintf fmt "%s@." str

let extWarn fmt =
  let str1 = "Extern storage class only supported in function " ^
             "declarations" in
  let str2 = "MC_UNSUPPORTED CONSTRUCT ERROR: extern storage class " ^
             "used outside of function declaration;" in
  Self.warning "%s" str1;
  Format.fprintf fmt "%s@." str2

let addGlobal fmt vi =
  globalDefs := VarinfoSet.add vi !globalDefs

let dumpStorageClass fmt vi ?(isGlobal = false) isFn =
  match vi.vstorage with
  | NoStorage ->
    if not isGlobal then Format.fprintf fmt "auto "
  | Static ->
    Format.fprintf fmt "static "
  | Register ->
    regWarn fmt
  | Extern ->
    if not(isFn) then (
      extWarn fmt
    )

(*************************************************************************)
(* Main part of mc                                                       *)
(*************************************************************************)
(*
 * The type mappings here assume that ANSI-C 99, Frama-C and the CEGAR
 * backend tools are consistent - e.g., an int in the 3 are the same
 * (including bitwidth).
 * The mappings are based on the SATABS user's manual, and have not
 * been otherwise tested in any rigorous manner.
 *
 * All unsupported types return a string that is guaranteed to start
 * with "MC".
 *
 * Only some combinations of types are supported, since its unlikely
 * that a model checker can handle anything else anyway. In
 * particular, composiite and pointer types make major constraints on
 * the base type. This also means that we don't follow the full
 * official C grammar for declarations.
 *
 * Note that we map bools to an int. This means that ACSL contracts
 * for now have to use 0 or 1 instead of /true or /false.
*)

let unparsableString = "MC_UNPARSABLE_STRING;"

let rec nondetVarDecl typ =
  match typ with
  | TInt (IBool,[]) -> "bool";
  | TInt (IChar,[]) -> "char";
  | TInt (ISChar,[]) -> "schar";
  | TInt (IUChar,[]) -> "uchar";
  | TInt (IInt,[]) -> "int";
  | TInt (IUInt,[]) -> "uint";
  | TInt (IShort,[]) -> "short";
  | TInt (IUShort,[]) -> "ushort";
  | TInt (ILong,[]) -> "long";
  | TInt (IULong,[]) -> "ulong";
  | TInt (ILongLong,[]) -> "longlong";
  | TInt (IULongLong,[]) -> "ull";
  | TFloat(FFloat,[]) -> "float";
  | TFloat(FDouble,[]) -> "double";
  | TFloat(FLongDouble,[]) -> "longdouble";
  | TPtr(typ2,[]) -> "pointer";
  | TPtr(_,_) ->
    (Self.warning "Type not supported by mc" );
    "MC_UNSUPPORTED_TYPE_PTR ";
  | TArray(typarr,Some size,_,[]) ->
    nondetVarDecl typarr
  | TArray(_,_,_,_) ->
    (Self.warning "Type of array not supported by mc" );
    "MC_UNSUPPORTED_TYPE_ARR ";
  | TComp(comp,_,[]) ->
    (Self.warning "Type of struc not supported by mc" );
    "MC_UNSUPPORTED_TYPE_COMP ";
  | TComp(_,_,_) ->
    (Self.warning "Type of struc not supported by mc" );
    "MC_UNSUPPORTED_TYPE_COMP ";
  | TVoid(_) ->   (* This shouldnt happen *)
    (Self.warning "Void types for data not supported by mc");
    "MC_UNSUPPORTED_TYPE_VOID ";
  | TFun(_,_,_,_) ->
    ""
  | TNamed(_,_) ->
    (Self.warning "Named types not supported by mc");
    "MC_UNSUPPORTED_TYPE_NAMED ";
    (* Commented out so that catchall case parses
       | TEnum(_,_) ->
       (Self.warning "Enumerated types not supported by mc");
       "MC_UNSUPPORTED_TYPE_ENUM ";
    *)
  | _ ->
    (Self.warning "Type (or type attribute) not supported by mc");
    "MC_UNSUPPORTED_TYPE_OTHER "

let rec dumpFormals = function
  | [] -> ""
  | (str, typ, _)::t ->
    let returnStr = (varDecl (Cil.unrollType typ) str) in
    let returnStr2 = match t with
      | [] -> returnStr
      | h::t -> returnStr ^ ", " in
    returnStr2 ^ dumpFormals t

and
  varDecl typ vname =
  match typ with
  | TInt (IBool,[]) -> "int " ^ vname;
  | TInt (IChar,[]) -> "char " ^ vname;
  | TInt (ISChar,[]) -> "signed char " ^ vname;
  | TInt (IUChar,[]) -> "unsigned char " ^ vname;
  | TInt (IInt,[]) -> "int " ^ vname;
  | TInt (IUInt,[]) -> "unsigned int " ^ vname;
  | TInt (IShort,[]) -> "short " ^ vname;
  | TInt (IUShort,[]) -> "unsigned short " ^ vname;
  | TInt (ILong,[]) -> "long " ^ vname;
  | TInt (IULong,[]) -> "unsigned long " ^ vname;
  | TInt (ILongLong,[]) -> "long long " ^ vname;
  | TInt (IULongLong,[]) -> "unsigned long long " ^ vname;
  | TFloat(FFloat,[]) -> "float " ^ vname;
  | TFloat(FDouble,[]) -> "double " ^ vname;
  | TFloat(FLongDouble,[]) -> "long double " ^ vname;
  | TPtr(typ2,[]) ->
    varDecl typ2 ("*" ^ vname)
  | TPtr(_,_) ->
    (Self.warning "Type of %s not supported by mc" vname);
    "MC_UNSUPPORTED_TYPE_PTR " ^ vname;
  | TArray(typarr,Some size,_,[]) ->
    varDecl typarr
      (vname ^ "[" ^
       ((Pretty_utils.to_string Printer.pp_exp) size) ^
       "]");
  | TArray(_,_,_,_) ->
    (Self.warning "Type of %s array not supported by mc" vname);
    "MC_UNSUPPORTED_TYPE_ARR " ^ vname;
  | TComp(comp,_,[]) ->
    (Cil.compFullName comp) ^ " " ^ vname;
  | TComp(_,_,_) ->
    (Self.warning "Type of %s struc not supported by mc" vname);
    "MC_UNSUPPORTED_TYPE_COMP " ^ vname;
  (* Removed warning/error about void types for data not supported 
     by mc, but needs further thought *)
  | TVoid(_) -> "void " ^ vname;
  | TFun(typ2,argList,_,_) ->
    let formalsStr = match argList with
      | None -> ""
      | Some formalsLst -> dumpFormals formalsLst in
    (varDecl typ2 vname) ^ "(" ^ formalsStr ^ ")"
  | TNamed(_,_) ->
    (Self.warning "Named types not supported by mc");
    "MC_UNSUPPORTED_TYPE_NAMED " ^ vname;
    (* Commented out so that catchall case parses
       | TEnum(_,_) ->
       (Self.warning "Enumerated types not supported by mc");
       "MC_UNSUPPORTED_TYPE_ENUM " ^ vname;
    *)
  | _ ->
    (Self.warning "Type (or type attribute) not supported by mc");
    "MC_UNSUPPORTED_TYPE_OTHER "  ^ vname

let dumpExternNondets fmt =
  Format.fprintf fmt "extern int __VERIFIER_nondet_bool();@.";
  Format.fprintf fmt "extern char __VERIFIER_nondet_char();@.";
  Format.fprintf fmt "extern signed char __VERIFIER_nondet_schar();@.";
  Format.fprintf fmt "%s@." ("extern unsigned char " ^
                             "__VERIFIER_nondet_uchar();");
  Format.fprintf fmt "extern int __VERIFIER_nondet_int();@.";
  Format.fprintf fmt "extern unsigned int __VERIFIER_nondet_uint();@.";
  Format.fprintf fmt "extern short __VERIFIER_nondet_short();@.";
  Format.fprintf fmt "%s@." ("extern unsigned short " ^
                             "__VERIFIER_nondet_ushort();");
  Format.fprintf fmt "extern long __VERIFIER_nondet_long();@.";
  Format.fprintf fmt "%s@." ("extern unsigned long " ^
                             "__VERIFIER_nondet_ulong();");
  Format.fprintf fmt "extern long long __VERIFIER_nondet_longlong();@.";
  Format.fprintf fmt "%s@." ("extern unsigned long long " ^
                             "__VERIFIER_nondet_ull();");
  Format.fprintf fmt "extern float __VERIFIER_nondet_float();@.";
  Format.fprintf fmt "extern double __VERIFIER_nondet_double();@.";
  Format.fprintf fmt "%s@." ("extern long double " ^
                             "__VERIFIER_nondet_longdouble();");
  Format.fprintf fmt "extern void * __VERIFIER_nondet_pointer();@.";
  Format.fprintf fmt "@."

let rec uniq = function
  | [] -> []
  | h::t -> h::(uniq (List.filter (fun x -> x<>h) t))

(* Given stmt, return its line number in the source file *)
let getStmtLineNum stmt =
  let loc = Cil_datatype.Stmt.loc stmt in
  let str = ((Pretty_utils.to_string Printer.pp_location) loc) in
  let len = String.length str in
  let numStart = (String.rindex str ':') + 1 in
  let lineNum = String.sub str numStart (len - numStart) in
  int_of_string lineNum

let createEmitter str =
  try (Emitter.create str [Emitter.Property_status] ~correctness:[]
         ~tuning:[])
  with Invalid_argument arg -> mcStmtPrf

let setEmitter str =
  let em = EmitterSet.filter
      ( fun em2 -> ((Emitter.get_name em2) = str) )
      !emitters in
  if ((EmitterSet.cardinal em) = 0) then (
    emitter := createEmitter str;
    emitters := EmitterSet.add !emitter !emitters
  ) else (
    emitter := EmitterSet.choose em
  )

let rec dumpVarinfoList fmt = function
  | [] -> ()
  | h::t ->
    Format.fprintf fmt "@.  ";
    dumpStorageClass fmt h ~isGlobal:false false;
    Format.fprintf fmt "%s;"
      (varDecl (Cil.unrollType h.vtype) h.vname);
    dumpVarinfoList fmt t

(* This dumps nondet globals *)
let dumpNondet fmt =
  VarinfoSet.iter
    (fun vi ->
       Format.fprintf fmt "@.%s = __VERIFIER_nondet_%s();"
         vi.vname
         (nondetVarDecl (Cil.unrollType vi.vtype))
    )
    !globalDefs

(* This does the work of dumpGlobalVars. Any Frama-C-specific functions 
 * will not be dumped.*)
let checkGlobals fmt name =
  Globals.Vars.iter
    (fun vi init ->
       if ((name = vi.vname) && (not (List.mem name !globalsDumped)) && (
           try (Str.search_forward (Str.regexp "Frama_C_") name 0) < 0;
           with Not_found -> true)) then (
         dumpStorageClass fmt vi ~isGlobal:true false;
         Format.fprintf fmt "%s"
           (varDecl (Cil.unrollType vi.vtype) vi.vname);
         (match init.init with
          | Some x ->
            Format.fprintf fmt " = %a;@."
              Printer.pp_init x
          | None ->
            if (Checker.get() = "satabs") then (
              Format.fprintf fmt " = __VERIFIER_nondet_%s();@."
                (nondetVarDecl (Cil.unrollType vi.vtype)))
            else (
              addGlobal fmt vi;
              Format.fprintf fmt ";@."
            )
         );
         globalsDumped := name::!globalsDumped
       )
    )

(* This builds a StringSet from the lvals in lvalsAssignedTo. Note
   that this is not recursive, so the StringSet will not contain any
   lvals that have another lval inside them.
*)
let buildStrSet fmt lvalsAssignedTo p1str p2str =
  let str2 = function
    | (Var(vi),_) -> StringSet.singleton(vi.vname)
    | (Mem(exp),_) ->
      let s = ((Pretty_utils.to_string Printer.pp_exp) exp) in
      StringSet.singleton(s)
  in
  LvalSet.fold (fun lv str -> StringSet.union str (str2 lv)) 
               lvalsAssignedTo StringSet.empty

(*
 * If an assigns clause is missing or contains \nothing or \empty, this
 * will modify the assigns clause to be the subset of variables inside
 * the body (if present) that are assigned to. If there is no body, the
 * proof proceeds using the emitter MC.ind, which assumes independence.
*)
let checkAssigns fmt name b_assigns body assigns fnList : assignstype
    list =
  let str = ref ((Pretty_utils.to_string Printer.pp_assigns)
                   b_assigns) in
  let p1str = "Pointer variables not supported in assigns clauses" in
  let p2str = "MC_UNSUPPORTED ARGUMENT ERROR: Pointer in assigns " ^
              "clause;" in
  match body with
  | Stmt stmt ->
    if (((List.length fnList) > 0) && ((!str = "") || (
        try (Str.search_forward (Str.regexp "\\(\\nothing\\|\\empty\\)")
               !str 0) > -1;
        with Not_found -> false))) then (
      let lvalsAssignedTo = lvalsInStmt stmt true true false in
      let p1str = "Unsupported use case: function pointer or pointer " ^
                  "variable in assigns clause or statement" in
      let p2str = "MC_UNSUPPORTED ARGUMENT ERROR: " ^
                  "Function pointer or pointer " ^
                  "in assigns clause or statement" in
      { name = name; locs = (buildStrSet fmt lvalsAssignedTo p1str p2str) }
      ::assigns
    ) else (
      if (String.contains !str '*') then (warn fmt p1str p2str);
      str := Str.replace_first (Str.regexp "assigns ") "" !str;
      let strlist = Str.split (Str.regexp "[,;]") !str in
      let strset = List.fold_left (fun set elem ->
          StringSet.add (String.trim elem) set) StringSet.empty strlist in
      { name = name; locs = strset }::assigns
    )
  | Blk blk ->
    if ((!str = "") || (
        try (Str.search_forward (Str.regexp "\\(\\nothing\\|\\empty\\)")
               !str 0) > -1;
        with Not_found -> false)) then (
      let lvalsAssignedTo = lvalsInBlock blk true false false in
      { name = name; locs = (buildStrSet fmt lvalsAssignedTo p1str p2str) }
      ::assigns
    ) else (
      if (String.contains !str '*') then (warn fmt p1str p2str);
      str := Str.replace_first (Str.regexp "assigns ") "" !str;
      let strlist = Str.split (Str.regexp "[,;]") !str in
      let strset = List.fold_left (fun set elem ->
          StringSet.add (String.trim elem) set) StringSet.empty strlist in
      { name = name; locs = strset }::assigns
    )
  | NoBody -> (* prove using MC.ind *)
    if ((!emitterName = "MC.context") ||
        (!emitterName = "MC.ind.context"))
    then (emitterName := "MC.ind.context")
    else (emitterName := "MC.ind");
    if not ((!str = "") || (
        try (Str.search_forward (Str.regexp "\\(\\nothing\\|\\empty\\)")
               !str 0) > -1;
        with Not_found -> false))
    then (
      if (String.contains !str '*') then (warn fmt p1str p2str);
      str := Str.replace_first (Str.regexp "assigns ") "" !str;
      let strlist = Str.split (Str.regexp "[,;]") !str in
      let strset = List.fold_left (fun set elem ->
          StringSet.add (String.trim elem) set) StringSet.empty strlist in
      { name = name; locs = strset }::assigns
    )
    else assigns

let addFnList fmt cnt vi : fntype =
  (* Check functions for register/extern *)
  (match vi.vstorage with
   | NoStorage
   | Static -> ()
   | Register ->
     regWarn fmt
   | Extern ->
     let kf = try Globals.Functions.get vi with Not_found ->
       (let str = if ConstrainVals.get() then
            "Declaration of varinfo " ^ vi.vname ^ 
            " not found in sliced program"
          else "given varinfo has no associated kernel function " ^
               "and is not a built-in" in
        raise (MC_Internal_Bug str)) in
     match kf.fundec with
     | Definition _ ->
       extWarn fmt
     | Declaration _ -> ()
  );
  (* Note: function contracts are *not* accessible via Ast.get()! *)
  let kf = Globals.Functions.get vi in
  let funspec = Annotations.funspec kf in
  {count = cnt; vinfo = vi; funspec = funspec}

(*
 * This returns a set of varinfo's corresponding to all array
 * references in lvalSet. Multiple array refs (e.g. a[5] and a[6])
 * only get one element in the list. We are careful to include those
 * arising from references to an array as a whole (e.g., *arr)
*)
let arrayVarsInLvals lvals =
  LvalSet.fold
    (fun lval vis ->
       VarinfoSet.union
         vis
         (match lval with
          | (Var(vi),Index(_,_)) -> VarinfoSet.singleton(vi)
          | (Var(vi),NoOffset) -> (
              (match (Cil.unrollType vi.vtype) with
               | TArray(_,_,_,_) -> VarinfoSet.singleton(vi);
               | _ -> VarinfoSet.empty
              ))
          | _ -> VarinfoSet.empty
         )
    )
    lvals
    VarinfoSet.empty

(*
 * Same for structs/unions. Multiple lvals from a single struct
 * (e.g., x.a, x.b) only get one element in the list.
*)
let structVarsInLvals lvals =
  LvalSet.fold
    (fun lval vis ->
       CompSet.union
         vis
         (match lval with
          | (Var(vi),Field(_,_)) -> CompSet.singleton(vi)
          | (Var(vi),NoOffset) -> (
              (match (Cil.unrollType vi.vtype) with
               | TComp(_,_,_) -> CompSet.singleton(vi);
               | _ -> CompSet.empty
              ))
          | _ -> CompSet.empty
         )
    )
    lvals
    CompSet.empty

(*
 * This populates fnList with the varinfos of each function call in the
 * statement being checked. Multiple function calls to the same function
 * only get one element in the list.
*)
let rec fnCallsInStmt fmt lvalList fnList : fntype list =
  match lvalList with
  | hd :: tl -> (
      match hd with
      | (Var(vi),NoOffset) -> (
          match (Cil.unrollType vi.vtype) with
          | TFun(_,_,_,_) ->
            let x = addFnList fmt 0 vi in
            x :: (fnCallsInStmt fmt tl fnList)
          | _ -> fnCallsInStmt fmt tl fnList
        )
      | _ -> fnCallsInStmt fmt tl fnList
    )
  | [] -> fnList

(*
 * This returns a set of compinfos corresponding to all struct/union
 * references in lvalSet. Multiple lvals corresponding to the same
 * struct/union type (e.g., struct structname a and struct structname
 * b) only get one element in the list.
*)
let structsInLvals fmt lvals =
  let rec checkFields flist =
    match flist with
    | [] -> CompinfoSet.empty
    | field::fields ->
      CompinfoSet.union
        (match field.ftype with
         | TComp(comp,_,_)
         | TPtr(TComp(comp,_,_),_) ->
           (Self.warning "Nested structs/unions not yet supported by mc");
           Format.fprintf fmt
             "@.MC_UNSUPPORTED CONSTRUCT ERROR: Nested TComp;";
           CompinfoSet.empty
         | _ -> CompinfoSet.empty
        )
        (checkFields fields)
  in
  let rec checkExp exp =
    match exp.enode with
    | SizeOf(TPtr(TComp(comp,_,_),_))
    | AlignOf(TPtr(TComp(comp,_,_),_))
    | UnOp(_,_,TPtr(TComp(comp,_,_),_))
    | BinOp(_,_,_,TPtr(TComp(comp,_,_),_))
    | CastE(TPtr(TComp(comp,_,_),_),_) ->
      CompinfoSet.union
        (CompinfoSet.singleton(comp))
        (checkFields comp.cfields)
    | SizeOfE(exp1)
    | AlignOfE(exp1)
    | Info(exp1,_) ->
      checkExp exp1
    | SizeOf(_)
    | AlignOf(_)
    | UnOp(_,_,_)
    | BinOp(_,_,_,_)
    | CastE(_,_)
    | Const(_)
    | Lval(_)
    | SizeOfStr(_)
    | AddrOf(_)
    | StartOf(_) ->
      CompinfoSet.empty
  in
  LvalSet.fold
    (fun lval vis ->
       CompinfoSet.union
         vis
         (match lval with
          | (_,Field(f,_)) ->
            CompinfoSet.union
              (CompinfoSet.singleton(f.fcomp))
              (checkFields f.fcomp.cfields)
          | (Var(vi),NoOffset) -> (
              (match (Cil.unrollType vi.vtype) with
               | TComp(comp,_,_)
               | TPtr(TComp(comp,_,_),_) ->
                 CompinfoSet.union
                   (CompinfoSet.singleton(comp))
                   (checkFields comp.cfields)
               | _ -> CompinfoSet.empty
              ))
          | (Mem(exp),NoOffset) ->
            checkExp exp
          | _ -> CompinfoSet.empty
         )
    )
    lvals
    CompinfoSet.empty


(*
 * This should never be called unless lvalsInStmt is also called, since it
 * does not do error checking for unsupported constructs.
 *)
let rec stmtsInStmt stmt =
  (stmt.sid)::
  (match stmt.skind with
   | Switch(_,blk,_,_)
   | Loop(_,blk,_,_,_)
   | Block(blk) ->
     stmtsInBlock blk

   | If(_,blk1,blk2,_) ->
     (stmtsInBlock blk1) @ (stmtsInBlock blk2)

   | _ -> []
  )

and stmtsInBlock blk =
  stmtsInStmts blk.bstmts

and stmtsInStmts stmts =
  match stmts with
  | [] -> []
  | stmt::stmts ->
    (stmtsInStmt stmt) @ (stmtsInStmts stmts)

(* This returns the destination label of the first goto encountered
   whose target is not _LAND or "" if not found. (_LAND is a label
   specifically generated by Frama-C.) *)
let rec gotoInStmt stmt =
  match stmt.skind with
  | Switch(_,blk,_,_)
  | Loop(_,blk,_,_,_)
  | Block(blk) ->
    gotoInStmts blk.bstmts
  | If(_,blk1,blk2,_) ->
    let str = gotoInStmts blk1.bstmts in
    if str = "" then gotoInStmts blk2.bstmts else str
  | Goto(stmt2,_) ->
    let l = !stmt2.labels in
    let getLabel = function
      | Label(str,_,_) -> str
      | _ -> ""
    in
    if l <> [] then
      let label = getLabel (List.hd l) in
      if label = "_LAND" then "" else label
    else
      raise (MC_Internal_Bug "Goto stmt with no label")
  | _ -> ""

and gotoInStmts = function
  | [] -> ""
  | stmt::stmts ->
    let str = gotoInStmt stmt in
    if str = "" then gotoInStmts stmts else str

(*
 * This returns the value of lval in state, as follows:
 *   IntPoints(number of points, list of values)
 *     at most maxpts integral values
 *   IntInterval(minInt,maxInt,r,modu)
 *     integral with min/max determinable, congruent to r modulo modu
 *   Int{Left,Right}Interval(boundInt)
 *     integral half interval
 *   RealInterval(minReal,maxReal)
 *   NoInfo
 *     else (including non-integral types)
 * Note that the values are a conservative guess based on value
 * analysis.
 *
 * The current implementation is very ugly since it basically handles
 * everything we can't handle as an exception and returns NoInfo for
 * these cases.
 *
 * TODO:
 *   This should be rewritten to handle any low-entropy set if/when
 *     ival/equivalent gets an API. Or see value/state_imp.mli to
 *     improve right now.
 *   Rewrite so that array and struct variables are supported. Currently
 *    it appears that this would involve calling Db.Value.eval_lval and
 *    Db.Value.eval_expr at different states inside stmt as opposed to
 *    just the state before entering stmt.
 *  Pointers aren't handled right now. This needs to be rethought based
 *    on what the CEGAR checkers can do.  NULL vs nonNULL only?
*)

type valType =
  | IntPoints of int * int list
  | IntLeftInterval of int    (* useful only if there are cases where *)
  | IntRightInterval of int   (* value generates this                 *)
  | IntInterval of int * int * int * int
  | RealInterval of float * float
  | NoInfo

let rec intervalToList min max =
  if (min>max) then []
  else min :: (intervalToList (min + 1) max)

let getValReal vals maxpts =
  (try
     let iv = (Cvalue.V.project_ival vals) in
     let (min_and_max,_) = Ival.min_and_max_float iv in
     match min_and_max with
     | Some (min,max) ->
       RealInterval(Fval.F.to_float min,Fval.F.to_float max)
     | None ->
       NoInfo
   with
   | _ -> NoInfo
  )

let getValInt vals maxpts =
  (try
     let iv = (Cvalue.V.project_ival vals) in
     if (Ival.cardinal_is_less_than iv (maxpts+1)) then
       let intvals =
         List.map (fun x -> Int.to_int (Ival.project_int x))
           (Ival.fold_enum (fun x y -> x:: y) iv [])
       in IntPoints((List.length intvals), intvals)
     else
       let min, max, r, modu = Ival.min_max_r_mod iv in
       (match min,max with
        | Some m,Some n ->
          IntInterval((Int.to_int m),(Int.to_int n), (Int.to_int r),
                      (Int.to_int modu))
        | None, Some n ->
          IntRightInterval(Int.to_int n)
        | Some n, None ->
          IntLeftInterval(Int.to_int n)
        | _ ->
          NoInfo
       )
   with
   | _ -> NoInfo
  )

(*
  This relies on the type being public. It will become private
  at some point (see kernel_services/abstract_interp/locations.mli)
*)
let getVal vals maxpts =
  match vals with
  | Map m ->
    let intVal = getValInt vals maxpts in
    if (intVal != NoInfo) then intVal
    else getValReal vals maxpts
  | Top(_,_) -> NoInfo


let getExprVals state expr maxpts =
  getVal (!Db.Value.eval_expr
            ~with_alarms:CilE.warn_none_mode state expr)
    maxpts

let getLvalVals state lval maxpts =
  getVal
    (snd (!Db.Value.eval_lval
            ~with_alarms:CilE.warn_none_mode None state lval))
    maxpts

let getAfterVals stmt lval maxpts =
  let kinstr = Kstmt stmt in (* make a kinstr from a stmt *)
  let valTypeLst = Db.Value.fold_state_callstack (fun state acc -> (
        (* for each state in the callstack *)
        getVal
          (snd (!Db.Value.eval_lval
                  ~with_alarms:CilE.warn_none_mode None state lval))
          maxpts
      )::acc
    ) [] ~after:true kinstr in
  List.hd valTypeLst

let changeEmitter () =
  if ((!emitterName = "MC.ind") ||
      (!emitterName = "MC.ind.context"))
  then (emitterName := "MC.ind.context")
  else emitterName := "MC.context"

(*
 * This shouldn't be called directly since it relies on checks by
 * dumpVarDecls
*)
let dumpVarInitVal ui fmt stmt lval maxpts contextStr isAfter =
  let lvalstr = ((Pretty_utils.to_string Printer.pp_lval) lval) in
  let state = if isAfter then getAfterVals stmt lval maxpts
    else getLvalVals (Db.Value.get_stmt_state stmt) lval maxpts in
  let isInt = match fst lval with
    | Var vi ->
      (match vi.vtype with
       | TInt(IInt,_) -> true
       | _ -> false
      )
    | _ -> false
  in
  let isUInt = match fst lval with
    | Var vi ->
      (match vi.vtype with
       | TInt(IUInt,_) -> true
       | _ -> false
      )
    | _ -> false
  in
  let isDbl = match fst lval with
    | Var vi ->
      (match vi.vtype with
       | TFloat(FDouble,_) -> true
       | _ -> false
      )
    | _ -> false
  in
  match state with
  | IntPoints(num,pts) ->
    if (num==1) then (
      Format.fprintf fmt "%s = %d;@." lvalstr (List.hd pts);
    )
    else begin
      Format.fprintf fmt "__VERIFIER_assume((%s==%d)"
        lvalstr (List.hd pts);
      List.iter
        (fun n ->
           Format.fprintf fmt "@.                 || (%s==%d)"
             lvalstr n)
        (List.tl pts);
      Format.fprintf fmt ");@."
    end;
    changeEmitter ()
  | IntInterval(min, max, r, modu) ->
    (* Do not dump assume for ints if lower bound is min_int or upper
       bound is max_int or for unsigned ints if lower bound is 0 or
       upper bound is 2 * max_int + 1 *)
    let notMinInt = min <> (Int32.to_int Int32.min_int) in
    let notMaxInt = max <> (Int32.to_int Int32.max_int) in
    let notMinUInt = min <> 0 in
    let notMaxUInt = max <> 2 * (Int32.to_int Int32.max_int) + 1 in
    let checkLowerBound = isInt && notMinInt || isUInt && notMinUInt in
    if checkLowerBound then
      Format.fprintf fmt "__VERIFIER_assume(%s >= %d);@."
        lvalstr min;
    let checkUpperBound = isInt && notMaxInt || isUInt && notMaxUInt in
    if checkUpperBound then
      Format.fprintf fmt "__VERIFIER_assume(%s <= %d);@."
        lvalstr max;
    if modu <> 1 then
      Format.fprintf fmt "__VERIFIER_assume(%s %% %d == %d);@."
        lvalstr modu r;
    if checkLowerBound || checkUpperBound then changeEmitter ()
  | IntLeftInterval(max) ->
    let notMaxInt = max <> (Int32.to_int Int32.max_int) in
    let checkInt = isInt && notMaxInt in
    let notMaxUInt = max <> 2 * (Int32.to_int Int32.max_int) + 1 in
    let checkUInt = isUInt && notMaxUInt in
    if checkInt || checkUInt then (
      Format.fprintf fmt "__VERIFIER_assume(%s <= %d);@."
        lvalstr max;
      changeEmitter ()
    )
  | IntRightInterval(min) ->
    let notMinInt = min <> (Int32.to_int Int32.min_int) in
    let checkInt = isInt && notMinInt in
    let notMinUInt = min <> 0 in
    let checkUInt = isUInt && notMinUInt in
    if checkInt || checkUInt then (
      Format.fprintf fmt "__VERIFIER_assume(%s >= %d);@."
        lvalstr min;
      changeEmitter ()
    )
  | RealInterval(min,max) ->
    if (min = max) then (
      Format.fprintf fmt "__VERIFIER_assume(%s == %f);@."
        lvalstr min;
      changeEmitter ()
    )
    else begin
      let maxDbl = 179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368. in
      let notMinDbl = min <> -.maxDbl in
      let notMaxDbl = max <> maxDbl in
      let checkLowerBound = isDbl && notMinDbl in
      if checkLowerBound then
        Format.fprintf fmt "__VERIFIER_assume(%s >= %g);@."
          lvalstr min;
      let checkUpperBound = isDbl && notMaxDbl in
      if checkUpperBound then
        Format.fprintf fmt "__VERIFIER_assume(%s <= %g);@."
          lvalstr max;
      if checkLowerBound || checkUpperBound then changeEmitter ()
    end;
  | NoInfo -> ()

(* Slice on assertions of stmt's function *)
let sliceAssert stmt =
  let name = "sliced program" in
  Slicing.Api.Project.reset_slicing ();
  let kf = Kernel_function.find_englobing_kf stmt in
  let sel = Slicing.Api.Select.select_func_annots
      Slicing.Api.Select.empty_selects
      (Slicing.Api.Mark.make ~addr:true ~ctrl:true ~data:true)
      ~threat:false ~user_assert:true ~slicing_pragma:false ~loop_inv:false
      ~loop_var:false ~spare:false kf
  in
  Slicing.Api.Request.add_persistent_selection sel;
  Slicing.Api.Request.apply_all_internal ();
  Slicing.Api.Slice.remove_uncalled ();
  let extracted_prj = Slicing.Api.Project.extract name in
  extracted_prj

(*
 * This dumps struct/union definitions. For each lval that is a
 * struct/union, it dumps its name, then each field is passed as an
 * argument to varDecl, making sure that unsupported types are caught.
*)
let dumpStructDefs fmt compinfoSet =
  CompinfoSet.iter
    (fun comp ->
       Format.fprintf fmt "%s {@."
         (Cil.compFullName comp);
       List.iter
         (fun f ->
            Format.fprintf fmt "  %s;@."
              (varDecl (Cil.unrollType f.ftype) f.fname)
         )
         comp.cfields;
       Format.fprintf fmt "};@."
    )
    compinfoSet

(*
 * Only arrays that meet all of the following conditions are
 * supported:
 * - Dimension/s are [exactly] determinable. For variable-size arrays
 *   (supported by C-99 for the 1st dimension), we might want to use
 *   value analysis to determine the size. But CIL converts such
 *   arrays to pointers anyway, so this is deferred for now.
*)
let dumpArrayDecls ui fmt arrVarSet =
  VarinfoSet.iter
    (fun vi ->
       dumpStorageClass fmt vi false;
       Format.fprintf fmt "%s;@."
         (varDecl (Cil.unrollType vi.vtype) vi.vname)
    )
    arrVarSet

(*
 * Same for structs/unions.
*)
let dumpStructDecls ui fmt structVarSet =
  CompSet.iter
    (fun vi ->
       dumpStorageClass fmt vi false;
       Format.fprintf fmt "%s;@."
         (varDecl (Cil.unrollType vi.vtype) vi.vname)
    )
    structVarSet

(* This adds a given list of annotations to stmt inside kernel function kf *)
let rec addAnnots kf stmt = function
  | [] -> ()
  | h::t ->
    Annotations.add_code_annot !emitter ~kf:kf stmt h;
    addAnnots kf stmt t

(* This inserts a no op before and after the loop with the given sid. *)
class insert_stmt fmt sid = object(self)
  inherit Visitor.frama_c_inplace

  val my_local_counts = Stack.create ()

  method vblock b =
    let rec matchLoop = function
      | [] -> false
      | h::t ->
        (match h.skind with
         | Loop(_) ->
           if h.sid = sid then true else matchLoop t
         | _ -> matchLoop t
        ) in
    if matchLoop b.bstmts then
      let loc = Cil_datatype.Location.unknown in
      let n = Stack.length my_local_counts in
      let v =
        Cil.makeLocalVar (Extlib.the self#current_func) ~scope:b
          ("CMC" ^ string_of_int n) Cil.intType
      in
      Stack.push v my_local_counts;
      ChangeDoChildrenPost
        (b,
         fun b ->
           ignore (Stack.pop my_local_counts);
           b.bstmts <-
             if ConstrainVals.get() then (
               let stmt1 = Cil.mkStmt
                   (Instr (Set (Cil.var v,Cil.zero ~loc,loc))) in
               let stmt2 = Cil.mkStmt
                   (Instr (Set (Cil.var v,Cil.zero ~loc,loc))) in
               let rec insertAfterLoop stmt = function
                 | [] -> [stmt]
                 | h::t ->
                   match h.skind with
                   | Loop _ ->
                     h :: stmt :: t
                   | _ ->
                     h :: insertAfterLoop stmt t
               in
               stmt1 :: insertAfterLoop stmt2 b.bstmts
             ) else
               Cil.mkStmt (Instr (Set (Cil.var v,Cil.zero ~loc,loc))) ::
               b.bstmts;
           b)
    else DoChildren
end

(* If sid is the first statement in a loop body, this inserts a no op after the
   last statement in the loop body.
*)
class insert_stmt_loop_body_end fmt sid = object(self)
  inherit Visitor.frama_c_inplace

  val my_local_counts = Stack.create ()

  method vblock b =
    if (List.length b.bstmts) > 0 && (List.hd b.bstmts).sid = sid then
      let loc = Cil_datatype.Location.unknown in
      let n = Stack.length my_local_counts in
      let v =
        Cil.makeLocalVar (Extlib.the self#current_func) ~scope:b
          ("CMC" ^ string_of_int n) Cil.intType
      in
      Stack.push v my_local_counts;
      ChangeDoChildrenPost
        (b,
         fun b ->
           ignore (Stack.pop my_local_counts);
           b.bstmts <-
             b.bstmts @
             Cil.mkStmt (Instr (Set (Cil.var v,Cil.zero ~loc,loc))) :: [];
           b)
    else DoChildren
end

(* This inserts a new statement with location oldloc before the
   statement with the given sid *)
class insert_assert sid oldloc = object(self)
  inherit Visitor.frama_c_inplace
  method vblock b =
    let rec matchSid = function
      | [] -> false
      | h::t ->
        if h.sid = sid then true else matchSid t
    in
    if matchSid b.bstmts then
      let loc = Cil_datatype.Location.unknown in
      let newStmt = Cil.mkStmt (Instr (Skip oldloc)) in
      let rec insert newStmt = function
        | [] -> [newStmt]
        | h::t ->
          if h.sid = sid then newStmt :: h :: t else h :: insert newStmt t in
      let newb = insert newStmt b.bstmts in
      ChangeDoChildrenPost
        (b,
         fun b ->
           b.bstmts <-
             newb;
           b)
    else DoChildren
end

(* This returns the function body containing stmt.
*)
let getFnBlk stmt =
  let kf = Kernel_function.find_englobing_kf stmt in
  match kf.fundec with
  | Definition(fundec2,_) -> fundec2.sbody
  | Declaration _ ->
    let str = "Function body not found" in
    raise (MC_Internal_Bug str)

let rec dumpVarDecls ui fmt origStmt stmt lvals oldprj prj isFirstCall isAfter
    sid insertStmtArr matchGotoLabel =
  let contextStr = ref "" in
  if isFirstCall then (
    if Diagnostics.get() then (
      Format.fprintf fmt "//@.// Number of lvals: %d@."
        (LvalSet.cardinal lvals);
      LvalSet.iter
        (fun lval ->
           Format.fprintf fmt "//   ";
           Printer.pp_lval fmt lval;
           Format.fprintf fmt ": ";
           Printer.pp_typ fmt (Cil.typeOfLval lval);
           Format.fprintf fmt "@.//      ";
           Printer.pp_typ fmt (Cil.unrollType (Cil.typeOfLval lval));
           Format.fprintf fmt "@."
        )
        lvals;
      Format.fprintf fmt "//@.";
    );
    let llvals =
      LvalSet.filter
        (fun lval ->
           let name = ref ((Pretty_utils.to_string Printer.pp_lval) lval)
           in
           let len = try (String.index !name '.') with Not_found -> -1 in
           if (len >= 1) then name := (try (String.sub !name 0 len)
                                       with Invalid_argument _ -> !name);
           not (List.mem !name !globalsDumped)
        )
        lvals in
    dumpArrayDecls ui fmt (arrayVarsInLvals llvals);
    dumpStructDecls ui fmt (structVarsInLvals llvals);
    if (Checker.get() = "cpa") then dumpNondet fmt;
    Format.fprintf fmt "@."
  );
  (* If context is enabled and statement starts with a loop, Eva gets the value
     after the loop condition, not before. As a workaround, insert a no op
     immediately before the loop, then in the call to Eva, get the value after
     the inserted statement.
     Eva also does not get the correct value at the end of the loop body or at
     the end of the loop, so another no op is inserted after the last statement
     in the loop body and after the loop.
  *)
  let rec addNoop = function
    | [] -> ()
    | h::t ->
      match h.skind with
      | Loop(_,blk,_,_,_) ->
        let kf = Kernel_function.find_englobing_kf h in
        ignore (Visitor.visitFramacKf (new insert_stmt fmt h.sid) kf);
        if ConstrainVals.get() then (
          let loop = List.hd blk.bstmts in
          let loopHead = match loop.skind with
            | Block(blk2) ->
              List.hd blk2.bstmts
            | _ -> loop
          in
          ignore (Visitor.visitFramacKf
                    (new insert_stmt_loop_body_end fmt loopHead.sid) kf)
        );
        (* Note: calling Ast.get() here, which is a possible effiency issue *)
        Cfg.clearFileCFG ~clear_id:false (Ast.get());
        Cfg.computeFileCFG (Ast.get())
      | _ ->
        addNoop h.succs
  in
  if isFirstCall && (Context.get() || ConstrainVals.get()) 
    then addNoop stmt.succs;
  let targetStmt =
    if ConstrainVals.get() then (
      let sblk = getFnBlk stmt in
      let rec findLoop = function
        | [] ->
          let str = "ConstrainVals flag enabled, but statement is not a loop" in
          raise (MC_Unsupported_Construct str)
        | h::t ->
          (match h.skind with
           | Loop(_,blk,_,_,_) ->
             if sid = insertStmtArr.(3) then (
               let loopBlk = (List.nth blk.bstmts
                                ((List.length blk.bstmts) - 1)) in (
                 match loopBlk.skind with
                 | Block(blk2) ->
                   List.nth blk2.bstmts ((List.length blk2.bstmts) - 1)
                 | _ -> loopBlk
               )
             ) else if sid = insertStmtArr.(1) then (
               if t <> [] then
                 if insertStmtArr.(1) <> insertStmtArr.(4) && matchGotoLabel
                 then List.hd (List.tl t)
                 else List.hd t
               else
                 let str = "Unable to find no op (targetStmt findLoop)" in
                 raise (MC_Internal_Bug str)
             ) else stmt
           | _ -> findLoop t
          )
      in
      let rec findStmt = function
        | [] -> Cil.mkStmt (Instr (Skip (Cil_datatype.Location.unknown)))
        | h::t ->
          match h.skind with
          | Block(b) ->
            if h.sid = origStmt.sid then findLoop b.bstmts
            else
              let bStmt = findStmt b.bstmts in
              if bStmt.sid = -1 then findStmt t else bStmt
          | _ ->
            findStmt t in
      let findStmtResult = findStmt sblk.bstmts in
      if findStmtResult.sid = -1 then stmt else findStmtResult
    ) else stmt
  in
  let rec dumpContext = (fun lval ->
      if Context.get() || ConstrainVals.get() then (
        if Db.Value.is_computed () then (
          match lval with
          | (Var(vi),Index(_,_)) -> (
              match vi.vtype with
              | TArray(t,e,b,a) ->
                let str = "// Array detected. Dumping all initialized array " ^
                          "values:" in
                Format.fprintf fmt "@.%s@." str;
                let len = Cil.lenOfArray e in
                let rec loc_rec acc max =
                  if acc < max then (
                    let inc = Cil.increm
                        (Cil.zero Cil_datatype.Location.unknown) acc in
                    let new_offset = (Index(inc, NoOffset)) in
                    let lval2 = (Var vi, new_offset) in
                    dumpVarInitVal ui fmt targetStmt lval2 (MaxContext.get())
                      contextStr isAfter;
                    loc_rec (acc + 1) max
                  ) in
                loc_rec 0 len
              | _ -> dumpVarInitVal ui fmt targetStmt lval (MaxContext.get())
                       contextStr isAfter
            )
          | _ ->
            dumpVarInitVal ui fmt targetStmt lval (MaxContext.get())
              contextStr isAfter
        ) else (
          !Db.Value.compute (); (* Run Eva *)
          dumpContext lval
        )
      )
    ) in
  Format.fprintf fmt "@.";
  LvalSet.iter
    (fun lval -> match lval with
       | (Var(var),NoOffset) ->
         (* dont print composites that appear as a whole, eg "*arr" *)
         (match (Cil.unrollType var.vtype) with
          | TArray(_,_,_,_) -> ();
          | TComp(_,_,_) -> ();
          | TFun(_,_,_,_) -> ();
          | _ ->
            if not (List.mem ((Pretty_utils.to_string Printer.pp_lval) lval)
                      !globalsDumped) &&
               not (List.mem var.vid !local_init) &&
               isFirstCall
            then (
              dumpStorageClass fmt var false;
              Format.fprintf fmt "%s;@."
                (varDecl (Cil.unrollType var.vtype) var.vname);
            )
         );
         dumpContext lval;
       | (Var(var),Field(fi,offset)) ->
         (* struct/union declaration already output above *)
         dumpContext lval;
       | (Var(var),Index(exp,offset)) ->
         (* array declaration already output above *)
         dumpContext lval;
       | (Mem(expr),_) ->
         (* ptr decl already output since lvals has vars in expr/offset *)
         dumpContext lval;
    )
    lvals

(* Output identified predicate after converting from frama-c to C
 * format, issuing exception if not supported by C assertions (thus,
 * the CEGAR checker) .
 *
 * For now, we simply output an identified predicate with limited
 * checking to see that the construct is supported by the cegar
 * checker (since it will just produce a parse error and be unable to
 * prove the predicate in that case). In particular, all terms aren't
 * checked.
 * EDIT: Terms are now checked.
*)
let rec legalIdentPred ip =
  legalPred ip.ip_content.pred_content

and legalLogicLabel label =
  match label with
  | Old
  | Here
  | Pre
  | Post
    -> true
  | LoopCurrent
  | LoopEntry
  | _ (* C labels and ghost labels are not yet supported *)
    -> false

and legalLogic logic =
  match logic with
  | BuiltinLabel(label)
    -> legalLogicLabel(label)
  | FormalLabel(_)
  | StmtLabel(_)
    -> false

and legalQuant logic_var =
  match logic_var with
  | [] -> true
  | h::t -> (
      match h.lv_kind with
      | LVQuant -> true
      | _ -> false
    ) && legalQuant t

and legalTerm t =
  match t.term_node with
  | Tat(t1,logic)
    -> (legalTerm t1) && (legalLogic logic)
  | TConst(_)
  | TLval(_)
  | TSizeOf(_)
  | TSizeOfStr(_)
  | TAlignOf(_)
  | TAddrOf(_)
  | TStartOf(_)
  | Tapp(_,_,_)
  | TDataCons(_,_)
  | Tnull
  | Ttype(_)
  | Tempty_set
  | Tunion(_)
  | Tinter(_)
  | Trange(_,_)
    -> true
  | TSizeOfE(t1)
  | TAlignOfE(t1)
  | TUnOp(_,t1)
  | TCastE(_,t1)
  | Tlambda(_,t1)
  | Tbase_addr(_,t1)
  | Toffset(_,t1)
  | Tblock_length(_,t1)
  | TLogic_coerce(_,t1)
  | Ttypeof(t1)
  | Tcomprehension(t1,_,_)
  | Tlet(_,t1)
    -> (legalTerm t1)
  | TBinOp(_,t1,t2)
  | TUpdate(t1,_,t2)
    -> (legalTerm t1) && (legalTerm t2)
  | Tif(t1,t2,t3)
    -> (legalTerm t1) && (legalTerm t2) && (legalTerm t3)

and legalPred pred =
  match pred with
  | Prel(_,t1,t2)
    -> (legalTerm t1) && (legalTerm t2)
  | Pnot(np)
  | Pat(np,_)
    -> (legalPred np.pred_content)
  | Pand(np1,np2)
  | Por(np1,np2)
  | Pimplies(np1,np2)
    -> (legalPred np1.pred_content) && (legalPred np2.pred_content)
  | Pif(t,np1,np2)
    -> (legalTerm t) && (legalPred np1.pred_content) &&
       (legalPred np2.pred_content)
  | Pforall(q,np)
    -> (legalQuant q) && (legalPred np.pred_content)
  | Pfalse
  | Ptrue
  | Papp(_,_,_)
  | Pseparated(_)
  | Plet(_,_)
  | Pexists(_,_)
  | Pvalid_read(_,_)
  | Pvalid(_,_)
  | Pinitialized(_,_)
  | Pallocable(_,_)
  | Pfreeable(_,_)
  | Pxor(_,_)
  | Piff(_,_)
  | Pfresh(_,_,_,_)
  (* Handled using catch all case since Fluorine/Neon have just
   * Psubtype(_,_), but Sodium also has Pdangling.
  *)
  | _ ->
    false

(* This reads all the term_lvals in a given contract. It returns an
   LvalSet that is the set of all lvals such that an lval in lvalsInFn
   is of a C variable that matches the corresponding C variable on
   which a term_lval that is a logic variable is based. If the
   constrainVals flag is enabled, the variable names and locations
   must match. 
*) 
let lvalsInContract lvalsInFn = function
  | Bhv bhv ->
    let rec getTLvals = function
      | [] -> TLvalSet.empty
      | h::t ->
        TLvalSet.union (tlvalsInPred h.ip_content.pred_content) (getTLvals t)
    in
    let tlvalsPre = getTLvals bhv.b_requires in
    let rec get_b_post_cond_ip = function
      | [] -> []
      | h::t -> snd h :: get_b_post_cond_ip t
    in
    let b_post_cond_ip = get_b_post_cond_ip bhv.b_post_cond in
    let allTLvals = TLvalSet.union tlvalsPre (getTLvals b_post_cond_ip) in
    let tlvalLst = TLvalSet.elements allTLvals in
    let lvalLst = LvalSet.elements lvalsInFn in
    let rec lvals = function
      | [] -> LvalSet.empty
      | h::t ->
        let viTLval = match fst h with
          | TVar lv -> lv.lv_origin
          | _ -> None
        in
        let rec matchLval = function
          | [] -> LvalSet.empty
          | h2::t2 ->
            (match fst h2 with
             | Var vi ->
               (match viTLval with
                | Some vi2 ->
                  if vi2.vid == vi.vid ||
                     ConstrainVals.get() && vi2.vname = vi.vname &&
                     vi2.vdecl = vi.vdecl
                  then LvalSet.singleton(h2)
                  else matchLval t2
                | None -> matchLval t2
               )
             | _ -> matchLval t2
            )
        in LvalSet.union (matchLval lvalLst) (lvals t)
    in lvals tlvalLst
  | Pred pred ->
    LvalSet.empty

(* Helper function for checkPreOrPost. *)
let checkPreOrPost2 fmt tlvals =
  TLvalSet.iter
    (fun tlval ->
       let name = ref ((Pretty_utils.to_string Printer.pp_term_lval)
                         tlval) in
       checkGlobals fmt !name
    )
    tlvals

(* This checks pre- or post-conditions for globals. *)
let checkPreOrPost fmt ip oldprj prj =
  let vis =
    object
      inherit Visitor.frama_c_copy prj
      method vterm t =
        checkPreOrPost2 fmt (tlvalsInTerm t);
        Cil.DoChildren
      method vpredicate p =
        checkPreOrPost2 fmt (tlvalsInPred p.pred_content);
        Cil.DoChildren
    end
  in
  if (legalIdentPred ip) then (
    ignore (Visitor.visitFramacIdPredicate vis ip)
  ) else (
    Format.fprintf fmt "1==2";
    Self.warning "Unsupported annotation predicate (not checked)"
  )

(* This checks all clauses for globals. *)
let checkClauses fmt name bhv body assignsarg fnList oldprj prj lvals :
  assignstype list =
  List.iter
    (fun req -> checkPreOrPost fmt req oldprj prj)
    bhv.b_requires;
  let assigns : assignstype list =
    checkAssigns fmt name bhv.b_assigns body assignsarg fnList
  in
  let p1str = "Unsupported use case: function pointer or pointer variable in"
              ^ " assigns clause or statement" in
  let p2str = "MC_UNSUPPORTED ARGUMENT ERROR: Function pointer or pointer in"
              ^ " assigns clause or statement" in
  let strset = buildStrSet fmt lvals p1str p2str in
  StringSet.iter
    (fun str ->
       checkGlobals fmt str
    )
    strset;
  List.iter
    (fun post ->
       checkPreOrPost fmt (snd post) oldprj prj)
    bhv.b_post_cond;
  assigns

(* Checks function contracts of functions called from stmt for globals. *)
let rec checkFnClauses fmt fnList oldprj prj lvals : assignstype list =
  match fnList with
  | fn :: tl -> (
      match fn.vinfo.vtype with
      | TFun(typ,_,_,_) -> (
          let kf = Globals.Functions.get fn.vinfo in
          match fn.funspec.spec_behavior with
          | [] ->
            let hd = match kf.fundec with
              | Definition(fundec2,_) ->
                let lvalsAssignedTo =
                  lvalsInBlock fundec2.sbody true false false in
                let p1str = "Unsupported use of pointers" in
                let p2str = "MC_UNSUPPORTED CONSTRUCT ERROR: " ^ p1str in
                let strset = buildStrSet fmt lvalsAssignedTo p1str p2str in
                { name = fn.vinfo.vname; locs = strset }::[]
              | Declaration _ ->
                Self.warning "No function contract or body";
                Format.fprintf fmt "@.MC_ERROR: No function contract or body;";
                Format.fprintf fmt "@.";
                [] in
            if (hd==[]) then (checkFnClauses fmt tl oldprj prj lvals)
            else (hd @ (checkFnClauses fmt tl oldprj prj lvals))
          | [bhv] -> (* Check requires, assigns and ensures clauses *)
            (* Skip any Frama-C-specific functions *)
            if try Str.search_forward (Str.regexp "Frama_C_")
                     fn.vinfo.vname 0 < 0
              with Not_found -> true then (
              let body : stmtorblock =
                match kf.fundec with
                | Definition(fundec2,_) ->
                  Blk fundec2.sbody
                | Declaration(_,vi,_,_) ->
                  NoBody
              in
              let hd = checkClauses fmt fn.vinfo.vname bhv body [] fnList
                  oldprj prj lvals in
              if (hd==[]) then (checkFnClauses fmt tl oldprj prj lvals)
              else (hd @ (checkFnClauses fmt tl oldprj prj lvals))
            ) else checkFnClauses fmt tl oldprj prj lvals
          | _ ->
            raise (MC_Unsupported_Construct
                     "Multiple behaviors not supported")
        )
      | _ -> checkFnClauses fmt tl oldprj prj lvals
    )
  | [] -> []

(*
 * This checks the variables of the contracts of stmt and those of each
 * function called from stmt against all global declarations/
 * definitions. If there is a match, the declaration/definition is
 * printed to the output file.
 * This also calls checkClauses and checkFnClauses. Those functions
 * populate "assigns", which is an assignstype data structure. This
 * structure holds each variable assigned to for stmt and each function
 * called by stmt. checkClauses and checkFnClauses read assigns clauses,
 * and if that clause is missing, those functions determine which
 * variables are assigned to and populate "assigns" accordingly.
 *)
let dumpGlobalVars fmt ca stmt assigns fnList oldprj prj lvals : assignstype
    list =
  (* Check stmt contract *)
  let assigns2 : assignstype list =
    (match ca.annot_content with
     | AStmtSpec([],spec) ->
       (match spec.spec_behavior with
        | [bhv] ->
          checkClauses fmt "CMCstmt" bhv (Stmt stmt) assigns fnList
            oldprj prj lvals
        | _ ->
          raise (MC_Unsupported_Construct
                   "Multiple behaviors not supported")
       )
     | _ -> assigns
    ) in
  (* Iterate over function contracts of functions called from stmt *)
  let assigns3 : assignstype list = (
    checkFnClauses fmt fnList oldprj prj lvals
  ) @ assigns2 in
  assigns3

(* This modifies the default printer to handle Here labels inside \at.
 * Method for changing printers changed in Aluminum.
*)
module PrintHere (X: PrinterClass) = struct
  class printer : Printer.extensible_printer = object(self)
    inherit X.printer as super
    (* Override the standard methods *)
    val isHere = ref false;
    method term_node fmt t =
      match t.term_node with
      | Tat(t1,(BuiltinLabel(Here)))
      | Tat(t1,(BuiltinLabel(Pre))) ->
        super#term_node fmt t1
      | _ ->
        super#term_node fmt t
    method predicate fmt p =
      match p.pred_content with
      | Pat(pn,(BuiltinLabel(Here)))
      | Pat(pn,(BuiltinLabel(Pre))) ->
        super#predicate fmt pn
      | _ ->
        super#predicate fmt p
  end
end

module PrintDefault (X: Printer.PrinterClass) = struct
  class printer : Printer.extensible_printer = object(self)
    inherit X.printer as super
  end
end

let dumpStmtIdentPred fmt ip =
  if (legalIdentPred ip) then (
    Printer.update_printer
      (module PrintHere: Printer.PrinterExtension);
    Kernel.Unicode.without_unicode
      (fun () -> Printer.pp_predicate fmt ip.ip_content) ();
    (* Important: return printer to default behavior! *)
    Printer.update_printer
      (module PrintDefault: Printer.PrinterExtension);
  ) else (
    Format.fprintf fmt "1==2";
    Self.warning "Unsupported annotation predicate (not checked)"
  )

(* Output a requires clause *)
let dumpStmtReq fmt req =
  Format.fprintf fmt "__VERIFIER_assume(";
  dumpStmtIdentPred fmt req;
  Format.fprintf fmt ");@."

(* Functions to handle \old expressions *)
type oldtype = {
  mutable names: string list;
  (** List of variable names (as strings) inside \old expressions. *)
  mutable tlvals: TLvalSet.t;
  (** Set of tlvals inside \old expressions. *)
  mutable varinfos: VarinfoSet.t
  (** Set of varinfos of variables inside \old expressions. *)
}

let oldStruct = { names = []; tlvals = TLvalSet.empty;
                  varinfos = VarinfoSet.empty }

let addOldStruct name tlval varinfo =
  if not (name = "") then (
    oldStruct.names <- name::oldStruct.names
  );
  oldStruct.tlvals <- (TLvalSet.union tlval oldStruct.tlvals);
  oldStruct.varinfos <- (VarinfoSet.union varinfo oldStruct.varinfos)

(* This is a helper function for dumpOldsPre. *)
let dumpOlds fmt tlvals =
  let dump tlval = (
    let name = ref ((Pretty_utils.to_string Printer.pp_term_lval)
                      tlval) in
    if not (List.mem !name oldStruct.names) then (
      match tlval with
      | (TVar(lv),TNoOffset) ->
        (match lv.lv_type with
         | Ctype(TPtr(_,_)) -> () (* do nothing (wait for TMem()
                                     case) *)
         | Ctype(TComp(_,_,_)) ->
           let str1 = "Entire structs/unions inside \\at expressions" ^
                      " are not supported" in
           let str2 = "MC_UNSUPPORTED CONSTRUCT ERROR: Entire " ^
                      "TComp inside \\at;" in
           Self.warning "%s" str1;
           Format.fprintf fmt "@.%s" str2
         | Ctype(TArray(_,_,_,_)) ->
           let str1 = "Entire arrays inside \\at expressions are not" ^
                      " supported" in
           let str2 = "MC_UNSUPPORTED CONSTRUCT ERROR: Entire " ^
                      "TArray inside \\at;" in
           Self.warning "%s" str1;
           Format.fprintf fmt "@.%s" str2
         | Ctype(typ) ->
           let varinfo =
             match lv.lv_origin with
             | Some vi -> vi
             | None ->
               let str = "Logic variable " ^ lv.lv_name ^ "missing " ^
                         "varinfo" in
               raise (MC_Internal_Bug str)
           in
           addOldStruct !name TLvalSet.empty
             (VarinfoSet.singleton varinfo);
           Format.fprintf fmt "@.%a CMC_OLD%s = %s;"
             Printer.pp_logic_type
             lv.lv_type
             !name
             !name
         | _ -> ()
        )
      | (TMem(t),TNoOffset) ->
        (match t.term_node with
         | TBinOp(_,t1,t2) ->
           (match t1.term_type with
            | Ctype(TPtr(typ,_)) ->
              name := (Pretty_utils.to_string Printer.pp_term) t1;
              addOldStruct !name TLvalSet.empty VarinfoSet.empty;
              Format.fprintf fmt "@.%a CMC_OLD%s = %s;"
                Printer.pp_logic_type
                t1.term_type
                !name
                !name
            | _ -> ()
           )
         | TLval(tlval1) ->
           addOldStruct !name TLvalSet.empty VarinfoSet.empty;
           (name :=
              try String.sub !name 1 (String.length !name - 1)
              with _ -> "");
           Format.fprintf fmt "@.%a CMC_OLD%s = %s;"
             Printer.pp_logic_type
             t.term_type
             !name
             !name
         | _ ->
           let str1 = "Unsupported construct inside \\at expression" in
           Self.warning "%s" str1;
           Format.fprintf fmt "@.MC_UNSUPPORTED CONSTRUCT ERROR: ";
           Format.fprintf fmt "%a inside \\at;"
             Printer.pp_logic_type t.term_type
        )
      | (TVar(lv),TField(f,ofs)) ->
        (match lv.lv_type with
         | Ctype(typ) ->
           if not (TLvalSet.mem tlval oldStruct.tlvals) then (
             Format.fprintf fmt "@.%s;@."
               (varDecl typ ("CMC_OLD" ^ lv.lv_name));
           );
           addOldStruct !name (TLvalSet.singleton tlval)
             VarinfoSet.empty;
           Format.fprintf fmt "@.CMC_OLD%s = %s;"
             !name
             !name
         | _ -> ()
        )
      | (TVar(lv),TIndex(t,ofs)) ->
        (match lv.lv_type with
         | Ctype(typ) ->
           let varinfo =
             match lv.lv_origin with
             | Some vi -> vi
             | None ->
               let str = "Logic variable " ^ lv.lv_name ^ "missing " ^
                         "varinfo" in
               raise (MC_Internal_Bug str)
           in
           if not (VarinfoSet.mem varinfo oldStruct.varinfos) then (
             Format.fprintf fmt "@.%s;@."
               (varDecl typ ("CMC_OLD" ^ lv.lv_name));
           );
           addOldStruct !name TLvalSet.empty
             (VarinfoSet.singleton varinfo);
           Format.fprintf fmt "@.CMC_OLD%s = %s;"
             !name
             !name
         | _ -> ()
        )
      | (TMem(t),TField(f,ofs)) ->
        (match t.term_type with
         | Ctype(typ) ->
           (match typ with
            | TPtr(TComp(comp,_,_),_) ->
              if not (TLvalSet.mem tlval oldStruct.tlvals) then (
                Format.fprintf fmt "@.%s;@."
                  (varDecl typ ("CMC_OLD" ^ (Pretty_utils.to_string
                                               Printer.pp_term) t))
              );
              addOldStruct !name (TLvalSet.singleton tlval)
                VarinfoSet.empty;
              Format.fprintf fmt "@.CMC_OLD%s = %s;"
                !name
                !name
            | _ -> ()
           )
         | _ -> ()
        )
      (* This next case never seems to trigger. *)
      | (TMem(t),TIndex(_,ofs)) ->
        let str2 = "MC_UNSUPPORTED CONSTRUCT ERROR: (TMem(t)," ^
                   "TIndex(_,ofs));" in
        Self.warning
          "Unsupported tlval type: (TMem(t),TIndex(_,ofs))";
        Format.fprintf fmt "@.%s" str2
      | (TResult(typ),_) ->
        let str2 = "MC_UNSUPPORTED CONSTRUCT ERROR: \\result " ^
                   "inside statement contract;" in
        Self.warning
          "\\result inside statement contracts not yet supported";
        Format.fprintf fmt "@.%s" str2
      | (_,TModel(m,ofs)) ->
        Self.warning
          "Model fields inside \\at expressions not supported";
        Format.fprintf fmt
          "@.MC_UNSUPPORTED CONSTRUCT ERROR: TModel;"
    )
  ) in
  TLvalSet.iter dump tlvals

(* This declares and initializes variables found inside \old
 * expressions.
*)
let dumpOldsPre fmt post oldprj prj =
  let vis =
    object
      inherit Visitor.frama_c_copy prj
      method vterm t =
        match t.term_node with
        | Tat(t1,(BuiltinLabel(Old)))
        | Tat(t1,(BuiltinLabel(Pre))) ->
          dumpOlds fmt (tlvalsInTerm t1);
          Cil.DoChildren
        | _ ->
          Cil.DoChildren
      method vpredicate p =
        match p.pred_content with
        | Pat(pn,(BuiltinLabel(Old)))
        | Pat(pn,(BuiltinLabel(Pre))) ->
          dumpOlds fmt (tlvalsInPred pn.pred_content);
          Cil.DoChildren
        | _ ->
          Cil.DoChildren
    end
  in
  ignore (Visitor.visitFramacIdPredicate vis (snd post))

(* This modifies the default printer to prefix variables inside \old
 * expressions with CMC_OLD.
*)
class dumpOldsPost2 fmt = object(self)
  inherit Visitor.frama_c_inplace as super
  val isOld = ref false;
  method! vterm_node t =
    match t with
    | Tat(t1,(BuiltinLabel(Here)))
    | Tat(t1,(BuiltinLabel(Post))) ->
      super#vterm_node t1.term_node
    | Tat(t1,(BuiltinLabel(Old)))
    | Tat(t1,(BuiltinLabel(Pre))) ->
      let gettype name = (
        VarinfoSet.choose (
          VarinfoSet.filter (fun vi -> name = vi.vname)
            oldStruct.varinfos
        )
      ).vtype in
      (** Returns a term representing the variable associated to the
          given varinfo *)
      let mk_term_from_vi vi =
        Logic_const.term
          (TLval((Logic_utils.lval_to_term_lval (Cil.var vi))))
          (Ctype vi.vtype) in
      let dump name checkderef =
        if (List.mem !name oldStruct.names) then (
          if (checkderef && (!name.[0] = '*')) then (
            Format.fprintf fmt "*";
            name :=
              try String.sub !name 1 (String.length !name - 1)
              with _ -> ""
          );
          let vi = Cil.makeVarinfo false false ("CMC_OLD" ^ !name)
              (gettype !name) in
          Cil.ChangeDoChildrenPost((mk_term_from_vi vi).term_node,
                                   fun x -> x)
        ) else
          Cil.DoChildren
      in (
        match t1.term_node with
        | TLval(t2) -> (
            match t2 with
            | (TVar(lv),TNoOffset) ->
              dump (ref (lv.lv_name)) true
            | (TMem(t3),TNoOffset) ->
              isOld := false;
              let name = ref ((Pretty_utils.to_string
                                 Printer.pp_term_lval) t2) in
              isOld := true;
              dump name true
            | (TVar(lv),TField(f,ofs)) ->
              dump (ref (lv.lv_name ^ "." ^ f.fname)) true
            | (TVar(lv),TIndex(t3,ofs)) ->
              isOld := false;
              let name = ref (lv.lv_name ^ "[" ^ ((
                  Pretty_utils.to_string Printer.pp_term) t3) ^ "]") in
              isOld := true;
              dump name true
            | (TMem(t3),TField(f,ofs)) ->
              isOld := false;
              let name = ref ((Pretty_utils.to_string
                                 Printer.pp_term_lval) t2) in
              isOld := true;
              dump name false
            | (TMem(_),TIndex(_,_))
            | _ ->
              Cil.DoChildren
          )
        | _ ->
          Cil.DoChildren
      )
    | _ ->
      Cil.DoChildren
  method! vterm_lval t =
    let dump name checkderef =
      if !isOld then (
        if (List.mem !name oldStruct.names) then (
          if (checkderef && (!name.[0] = '*')) then (
            Format.fprintf fmt "*";
            name :=
              try String.sub !name 1 (String.length !name - 1)
              with _ -> "");
          Format.fprintf fmt "CMC_OLD%s"
            !name;
          Cil.DoChildren
        ) else
          super#vterm_lval t
      ) else
        super#vterm_lval t
    in
    match t with
    | (TVar(lv),TNoOffset) ->
      (match lv.lv_type with
       | Ctype(ct) ->
         (match ct with
          | TInt(k,alist) ->
            (match alist with
             | h::t ->
               List.iter
                 (fun attr ->
                    match attr with
                    | Attr(_,_) ->
                      ()
                    | AttrAnnot(_) ->
                      ()
                 )
                 alist;
             | [] -> ()
            );
          | _ -> ());
       | _ -> ()
      );
      dump (ref (lv.lv_name)) true
    | (TMem(t1),TNoOffset) ->
      isOld := false;
      let name = ref ((Pretty_utils.to_string Printer.pp_term_lval) t)
      in
      isOld := true;
      dump name true
    | (TVar(lv),TField(f,ofs)) ->
      dump (ref (lv.lv_name ^ "." ^ f.fname)) true
    | (TVar(lv),TIndex(t1,ofs)) ->
      isOld := false;
      let name = ref (lv.lv_name ^ "[" ^ ((Pretty_utils.to_string
                                             Printer.pp_term) t1) ^ "]") in
      isOld := true;
      if (List.mem !name oldStruct.names) then (
        Format.fprintf fmt "CMC_OLD%s[%a]"
          lv.lv_name Printer.pp_term t1;
        Cil.DoChildren
      ) else
        super#vterm_lval t
    | (TMem(t1),TField(f,ofs)) ->
      isOld := false;
      let name = ref ((Pretty_utils.to_string Printer.pp_term_lval) t)
      in
      isOld := true;
      dump name false
    | (TMem(_),TIndex(_,_))
    | _ ->
      Cil.DoChildren
  method! vpredicate p =
    match p.pred_content with
    | Pat(pn,(BuiltinLabel(Here)))
    | Pat(pn,(BuiltinLabel(Post))) ->
      super#vpredicate pn
    | Pat(pn,(BuiltinLabel(Old)))
    | Pat(pn,(BuiltinLabel(Pre))) ->
      isOld := true;
      Format.fprintf fmt "(";
      ignore (self#vpredicate pn);
      isOld := false;
      Format.fprintf fmt ")";
      Cil.DoChildren
    | Pfalse (** always-false predicate. *)
    | Ptrue (** always-true predicate. *)
    | Papp(_,_,_)      (** application of a predicate. *)
    | Pseparated(_)
    | Prel(_,_,_)
    | Pand(_,_)
    | Por(_,_)
    | Pxor(_,_)
    | Pimplies(_,_)
    | Piff(_,_)
    | Pnot(_)
    | Pif(_,_,_)
    | Plet(_,_)
    | Pforall(_,_)
    | Pexists(_,_)
    | Pvalid_read(_,_)
    | Pvalid(_,_)
    | Pvalid_function(_) (** the pointed function has a type compatible with the
                             one of pointer. *)
    | Pinitialized(_,_)
    | Pdangling(_,_)
    | Pallocable(_,_)
    | Pfreeable(_,_)
    | Pfresh(_,_,_,_) ->   (** \fresh(pointer, n)
                               A memory block of n bytes is newly allocated to
                               the pointer.*)
      Cil.DoChildren
    | _ ->
      Format.fprintf fmt "_";
      super#vpredicate p
end

(* This dumps the \old variables created in dumpOldsPre. *)
let dumpOldsPost fmt post oldprj prj =
  let p = Visitor.visitFramacPredicate (new dumpOldsPost2 fmt)
      (snd post).ip_content in
  Kernel.Unicode.without_unicode
    (fun () -> Printer.pp_predicate fmt p) ()

(*
 * Check code annotation to see if its supported, and pass its
 * requires clauses to the next stage, one at a time
 *
 * TODO:
 *   Handle named behaviors (1st arg of AStmtSpec is namelist)
 *   Handle multiple bhvs
*)
let dumpStmtPre fmt ca oldprj prj =
  match ca.annot_content with
  | AStmtSpec([],spec) ->
    (match spec.spec_behavior with
     | [bhv] ->
       List.iter (fun req -> dumpStmtReq fmt req) bhv.b_requires;
       (* Check for Old labels in post-conditions. This applies
        * whether the checker is satabs or cpa. Old labels may also
        * appear in assigns clauses.
       *)
       if ((List.length bhv.b_post_cond) > 0) then
         List.iter
           (fun post -> dumpOldsPre fmt post oldprj prj)
           bhv.b_post_cond
     | _ ->
       raise (MC_Unsupported_Construct "Multiple behaviors not supported")
    )
  | AStmtSpec(_,spec) ->
    raise (MC_Unsupported_Construct "AStmtSpec behaviors not supported")
  (* following ignored for now, but cegar could potential support some *)
  | AAssert(_,_,_)
  | AInvariant(_,_,_)
  | AVariant(_)
  | AAssigns(_,_)
  | AAllocation(_,_)
  | APragma(_)
  | AExtended(_,_,_) ->
    (* Note warning already printed before getting here *)
    ()

(* Returns true if postcondition contains \forall *)
let hasForall postcond = match (snd postcond).ip_content.pred_content with
  | Pforall(_,_) -> true
  | _ -> false

(* Output a postcondition (ensures clause) *)
let dumpStmtPost fmt stmt postcond oldprj prj =
  Format.fprintf fmt "assert (";
  dumpOldsPost fmt postcond oldprj prj;
  Format.fprintf fmt ");@."

(*
 * Note that ACSL ensures clauses do not constrain the post-state when
 * the statement terminates abnormally (goto, break, continue,
 * return) - See ACSL 1.7 manual Sec 2.4.4. In such cases, we jump to
 * CMCBADEND if the target point is not in the statement, where the
 * CMCBADEND is after assert(postcondition). CMCGOODEND is the label
 * used for normal exit from the function.
*)
let dumpStmtClose fmt stmt postcond oldprj prj =
  if not(hasForall postcond) then (
    Format.fprintf fmt "CMCGOODEND:@.";
    dumpStmtPost fmt stmt postcond oldprj prj
  );
  Format.fprintf fmt "CMCBADEND:  return;@.";
  Format.fprintf fmt "}@."

(*
 * This is equivalent to Printer.pp_stmt, except that it has special
 * handling for certain constructs. Its also not particularly pretty,
 * though there is some indentation for readability reasons.
 * For constructs that are not supported, an error message is output
 * to fmt, since the result will be unparsable by the model checker
 * and lead to a parse error down the line. 
 *
 * Note that all the mcpp functions are called while on the previous
 * line (thus the need to carriage return before printing anything on
 * a new line).
 *)

let rec indent fmt ind =
  if ind>0 then
    Format.fprintf fmt "%s" (String.make (2*ind) ' ')

(* This substitutes formal arguments with actual arguments. *)
let dumpFnSubst fmt ind req isPre currFn fnList oldprj prj =
  if isPre then (
    if ind > 0 then
      Format.fprintf fmt " && ";
    Format.fprintf fmt "("
  );
  if (isPre && not(legalIdentPred req)) then (
    Format.fprintf fmt "1==2";
    Self.warning "Unsupported annotation predicate (not checked)"
  ) else (
    let str = ref (Kernel.Unicode.without_unicode
                     (fun () -> (Pretty_utils.to_string Printer.pp_predicate)
                         req.ip_content) ()) in
    let hd = try List.hd currFn
      with _ -> raise (MC_Internal_Bug "Empty function list") in
    let str2 = ref (Format.sprintf "CMC%s%d"
                      (List.nth fnList hd.idx).vinfo.vname
                      (List.nth fnList hd.idx).count) in
    str := Str.global_replace (Str.regexp "\\\\result") !str2 !str;
    str := Str.global_replace (Str.regexp "\\\\old") "" !str;
    let kf = Globals.Functions.get (List.nth fnList (List.hd
                                                       currFn).idx).vinfo in
    let formals = Globals.Functions.get_params kf in
    List.iteri
      (fun idx vi ->
         let formalarg = "\\b" ^ vi.vname ^ "\\b" in
         let placeholder = "CMCtmp" ^ (string_of_int idx) in
         str := Str.global_replace (Str.regexp formalarg)
             ("(" ^ placeholder ^ ")") !str;
      )
      formals;
    List.iteri
      (fun idx vi ->
         let placeholder = "CMCtmp" ^ (string_of_int idx) in
         let actualarg = (Pretty_utils.to_string Printer.pp_exp)
             (List.nth (List.hd currFn).args idx) in
         str := Str.global_replace (Str.regexp placeholder) actualarg
             !str;
      )
      formals;
    Format.fprintf fmt "%s" !str;
    Printer.update_printer
      (module PrintDefault: Printer.PrinterExtension)
  );
  Format.fprintf fmt ")"

(* This handles printing P => Q. *)
let checkFC fmt funspec args currFn fnList oldprj prj =
  match funspec.spec_behavior with
  | [bhv] ->
    Format.fprintf fmt "!(";
    if ((List.length bhv.b_requires) > 0 ) then (
      List.iteri
        (fun ind req -> dumpFnSubst fmt ind req true currFn fnList
            oldprj prj)
        bhv.b_requires;
      Format.fprintf fmt ")"
    )
    else Format.fprintf fmt "%d)" 1;
    Format.fprintf fmt " || (";
    if ((List.length bhv.b_post_cond) > 0 ) then (
      List.iter (fun post -> dumpFnSubst fmt 0 (snd post) false currFn
                    fnList oldprj prj) bhv.b_post_cond
    )
  | _ -> (* Warnings already printed before getting here *)
    let str2 = "MC_INTERNAL_BUG: Error while checking function " ^
               "contract;" in
    Self.warning
      "MC_Internal_Bug while checking function contract";
    Format.fprintf fmt "@.%s@." str2

(* This sets hasSideEffects to true if the side effects of function fn affect
   stmt.
 *)
let checkSideEffects fmt stmt fn assigns fnList =
  let stmtAssigns = try (List.find (fun r -> r.name = "CMCstmt")
                           assigns).locs
    with Not_found -> StringSet.empty in
  let fnAssigns = try (List.find (fun r -> r.name = fn.vinfo.vname)
                         assigns).locs
    with Not_found -> StringSet.empty in
  let interSet = StringSet.inter fnAssigns stmtAssigns in
  if (interSet <> StringSet.empty) then (
    List.iter
      (fun str ->
         if StringSet.mem str interSet && not fn.vinfo.vdefined then
           hasSideEffects := true
      )
      !globalsDumped;
  )

(*
 * This makes substitutions for a function call based on information
 * from the function's contract.
*)
let substFnCall fmt stmt ind lv fnname args assigns fnList oldprj prj =
  let p1str = "Function pointers not supported" in
  let p2str = "MC_UNSUPPORTED CONSTRUCT ERROR: function pointer" in
  let rec findFn idx = function
    | [] -> warn fmt p1str p2str
    | fn::fns ->
      if (fnname = fn.vinfo.vname) then
        (match fn.vinfo.vtype with
         | TFun(typ,_,_,_) ->
  Self.warning "blah 1 %s" fnname;
           checkSideEffects fmt stmt fn assigns fnList;
           indent fmt ind;
           if (!hasSideEffects) then (
             (* Called function has side effects *)
             let str2 = "MC_ERROR: Side effects of function " in
             let str3 = " affect stmt.;" in
  Self.warning "blah 1B";
             Self.warning "Side effects of function %s affect stmt."
               fnname;
             Format.fprintf fmt "@.%s%s%s" str2 fnname str3;
             hasSideEffects := false 
           ) else if try Str.search_forward (Str.regexp "Frama_C_")
                           fn.vinfo.vname 0 > -1;
             with Not_found -> false then (
  Self.warning "blah 2";
             match lv with
             | Some x ->
               Format.fprintf fmt "%a = __VERIFIER_nondet_" Printer.pp_lval x;
               if fn.vinfo.vname = "Frama_C_unsigned_int_interval" then
                 Format.fprintf fmt "uint();"
               else if fn.vinfo.vname = "Frama_C_char_interval" then
                 Format.fprintf fmt "char();"
               else if fn.vinfo.vname = "Frama_C_unsigned_char_interval" then
                 Format.fprintf fmt "uchar();"
               else Format.fprintf fmt "int();"
             | None -> ()
           ) else if (not fn.vinfo.vdefined) ||
                      (AbstractCalls.get() && 
                       fn.vinfo.vdefined &&
                       fn.funspec.spec_behavior != []) then (
             (*
              * The head of this list serves as a pointer to the
              * function in fnList that is currently being printed.
             *)
             let currFn : currfntype list = {idx = idx; args = args}::[]
             in
  Self.warning "blah 3";
             (match lv with
              | Some x ->
                fn.count <- fn.count + 1;
                dumpStorageClass fmt fn.vinfo true;
                Format.fprintf fmt "%a CMC%s%d;"
                  Printer.pp_typ typ
                  fnname
                  fn.count;
                Format.fprintf fmt "@."; indent fmt ind
              | None -> ()
             );
             Format.fprintf fmt "__VERIFIER_assume(";
             checkFC fmt fn.funspec args currFn fnList oldprj prj;
             Format.fprintf fmt ");";
             Format.fprintf fmt "@."; indent fmt ind;
             (match lv with
              | Some x ->
                Format.fprintf fmt "%a = CMC%s%d;"
                  Printer.pp_lval x
                  fnname
                  fn.count
              | None -> ()
             )
           ) else ( (* Called fn. has a body, so leave stmt unchanged *)
  Self.warning "blah 4 %s %d" fnname idx;
             Printer.pp_stmt fmt stmt
           )
         | _ -> ()
        ) else findFn (idx + 1) fns
  in findFn 0 fnList

let checkInsertStmtArr fmt sid insertStmtArr isAfter ui lvals oldprj prj
    origStmt =
  if sid = insertStmtArr.(2) && not isAfter || (* before 1st stmt in loop *)
     sid = insertStmtArr.(1) && isAfter &&
     insertStmtArr.(1) = insertStmtArr.(4) || (* no stmt after loop *)
     sid = insertStmtArr.(3) && isAfter then (* after last stmt in loop *)
    let (stmt,_) = Kernel_function.find_from_sid sid in
    dumpVarDecls ui fmt origStmt stmt lvals oldprj prj false isAfter sid
      insertStmtArr false
  else if sid = insertStmtArr.(1) && insertStmtArr.(1) <> insertStmtArr.(4) then
    (* after loop *)
    let (stmt,_) = Kernel_function.find_from_sid sid in
    let gotoLabel = gotoInStmt origStmt in
    let l = stmt.labels in
    let label = if l <> [] then (
        match List.hd l with
        | Label(str,_,_) -> str
        | _ -> "CMC_NoLabel"
      ) else "CMC_NoLabel"
    in
    let matchGotoLabel = gotoLabel = label in
    if matchGotoLabel then (
      let isSkip = function
        | Instr(Skip _) -> true
        | _ -> false in
      if not (isSkip stmt.skind) then
        raise (MC_Unsupported_Construct "Target of goto is non-trivial");
      if isAfter then dumpVarDecls ui fmt origStmt stmt lvals oldprj prj false
          isAfter sid insertStmtArr matchGotoLabel
    ) else if not isAfter then
      dumpVarDecls ui fmt origStmt stmt lvals oldprj prj false isAfter sid
        insertStmtArr matchGotoLabel

let mcpp_labels fmt stmt ind = ignore(
    List.map
      (fun lbl -> (Format.fprintf fmt "@."; Printer.pp_label fmt lbl))
      stmt.labels)

(*
 * This prints stmt at indentation level ind, also handling
 * postconditions properly for all exit types. The stmtsScope argument
 * is a list of the ids of all statements that are legal targets.
 * The nest{Lp,Sw} arguments are booleans that indicate whether stmt
 * is nested inside a loop or switch, respectively.
*)
let rec mcpp_stmt fmt origStmt stmt postcond stmtsScope ind nestLp nestSw
    assigns fnList oldprj prj insertStmtArr ui lvals isFn =
  if ConstrainVals.get() then
    checkInsertStmtArr fmt stmt.sid insertStmtArr false ui lvals oldprj prj
      origStmt;
  (match stmt.skind with
   | Instr instr ->
     Format.fprintf fmt "@."; indent fmt ind;
     (match instr with
      | Call(lv,exp,args,_) ->
        let fnname = ((Pretty_utils.to_string Printer.pp_exp) exp) in
        substFnCall fmt stmt ind lv fnname args assigns fnList oldprj prj
      | Local_init(vi,ConsInit(f,args,_),_) ->
        dumpStorageClass fmt vi ~isGlobal:false false;
        Format.fprintf fmt "%s;@."
          (varDecl (Cil.unrollType vi.vtype) vi.vname);
        let lv = Some (Var vi, NoOffset) in
        substFnCall fmt stmt ind lv f.vname args assigns fnList oldprj prj
      | _ ->
        Printer.pp_stmt fmt stmt
     )
   | Goto (target,_) ->
     if isFn || List.mem !target.sid stmtsScope then (
       Format.fprintf fmt "@."; indent fmt ind;
       Printer.pp_stmt fmt stmt)
     else (    (* target isnt in verified part *)
       Format.fprintf fmt "@."; indent fmt ind;
       Format.fprintf fmt "goto CMCBADEND;"
     )
   | Break _ ->
     mcpp_labels fmt stmt ind;
     Format.fprintf fmt "@."; indent fmt ind;
     if isFn || (nestLp || nestSw) then
       Printer.pp_stmt fmt stmt
     else
       Format.fprintf fmt "goto CMCBADEND;"
   | Continue _ ->
     mcpp_labels fmt stmt ind;
     Format.fprintf fmt "@."; indent fmt ind;
     if isFn || nestLp then
       Printer.pp_stmt fmt stmt
     else
       Format.fprintf fmt "goto CMCBADEND;"
   | Return (None,loc) ->
     mcpp_labels fmt stmt ind;
     Format.fprintf fmt "@."; indent fmt ind;
     if isFn then (
       (* If stmt has label(s), dump the stmt only since the label(s) were
          previously dumped
       *)
       let s = String.split_on_char ':'
           ((Pretty_utils.to_string Printer.pp_stmt) stmt) in
       let rec dumpLast = function
         | [] -> ()
         | [x] -> Format.fprintf fmt "%s" x
         | h::t -> dumpLast t
       in dumpLast s
     ) else
       Format.fprintf fmt "goto CMCBADEND;"
   | Return (Some expr,loc) ->
     mcpp_labels fmt stmt ind;
     Format.fprintf fmt "@."; indent fmt ind;
     if isFn then (
       let s = String.split_on_char ':'
           ((Pretty_utils.to_string Printer.pp_stmt) stmt) in
       let rec dumpLast = function
         | [] -> ()
         | [x] -> Format.fprintf fmt "%s" x
         | h::t -> dumpLast t
       in dumpLast s
     ) else
       Format.fprintf fmt "goto CMCBADEND;"
   | If (expr,blkt,blkf,loc) ->
     mcpp_labels fmt stmt ind;
     Format.fprintf fmt "@."; indent fmt ind;
     Format.fprintf fmt "if (";
     Printer.pp_exp fmt expr;
     Format.fprintf fmt ") ";
     mcpp_blk fmt blkt postcond stmtsScope ind nestLp nestSw assigns
       fnList oldprj prj insertStmtArr false ui lvals isFn origStmt;
     Format.fprintf fmt "@."; indent fmt ind;
     Format.fprintf fmt "else ";
     mcpp_blk fmt blkf postcond stmtsScope ind nestLp nestSw assigns
       fnList oldprj prj insertStmtArr false ui lvals isFn origStmt
   | Loop (annots,blk,loc,contStmt,brkStmt) ->
     mcpp_labels fmt stmt ind;
     Format.fprintf fmt "@."; indent fmt ind;
     Format.fprintf fmt "while (1) ";
     mcpp_blk fmt blk postcond stmtsScope ind true nestSw assigns fnList
       oldprj prj insertStmtArr true ui lvals isFn origStmt
   | Switch (expr,blk,cases,loc) ->
     mcpp_labels fmt stmt ind;
     Format.fprintf fmt "@."; indent fmt ind;
     Format.fprintf fmt "switch (";
     Printer.pp_exp fmt expr;
     Format.fprintf fmt ")";
     mcpp_blk fmt blk postcond stmtsScope ind nestLp true assigns fnList
       oldprj prj insertStmtArr false ui lvals isFn origStmt
   | Block (blk) ->
     mcpp_labels fmt stmt ind;
     Format.fprintf fmt "@."; indent fmt ind;
     mcpp_blk fmt blk postcond stmtsScope ind nestLp nestSw assigns
       fnList oldprj prj insertStmtArr false ui lvals isFn origStmt
   | UnspecifiedSequence us ->
     mcpp_labels fmt stmt ind;
     Format.fprintf fmt "@."; indent fmt ind;
     mcpp_blk fmt (Cil.block_from_unspecified_sequence us) postcond
       stmtsScope ind nestLp nestSw assigns fnList oldprj prj insertStmtArr
       false ui lvals isFn origStmt
   (* Need to check correctness of this; commented out for now
      Format.fprintf fmt
      "@.MC_UNSUPPORTED CONSTRUCT ERROR: Unspecified Sequence;";
   *)
   (* Handled using catch all case since Fluorine/Neon have
    * TryFinally and TryExcept, but Sodium also has Throw and
    * TryCatch.
   *)
   | _ ->
     mcpp_labels fmt stmt ind;
     Format.fprintf fmt "@.MC_UNSUPPORTED CONSTRUCT ERROR: Throw or Try;";
  );
  if ConstrainVals.get() then
    checkInsertStmtArr fmt stmt.sid insertStmtArr true ui lvals oldprj prj
      origStmt

(* mcpp_blk has the same arguments as mcpp_stmt except for loopOnly, which is
   true if the block is inside a loop *)
and
  mcpp_blk fmt blk postcond stmtsScope ind nestLp nestSw assigns fnList
    oldprj prj insertStmtArr loopOnly ui lvals isFn origStmt =
  Format.fprintf fmt "{";
  ignore(
    List.map
      (fun stmt -> mcpp_stmt fmt origStmt stmt postcond stmtsScope (ind + 1)
          nestLp nestSw assigns fnList oldprj prj insertStmtArr ui lvals isFn)
      blk.bstmts);
  Format.fprintf fmt "@.";
  (match (snd postcond).ip_content.pred_content with
   | Pforall(_,p) ->
     if loopOnly then (
       indent fmt (ind+1);
       Format.fprintf fmt "CMCGOODEND:@.";
       indent fmt (ind+1);
       Format.fprintf fmt "__VERIFIER_assert(";
       (match p.pred_content with
        | Pimplies(_,ip) ->
          Kernel.Unicode.without_unicode
            (fun () -> Printer.pp_predicate fmt ip) ()
        | _ ->
          Self.warning "\forall used without implication";
          Format.fprintf fmt "@.MC_ERROR: \forall used without implication;@."
       );
       Format.fprintf fmt ");@."
     )
   | _ -> ()
  );
  indent fmt (ind+1);
  Format.fprintf fmt "}"

let rec dumpFunctionDecs fmt = function
  | [] -> ()
  | h::t -> (
      match (Globals.Functions.get h.vinfo).fundec with
      | Definition(fundec, _) ->
        Format.fprintf fmt "%s;@."
          (varDecl (Cil.unrollType fundec.svar.vtype) fundec.svar.vname)
      | _ -> ()
    );
    dumpFunctionDecs fmt t

let rec dumpFunctionDefs fmt stmt postcond assigns fnList fullFnList oldprj prj
    insertStmtArr ui lvals = match fnList with
  | [] -> ()
  | h::t -> (
      match (Globals.Functions.get h.vinfo).fundec with
      | Definition(fundec, _) ->
        Format.fprintf fmt "%s {"
          (varDecl (Cil.unrollType fundec.svar.vtype) fundec.svar.vname);
        dumpVarinfoList fmt fundec.slocals;
        Format.fprintf fmt "@.  ";
        mcpp_blk fmt fundec.sbody postcond (stmtsInBlock fundec.sbody) 0 false
          false assigns fullFnList oldprj prj insertStmtArr false ui lvals true
          stmt;
        Format.fprintf fmt "@.}@."
      | _ -> ()
    );
    Format.fprintf fmt "@.";
    dumpFunctionDefs fmt stmt postcond assigns t fullFnList oldprj prj
      insertStmtArr ui lvals

let dumpFunctions fmt stmt postcond assigns fnList oldprj prj insertStmtArr ui
    lvals =
  Format.fprintf fmt "@.";
  dumpFunctionDecs fmt fnList;
  Format.fprintf fmt "@.";
  dumpFunctionDefs fmt stmt postcond assigns fnList fnList oldprj prj
    insertStmtArr ui lvals

(* Builds list of all sids in sliced program *)
class sliceGetStmts = object
  inherit Visitor.frama_c_inplace
  method! vstmt_aux s =
    slicedSids := s.sid :: !slicedSids;
    DoChildren
end

let dumpStmtHeader ui fmt stmt postcond lvals ca assigns fnList oldprj
    prj insertStmtArr : assignstype list * fntype list =
  Format.fprintf fmt "// Automatically generated by mc@.";
  Format.fprintf fmt "//@.";
  if (Checker.get() = "cpa") then (
    Format.fprintf fmt "#include <assert.h>@.";
    Format.fprintf fmt "@.extern void __VERIFIER_assume(int);@.";
    dumpExternNondets fmt
  );
  dumpStructDefs fmt (structsInLvals fmt lvals);
  let fnList2 : fntype list = uniq (fnCallsInStmt fmt
                                      (LvalSet.elements lvals) fnList) in
  let assigns2 : assignstype list = dumpGlobalVars fmt ca stmt assigns
      fnList2 oldprj prj lvals in
  dumpFunctions fmt stmt postcond assigns2 fnList2 oldprj prj insertStmtArr ui
    lvals;
  Format.fprintf fmt "void main () {@.";
  dumpVarDecls ui fmt stmt stmt lvals oldprj prj true false stmt.sid
    insertStmtArr false;
  Format.fprintf fmt "@.";
  (assigns2,fnList2)

(* ZH NOTE:
 * Presently, cpa requires the use of the script cpa-helper.sh
 * due to the fact that CPAchecker has no return value like satabs.
 * The script parses the file in output/Statistics.txt which is created
 * when CPAchecker is run over a file and returns 0, if verification
 * succeeded.
 *
 * ZH TODO:
 * A future version should have mc parse the file rather than an
 * outside script. This was just an easy way to test if using CPAchecker
 * was feasible.
 *
 * NOTE: nov12 version: CPAchecker does not generate any output files
 * (with -noout).
 * NOTE: nov21 version: CPAchecker - replaced predicateAnalysis option
 * with bitprecise version so that all variables are treated as unbounded
 * integers per this post:
 * https://groups.google.com/forum/#!topic/cpachecker-users/h8gajclFTuM
 * to disable rational analysis.
*)
let callChecker checker fileName maxIter maxTime =
  match checker with
  | "satabs" ->
    "timeout " ^ (string_of_int maxTime) ^ " " ^
    "./mc-helper.sh satabs --iterations " ^ (string_of_int maxIter)
    ^ " " ^ (fileName)
    ^ if (not (Diagnostics.get())) then ">/dev/null 2>/dev/null"
    else ""
  | "cpa" ->
    "./mc-helper.sh $CPACHECKER/scripts/cpa.sh " ^
    "-spec $CPACHECKER/config/specification/Assertion.spc " ^
    "-preprocess -predicateAnalysis"
    ^ " -noout "
    ^ "-timelimit " ^ (string_of_int maxTime) ^ " " ^ (fileName)
    ^ if (not (Diagnostics.get())) then ">/dev/null 2>/dev/null"
    else ""
  | _ ->
    Self.warning "Bad checker name; model checking not done"; "1"

let checkStmtPost ui fileName stmt em ca behav postcond maxIter maxTime
    lvals2 insertStmtArr =
  let checker = "" in
  (*  let ast = (Ast.get ()) in  *)
  let chan = open_out fileName in
  let fmt = Format.formatter_of_out_channel chan in
  (* Functions to handle function calls in stmt *)
  let fnList : fntype list = [] in
  (* Data structure for handling assigns *)
  let assigns : assignstype list = [] in
  if Slice.get() then
    Self.warning
      "-mc-slice option ignored (not supported in this version)";
  let oldprj = Project.current () in
  let prj = File.create_project_from_visitor "new" (fun proj ->
      new Visitor.frama_c_copy proj) in
  Project.copy ~selection:(Parameter_state.get_selection ()) prj;
  Project.set_current prj;
  let lvalsInFn = lvalsInBlock (getFnBlk stmt) false false true in
  let lvalc = lvalsInContract lvalsInFn behav in
  let lvals = LvalSet.union lvals2 lvalc in
  let ((assigns2,fnList2) : assignstype list * fntype list) =
    dumpStmtHeader ui fmt stmt postcond lvals ca assigns fnList oldprj
      prj insertStmtArr in
  dumpStmtPre fmt ca oldprj prj;
  mcpp_stmt fmt stmt stmt postcond (stmtsInStmt stmt) 0 false false assigns2
    fnList2 oldprj prj insertStmtArr ui lvals false;
  Format.fprintf fmt "@.";
  dumpStmtClose fmt stmt postcond oldprj prj;
  close_out chan;
  Project.set_current oldprj;
  (* interface with satabs *)
  Self.feedback "Model checking...";
  if ((0 == (Sys.command (
      callChecker (Checker.get()) fileName maxIter maxTime))))
  then (
    Self.feedback "Success!\n";
    (* Build list of dependencies*)
    match behav with
    | Bhv bhv -> (
        let rec depends2 lst =
          match lst with
          | [] -> []
          | x::l ->
            let kf = Globals.Functions.get x.vinfo in
            (* Using Property.ip_post_cond_of_spec because it appears to be
               the only function that takes a funspec as an argument *)
            (Property.ip_post_cond_of_spec kf Kglobal
               ~active:[bhv.b_name] x.funspec) @ (depends2 l)
        in
        (* depends has type Property.t list *)
        let depends = (Property.ip_requires_of_behavior
                         (Kernel_function.find_englobing_kf stmt) (Kstmt stmt)
                         bhv) @ (depends2 fnList2) in
        (* Remove any assigns clauses that Frama-C may have added *)
        let rec depends3 lst =
          match lst with
          | [] -> []
          | x::l ->
            let str = ((Pretty_utils.to_string Property.pretty) x) in
            if (try (Str.search_forward (Str.regexp "assigns") str 0) > -1;
                with Not_found -> false)
            then depends3 l
            else (x::(depends3 l))
        in
        let depends4 = depends3 depends in
        setEmitter !emitterName;
        Property_status.emit
          !emitter
          ~hyps: depends4
          (Property.ip_of_ensures
             (Kernel_function.find_englobing_kf stmt)
             (Kstmt stmt) bhv postcond)
          ~distinct:false
          Property_status.True;
      )
    | Pred pred ->
      setEmitter !emitterName;
      Property_status.emit
        !emitter
        ~hyps:[]
        (Property.ip_of_code_annot_single
           (Kernel_function.find_englobing_kf stmt)
           stmt ca)
        ~distinct:false
        Property_status.True
  )
  else (
    Self.feedback "Unable to Prove\n";
    match behav with
    | Bhv bhv ->
      Property_status.emit
        !emitter
        ~hyps:[]
        (Property.ip_of_ensures
           (Kernel_function.find_englobing_kf stmt)
           (Kstmt stmt) bhv postcond)
        ~distinct:false
        Property_status.Dont_know
    | Pred pred ->
      Property_status.emit
        !emitter
        ~hyps:[]
        (Property.ip_of_code_annot_single
           (Kernel_function.find_englobing_kf stmt)
           stmt ca)
        ~distinct:false
        Property_status.True
  );
  (* Empty out data structures for next run *)
  oldStruct.names <- [];
  oldStruct.tlvals <- TLvalSet.empty;
  oldStruct.varinfos <- VarinfoSet.empty;
  emitter := mcStmtPrf;
  emitterName := "MC";
  hasSideEffects := false;
  globalsDumped := [];
  local_init := [];
  globalDefs := VarinfoSet.empty;
  slicedSids := [];
  ui#rehighlight ()

let checkStmtContract ui stmt =
  if Enabled.get() then begin
    let fileName = OutputFile.get () in
    let maxIter = MaxIterations.get () in
    let maxTime = TimeLimit.get () in
    if not(Iteration.is_default()) then
      raise (MC_Unsupported_Construct
               "-mc-iter option not supported in this version")
    else begin
      (* Model check, once for each postcondition *)
      if not(Annotations.has_code_annot stmt) then
        Self.warning "No statement contract to check!"
      else (
        (* Save original project before slicing *)
        let presliceprj = Project.current() in
        (* Save statement contract *)
        let annotList = Annotations.code_annot stmt in
        (* Perform slicing *)
        let sliceprj = if ConstrainVals.get() 
          then sliceAssert stmt else presliceprj in
        let stmt = if ConstrainVals.get() then (
            (* Copy command line parameters to sliced project *)
            Project.copy ~selection:(Parameter_state.get_selection ()) sliceprj;
            Project.set_current sliceprj;
            (* Call sliceGetStmts, which populates slicedSids with all
               the sids in the sliced program *)
            Visitor.visitFramacFileSameGlobals (new sliceGetStmts) (Ast.get());
            (* Get the location of the original stmt *)
            let oldloc = Cil_datatype.Stmt.loc stmt in
            (* Get the sid of the loop in the sliced program. The
               location of this statement will have the same line
               number as that of the loop in the original program. *)
            let sliceLoopSid =
              let rec findBlock = function
                | [] -> -1
                | h::t ->
                  let (s,_) = Kernel_function.find_from_sid h in
                  match s.skind with
                  | Block b ->
                    if getStmtLineNum s = getStmtLineNum stmt then s.sid
                    else findBlock t
                  | _ -> findBlock t in
              findBlock !slicedSids in
            (* If the loop was sliced out *)
            if sliceLoopSid = -1 then (
              (* Find the first ACSL assert in the sliced program *)
              let rec findAssert = function
                | [] ->
                  let str = "ConstrainVals flag enabled, but assert is  " ^
                            "either missing or accesses uninitialized " ^ 
                            "left-value" in
                  raise (MC_Unsupported_Construct str)
                | h::t ->
                  let (s,_) = Kernel_function.find_from_sid h in
                  match s.skind with
                  | Instr (Skip _) ->
                    let l = Annotations.code_annot s in
                    let rec findAssert2 = function
                      | [] -> findAssert t
                      | h::t ->
                        (match h.annot_content with
                         | AAssert _ -> s.sid
                         | _ -> findAssert2 t) in
                    findAssert2 l
                  | _ -> findAssert t in
              let assertSid = findAssert !slicedSids in
              (* Insert a no op before the assert *)
              Visitor.visitFramacFileSameGlobals
                (new insert_assert assertSid oldloc) (Ast.get());
              (* Re-compute AST *)
              Cfg.clearFileCFG ~clear_id:false (Ast.get());
              Cfg.computeFileCFG (Ast.get());
              (* Temporarily save old slicedSids *)
              let oldSlicedSids = !slicedSids in
              (* Update slicedSids *)
              slicedSids := [];
              Visitor.visitFramacFileSameGlobals (new sliceGetStmts)
                (Ast.get());
              (* Get the inserted no op *)
              let sliceStmt =
                let rec diffSids = function
                  | [] ->
                    let str = "Unable to insert new statement" in
                    raise (MC_Internal_Bug str)
                  | h::t ->
                    if List.mem h oldSlicedSids then diffSids t
                    else fst (Kernel_function.find_from_sid h) in
                diffSids !slicedSids in
              (* Copy contract *)
              let kf = Kernel_function.find_englobing_kf sliceStmt in
              addAnnots kf sliceStmt annotList;
              sliceStmt)
            else (
              (* Otherwise, copy the contract to the loop in the
                 sliced program *)
              let stmt = fst (Kernel_function.find_from_sid sliceLoopSid) in
              let kf = Kernel_function.find_englobing_kf stmt in
              addAnnots kf stmt annotList;
              stmt))
          else stmt in
        (* Populates an array that holds the sid's of statements that indicate
           important locations for inserting assumes. The statements are (0)
           the statement immediately before the loop, (1) the statement
           immediately after (the loop itself), (2) the first statement in the
           loop, (3) the last statement in the loop, and (4) the loop itself.
        *)
        let insertStmtArr =
          if ConstrainVals.get() then (
            let stmtArr = Array.make 5 0 in
            let stmtLst = stmtsInStmt stmt in
            let rec getLoopBlk = function
              | [] -> (* Loop not found *)
                let str = "ConstrainVals flag enabled, but loop not found" in
                Self.warning "%s" str;
                None
              | h::t ->
                let (s,_) = Kernel_function.find_from_sid h in
                match s.skind with
                | Loop(_,blk,_,_,_) -> Some blk
                | _ -> getLoopBlk t
            in
            let rec hasLoop = function
              | [] -> false
              | h::t -> (
                  match h.skind with
                  | Block(b) -> hasLoop b.bstmts
                  | Loop(_) -> true
                  | _ -> false
                ) || hasLoop t
            in
            let loopBlock = getLoopBlk stmtLst in
            (match loopBlock with
             | Some blk ->
               if hasLoop blk.bstmts then
                 let str = "Nested loop detected -- assume statements " ^
                           "inserted in outer loop only" in
                 Self.warning "%s" str
             | None -> ());
            let sblk = getFnBlk stmt in
            let rec findLoop arr prv = function
              | [] ->
                let str = "ConstrainVal flag enabled, " ^
                          "but statement is not a loop" in
                raise (MC_Unsupported_Construct str)
              | h::t ->
                (match h.skind with
                 | Loop(_,blk,_,_,_) ->
                   let loopBlk = (List.nth blk.bstmts
                                    ((List.length blk.bstmts) - 1)) in
                   let lastStmt = match loopBlk.skind with
                     | Block(blk2) ->
                       List.nth blk2.bstmts ((List.length blk2.bstmts) - 1)
                     | _ -> loopBlk
                   in
                   arr.(0) <- prv.sid;
                   arr.(1) <- (if t <> [] then (List.hd t).sid else h.sid);
                   arr.(2) <- (List.hd blk.bstmts).sid;
                   arr.(3) <- lastStmt.sid;
                   arr.(4) <- h.sid;
                   arr
                 | _ -> findLoop arr prv t
                )
            in
            let rec buildStmtArr arr prv = function
              | [] -> arr
              | h::t ->
                match h.skind with
                | Block(b) ->
                  if h.sid = stmt.sid then findLoop arr prv b.bstmts
                  else
                    let bStmt = buildStmtArr arr prv b.bstmts in
                    if bStmt.(0) = 0 then buildStmtArr arr prv t else bStmt
                | _ ->
                  buildStmtArr arr prv t
            in buildStmtArr stmtArr (List.hd sblk.bstmts) sblk.bstmts
          ) else Array.make 0 0 in
        (* determine all variables in statement (including globals) *)
        (* HERE *)
        let lvals = lvalsInStmt stmt false true false in
        Self.warning "Assuming no RTEs";
        Annotations.iter_code_annot
          (fun _ ca -> match ca.annot_content with
             | AStmtSpec([],spec) ->
               (match spec.spec_behavior with
                | [bhv] ->
                  if List.length bhv.b_post_cond > 1 && ConstrainVals.get() 
                  then
                    let str = "Multiple ensures clauses not supported when " ^
                              "constrainVals flag enabled" in
                    raise (MC_Unsupported_Construct str)
                  else List.iter
                      (fun ens ->
                         let bp : bhvOrPred = Bhv bhv in
                         checkStmtPost ui fileName stmt !emitter ca bp ens
                           maxIter maxTime lvals insertStmtArr)
                      bhv.b_post_cond
                | _ ->
                  raise (MC_Unsupported_Construct
                           "Multiple Behaviors not supported")
               );
             | AStmtSpec(_,spec) ->
               raise (MC_Unsupported_Construct
                        "AStmtSpec behaviors not supported")
             (* following ignored for now, but may be potentially supportable *)
             | AAssert(_,_,pred) ->
               let bp : bhvOrPred = Pred pred in
               checkStmtPost ui fileName stmt !emitter ca bp
                 (Normal, Logic_const.new_predicate pred) maxIter
                 maxTime lvals insertStmtArr
             | AInvariant(_,_,_)
             | AVariant(_)
             | AAssigns(_,_)
             | AAllocation(_,_)
             | APragma(_)
             | AExtended(_,_,_) ->
               (Self.warning "Ignoring unsupported ACSL construct";
                Self.warning
                  "  (assert,invariant,variant,assigns,allocation,pragma)\n";)
          )
          stmt;
      )
    end; (* else (not single-iteration) *)
  end  (* if Enabled.get *)

let checkStmtContract2 ui bhv tk kf ki cilip =
  Self.warning "BOO"

let mcSelector
    (popup_factory:GMenu.menu GMenu.factory)
    main_ui ~button:_ localizable = match localizable with
  | Pretty_source.PStmt(kf,stmt) ->
    let callback () =
      (* stmt is selected annotation or annotation for selected
         statement (defaults to closest if multiple annotations exist *)
      checkStmtContract main_ui stmt
    in
    ignore (popup_factory#add_item
              "Prove contract using MC" ~callback)
  (* XXX REMOVE (probably) or implement following case *)
  | Pretty_source.PIP
      (Property.IPPredicate({ip_kind = Property.PKEnsures(bhv,tk); ip_kf;
                             ip_kinstr; ip_pred}))
    ->
    let callback () =
      checkStmtContract2 main_ui bhv tk ip_kf ip_kinstr ip_pred
    in
    ignore (popup_factory#add_item "Prove property using MC" ~callback)
  | _ -> ()

let mcMainGui main_ui = main_ui#register_source_selector mcSelector

let () = Design.register_extension mcMainGui
