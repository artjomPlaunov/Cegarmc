open Cil_types
open Utils

(* This is a list of the vid's of the varinfos of variables that
   were initialized locally. This is necessary to handle Frama-C's
   Local_init type of instruction. *)
   let local_init : int list ref = ref []

module LvalSet = Set.Make (
  struct
    (* ordered by position, with pointer > pointee *)
    let compare =
      (fun v1 v2 ->
         match (v1,v2) with
         | ((Var(vi1),off1),(Var(vi2),off2)) ->
           if ((Stdlib.compare vi1.vdecl vi2.vdecl) = 0) then (
             if ((Stdlib.compare vi1.vid vi2.vid) = 0) then
               (Cil_datatype.Offset.compare off1 off2)
             else (Stdlib.compare vi1.vid vi2.vid)
           )
           else (Stdlib.compare vi1.vdecl vi2.vdecl)
         | ((Var(_vi1),_),(Mem(_),_)) -> -1
         | ((Mem(_),_),(Var(_vi2),_)) -> 1
         | _ ->
           Cil_datatype.LvalStructEq.compare v1 v2
      )
    type t = Cil_types.lval
  end
  )

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
  | StartOf(lval) -> isLvalGlobal lval
  | SizeOfE(expr)
  | AlignOfE(expr)
  | UnOp(_,expr,_)
  | CastE(_,expr) ->
  (*| Info(expr,_) *)
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
  let _lvalstr = ((Pretty_utils.to_string Printer.pp_lval) lval) in
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
  | CastE(_,expr) ->
  (*| Info(expr,_) -> *)
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
  | SingleInit expr -> 
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
    | Instr Set(lval,_expr,_) ->
      lvalsInLval lval assignedTo inStmt isFnName
    | Instr Call(Some lval,expr,_exprs,_) ->
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
    | Instr Call(None,expr,_exprs,_) ->
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
       | ConsInit(f,_args,_) ->
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
    | Return (Some _expr,_) ->
      LvalSet.empty
    | Switch (_expr,blk,_,_) ->
      lvalsInBlock blk assignedTo inStmt isFnName
    | If(_expr,blk1,blk2,_) ->
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

    | Switch (_expr,blk,_,_) ->
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
    | _ -> raise (MC_Unsupported_Construct "Try/Throw statements")
  )