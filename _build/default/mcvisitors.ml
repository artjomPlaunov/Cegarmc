module CT = Cil_types
module CB = Cil_builder.Pure
module T = Translate
module U = Utils

exception MC_Unsupported_Code_Annot of string

(* Copy Visitor for inserting <mc> function declarations into the
   global environment. Any actual function definitions needed by
   <mc> are appended at the start of the file, the main purpose
   for this visitor is to make function declarations available
   in case we need to insert assert or assume function calls later. *)
class insert_mc_functions prj =
object (_)
  inherit Visitor.generic_frama_c_visitor (Visitor_behavior.copy prj)

  method! vfile f =
    let module CT = CT in
    let params = ("", CT.TInt (CT.IInt, []), []) in
    let new_fun =
      Cil.makeGlobalVar "__VERIFIER_assert"
        (CT.TFun (CT.TVoid [], Some [ params ], false, []))
    in
    new_fun.vstorage <- CT.Extern;
    let cil_function =
      CT.Declaration (U.empty_spec, new_fun, None, new_fun.vdecl)
    in
    let kf = { CT.fundec = cil_function; spec = U.empty_spec } in
    let () = Globals.Functions.register kf in
    f.globals <-
      CT.GFunDecl (U.empty_spec, new_fun, new_fun.vdecl) :: f.globals;
    JustCopy
end
 
(* constructor for insert_mc_functions visitor. *)
let create_insert_mc_functions_visitor () =
  File.create_project_from_visitor "insert mc functions and declarations "
    (new insert_mc_functions)
 
(* Copy visitor for inserting an <mc> assert
  right before the ACSL assert that is selected,
  which is located via its sid, the parameter being passed
  to the copy visitor.
*)
class insert_mc_assert (sid : int) prj =
  object (_)
    inherit Visitor.generic_frama_c_visitor (Visitor_behavior.copy prj)

    (* An ACSL assert is tied to a statement, so in order to access it and
      insert  an <mc> assert function call statement, we perform the
      insertion at block level. *)
    method! vblock (b : CT.block) =
      (* Split the statements comprising the block on the sid
        of the ACSL assert predicate statement being verified.
      *)
      let stmts = b.bstmts in
      let stmts1, stmts2 = Utils.split_stmts_on_sid stmts sid in

      (* If stmts2 is empty, then we are in a different block.
        Just copy this block and move on.
      *)
      if stmts2 = [] then JustCopy
      else
        (* Otherwise, we are in the block with the assert to be
          verified, and we can insert an <mc> assert.
        *)

        (* Fetch the statement corresponding to the ACSL assert,
          fetch the assert code annotation, and convert the
          ACSL predicate to a CB exp.
        *)
        let assert_stmt = List.hd stmts2 in
        let code_annots = Annotations.code_annot assert_stmt in
        let assert_annot = List.hd code_annots in

        let acsl_exp =
          match assert_annot.annot_content with
          | CT.AAssert (_, tp) ->
              let pred_content = tp.tp_statement.pred_content in
              T.acsl_predicate_to_exp pred_content
          | _ ->
              raise
                (MC_Unsupported_Code_Annot
                  "Expected Assert Code annotation in insert_mc_assert vblock \
                    visitor")
        in

        (* Fetch the varinfo for the <mc> assert function,
          and construct a CB var for it. *)
        let ast = Ast.get () in
        let globals = ast.globals in
        let assume_varinfo, location = Utils.find_assert_varinfo globals in
        let assume_var = CB.var assume_varinfo in

        (* Construct a CT instruction
          which corresponds to an <mc> assert call.*)
        let fun_call = CB.call `none assume_var [ acsl_exp ] in
        let fun_call_instr = CB.cil_instr ~loc:location fun_call in

        (* Insert the <mc> assert function call as a new
          statement in the block. *)
        let newStmt = Cil.mkStmtOneInstr fun_call_instr in
        b.bstmts <- stmts1 @ [ newStmt ] @ stmts2;
        Cil.ChangeTo b
  end

(* Constructor for insert_mc_assert visitor. *)
let create_insert_mc_assert_visitor sid () =
  File.create_project_from_visitor "insert mc assert" (new insert_mc_assert sid)
