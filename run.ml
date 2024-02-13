exception MC_Unsupported_Code_Annot of string

module T = Translate
module CT = Cil_types
module CB = Cil_builder.Pure
module U = Utils

let (prove_assert_msg : string) = "Prove assert using model checking"

(* Copy Visitor for inserting <mc> functions
   into the global environment. *)
class insert_mc_functions prj =
  object (_)
    inherit Visitor.generic_frama_c_visitor (Visitor_behavior.copy prj)

    method! vfile f =
      let module CT = CT in
      let params = ("", CT.TInt (CT.IInt, []), []) in
      let new_fun =
        Cil.makeGlobalVar "__VERIFIER_assert"
          (CT.TFun (CT.TVoid ([]), Some [ params ], false, []))
      in
      new_fun.vstorage <- CT.Extern;
      let cil_function = CT.Declaration (U.empty_spec, new_fun, None, new_fun.vdecl) in
      let kf = { CT.fundec = cil_function; spec = U.empty_spec } in
      let () = Globals.Functions.register kf in
      f.globals <- CT.GFunDecl (U.empty_spec, new_fun, new_fun.vdecl) :: f.globals;
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
        let assertStmt = List.hd stmts2 in
        let code_annots = Annotations.code_annot assertStmt in
        let assert_annot = List.hd code_annots in
        
        let acsl_exp =
          match assert_annot.annot_content with
          | CT.AAssert (_, tp) ->
              let pred_content = tp.tp_statement.pred_content in
              T.acsl_predicate_to_exp pred_content
          | _ ->
              raise
                (MC_Unsupported_Code_Annot
                   "Expected Assert Code annotation in \
                    insert_mc_assert vblock visitor")
        in

        (* Fetch the varinfo for the <mc> assert function,
           and construct a CB var for it. *)
        let ast = Ast.get () in
        let globals = ast.globals in
        let assume_varinfo, location = Utils.find_assert_varinfo globals in
        let assume_var = CB.var assume_varinfo in

        (* Construct a CT instruction
           which corresponds to an <mc> assert call.*)
        let funCall = CB.call `none assume_var [ acsl_exp ] in
        let funCallInstr = CB.cil_instr ~loc:location funCall in

        (* Insert the <mc> assert function call as a new
           statement in the block. *)
        let newStmt = Cil.mkStmtOneInstr funCallInstr in
        b.bstmts <- stmts1 @ [ newStmt ] @ stmts2;
        Cil.ChangeTo b
  end

(* Constructor for insert_mc_assert visitor. *)
let create_insert_mc_assert_visitor sid () =
  File.create_project_from_visitor "insert mc assert" (new insert_mc_assert sid)

(* Model check a standalone assert, i.e.,
   a basic reachability verification.
*)
let mc_standalone_assert (s : CT.stmt) () : unit =

  (* First, use a copy visitor to insert the necessary
     declarations and functions for the model checker. *)
  let insert_decls_prj = create_insert_mc_functions_visitor () in

  (* Next, use a copy visitor to create the project from
     which we call the model checker.
     This calls the insert_assert visitor to insert the
     <mc_verifier> assert function call.
  *)
  let mc_project =
    Project.on insert_decls_prj (create_insert_mc_assert_visitor s.sid) ()
  in

  (* Finally we print the AST to an output file, and this
     should be <mc> ready. *)
  Project.on mc_project
    (fun () ->
      let lines = ref [] in 
      let in_chan = open_in "cpa_defs.c" in 
      let cpa_headers = 
        try 
        while true; do
          lines := input_line in_chan :: !lines
          done; !lines
        with End_of_file ->
          close_in in_chan;
          List.rev !lines;
      in 
      let f = Ast.get () in
      let chan = open_out "cegarmc_output.c" in
      let fmt = Format.formatter_of_out_channel chan in
      let () = List.iter (fun s  -> Printf.fprintf chan "%s\n" s) cpa_headers in
      Printer.pp_file fmt f

      )
    ()

(* Check if code annotations have a standalone assert. *)
let has_standalone_assert (cs : CT.code_annotation list) : bool =
  if List.length cs <> 1 then false
  else
    match (List.hd cs).annot_content with
    | CT.AAssert (behaviors, _) ->
        (* We don't want any behaviors here, just looking for a standalone
           assert to model check. *)
        if List.length behaviors <> 0 then false else true
    | _ -> false

let model_checking_selector (popup_factory : GMenu.menu GMenu.factory)
    (_ : Design.main_window_extension_points) ~button:_
    (localizable : Pretty_source.localizable) =
  match localizable with
  (*  User has made a statement selection. *)
  | Printer_tag.PStmt (_, stmt) ->
      if not (Annotations.has_code_annot stmt) then
        Options.Self.feedback "Nothing to check here."
      else
        let code_annots = Annotations.code_annot stmt in
        (* Standalone Assert Verification *)
        if has_standalone_assert code_annots then
          let callback = mc_standalone_assert stmt in
          ignore (popup_factory#add_item prove_assert_msg ~callback)
        else ()
  | _ -> ()

let model_checking_gui (main_ui : Design.main_window_extension_points) : unit =
  main_ui#register_source_selector model_checking_selector

let () = Design.register_extension model_checking_gui
