exception MC_Unsupported_Code_Annot of string
exception MC_Varinfo_Not_Found 

let (prove_assert_msg : string) = "Prove assert using model checking"

let rec split_stmts_on_sid_aux res (stmts : Cil_types.stmt list) sid =
  match stmts with
  | [] -> (res, [])
  | hd :: tl ->
      if hd.sid = sid then (res, stmts)
      else split_stmts_on_sid_aux (res @ [ hd ]) tl sid

let split_stmts_on_sid (stmts : Cil_types.stmt list) (sid : int) :
    Cil_types.stmt list * Cil_types.stmt list =
  split_stmts_on_sid_aux [] stmts sid

let syntax_alarm =
  Emitter.create "Insert Assume For Standalone Assert Check"
    [ Emitter.Code_annot ] ~correctness:[] ~tuning:[]

let rec find_assume_varinfo globals = 
  match globals with 
  | [] -> raise MC_Varinfo_Not_Found
  | (Cil_types.GVarDecl (varinfo,location))::tl ->
    if varinfo.vname = "__VERIFIER_assume" then 
      (varinfo,location)
    else 
      find_assume_varinfo tl
  | _::tl -> find_assume_varinfo tl 


(* Copy Visitor for inserting an <model checker> assume function call
   right after a standalone ACSL assert contract. *)
   class insert_assume_decl prj =
   object (_)
     inherit Visitor.generic_frama_c_visitor (Visitor_behavior.copy prj)
 
     method! vfile (f) =
       let new_fun = Cil.makeGlobalVar "__VERIFIER_assume" (Cil_types.TFun (Cil_types.TVoid [], None, false, [])) in 
       f.globals <- (Cil_types.GVarDecl  (new_fun, new_fun.vdecl)) :: f.globals;
       JustCopy

   end
   
   



(* Copy Visitor for inserting an <model checker> assume function call
   right after a standalone ACSL assert contract. *)
class insert_assume_standalone_assert (sid : int) prj =
  object (_)
    inherit Visitor.generic_frama_c_visitor (Visitor_behavior.copy prj)

    method! vblock (b : Cil_types.block) =
      let ast = Ast.get () in
      let globals = ast.globals in 
      let (assume_varinfo, location) = find_assume_varinfo globals in 
      let assume_var = Cil_builder.Pure.var assume_varinfo in 
      let funCall = Cil_builder.Pure.call `none assume_var [] in
      let funCallInstr = Cil_builder.Pure.cil_instr ~loc:location funCall in 
      let stmts = b.bstmts in
      let stmts1, stmts2 = split_stmts_on_sid stmts sid in
      let newStmt = Cil.mkStmtOneInstr funCallInstr in
      b.bstmts <- stmts1 @ [ newStmt ] @ stmts2;
      Cil.ChangeTo b
  end

let create_insert_assume_standalone_assert_project (sid : int) () =
  ignore
    (File.create_project_from_visitor "insert assume for standalone assert"
       (new insert_assume_standalone_assert sid))

let create_insert_assume_decl () =
ignore
  (File.create_project_from_visitor "insert assume decl"
      (new insert_assume_decl))

(* Call the model checker on a *standalone* assert contract.

   TODO: right now, the plugin only integrates with CPAchecker;
   once support for other model checkers is added, there is a different
   assume functional call syntax for each model checker (SATABS, CBMC).
*)
let model_check_standalone_assert (_ : Design.main_window_extension_points)
    (s : Cil_types.stmt) () : unit =
  let newPrj =
    File.create_project_from_visitor "insert assume decl"
      (new insert_assume_decl)
  in

  Project.on newPrj
    (fun () ->
      let finalPrj = 
        File.create_project_from_visitor "insert assume"
        (new insert_assume_standalone_assert s.sid)
      in 
      Project.on finalPrj
        (fun () -> 
          let f = Ast.get () in
          let chan = open_out "cegarmc_output.c" in
          let fmt = Format.formatter_of_out_channel chan in
          Printer.pp_file fmt f) () ) ()

(* Check if code annotations is a single assert. *)
let code_annots_eq_standalone_assert (cs : Cil_types.code_annotation list) :
    bool =
  if List.length cs <> 1 then false
  else
    match (List.hd cs).annot_content with
    | Cil_types.AAssert (behaviors, _) ->
        (* We don't want any behaviors here, just looking for a standalone
           assert to model check. *)
        if List.length behaviors <> 0 then false else true
    | _ -> false

(* Fetch the predicate from an assert code annotation.*)
let get_code_annot_assert_predicate
    (code_annot : Cil_types.code_annotation_node) : Cil_types.predicate =
  match code_annot with
  | AAssert (_, tp) -> tp.tp_statement
  | _ ->
      raise
        (MC_Unsupported_Code_Annot
           "Unsupported code annotation in get_code_annot_predicate")

let model_checking_selector (popup_factory : GMenu.menu GMenu.factory)
    (main_ui : Design.main_window_extension_points) ~button:_
    (localizable : Pretty_source.localizable) =
  match localizable with
  (*  User has made a statement selection. *)
  | Printer_tag.PStmt (_, stmt) ->
      (*  Check if statement has any code annotations. *)
      if not (Annotations.has_code_annot stmt) then
        Options.Self.feedback "Nothing to check here."
      else
        (*  Fetch statement code annotations. *)
        let code_annots = Annotations.code_annot stmt in
        (* Model Check an assert.
           This is the simplest case, when there is a stand-alone assert
           ACSL predicate to be verified by a model checker. *)
        if code_annots_eq_standalone_assert code_annots then
          let assert_annot = (List.hd code_annots).annot_content in
          let _ = get_code_annot_assert_predicate assert_annot in
          let callback = model_check_standalone_assert main_ui stmt in
          ignore (popup_factory#add_item prove_assert_msg ~callback)
        else ()
  | _ -> ()

let model_checking_gui (main_ui : Design.main_window_extension_points) : unit =
  main_ui#register_source_selector model_checking_selector

let () = Design.register_extension model_checking_gui
