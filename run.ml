exception MC_Unsupported_Code_Annot of string
exception MC_Varinfo_Not_Found
exception MC_Unsupported_Predicate_to_C_Conversion
exception MC_Unsupported_Term_to_C_Conversion
exception MC_Unsupported_Logic_Constant_to_C_Conversion
exception MC_Unsupported_Term_lhost_to_C_Conversion

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

let rec find_assert_varinfo globals =
  match globals with
  | [] -> raise MC_Varinfo_Not_Found
  | Cil_types.GVarDecl (varinfo, location) :: tl ->
      if varinfo.vname = "__VERIFIER_assert" then (varinfo, location)
      else find_assert_varinfo tl
  | _ :: tl -> find_assert_varinfo tl

(* Copy Visitor for inserting an <model checker> assume function call
   right after a standalone ACSL assert contract. *)
class insert_assert_decl prj =
  object (_)
    inherit Visitor.generic_frama_c_visitor (Visitor_behavior.copy prj)

    method! vfile f =
      let new_fun =
        Cil.makeGlobalVar "__VERIFIER_assert"
          (Cil_types.TFun (Cil_types.TVoid [], None, false, []))
      in
      f.globals <- Cil_types.GVarDecl (new_fun, new_fun.vdecl) :: f.globals;
      JustCopy
  end

let acsl_logic_constant_to_exp (lc : Cil_types.logic_constant) =
  let module CT = Cil_types in
  let module CB = Cil_builder.Pure in
  match lc with 
  | Integer (x, _) -> CB.of_integer x
  | _ -> raise MC_Unsupported_Logic_Constant_to_C_Conversion

let acsl_term_lhost_to_exp (tlh : Cil_types.term_lhost) = 
  let module CT = Cil_types in
  let module CB = Cil_builder.Pure in
  match tlh with
  | TVar lv -> (
    match lv.lv_origin with 
    | Some varinfo -> CB.var varinfo
    | None -> raise MC_Unsupported_Term_lhost_to_C_Conversion)
  | _ -> raise MC_Unsupported_Term_lhost_to_C_Conversion

let rec acsl_term_to_exp (term : Cil_types.term) :
    Cil_builder.Pure.exp = 
    let module CT = Cil_types in
    let module CB = Cil_builder.Pure in
    match term.term_node with
    | CT.TConst lc -> 
      acsl_logic_constant_to_exp lc
    | CT.TLval (lhost,_) -> acsl_term_lhost_to_exp lhost
    | TLogic_coerce (_,t) -> acsl_term_to_exp t  
    | _ -> raise MC_Unsupported_Term_to_C_Conversion




let acsl_predicate_to_exp (predicate : Cil_types.predicate_node) :
    Cil_builder.Pure.exp =
  let module CT = Cil_types in
  let module CB = Cil_builder.Pure in
  match predicate with
  | CT.Prel (Req, t1, t2) -> 
    let e1 = acsl_term_to_exp t1 in 
    let e2 = acsl_term_to_exp t2 in 
    CB.( == ) e1 e2
  | _ -> raise MC_Unsupported_Predicate_to_C_Conversion


class insert_assert (sid : int) prj =
  object (_)
    inherit Visitor.generic_frama_c_visitor (Visitor_behavior.copy prj)

    method! vblock (b : Cil_types.block) =
      let ast = Ast.get () in
      let globals = ast.globals in
      let assume_varinfo, location = find_assert_varinfo globals in
      let assume_var = Cil_builder.Pure.var assume_varinfo in

      let stmts = b.bstmts in
      let stmts1, stmts2 = split_stmts_on_sid stmts sid in
      let assertStmt = List.hd stmts2 in
      let code_annots = Annotations.code_annot assertStmt in
      let assert_annot = List.hd code_annots in
      let e =
        match assert_annot.annot_content with
        | Cil_types.AAssert (_, tp) ->
            let pred_content = tp.tp_statement.pred_content in
            acsl_predicate_to_exp pred_content
        | _ ->
            raise
              (MC_Unsupported_Code_Annot
                 "Expected Assert Code annotation in \
                  insert_assume_standalone_assert vblock visitor")
      in
      let funCall = Cil_builder.Pure.call `none assume_var [ e ] in
      let funCallInstr = Cil_builder.Pure.cil_instr ~loc:location funCall in

      let newStmt = Cil.mkStmtOneInstr funCallInstr in
      b.bstmts <- stmts1 @ [ newStmt ] @ stmts2;
      Cil.ChangeTo b
  end

let create_insert_assume_standalone_assert_project (sid : int) () =
  ignore
    (File.create_project_from_visitor "insert assert"
       (new insert_assert sid))

let create_insert_assume_decl () =
  ignore
    (File.create_project_from_visitor "insert assume decl"
       (new insert_assert_decl))

let model_check_standalone_assert (_ : Design.main_window_extension_points)
    (s : Cil_types.stmt) () : unit =
  let newPrj =
    File.create_project_from_visitor "insert assume decl"
      (new insert_assert_decl)
  in

  Project.on newPrj
    (fun () ->
      let finalPrj =
        File.create_project_from_visitor "insert assert"
          (new insert_assert s.sid)
      in
      Project.on finalPrj
        (fun () ->
          let f = Ast.get () in
          let chan = open_out "cegarmc_output.c" in
          let fmt = Format.formatter_of_out_channel chan in
          Printer.pp_file fmt f)
        ())
    ()

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
        let code_annots = Annotations.code_annot stmt in
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
