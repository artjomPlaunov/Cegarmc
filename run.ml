exception MC_Unsupported_Code_Annot of string

let (prove_assert_msg : string) = "Prove assert using model checking"

let model_check_assert (_ : Design.main_window_extension_points)
    (_ : Cil_types.stmt) () =
  ()

(* Check if code annotations are a single assert. *)
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

let get_code_annot_predicate (code_annot : Cil_types.code_annotation_node) :
    Cil_types.predicate =
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
           ACSL predicate. *)
        if code_annots_eq_standalone_assert code_annots then
          let assert_annot = (List.hd code_annots).annot_content in
          let predicate = get_code_annot_predicate assert_annot in
          let callback = model_check_assert main_ui stmt in
          ignore (popup_factory#add_item prove_assert_msg ~callback)
        else ()
  | _ -> ()

let model_checking_gui (main_ui : Design.main_window_extension_points) : unit =
  main_ui#register_source_selector model_checking_selector

let () = Design.register_extension model_checking_gui
