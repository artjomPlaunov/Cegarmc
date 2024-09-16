module CT = Cil_types
module OPT = Options

let (mc_stmt_contract_msg : string) = "Prove statement contract using model checking"

let mc_stmt_contract 
  (s : CT.stmt) 
  (_cs : CT.code_annotation list) 
  (_ui : Design.main_window_extension_points) () : unit = 
  let _file_name = OPT.OutputFile.get () in 
  (* Get all lvalues (variables) in statement, including globals. *)
  let _lvals = LvalUtils.lvalsInStmt s false true false in
  () 

(* GUI selector for calling the model checker. *)
let model_checking_selector (popup_factory : GMenu.menu GMenu.factory)
    (ui : Design.main_window_extension_points) ~button:_
    (localizable : Pretty_source.localizable) =
  match localizable with
  (*  User has made a statement selection. *)
  | Printer_tag.PStmt (_, stmt) -> (
      if not (Annotations.has_code_annot stmt) then
        Options.Self.feedback "User Selection is empty"
      else
        let code_annots = Annotations.code_annot stmt in
        let callback = mc_stmt_contract stmt code_annots ui in 
        ignore (popup_factory#add_item mc_stmt_contract_msg ~callback)
      )
  | _ -> ()

let model_checking_gui (main_ui : Design.main_window_extension_points) : unit =
  main_ui#register_source_selector model_checking_selector

let () = Design.register_extension model_checking_gui
