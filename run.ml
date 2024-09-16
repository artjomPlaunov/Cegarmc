module CT = Cil_types
module CB = Cil_builder.Pure
module MCV = Mcvisitors
module U = Utils
module OPT = Options



(* This type delineates supported ACSL expressions for model checking. 
   The two supported types are currently a standalone assert or a 
   statement contract. 

   This is meant to explicitly delineate what is supported by Cegarmc 
   and otherwise throw an error if the user tries to verify anything 
   else (the Unknown type).
*)
type mc_contract_type = 
   Assert | StmtContract | Unknown

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

let get_mc_contract_type code_annots = 
  if has_standalone_assert code_annots then Assert 
  else Unknown


let (mc_assert_msg : string) = "Prove assert using model checking"
let (mc_stmt_contract_msg : string) = "Prove statement contract using model checking"

let mc_assert_emitter =
  Emitter.create "mc_assert"
    [ Emitter.Property_status ]
    ~correctness:[] ~tuning:[]

let output_mc_file () = 
  let f = Ast.get () in
    let chan = open_out "cegarmc_output.c" in
    let fmt = Format.formatter_of_out_channel chan in
    let cpa_headers = U.read_mc_defs "cpa_defs.h" in 
    let () = List.iter (fun s -> Printf.fprintf chan "%s\n" s) cpa_headers in
    Printer.pp_file fmt f

let run_mc () : int = 
  let cpa_cmd =
    "$CPACHECKER/scripts/cpa.sh -predicateAnalysis cegarmc_output.c"
  in
  (* Handle case with bad script command. *)
  let _ = Sys.command cpa_cmd in
  Sys.command "./mc-helper.sh < output/Statistics.txt"


(* Model check a standalone assert, i.e.,
   a basic reachability verification.
*)
let mc_standalone_assert 
  (s : CT.stmt) 
  (c : CT.code_annotation) 
  (ui : Design.main_window_extension_points) () : unit =
  
  (* First, use a copy visitor to insert the necessary
     declarations and functions for the model checker. 
  *)
  let insert_decls_prj = MCV.create_insert_mc_functions_visitor () in
  
  (* Next, use a copy visitor to create the project from
     which we call the model checker.
     This calls the insert_assert visitor to insert the
     <mc_verifier> assert function call.
  *)
  let mc_project =
    Project.on insert_decls_prj (MCV.create_insert_mc_assert_visitor s.sid) ()
  in
  (* Finally we print the AST to an output file, and this
     should be <mc> ready. 
  *)
  Project.on mc_project (fun () -> output_mc_file ()) ();

  (* Run <mc> on generated file and register property status. *)
  let mc_result = run_mc () in 
  let kf = Kernel_function.find_englobing_kf s in
  let p = Property.ip_of_code_annot_single kf s c in

  match mc_result with
  | 0 ->
      Options.Self.feedback "MC Verification: TRUE";
      Property_status.emit mc_assert_emitter ~hyps:[] p Property_status.True;
      ui#rehighlight ()
  | 1 -> Options.Self.feedback "FALSE/UNKNOWN"
  | _ -> Options.Self.feedback "somethin' else"

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
        match get_mc_contract_type code_annots with 
        (* Assert verification. *)
        | Assert -> 
            let callback = mc_standalone_assert stmt (List.hd code_annots) ui in
            ignore (popup_factory#add_item mc_assert_msg ~callback)
        (* Statement contract verification. *)
        | StmtContract -> ()
        | Unknown -> 
            let callback = mc_stmt_contract stmt code_annots ui in 
            ignore (popup_factory#add_item mc_stmt_contract_msg ~callback)
      )
  | _ -> ()

let model_checking_gui (main_ui : Design.main_window_extension_points) : unit =
  main_ui#register_source_selector model_checking_selector

let () = Design.register_extension model_checking_gui
