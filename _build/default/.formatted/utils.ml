module CT = Cil_types

exception MC_Varinfo_Not_Found

let empty_spec =
  {
    CT.spec_behavior = [];
    CT.spec_variant = None;
    CT.spec_terminates = None;
    CT.spec_complete_behaviors = [];
    CT.spec_disjoint_behaviors = [];
  }

(*
    Search globals declarations to fetch (varinfo,location)
    of a model checker's function.

    Right now this is just for the model checker's assert function, 
    but this will be generalized. 
*)
let rec find_assert_varinfo globals =
  match globals with
  | [] -> raise MC_Varinfo_Not_Found
  | CT.GFunDecl (_, varinfo, location) :: tl ->
      if varinfo.vname = "__VERIFIER_assert" then (varinfo, location)
      else find_assert_varinfo tl
  | _ :: tl -> find_assert_varinfo tl

(* helper function for split_stmts_on_sid. *)
let rec split_stmts_on_sid_aux res (stmts : CT.stmt list) sid =
  match stmts with
  | [] -> (res, [])
  | hd :: tl ->
      if hd.sid = sid then (res, stmts)
      else split_stmts_on_sid_aux (res @ [ hd ]) tl sid

(* Split a list of statements in two, with stmt sid used as delimieter.*)
let split_stmts_on_sid (stmts : CT.stmt list) (sid : int) :
    CT.stmt list * CT.stmt list =
  split_stmts_on_sid_aux [] stmts sid
