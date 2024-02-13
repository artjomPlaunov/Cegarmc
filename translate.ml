exception MC_Unsupported_Logic_Constant_to_C_Conversion
exception MC_Unsupported_Term_to_C_Translation
exception MC_Unsupported_Predicate_to_C_Translation
exception MC_Unsupported_Term_lhost_to_C_Translation

module CT = Cil_types
module CB = Cil_builder.Pure

let acsl_logic_constant_to_exp (lc : CT.logic_constant) =
  match lc with
  | CT.Integer (x, _) -> CB.of_integer x
  | _ -> raise MC_Unsupported_Logic_Constant_to_C_Conversion

let acsl_term_lhost_to_exp (tlh : CT.term_lhost) =
  match tlh with
  | TVar lv -> (
      match lv.lv_origin with
      | Some varinfo -> CB.var varinfo
      | None -> raise MC_Unsupported_Term_lhost_to_C_Translation)
  | _ -> raise MC_Unsupported_Term_lhost_to_C_Translation

let rec acsl_term_to_exp (term : CT.term) : CB.exp =
  match term.term_node with
  | CT.TConst lc -> acsl_logic_constant_to_exp lc
  | CT.TLval (lhost, _) -> acsl_term_lhost_to_exp lhost
  | TLogic_coerce (_, t) -> acsl_term_to_exp t
  | _ -> raise MC_Unsupported_Term_to_C_Translation

let acsl_predicate_to_exp (predicate : CT.predicate_node) : CB.exp =
  match predicate with
  | CT.Prel (Req, t1, t2) ->
      let e1 = acsl_term_to_exp t1 in
      let e2 = acsl_term_to_exp t2 in
      CB.( == ) e1 e2
  | _ -> raise MC_Unsupported_Predicate_to_C_Translation
