

structure lpodef = struct val thy = the_context () end ;
val _ = use_legacy_bindings lpodef.thy ;

val _ = qed_goalw "corl_props_lex" cpodef.thy [corl_props_def']
  "corl_props lex"
  (fn _ => [ Safe_tac, (eatac lex_mono' 1 1),
    (etac (mk_mono' onerel_lex) 1), (eatac wf_lex_fwf 1 1) ]) ;

val cpo_lex = corl_props_lex RSN (2, cpocsn) ;

val _ = qed_goal "lpo_cpo" lpodef.thy "lpo = cpo lex"
  (fn _ => [ (rtac ext 1), Safe_tac,
    (etac lpo.induct 1), (TRYALL (fast_tac (ces cpo.intros))),
    (etac cpo.induct 1), (TRYALL (fast_tac (ces lpo.intros))),
    (rtac lpo.lexI 1), (etac lex_mono' 1), TRYALL Fast_tac ]) ;

val lposn = fold_rule [mk_eq lpo_cpo] cpo_lex ;

