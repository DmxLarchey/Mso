
structure mpodef = struct val thy = the_context () end ;
val _ = use_legacy_bindings mpodef.thy ;

val _ = qed_goalw "corl_props_smsol" mpodef.thy [corl_props_def']
  "corl_props smsol"
  (fn _ => [ (safe_tac (claset () delrules [subsetI])),
    (etac smsol_mono 1), (rtac onerel_smsol 1),
    (etac wf_smsol 1), (eatac smsol_fwfI 1 1) ]) ;

val cpo_smsol = corl_props_smsol RSN (2, cpocsn) ;
    
val _ = qed_goal "mpo_cpo" mpodef.thy "mpo = cpo smsol"
  (fn _ => [ (rtac ext 1), Safe_tac,
    (etac mpo.induct 1), (subgoal_tac "(ts, ss) : smsol ?s" 1),
    (simp_tac (esimps [smsol_def, inv_image_def]) 2),
    (etac cpo.corlI 1), 
    (TRYALL (fast_tac (ces cpo.intros))),
    (Clarify_tac 1), (dtac in_smso 1), 
    (simp_tac (esimps [mset_set]) 1),
    (clarsimp_tac (cesimps [mset_set]) 1), 
    Safe_tac, (TRYALL (fast_tac (ces cpo.intros))),

    (etac cpo.induct 1), (TRYALL (fast_tac (ces mpo.intros))),
    (rtac mpo.msoI 1),
    (full_simp_tac (esimps [smsol_def, inv_image_def]) 1),
    (etac (mk_mono' smso_mono) 1), Fast_tac 1 ]) ;

val mposn = fold_rule [mk_eq mpo_cpo] cpo_smsol ;

