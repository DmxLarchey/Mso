
structure spodef = struct val thy = the_context () end ;
val _ = use_legacy_bindings spodef.thy ;

val rel_refl = order_refl RS rel_subsetD ;
val s_gpocE = tacthm Safe_tac (rel_refl RS s_gpoc.elims) ;

AddSIs [pord_of.intros] ;
AddSEs [spo_spo2.subtI] ;
val spo_intrs = (spo_spo2.intros RL [spo_spo2.spo2I]) @ spo_spo2.intros ;
val spo_elim = tacthm (eresolve_tac spo_spo2.elims 2) (hd spo_spo2.elims) ;
val spo_induct = rotate_prems ~1 
  (tacthm (chop_tac 1 (atac 3)) spo_spo2.induct RS conjunct1 RS mp) ;

val _ = qed_goalw_spec_mp "mono_s_gpoc" spodef.thy [mono_def]
  "mono screl --> mono (s_gpoc screl q)"
  (fn _ => [Safe_tac, (etac s_gpoc.elims 1),
    (safe_tac (ces s_gpoc.intros)), Auto_tac]) ;

val _ = qed_goalw_spec_mp "s_gpoc_ii" spodef.thy [inv_image_def]
  "s_gpoc screl qord r = pord_of qord Un (qord Int inv_image (screl r) isubts)"
  (fn _ => [ (safe_tac (ces (s_gpocE :: s_gpoc.intros))), 
    (case_tac "a" 2), (case_tac "b" 2), 
    (safe_tac (ces (s_gpocE :: s_gpoc.intros))), Auto_tac]) ;

val _ = qed_goal_spec_mp "wf_pq" spodef.thy 
  "trans q --> ?P --> wf r --> wf (pord_of q Un (q Int r))"
  (fn _ => [ (Safe_tac), (rtac wfUn_absl 1), atac 2, 
    (rtac wf_subset 2), (atac 2 THEN Fast_tac 2),
    (safe_tac (ces [pord_of.elims])), 
    rewtac trans_def, (TRYALL Fast_tac) ]) ;

val _ = qed_goal_spec_mp "wf_s_gpoc" spodef.thy 
  "?Q --> ?P --> wf (screl r) --> wf (s_gpoc screl qord r)"
  (fn _ => [ (clarsimp_tac (cesimps [s_gpoc_ii]) 1),
    (eatac wf_pq 1 1), (etac wf_inv_image 1) ]) ;
   
val _ = qed_goalw_spec_mp "wf_s_gpoc_der" spodef.thy [wf_der_def]
  "?Q --> ?P --> wf_der screl --> wf_der (s_gpoc screl qord)"
  (fn _ => [ (Safe_tac), (eatac wf_s_gpoc 1 1), Fast_tac 1]) ;

val _ = qed_goalw_spec_mp "wf_af_der" spodef.thy [wf_gpoc_fwf_def]
  "wf_derl_fwf screl --> wf_gpoc_fwf isubt (s_gpoc screl qord)"
  (fn _ => [ Safe_tac, (etac s_gpocE 1), (etac s_gpoc.r2I 1),
    Safe_tac, (etac s_gpoc.r3I 1), (etac wf_derl_fwfD 1), atac 2,
    (fast_tac (cis [isubt_psubt]) 1) ]) ;

val _ = qed_goalw_spec_mp "s_gpoc_props" spodef.thy [gpoc_props_def]
  "?Q --> ?P --> spoc_props screl --> gpoc_props isubt (s_gpoc screl qord)"
  (fn _ => [ Safe_tac, (rtac mono_s_gpoc 1),
    (rtac wf_s_gpoc_der 2), (rtac wf_af_der 5),
    (rewtac spoc_props_def), Safe_tac, Auto_tac ]) ;

val gslem1 = prove_goal spodef.thy 
  "((a, b) : gpo isubt (s_gpoc scr q) --> (a, b) : spo scr q) & \
    \ ((c, d) : gpo2 isubt (s_gpoc scr q) --> (c, d) : spo2 scr q)"
  (fn _ => [ (rtac gpo_gpo2.induct 1),
    (etac s_gpoc.elims 1), (TRYALL (etac isubt.elims)),
    (case_tac "ta" 1), Safe_tac,
    (TRYALL (eresolve_tac spo_spo2.intros)), atac 2, Auto_tac]) ;

val gslem2 = prove_goal spodef.thy 
  "((a, b) : spo scr q --> (a, b) : gpo isubt (s_gpoc scr q)) & \
    \ ((c, d) : spo2 scr q --> (c, d) : gpo2 isubt (s_gpoc scr q))"
  (fn _ => [ (rtac spo_spo2.induct 1),
    (TRYALL (dtac isubt.isubtI)),
    (TRYALL (eresolve_tac gpo_gpo2.intros)), atac 3, 
    (TRYALL (resolve_tac gpo_gpo2.intros)),
    (TRYALL (ematch_tac s_gpoc.intros)),
    (rewtac (mk_eq isubt_iff)), (fold_goals_tac [Ball_def]),
    (TRYALL (etac ball_match THEN' Fast_tac)), (rtac order_refl 1), 
    (res_inst_tac [("B", "spot")] Int_lower1 2),
    (subgoal_tac "gpo isubt (s_gpoc scr q) Int spot = spot" 1), Auto_tac ]) ;

val ths = msc gslem1 @ msc gslem2 ;

val _ = qed_goal "gpo_spo" spodef.thy 
  "gpo isubt (s_gpoc screl qord) = spo screl qord"
  (fn _ => [ Safe_tac, (TRYALL (eresolve_tac ths)) ]) ;
    
val spocwf = rewrite_rule [mk_eq gpo_spo] 
  ([wf_isubt, s_gpoc_props] MRS gpocwf) ;

