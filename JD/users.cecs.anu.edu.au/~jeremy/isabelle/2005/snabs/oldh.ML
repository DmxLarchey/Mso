
(* contains results used only for old proof *)

(* not sure if we want the _tc versions *)

val _ = qed_goal_spec_mp "cut1_hlem_tc_alt'" hier.thy 
  "(a, b) : (nured X)^+ --> symb_of b ~: S --> \
    \ (a, b) : (hds_notin S Int nured X)^+" 
  (fn _ => [ (rtac impI 1), (etac trancl_induct 1), 
    (clarsimp_tac (cis [r_into_trancl], esimps [nured_def]) 1),
    (etac oneup.elims 1), Force_tac 1,
    Clarify_tac 1, (dtac (nured_def RS def_imp_eq RS equalityD1') 1),
    (etac oneup.elims 1), Clarsimp_tac 1,
    (etac (nth (transitive_closure_trans, 3)) 1), 
    (clarsimp_tac (cesimps [nured_def]) 1) ]) ;

val _ = qed_goal_spec_mp "cut1_hlem_tc'" hier.thy 
  "(a, b) : (nured X)^+ --> symb_of a ~: S --> \
    \ (a, b) : (hds_notin S Int nured X)^+" 
  (fn _ => [ (rtac impI 1), 
    (etac converse_trancl_induct 1), 
    (clarsimp_tac (cis [r_into_trancl], esimps [nured_def]) 1),
    (etac oneup.elims 1), Force_tac 1,
    Clarify_tac 1, (dtac (nured_def RS def_imp_eq RS equalityD1') 1),
    (etac oneup.elims 1), Clarsimp_tac 1,
    (rtac (nth (transitive_closure_trans, 4)) 1), atac 2,
    (clarsimp_tac (cesimps [nured_def]) 1) ]) ;

val _ = qed_goal_spec_mp "cut1_hlem_rtc'" hier.thy 
  "(a, b) : (nured X)^* --> symb_of a ~: S --> \
    \ (a, b) : (hds_notin S Int nured X)^*" 
  (fn _ => [ (rtac impI 1), 
    (etac converse_rtrancl_induct 1), Fast_tac 1,
    Clarify_tac 1, (dtac (nured_def RS def_imp_eq RS equalityD1') 1),
    (etac oneup.elims 1), Clarsimp_tac 1,
    (rtac (nth (transitive_closure_trans, 6)) 1), atac 2,
    (clarsimp_tac (cesimps [nured_def]) 1) ]) ;

val _ = qed_goal_spec_mp "cut1_hlem_tc" hier.thy 
  "c1 <= hds_notin S --> (nured X)^+ O c1 <= (hds_notin S Int nured X)^+ O c1"
  (fn _ => [ Safe_tac, (datac subsetD 1 1), (etac rel_compI 1),
    (etac cut1_hlem_tc' 1), (case_tac "y" 1), Auto_tac ]) ;

val _ = qed_goal_spec_mp "cut1_hlem_rtc" hier.thy 
  "c1 <= hds_notin S --> (nured X)^* O c1 <= (hds_notin S Int nured X)^* O c1"
  (fn _ => [ Safe_tac, (datac subsetD 1 1), (etac rel_compI 1),
    (etac cut1_hlem_rtc' 1), (case_tac "y" 1), Auto_tac ]) ;

val [chl_tc, chl_rtc] = [cut1_hlem_rtc] RL [trancl_mono', rtrancl_mono] ;

val _ = qed_goalw_spec_mp "cut1_hlem_gip" hier.thy [gip_rel_alt]
  "c1 <= hds_notin S --> c1 O any <= gip_rel c1 (nured X) --> \
    \ c1 O any <= gip_rel c1 (hds_notin S Int nured X)"
  (fn _ => [ (strip_tac 1), (rtac subsetI 1), (datac subsetD 1 1),
    (REPEAT1 (etac UnE 1)), (etac UnI2 3),
    (chop_tac 1 (etac rel_compE 2)),
    (ftac cut1_hlem_tc 2), (datac subsetD 1 2),
    (ftac chl_rtc 2), (datac subsetD 1 2), Fast_tac 2,
    (Clarify_tac 1), (etac cut1_hlem_tc_alt' 1), 
    (force_tac (ces [hds_notin.elims], esimps []) 1) ]) ;

val _ = qed_goal_spec_mp "cut1_ha_gip" hier.thy 
  "c1 <= hds_notin S --> cut1_gip_propa c1 ?Y --> cut1_gip_propa c1 X --> \
    \ s = ctxt (hds_notin S Int nured X) --> c1 O s <= gip_rel c1 s"
  (fn _ => [ (clarsimp_tac (HOL_cs, esimps [red_cases', O_Un]) 1),
    (rewrite_goals_tac [cut1_gip_propa_def']), 
    (rtac conjI 1), (etac subset_trans 1),
    (fast_tac (ces [gip_rel_mono']) 1),
    (chop_tac 1 (datac cut1_hlem_gip 1 1)),
    (rtac (subset_trans RS subset_trans) 1), (chop_tac 2 (atac 2)),
    (rtac gip_rel_mono 2), (rtac rel_comp_mono 1), Auto_tac ]) ;

val _ = bind_thm ("cut1_h_gip",
  rem_dup_prems (tacthm (TRYALL (rtac cut1_gip_propaI)) cut1_ha_gip)) ;

(* cut1_ha_gip above identifies uses of cut1_gip_prop
val _ = qed_goal_spec_mp "cut1_h_gip" hier.thy 
  "c1 <= hds_notin S --> cut1_gip_prop c1 --> \
    \ s = ctxt (hds_notin S Int nured X) --> c1 O s <= gip_rel c1 s"
  (fn _ => [ (clarsimp_tac (HOL_cs, esimps [red_cases', O_Un]) 1),
    (rewrite_goals_tac [cut1_gip_prop_def']), 
    (rtac conjI 1), (etac allE 1), (etac subset_trans 1),
    (fast_tac (ces [gip_rel_mono']) 1),
    (etac allE 1), (datac cut1_hlem_gip 1 1),
    (rtac (subset_trans RS subset_trans) 1), (chop_tac 1 (atac 2)),
    (rtac gip_rel_mono 2), (rtac rel_comp_mono 1), Auto_tac ]) ;
*)

val _ = qed_goal_spec_mp "cut1_ha" hier.thy 
  "c1 <= hds_notin S --> cut1_propa c1 ?Y --> cut1_propa c1 X --> \
    \ s = ctxt (hds_notin S Int nured X) --> c1 O s <= s^* O c1"
  (fn _ => [ (safe_tac (cds [red_cases' RS equalityD1'])), 
    (rewtac cut1_propa_def), 
    (dtac subsetD 1 THEN eatac rel_compI 1 1),
    (etac rel_comp_mono' 1), (rtac rtrancl_mono 1),
    (rtac red_nured_sub 1), Fast_tac 1, 
    (dtac subsetD 1 THEN eatac rel_compI 1 1),
    (dtac cut1_hlem_rtc 1), (datac subsetD 1 1),
    (EVERY [(etac rel_comp_mono' 1), (rtac rtrancl_mono 1), 
      (rtac r_into_red 1)]), (rtac order_refl 1) ]) ;

val _ = bind_thm ("cut1_h",
  rem_dup_prems (tacthm (TRYALL (rtac cut1_propaI)) cut1_ha)) ;

(* cut1_ha above identifies uses of cut1_prop
val _ = qed_goal_spec_mp "cut1_h" hier.thy 
  "c1 <= hds_notin S --> cut1_prop c1 --> \
    \ s = ctxt (hds_notin S Int nured X) --> c1 O s <= s^* O c1"
  (fn _ => [ (safe_tac (cds [red_cases' RS equalityD1'])), 
    (rewtac cut1_prop_def), (etac allE 1), 
    (dtac subsetD 1 THEN eatac rel_compI 1 1),
    (etac rel_comp_mono' 1), (rtac rtrancl_mono 1),
    (rtac red_nured_sub 1), Fast_tac 1, 
    (etac allE 1), (dtac subsetD 1 THEN eatac rel_compI 1 1),
    (dtac cut1_hlem_rtc 1), (datac subsetD 1 1),
    (EVERY [(etac rel_comp_mono' 1), (rtac rtrancl_mono 1), 
      (rtac r_into_red 1)]), (rtac order_refl 1) ]) ;
*)

fun rtaca1 th = rtac th THEN' EVERY' (replicate (nprems_of th - 1) atac) ;

structure gip = struct 
  val ths = map (tacthm (TRYALL (rtac refl))) [ cut1_ha_gip,
    cut1_gip_propa_def' RS defD1, wfh_lem3a_gip, wfh_lem3b_gip] ;
  val ths1 = ths RL [subset_trans] ;
  val htac = FIRST' (map rtaca1 ths1) ;
  end ;

val _ = qed_goalw_spec_mp "wfh_lem4a_gip'" hier.thy [cuth_def, sn2_alt_def]
  "r = (cuth S r0s c1) --> s = sn2_alt S r0s r1s --> \
    \ r0s <= rule0_hd_S S --> r1s <= hds_notin S --> c1 <= hds_notin S --> \
    \ cut1_gip_propa c1 ?X --> cut1_gip_propa c1 ?Y --> \
    \ cut1_gip_propa c1 ?Z --> r O s <= gip_rel r s"
  (fn _ => [ (clarsimp_tac (cesimps [O_Un, Un_O]) 1), 
    (REPEAT_SOME (rtac conjI)), (ALLGOALS gip.htac),
    (ALLGOALS (rtac gip_rel_mono)), Auto_tac ]) ;

val wfh_lem4a_gip = wfh_lem4a_gip' RS wfUn_gip ;

val _ = bind_thm ("wfh_lem4_gip",
  rem_dup_prems (tacthm (TRYALL (rtac cut1_gip_propaI)) wfh_lem4a_gip)) ;

structure orig = struct 
  val ths = map (tacthm (TRYALL (rtac refl))) 
    [cut1_ha, cut1_propa_def RS defD1, wfh_lem3a, wfh_lem3b] ;
  val ths1 = ths RL [subset_trans] ;
  val htac = FIRST' (map rtaca1 ths1) ;
  end ;

val _ = qed_goalw_spec_mp "wfh_lem4a'" hier.thy [sn2_alt_def]
  "r = (cuth S r0s c1) --> s = sn2_alt S r0s r1s --> \
    \ r0s <= rule0_hd_S S --> r1s <= hds_notin S --> c1 <= hds_notin S --> \
    \ cut1_propa c1 ?Z --> cut1_propa c1 ?Y --> cut1_propa c1 ?X --> \
    \ r O s <= s^* O r"
  (fn _ => [ (clarsimp_tac (cesimps [cuth_def, O_Un, Un_O]) 1), 
    (REPEAT_SOME (rtac conjI)), (ALLGOALS orig.htac),
    (ALLGOALS ((REPEAT o resolve_tac untrs) THEN'
      rtac (order_refl RSN (2, rel_comp_mono)))),
    (ALLGOALS (rtac rtrancl_mono)), Auto_tac ]) ; 

val wfh_lem4a = wfh_lem4a' RS wfUn_movr ;

val _ = bind_thm ("wfh_lem4",
  rem_dup_prems (tacthm (TRYALL (rtac cut1_propaI)) wfh_lem4a)) ;

val wfh_lem7a = zero_var_indexes (tacsthm [TRYALL (rtac refl),
  TRYALL (resolve_tac [wf_cuth, wfh_lem5])] wfh_lem4a) ;
val wfh_lem7a_gip = zero_var_indexes (tacsthm [TRYALL (rtac refl),
  TRYALL (resolve_tac [wf_cuth, wfh_lem5])] wfh_lem4a_gip RS wf_Un_sym) ;
val wfh_hier2a = 
  tacsthm [TRYALL (rtac refl), SOMEGOAL (rtac wfh_lem7a_gip)] wfh_lem6 ;
val wfh_hier1a = wfh_hier2a RS wf_cus12 ;

val wfh_lem7 = zero_var_indexes (tacsthm [TRYALL (rtac refl),
  TRYALL (resolve_tac [wf_cuth, wfh_lem5])] wfh_lem4) ;
val wfh_lem7_gip = zero_var_indexes (tacsthm [TRYALL (rtac refl),
  TRYALL (resolve_tac [wf_cuth, wfh_lem5])] wfh_lem4_gip RS wf_Un_sym) ;
val wfh_hier2 = 
  tacsthm [TRYALL (rtac refl), SOMEGOAL (rtac wfh_lem7_gip)] wfh_lem6 ;
val wfh_hier1 = wfh_hier2 RS wf_cus12 ;

val rp_c_hier2 = wfh_hier1 RSN (3, rp_c_hier') ;
val rp_c_hier3 = tacthm (TRYALL (rtac rph)) rp_c_hier2 ;
val _ = bind_thm ("rp_c_hier", rem_dup_prems rp_c_hier3) ;

val rp_c_hier2a = wfh_hier1a RSN (3, rp_c_hier') ;
val rp_c_hier3a = tacthm (TRYALL (rtac rph)) rp_c_hier2a ;
val _ = bind_thm ("rp_c_hiera", rem_dup_prems rp_c_hier3a) ;


(* following two never used *)
val _ = qed_goalw_spec_mp "wfh_lem1_gip" hier.thy [cuth_def]
  "cut1_gip_prop c1 --> r0s <= rule0_hd_S S --> r = cuth S r0s c1 --> \
    \ X <= hds_notin S --> s = nured X --> r O s <= gip_rel r s"
  (fn _ => [ (strip_tac 1), (hyp_subst_tac 1),
    (simp_tac (esimps [O_Un, Un_O]) 1), (rtac conjI 1),
    (full_simp_tac (esimps [cut1_gip_prop_def']) 2),
    (etac allE 2), (datac sc_nured 1 1), 
    (ALLGOALS (etac subset_trans)),
    (rtac (movr_gip RS subset_trans) 1),
    (ALLGOALS (rtac gip_rel_mono)), Auto_tac ]) ;

val _ = qed_goalw_spec_mp "wfh_lem1" hier.thy [cuth_def]
  "cut1_prop c1 --> r0s <= rule0_hd_S S --> r = cuth S r0s c1 --> \
    \ X <= hds_notin S --> s = nured X --> r O s <= s^* O r" 
  (fn _ => [ (strip_tac 1), (hyp_subst_tac 1),
    (simp_tac (esimps [O_Un, Un_O]) 1),
    (REPEAT_FIRST (rtac conjI)), 
    (full_simp_tac (esimps [cut1_prop_def]) 2),
    (datac sc_nured 1 1), 
    (ALLGOALS (fast_tac (claset_of Set.thy))) ]) ;

(* cutd results no longer needed *)
val _ = qed_goal "wf_cutd" hier.thy "wf (cutd S)"
  (fn _ => [
    (res_inst_tac [("n", "Suc (Suc 0)")] wf_lim_comp 1),
    (force_tac (ces [cutd.elims], esimps []) 1) ]) ; 

val _ = qed_goalw "cutd_nured" hier.thy 
  [cutd.defs, nured_def, oneup.defs]
  "cutd S O nured any <= cutd S" fn_at ;
  
val _ = qed_goal "cutd_nured'" hier.thy 
  "cutd S O nured any <= r^* O cutd S" 
  (fn _ =>  [ (rtac (cutd_nured RS order_trans) 1), Fast_tac 1 ]) ;
  
val _ = qed_goalw "cutd_ctxth" hier.thy [cutd.defs, lfp_const]
  "cutd S O (ctxt (hds_notin S Int nured any)) <= cutd S" 
  (fn _ => [ (clarsimp_tac (cesimps [red_cases']) 1),
    (case_tac "a" 1), (clarsimp_tac (cesimps [nured_def]) 1) ]) ;
  
val _ = qed_goal "cutd_ctxth'" hier.thy 
  "cutd S O ctxt ?any <= r^* O cutd S" 
  (fn _ =>  [ (rtac (cutd_ctxth RS order_trans) 1), Fast_tac 1 ]) ;
  
