
structure hier = struct val thy = theory "hier" ;
  val ipt_mk_cases = InductivePackage.the_mk_cases thy ; end ;
use_legacy_bindings hier.thy ;
fun u _ = use_thy "hier" ; 

val cut1_gip_epr_def' = rewrite_rule [gip_cond_def] cut1_gip_epr_def ;    
val cut1_dvk_epr_def' = rewrite_rule [dvk_cond_def] cut1_dvk_epr_def ;    

val _ = qed_goalw_spec_mp "cut1_gip_dvk_epr" hier.thy 
  [cut1_gip_epr_def', cut1_dvk_epr_def']
  "cut1_gip_epr c1 r1s S --> cut1_dvk_epr c1 r1s S"
  (fn _ => [ (rtac impI 1), 
    (REPEAT (eresolve_tac [imp_forward, all_forward, subset_trans] 1)),
    (rtac gip_dvk 1) ]) ; 

val _ = qed_goal_spec_mp "wf_cut0" hier.thy 
  "wf (ctxt (subs r0s)) --> wf (subs (cut0 S r0s))"
  (fn _ => [ (rtac impI 1), (dtac wf_O_subt_redn 1),
    (etac wf_subset 1), (clarify_tac (ces [subs.elims, cut0.elims ]) 1), 
    (rtac rel_compI 1), (etac subst_subt_S 1), (etac subst_ctxt_S 1) ]) ;
   
(* note - could always replace c1 by c1 Un cutd in the following,
  but not needed, cutd proofs in oldh.ML *)
val _ = qed_goal_spec_mp "wf_cuth_lem" hier.thy 
  "c1 <= hds_notin S --> wf c1 --> wf r0 --> \
    \ r0 <= symbs_in S --> wf (r0 Un c1)"
  (fn _ => [ (strip_tac 1), (rtac wfUn_absr 1), Safe_tac,
    (eatac (subsetD RS hds_notin.elims) 1 1), 
    (eatac (subsetD RS symbs_in.elims) 1 1), Auto_tac ]) ;

val _ = qed_goal_spec_mp "cuth_rel" hier.thy 
  "c1 <= hds_notin S --> r0s <= rule0_hd_S S --> \
    \ subs (cut0 S r0s) O c1 = {}"
  (fn _ => [ (Safe_tac), (dtac sc_inS 1), 
    (datac (subsetD RS symbs_in.elims) 1 1), 
    (datac (subsetD RS hds_notin.elims) 1 1), Auto_tac ]) ; 

val _ = qed_goalw_spec_mp "wf_cuth" hier.thy [cuth_def]
  "c1 <= hds_notin S --> wf c1 --> r0s <= rule0_hd_S S --> \
    \ wf (ctxt (subs r0s)) --> wf (cuth S r0s c1)"
  (fn _ => [ (strip_tac 1), (eatac wf_cuth_lem 1 1),
    (etac wf_cut0 1), (etac sc_inS 1) ]) ;

val _ = qed_goal_spec_mp "wfUn_movr_each" WfUn.thy
  "(ALL p : s. r O {p} <= {p}^* O r) --> r O s <= s^* O r"
  (fn _ => [ Safe_tac, (datac bspec 1 1), (dtac subsetD 1), Fast_tac 1,
    (etac rel_comp_mono' 1), (rtac rtrancl_mono 1), Auto_tac ]) ;
    
(* this is part of Lemma 18 in CATS'07 paper *)
val _ = qed_goalw_spec_mp "wfh_lem2" hier.thy [sn2o_defh, sn2_alt_def]
  "r0s <= rule0_proph S --> sn2order (subs r0s Un r1s) <= \
    \ subs (cut0 S r0s) Un sn2_alt S r0s r1s"
  (fn _ => [ (strip_tac 1), 
    (simp_tac (esimps [Int_Un_distrib2, nured_Un]) 1),
    (rtac conjI 1), (dtac nured_subs 1),
    (rtac Int_lower1 1), (etac subset_trans 1), Auto_tac ]) ;

val l3tacs = [ (strip_tac 1), hyp_subst_tac 1,
  (TRY (rtac (sc_chn RS order_trans) 1)),
  (TRYALL (ares_tac [sc_nured RS order_trans])),
  (REPEAT_FIRST (ares_tac [
    rtrancl_mono, rel_comp_mono, order_refl, Int_lower1])),
  Auto_tac ] ;

val _ = qed_goal_spec_mp "wfh_lem3a" hier.thy 
  "r1s <= hds_notin S --> r0s <= rule0_hd_S S --> \
    \ s = ctxt (hds_notin S Int any) --> \
    \ r = subs (cut0 S r0s) --> r O s <= s^* O r" (fn _ => l3tacs) ;

(* simpler version of wfh_lem3a *)
val wfh_lem3a' = order_refl RS wfh_lem3a ;

val _ = qed_goal_spec_mp "wfh_lem3b" hier.thy 
  "r1s <= hds_notin S --> r0s <= rule0_hd_S S --> \
    \ s = nured (r1s Int w) --> \
    \ r = subs (cut0 S r0s) --> r O s <= s^* O r" (fn _ => l3tacs) ;

val lem3s as [lem3a, lem3b] = map (tacthm (TRYALL (rtac refl)))
  ([wfh_lem3a, wfh_lem3b] RL [subset_trans]) ;

val _ = qed_goalw_spec_mp "wfh_lem3" hier.thy [sn2_alt_def]
  "r1s <= hds_notin S --> c1 <= hds_notin S --> r0s <= rule0_hd_S S --> \
    \ s = c1 Un sn2_alt S r0s r1s --> r = subs (cut0 S r0s) --> \
    \ r O s <= s^* O r" 
  (fn _ => [ (clarsimp_tac (HOL_cs, esimps [O_Un]) 1), (rtac conjI 1), 
    (datac cuth_rel 1 1 THEN 
      etac ([empty_subsetI, sym] MRS nth (xtrans, 3)) 1),
    (rtac conjI 1), (ALLGOALS (eresolve_tac lem3s THEN' atac)),
    (REPEAT_FIRST (resolve_tac [rel_comp_mono, rtrancl_mono, subset_refl])),
    Auto_tac ]) ;

val [wfh_lem3a_gip, wfh_lem3b_gip, wfh_lem3_gip] = 
  ([wfh_lem3a, wfh_lem3b, wfh_lem3] RL [movr_gip RSN (2, subset_trans)]) ;

val [wfh_lem3a_dvk, wfh_lem3b_dvk, wfh_lem3_dvk] = 
  ([wfh_lem3a, wfh_lem3b, wfh_lem3] RL [movr_dvk RSN (2, subset_trans)]) ;

val _ = qed_goal_spec_mp "wfh_lem5''" hier.thy 
  "s = ctxt (hn Int nured (sr0s Int w)) Un nured (r1s Int w) --> \
    \ s <= nured ((sr0s Un r1s) Int w)"
  (fn _ => [ Safe_tac, (etac nured_mono' 2),
    (dtac red_mono' 1), (rtac Int_lower2 1),
    (rewtac nured_alt), (Full_simp_tac 1), (etac red_mono' 1),
    (rtac oo_mono 1), Auto_tac ]) ;

(* this is part of Lemma 18 in CATS'07 paper *)
val _ = qed_goalw_spec_mp "wfh_lem5'" hier.thy [sn2o_defh, sn2_alt_def]
  "sn2_alt S r0s r1s <= sn2order (subs r0s Un r1s)"
  (fn _ => [ (strip_tac 1), (rtac wfh_lem5'' 1), Fast_tac 1 ]) ;

val _ = qed_goal_spec_mp "wfh_lem25'" hier.thy
  "?P --> subs ?c Un sn2order ?r = subs ?c Un sn2_alt S r0s r1s"
  (fn _ => [ (rtac impI 1), Safe_tac,
    (dtac wfh_lem2 1), (datac subsetD 1 1), Fast_tac 1,
    (dtac (wfh_lem5' RS subsetD) 1), contr_tac 1 ]) ;

val wfh_lem5 = [wf_sn2order, wfh_lem5'] MRS wf_subset ;

val _ = qed_goal_spec_mp "wfh_lem6" hier.thy 
  "r0s <= rule0_proph S --> r = (cuth S r0s c1) --> \
    \ wf (r Un sn2_alt S r0s r1s) --> wf (r Un sn2order (subs r0s Un r1s))"
  (fn _ => [ (strip_tac 1), (etac wf_subset 1), 
    (safe_tac csp), Fast_tac 1, 
    (dtac wfh_lem2 1), (rewtac cuth_def), (Fast_tac 1) ]) ;

(* try a different approach, using cut1_dvk_epr *)

val _ = qed_goalw_spec_mp "ll1_sn2_wf" hier.thy [cut1_dvk_epr_def']
  "wf c1 --> r0s <= rule0_hd_S S --> cut1_dvk_epr c1 r1s S --> \
    \ wf (c1 Un sn2order (subs r0s Un r1s))"
  (fn _ => [ (strip_tac 1), 
    (rtac (wfUn_dvk RS wf_Un_sym) 1), atac 3, Fast_tac 2,
    (etac allE 1), (etac mp 1), Safe_tac,
    (safe_tac (cis [subs_hd_S RS subsetD])),
    (eatac (mk_mono' subs_mono) 1 1) ]) ;

val _ = qed_goal_spec_mp "ll1_sn2_alt_wf" hier.thy 
  "wf c1 --> r0s <= rule0_hd_S S --> cut1_dvk_epr c1 r1s S --> \
    \ wf (c1 Un sn2_alt S r0s r1s)"
  (fn _ => [ (strip_tac 1), (datac ll1_sn2_wf 2 1), 
    (etac wf_subset 1), (fast_tac (cds [mk_mono' wfh_lem5']) 1) ]) ;

val wfh_epr = zero_var_indexes ( tacsthm [TRYALL (rtac refl),
    TRYALL (resolve_tac [wf_cut0, ll1_sn2_alt_wf])]
  (wfh_lem3_dvk RS wfUn_dvk RS wf_Un_sym)) ;

val wfh_lem6a = rewrite_rule [cuth_def] (refl RSN (2, wfh_lem6)) ;

val wfh_epr2 = fold_rule [cuth_def] 
  (wfh_epr RS (wf_Un_assoc RS iffD2) RSN (2, wfh_lem6a)) ;

val wfh_epr1 = wfh_epr2 RS wf_cus12 ;

