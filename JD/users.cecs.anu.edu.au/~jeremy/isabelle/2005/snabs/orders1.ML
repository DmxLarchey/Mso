
structure orders1 = struct val thy = theory "orders1" end ;
use_legacy_bindings orders1.thy ;
fun u _ = use_thy "orders1" ;

val dtoI = rewrite_rule [sn1red_def] (hd (sn1order.intrs RL dtorder.intros)) ;
val red_props_nr_def' = rewrite_rule [red_props_nrf_def] red_props_nr_def ;
val red_props_c2_def' = rewrite_rule [red_props_c2f_def] red_props_c2_def ;
val red_props_crel_def' = rewrite_rule [red_props_g_def] red_props_crel_def ;
val red_props_c_def = rewrite_rule [red_props_g_def] red_props_c_defg ;
val red_props_pc_def = 
  rewrite_rule [red_props_g_def, mk_eq Un_iff] red_props_pc_defg ;

val red_props_dt_def' = rewrite_rule [prp_def] 
  (prove_goalw orders1.thy [meta_eq_def, red_props_dt_def]
  "red_props_dt rho cuto == ALL t s. (t, s) : rho --> (t, s) : prp rho cuto"
  fn_at) ;

val rpgm = prove_goalw orders1.thy [red_props_g_def]
  "S <= T --> red_props_g rho S --> red_props_g rho T" fn_at ;
val _ = bind_thm ("red_props_g_mono", rpgm RS mp) ;
val _ = bind_thm ("red_props_g_mono'", mk_mono' red_props_g_mono) ;

val () = qed_goalw_spec_mp "rpcc'" orders1.thy 
  [red_props_pc_defg, red_props_c_defg]
  "red_props_pc rho cuto --> red_props_c rho cuto" 
  (fn _ => [ (fast_tac (ces [red_props_g_mono']) 1) ]) ;

val _ = qed_goalw_spec_mp "rp_g_Un" orders1.thy [red_props_g_def]
  "red_props_g ra ca --> red_props_g rb cb --> \
    \ red_props_g (ra Un rb) (ca Un cb)" fn_at ;

val _ = qed_goalw_spec_mp "rp_pc_Un" orders1.thy [red_props_pc_defg]
  "red_props_pc ra ca --> red_props_pc rb cb --> \
    \ red_props_pc (ra Un rb) (ca Un cb)" 
  (fn _ => [ Safe_tac, (datac rp_g_Un 1 1), 
    (etac red_props_g_mono' 1), Fast_tac 1 ]) ;

val rel_comp3_mono = rel_comp_mono RSN (2, rel_comp_mono) ;
val rel_comp3_mono' = mk_mono' rel_comp3_mono ;
val rel_comp3I = rel_compI RS rel_compI ;
val nrcm = [rel_comp3I, subset_refl, asm_rl, subset_refl] 
  MRS rel_comp3_mono' RSN (2, notE) ;

val _ = qed_goalw_spec_mp "rp_crel_Un" orders1.thy [red_props_crel_def]
  "mono crel --> red_props_crel ra S crel ca --> \
    \ red_props_crel rb S crel cb --> \
    \ red_props_crel (ra Un rb) S crel (ca Un cb)" 
  (fn _ => [ Safe_tac, (datac rp_g_Un 1 1), 
    (etac red_props_g_mono' 1), Safe_tac, 
    (TRYALL (EVERY' [ (eatac (oneupS_mono' RSN (2, notE)) 1),
      etac monoD, (rtac red_mono), Fast_tac])),
    (TRYALL (EVERY' [ (eatac nrcm 3), 
      (rtac rtrancl_mono), (rtac red_mono), Fast_tac ])),
    (TRYALL (EVERY' [ (eatac (trancl_mono RSN (2, notE)) 1),
      (rtac nured_mono), Fast_tac])) ]) ;

val Un_uppers = [Un_upper1, Un_upper2] ;
val untrs = Un_uppers RLN (2, [subset_trans]) ;
val uoths = Un_uppers RLN (2,
  [nured_mono RS rtrancl_mono RS subsetD RSN (2, rel_compI)])  ;

val utths = Un_uppers RL [nured_mono RS trancl_mono' RS subsetD]  ;

val _ = qed_goalw_spec_mp "rp_c_Un" orders1.thy [red_props_c_def]
  "red_props_c ra ca --> red_props_c rb cb --> \
    \ red_props_c (ra Un rb) (ca Un cb)" 
  (fn _ => [ Safe_tac,
    (REPEAT_FIRST (FIRST' [mp_tac, contr_tac, (etac allE)])), 
    (REPEAT_FIRST (thin_tac "?P --> ?Q")), Safe_tac,
    (ALLGOALS (clarsimp_tac (cesimps [O_Un, Un_O]))),
    (TRYALL (EVERY' [dresolve_tac uoths, atac, contr_tac])),
    (TRYALL (EVERY' [dresolve_tac utths, contr_tac])) ]) ;

val () = qed_goalw_spec_mp "rpcdt'" orders1.thy 
  [red_props_dt_def', red_props_c_def]
  "red_props_c rho cuto --> (red_props_dt rho cuto)" 
  (fn _ => [ Safe_tac,
    (etac allE3 1), (REPEAT (mp_tac 1)), Safe_tac,
    (rewtac psubt_def), (dtac converse_tranclD 1),
    (clarsimp_tac (cesimps [symmetric subt_def']) 1), 
    (dtac subsetD 1), Simp_tac 1, (eatac subt_sn 1 1),
    
    (Force_tac 1), (ALLGOALS (etac notE)), 
    (datac nuredtc_sn 1 1), (Clarify_tac 1), 
    (etac trancl_mono 1), (Force_tac 1),
    (rtac rtrancl_into_trancl2 1), (Force_tac 1),
    (datac nuredrtc_sn 1 1), (Clarify_tac 1), (etac rev_subsetD 1), 
    (rtac rtrancl_mono 1), (Force_tac 1)]) ;

val () = bind_thm ("rp_pc_dt", rpcc' RS rpcdt') ;

val _ = qed_goalw "spsrtc" base.thy [psubt_def, subt_def'] 
  "psubt^* = subt" fn_at ;

val _ = qed_goalw "nraf_nrf" orders1.thy 
  [red_props_nraf_def, red_props_nrf_def, mk_eq spsrtc]
  "red_props_nrf rho cuto dt = red_props_nraf psubt rho cuto dt" fn_at ;

val _ = qed_goalw_spec_mp "nr_nra" orders1.thy 
  [red_props_nra_def, red_props_nr_def, mk_eq nraf_nrf]
  "red_props_nr rho cuto --> red_props_nra psubt rho cuto"
  (fn _ => [ (rtac impI 1), (etac all_forward 1),
    (force_tac (cesimps [psubt_def]) 1) ]) ;

(* if red_props_c2 is satisfied for ruleredn,
  then red_props_nr is satisfied for ctxt ruleredn Un psubt,
  but using dtorder as the cutorder of red_props_nr *)

val _ = qed_goal_spec_mp "nrlem" orders1.thy 
  "(dts, ya) : subt --> (ya, za) : (ctxt rho)^* --> \
    \ (dts, za) : (ctxt rho Un psubt)^*"
  (fn _ => [ (strip_tac 1), 
    (rtac rtrancl_trans 1), (ALLGOALS (etac rev_subsetD)),
    (auto_tac (cis [rtrancl_mono], esimps [subt_def', psubt_def])) ]) ;

val _ = qed_goalw_spec_mp "red_props_c2_nra" orders1.thy 
  [red_props_nra_def', red_props_c2_def']
  "red_props_c2 rho cuto --> \
    \ red_props_nra psubt (ctxt rho Un psubt) ((cuto Un sn1order rho)^+)"
  (fn _ => [ Clarify_tac 1, (etac allE 1),
    (etac impE 1), (Clarsimp_tac 1),
    (etac allE 1), (etac impE 1), (etac wfp_mono' 2), 
    (Fast_tac 2), (Fast_tac 1), 

    (etac UnE 1), (rewtac (mk_eq spsrtc)),
    (datac subt_thms.spp 1 2), Fast_tac 2,
    (etac ron.E 1), (etac allE 2 THEN mp_tac 2), 
    (etac prp2allE 2), (etac allE 2 THEN mp_tac 2), 
    (etac prp2E' 2), contr_tac 3, (Clarify_tac 2),
    (rtac rel_compI 2), atac 3, (eatac nrlem 1 2),

    (rewtac subt_def), Safe_tac, 
    (subgoal_tac "(dtn, dt) : sn1order rho" 2),
    (simp_tac (esimps [sn1order_def']) 3),
    (etac oneup.elims 3), 
    (clarsimp_tac (ces [onerel_fwf], esimps []) 3),
    (etac allE 3), (etac impE 3), (etac wfp_mono' 4), Fast_tac 4,
    (rtac isubt_psubt 3), Simp_tac 3,

    (etac notE 2), (rtac r_into_trancl 2),
    (force_tac (cesimps [dtorder_def]) 2), 
    (datac nured_psubt' 1 1), (Clarify_tac 1), 
    (rtac rel_compI 1), (etac isubt_psubt 2), 
    (etac nrlem 1), Fast_tac 1]) ;

(* given a well-founded rewrite relation, can fit it into our thm,
  using cutorder = rho O subt *)

val _ = qed_goalw "wf_pc" orders1.thy [red_props_pc_def]
  "red_props_pc rho (rho O subt)" fn_ft1 ;

val _ = qed_goalw_spec_mp "wf_dtwf" orders1.thy [subt_def]
  "wf (ctxt rho) --> wf ((rho O subt) Un sn1order rho)"
  (fn _ => [ (rtac impI 1), (dtac wf_psubt_redn 1), 
    (dtac wf_trancl 1), (etac wf_subset 1), Safe_tac,
    (resolve_tac transitive_closure_trans 1),
    (dtac (sn1o_nured RS subsetD RS red_nured) 4), Auto_tac]) ;

(* assume no infinite constricting derivation, then no infinite derivation *) 
val _ = qed_goalw "wfc_dt" orders1.thy [red_props_dt_def]
  "red_props_dt rho (constrict rho O subt)"
  (fn _ => [ (force_tac (cis [prp.prpI], esimps [constrict_def]) 1) ]) ;

val _ = qed_goalw_spec_mp "wfc_dtwf" orders1.thy [subt_def]
  "wf (ctxt (constrict rho)) --> \
    \ wf ((constrict rho O subt) Un sn1order rho)"
  (fn _ => [ (rtac impI 1), (dtac wf_psubt_redn 1), 
    (dtac wf_trancl 1), (etac wf_subset 1), Safe_tac,
    (resolve_tac transitive_closure_trans 1),
    (dtac (mk_mono' sn1_constrict) 4), 
    (dtac (sn1o_nured RS subsetD RS red_nured) 4), Auto_tac]) ;
  
   


