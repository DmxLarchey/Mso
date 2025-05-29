
structure dpdef = struct val thy = theory "dpdef" ;
  val ipt_mk_cases = InductivePackage.the_mk_cases thy ; end ;
use_legacy_bindings dpdef.thy ;
fun u _ = use_thy "dpdef" ;

val dpccd_mk_cases = dpdef.ipt_mk_cases "dpdef.dpccd" ;
val dpcs_mk_cases = dpdef.ipt_mk_cases "dpdef.dpcs" ;
val depprs_mk_cases = dpdef.ipt_mk_cases "dpdef.depprs" ;

AddSIs [dpccd.intros] ;
AddSEs [dpcs.intros] ;
val dpccdE = dpccd_mk_cases "(Node c ss, Node d ts) : dpccd" ;
val dpcsE = dpcs_mk_cases "(Node c ss, Node d ts) : dpcs" ;
AddSEs [dpccdE] ;
val dpcs = claset () addSEs [dpcs.elims, dpccd.elims, oneup.elims]
  addSIs [dpcs.intros] ;
val dpcss = (dpcs, esimps [nured_def, inv_image_def]) ;
AddIffs [wf_porder] ;
val depprsE' = depprs_mk_cases "(t, Node d ts) : depprs" ;
val dps_dsym = tacthm (etac defsyms.I 2) depprsE' ;
val rresE = mkpE rres.elims ;
val rev_injD = rotate_prems 1 injD ;

val _ = qed_goal "mk_ess_def" dpdef.thy "mk_ess ts = map mk_es ts" (indAu "ts");

val _ = qed_goal "mk_es_maptree" dpdef.thy 
  "mk_es t = maptree Nat t & mk_ess ts = maptrees Nat ts" (indAu "t ts") ;

val _ = qed_goal "rres_def" dpdef.thy 
  "rres = fwd_image dp_ruleredn (maptree Nat)"
  (fn _ => [ (clarsimp_tac 
      (cesimps [rres.defs, fwd_image.unfold, mk_es_maptree]) 1) ]) ;

val _ = qed_goal "rres_qorder" dpdef.thy "rres <= qorder"
  (fn _ => [ (clarsimp_tac (ces fwd_image.elims, esimps [rres_def]) 1),
    (dtac pqa 1), (full_simp_tac (esimps [mk_es_maptree]) 1) ]) ; 

val _ = qed_goal "inj_mk_es'" dpdef.thy 
  "(ALL y. mk_es x = mk_es y --> x = y) & \
    \ (ALL ys. mk_ess xs = mk_ess ys --> xs = ys)"
  (fn _ => [ (induct_tac "x xs" 1), (ALLGOALS Clarsimp_tac),
    (case_tac "y" 1), Clarsimp_tac 1, (TRYALL (case_tac "ys")), Auto_tac]) ;

val _ = qed_goalw "inj_mk_es" dpdef.thy [inj_on_def] "inj mk_es"  
  (fn _ => [ (fast_tac (ces (msc inj_mk_es')) 1) ]) ; 
  
val inj_mk_esD = inj_mk_es RS injD ;
AddSDs [inj_mk_esD] ;

(* qorder and porder 
  deduce poq from qorder being transitive and porder being its strict part 
val qorder_trans' = meta_std (rewrite_rule [trans_def] qorder_trans) ;

val _ = qed_goalw_spec_mp "poq" dpdef.thy [mk_eq porder.unfold]
  "(x, y) : porder O qorder --> (x, y) : porder"
  (fn _ => [ (auto_tac (claset () addIs [qorder_trans'], simpset ())) ]) ;
*)

val _ = qed_goal "wf_dpccd" dpdef.thy "wf dpccd"
  (fn _ => [ (res_inst_tac [("n", "Suc (Suc 0)")] wf_lim_comp 1),
    (force_tac dpcss 1) ]) ;

val _ = qed_goal "wf_cutorder'" dpdef.thy "wf (dpccd Un dpcs)"
  (fn _ => [ (rtac wfUn_absl 1), (rtac wf_dpccd 2), (rtac wf_subset 2),
    (res_inst_tac [("f", "mk_sharp_t o mk_es")] wf_inv_image 2),
    (rtac wf_porder 2), (force_tac dpcss 2), (force_tac dpcss 1)]) ;

val wf_cutorder = fold_rule [dpcdef] wf_cutorder' ;

val _ = qed_goal_spec_mp "lem_red" dpdef.thy
  "(x, y) : ctxt dp_ruleredn --> (mk_es x, mk_es y) : ctxt qorder"
  (fn _ => [ (rtac impI 1), (etac ron.induct 1), 
    (rtac ron.red_cutI 2), (etac pqa 2), 
    (etac oneup.elims 1), Clarsimp_tac 1, (rtac ro_intr 1),
    (etac onerel.induct 1), Auto_tac]) ;

val _ = qed_goalw_spec_mp "lem_nured" dpdef.thy [nured_def]
  "(x, y) : nured dp_ruleredn --> (mk_es x, mk_es y) : nured qorder"
  (fn _ => [ (rtac impI 1), (etac oneup.elims 1), Clarsimp_tac 1,
    (etac onerel.induct 1), Auto_tac, (etac lem_red 1)]) ; 

(* poq implies wfpsr *)
val _ = qed_goal "poq_wfpsr" dpdef.thy "wf (porder Un sn1order rres)"
  (fn _ => [ (cut_facts_tac [poq] 1), (etac disjE 1),
    (rtac wfUn_absl 2), (rtac wfUn_absr 1),
    (TRYALL (resolve_tac [wf_porder, wf_sn1order])),
    (ALLGOALS (rtac subset_trans)), (TRYALL atac), 
    (ALLGOALS (rtac rel_comp_mono)), (TRYALL (rtac subset_refl)), 
    (ALLGOALS (rtac (qorder_ctxt RSN (2, subset_trans)))), 
    (ALLGOALS (rtac (
      [mk_mono sn1o_red, rres_qorder RS red_mono] MRS subset_trans))) ]) ;

val _ = qed_goalw "dpwfdt" dpdef.thy [mk_eq dtorder_def, dpcdef] 
  "wf (dp_cutorder Un sn1order dp_ruleredn)"
  (fn _ => [ (rtac wfUn_abs 1), (rtac wf_cutorder' 2), 
    (cut_facts_tac [poq] 1), (etac disjE 1), 
    (rtac disjI1 1), (rtac disjI2 2), Safe_tac,
    (REPEAT (EVERY [(force_tac (dpcs, esimps [sn1order_def]) 1), 
      (dtac sn1o_nured' 1), (dtac lem_nured 1),
      (etac notE 1), (case_tac "a" 1), (case_tac "b" 1), 
      (clarsimp_tac dpcss 1), (rtac dpcs.I 1),
      (REPEAT (ares_tac [refl] 2)),
      (Simp_tac 1), (etac subsetD 1),
      (rtac rel_compI 1), FIRSTGOAL atac,
      (rtac (qorder_ctxt RS subsetD) 1), (rtac red_nured 1),
      (rewtac nured_def), (Clarify_tac 1) ])) ]) ;

val _ = qed_goalw_spec_mp "mks_sn1" dpdef.thy [sn1order_def']
  "((t, s) : sn1order q) --> ((mk_sharp_t t, mk_sharp_t s) : sn1order q)" 
  (fn _ => [clarsimp_tac (ces [oneup.elims], esimps []) 1]) ;

val _ = qed_goalw "rres_ii" dpdef.thy [inv_image_def, mk_eq rres.defs] 
  "dp_ruleredn = inv_image rres mk_es" fn_at ; (* >= only as mk_es injective *)

val _ = qed_goal "wfp_rres" dpdef.thy 
  "(t : wfp dp_ruleredn) = (mk_es t : wfp rres)"
  (fn _ => [ Safe_tac, (etac wfp.induct 1), (rtac wfp.wfpI 1),
    (fast_tac (ces [rres.elims]) 1),
    (simp_tac (esimps [rres_ii]) 1), (etac wfp_inv_image 1) ]) ;

val _ = qed_goal "wfdps" dpdef.thy 
  "wf (dpcs Un sn1order dp_ruleredn)"
  (fn _ => [ (rtac wf_subset 1), (rtac wf_inv_image 1), 
    (rtac wfpsr 1), (rewtac inv_image_def), Safe_tac, 
    (etac dpcs.elims 1), (Clarify_tac 1), atac 1, 
    (etac notE 1), (rtac mks_sn1 1),
    (simp_tac (esimps [rres_def, mk_es_maptree]) 1),
    (rtac fi_sn1' 1), (rtac injI 1), TRYALL Fast_tac]) ;

(* this proof of wf (dtorder) depends on wfpsr *)
val _ = qed_goalw "dpwfdt_alt" dpdef.thy [dpcdef, mk_eq Un_assoc] 
  "wf (dp_cutorder Un sn1order dp_ruleredn)"
  (fn _ => [ (rtac wfUn_absl 1), (* wfUn_absr would work also *)
    (TRYALL (resolve_tac [wfdps, wf_dpccd])),
    (Safe_tac), (TRYALL (etac dpccd.elims)), 
    (rewtac sn1order_def'), (etac dpcs.elims 1), 
    (etac oneup.elims 2), Safe_tac]) ;

val _ = qed_goal_spec_mp "dps_dpcs" dpdef.thy 
  "(t, s) : depprs --> (t, s) : dpcs | (t, s) : psubt"
  (fn _ => [ (case_tac "s" 1), (Clarify_tac 1), 
    (ftac dps_dsym 1), (ftac pqb 1), (etac depprs.elims 1),
    (Clarify_tac 1), (etac dpcs.I 1), (REPEAT (Fast_tac 1))]) ; 

val _ = qed_goalw_spec_mp "dp_red_props_pc'" dpdef.thy [dpcdef]
  "(dtn, dt) : dp_ruleredn --> (dts, dtn) : subt --> \ 
    \ (dts, dt) : psubt | (dts, dt) : dp_cutorder"
  (fn _ => [ Safe_tac, (case_tac "dts" 1), (case_tac "dt" 1),
    Clarify_tac 1, (ftac defsyms.I 1),
    (case_tac "a : defsyms" 1), (eatac dpccd.I 1 2),
    (datac depprs.I 2 1), (dtac dps_dpcs 1), Clarify_tac 1]) ;

val _ = qed_goalw_spec_mp "dp_red_props_pc" dpdef.thy [red_props_pc_def]
  "red_props_pc dp_ruleredn dp_cutorder"
  (fn _ => [ (fast_tac (cds [dp_red_props_pc']) 1) ]) ;

val dpsn = [dp_red_props_pc, dpwfdt] MRS all_sn3_pc ;

