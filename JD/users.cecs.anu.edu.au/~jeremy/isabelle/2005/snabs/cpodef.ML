
structure cpodef = struct val thy = the_context () end ;
val _ = use_legacy_bindings cpodef.thy ;

AddSIs [cpocfg.intros, cpocl.intros] ;
AddSEs [cpo.subtI] ;
AddSIs [hpocfg.intros, hpocl.intros, hpocl2.intros] ;

val _ = qed_goal_spec_mp "cpo_isubt" cpodef.thy 
  "(si, s) : isubt --> (si, s) : cpo crel symo"
  (fn _ => [ (fast_tac (ces [isubt.elims]) 1) ]) ;
AddSEs [cpo_isubt] ;

val _ = qed_goal_spec_mp "cpo_eisubt" cpodef.thy 
  "(si, s) : isubt --> (t, si) : cpo crel symo --> (t, s) : cpo crel symo"
  (fn _ => [ (clarify_tac (ces [isubt.elims, cpo.esubtI]) 1) ]) ;

val corl_props_def' = rewrite_rule
  [mono_def, onerel_corl_def, wf_der_def, wf_derl_fwf_def] corl_props_def ;

val _ = qed_goalw "cpocfg_hpocfg" cpodef.thy [meta_eq_def]
  "cpocfg == hpocfg UNIV"
  (fn _ => [ (safe_tac
      (cis [ext, UNIV_I] addSEs [cpocfg.elims, hpocfg.elims]))]);
  
val _ = qed_goalw "cpocl_hpocl" cpodef.thy [meta_eq_def] "cpocl == hpocl UNIV"
  (fn _ => [(safe_tac (cis [ext, UNIV_I] addSEs [cpocl.elims, hpocl.elims]))]);
  
val _ = qed_goalw "hpocl_ctxt" cpodef.thy [hpocl.defs]
  "hpocl S crel (ctxt ro) = hpocl S crel ro" fn_at ;
Addsimps [hpocl_ctxt] ;

(** cpo - monotonic in r **)
val _ = qed_goal_spec_mp "cpo_mono" cpodef.thy 
  "A <= B --> cpo crel A <= cpo crel B"
  (fn _ => [ Safe_tac, (etac cpo.induct 1),
    (TRYALL (eresolve_tac cpo.intros ORELSE' resolve_tac cpo.intros)),
    (TRYALL Fast_tac) ]) ;

(** cpo - closed under context, and transitive **)
val _ = qed_goal_spec_mp "red_cpo" cpodef.thy 
  "onerel_corl crel --> ctxt (cpo crel r) <= cpo crel r"
  (fn _ => [Safe_tac, (etac ctxt.induct 1), atac 2, 
    (etac oneup.elims 1), Safe_tac, (rtac cpo.corlI 1), 
    (rtac order_refl 2), 
    (clarsimp_tac (cesimps [onerel_corl_def]) 1),
    (etac allE 1), (Clarify_tac 1), (etac subsetD 1),
    (etac onerel_mono' 1), Safe_tac,
    (datac in_onerel 1 1), Safe_tac, (eatac cpo.esubtI 1 1) ]) ;

val _ = qed_goal_spec_mp "red_cpo_eq'" cpodef.thy 
  "onerel_corl crel --> ctxt (cpo crel r) = cpo crel r"
  (fn _ => [ (rtac impI 1), (rtac equalityI 1),
    (etac red_cpo 1), Auto_tac]) ;
    
val _ = qed_goal_spec_mp "isubt_cpo" cpodef.thy 
  "(Node f ts, s) : cpo cr r --> ti : set ts --> (ti, s) : cpo cr r" 
  (fn _ => [ (res_inst_tac [("rtree1", "s")] rtree_induct 1),
    Safe_tac, (etac cpo.elims 1), Safe_tac, Fast_tac 2, Fast_tac 1,
    (etac cpo.esubtI 1), (etac cpo.subtI 1), 
    (datac bspec 1 1), (REPEAT (mp_tac 1)), 
    (eatac cpo.esubtI 1 1)]) ; 

val _ = qed_goalw_spec_mp "subt_cpo" cpodef.thy [subt_def, psubt_def]
  "(ti, t) : subt --> (t, s) : cpo cr r --> (ti, s) : cpo cr r"
  (fn _ => [ (rtac impI 1), (etac UnE 1), Fast_tac 2,
    (etac trancl_induct 1),
    (ALLGOALS (etac isubt.elims)), Safe_tac,
    (ALLGOALS (datac isubt_cpo 1)), Safe_tac]) ;

val _ = qed_goalw_spec_mp "cpo_red_props_crel" cpodef.thy 
  [red_props_crel_def']
  "mono crel --> red_props_crel (cpo crel symo) UNIV crel (cpocfg symo)"
  (fn _ => [ Safe_tac,
    (datac subt_cpo 1 1), (thin_tac "?p : cpo crel symo" 1),
    (etac cpo.elims 1), (fast_tac (cis [isubt_psubt]) 3),
    (fast_tac (cis [isubt_psubt, r_into_rtrancl]) 3), Fast_tac 2, 
    Safe_tac, Fast_tac 2, (etac (monoD RS subsetD) 1), atac 2,
    (etac order_trans 1), (rtac r_into_red 1)]) ;

val _ = qed_goalw_spec_mp "red_props_dtp_lemh" cpodef.thy 
  [red_props_dt_def', red_props_crel_def']
  "wf_derl_fwf crel --> red_props_crel ro S crel cuto --> \
    \ red_props_dt ro (cuto Un hpocl S crel ro)"
  (fn _ => [ Safe_tac,
    (etac allE3 1), mp_tac 1, mp_tac 1, Safe_tac, Fast_tac 2,
    (etac (p_iOs RS equalityD2' RS rel_compEpair) 1),
    (dtac subsetD 1), Simp_tac 1, (datac subt_sn 1 1), 
    (datac wfp_red 1 1), (eatac subt_sn 1 1),
    (datac nuredtc_sn 1 1), (etac notE 1), (fast_tac (ces [trancl_mono]) 1),
    (rewtac wf_derl_fwf_def), (etac oneupS.elims 1), 
    (subgoal_tac "(dts, s) : hpocl S crel ro" 1), Auto_tac ]) ;

val _ = bind_thm ("cpo_red_props_dtp", fold_rule [mk_eq cpocl_hpocl]
  (cpo_red_props_crel RSN (2, red_props_dtp_lemh))) ;

val cpo_red_props_dtp' = meta_std (rewrite_rule [prp_def] (
  rewrite_rule [red_props_dt_def] (cpo_red_props_dtp) 
    RS rel_subsetD)) ;

val _ = qed_goalw "cpocfg_symb_of" cpodef.thy [inv_image_def]
  "cpocfg r = inv_image r symb_of"
  (fn _ => [ Safe_tac, (etac cpocfg.elims 1), 
    (case_tac "a" 2), (case_tac "b" 2), Auto_tac]) ;

val _ = qed_goalw "hpocfg_symb_of" cpodef.thy [inv_image_def]
  "hpocfg S r <= inv_image r symb_of"
  (fn _ => [ Safe_tac, (etac hpocfg.elims 1), Auto_tac]) ;

val _ = qed_goal_spec_mp "wf_hpocfg" cpodef.thy "wf r --> wf (hpocfg S r)"
  (fn _ => [ Safe_tac, (rtac wf_subset 1),
    (rtac hpocfg_symb_of 2), Fast_tac 1 ]) ;

val _ = qed_goal "hpocl_oneup" cpodef.thy 
  "hpocl S crel ro <= oneup (crel (fwf (ctxt ro)))" 
  (fn _ => [ (force_tac (ces [hpocl.elims], simpset ()) 1)]) ;

val _ = qed_goalw_spec_mp "wf_hpocl" cpodef.thy [wf_der_def]
  "wf_der crel --> wf (hpocl S crel ro)"
  (fn _ => [ Safe_tac, (rtac wf_subset 1), (rtac hpocl_oneup 2),
    (asm_simp_tac (esimps [wf1up]) 1) ]) ;

fun h2c th = fold_rule [cpocl_hpocl, cpocfg_hpocfg] 
  (read_instantiate [("S", "UNIV")] th) ;

val _ = qed_goal "hpocl2_oneup" cpodef.thy 
  "hpocl2 S crel ro <= oneup (crel (ctxt (fwf (ctxt ro))))" 
  (fn _ => [ (force_tac (ces [hpocl2.elims], simpset ()) 1)]) ;

val _ = qed_goalw_spec_mp "wf_hpocl2" cpodef.thy [wf_der_def]
  "wf_der crel --> wf (hpocl2 S crel ro)"
  (fn _ => [ Safe_tac, (rtac wf_subset 1), (rtac hpocl2_oneup 2),
    (asm_simp_tac (esimps [wf1up]) 1) ]) ;

val _ = qed_goal_spec_mp "hpocl2_ge" cpodef.thy 
  "mono crel --> hpocl2 S crel ro >= hpocl S crel ro"
  (fn _ => [ (safe_tac (ces [hpocl.elims])), 
    (eatac monoD' 1 1), (rtac r_into_red 1) ]) ;

val _ = qed_goal_spec_mp "hpowfcut" cpodef.thy 
  "wf so --> wf_der crel --> wf (hpocfg S so Un hpocl S crel ro)"
  (fn _ => [ (strip_tac 1), (rtac wfUn_absl 1), Clarify_tac 1, 
    (etac hpocfg.elims 1), (etac hpocl.elims 1), Clarify_tac 1, 
    (etac wf_hpocfg 1), (etac wf_hpocl 1)]) ;

val _ = qed_goalw_spec_mp "sn1cutp" cpodef.thy 
  [sn1order_def', onerel_corl_def] 
  "onerel_corl crel --> sn1order ro <= cpocl crel ro"
  (fn _ => [ (fast_tac (ces [oneup.elims] addSIs [UNIV_I]) 1) ]) ;

val _ = qed_goal_spec_mp "hpowfdt" cpodef.thy 
  "wf so --> wf_der crel --> onerel_corl crel --> \
    \ wf (hpocfg S so Un hpocl S crel ro Un sn1order ro)"
  (fn _ => [ (strip_tac 1), (rtac wf_subset 1), Safe_tac,
    (dtac sn1cutp 4), (datac subsetD 1 4),
    (rewtac cpocl_hpocl), (eatac hpowfcut 1 1), Fast_tac 3,
    (auto_tac (cesimps [hpocl.defs, hpocfg.defs])) ]) ;

val [cpocl_oneup, wf_cpocl, wf_cpocfg, cpowfcut, cpowfdt] = 
  map h2c [hpocl_oneup, wf_hpocl, wf_hpocfg, hpowfcut, hpowfdt] ;

val _ = qed_goal_spec_mp "hpowf2cut" cpodef.thy 
  "wf so --> wf_der crel --> wf (hpocfg S so Un hpocl2 S crel ro)"
  (fn _ => [ (strip_tac 1), (rtac wfUn_absl 1), Clarify_tac 1, 
    (etac hpocfg.elims 1), (etac hpocl2.elims 1), Clarify_tac 1, 
    (etac wf_hpocfg 1), (etac wf_hpocl2 1)]) ;

val _ = qed_goalw_spec_mp "sn2cutp" cpodef.thy 
  [sn2order_def', onerel_corl_def] 
  "onerel_corl crel --> sn2order ro <= hpocl2 UNIV crel ro"
  (fn _ => [ (fast_tac (ces [oneup.elims] addSIs [UNIV_I]) 1) ]) ;

val _ = qed_goal_spec_mp "hpowf2dt" cpodef.thy 
  "wf so --> wf_der crel --> onerel_corl crel --> \
    \ wf (hpocfg S so Un hpocl2 S crel ro Un sn2order ro)"
  (fn _ => [ (strip_tac 1), (rtac wf_subset 1), Safe_tac,
    (dtac sn2cutp 4), (datac subsetD 1 4),
    (eatac hpowf2cut 1 1), Fast_tac 3,
    (auto_tac (cesimps [hpocl2.defs, hpocfg.defs])) ]) ;

val _ = bind_thm ("all_sn3_crel'", red_props_dtp_lemh RS all_sn3_dt) ;
val _ = bind_thm ("all_sn3_crel", hpowfdt RSN (3, all_sn3_crel')) ;

val thc = rewrite_rule [cpocfg_hpocfg] cpo_red_props_crel RSN (2, all_sn3_crel);
val thp = tacthm (TRYALL (resolve_tac (msc (corl_props_def RS defD1)))) thc ;
val _ = bind_thm ("cpocsn", rdp thp) ;

(** use of this theorem - see lpodef.ML, mpodef.ML **)

(* 
set show_sorts ;
reset show_sorts ;
*)
