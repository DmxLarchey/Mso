

structure ipodef = struct val thy = the_context () end ;
val _ = use_legacy_bindings ipodef.thy ;

structure ipo = struct local open ipo_ipo1 in
  val cases = ipo.cases ;
  val [corlI, fgI, subtI, esubtI] = [corlI, fgI, subtI, esubtI] RL [ipo1I] ;
  val [pctxtI, hierI] = [pctxtI, hierI] ;
  val intros = [corlI, fgI, subtI, esubtI, pctxtI, hierI] ;
  val [elim, ipo1_elim] = elims ;
  val elims = tacthm (etac ipo1_elim 2) elim ;
  val induct' = tacthm (chop_tac 1 (atac 5)) induct ;
  val induct = rotate_prems ~1 (induct' RS conjunct1 RS mp) ;
  end ; end ;

AddSEs [ipo.subtI] ;

val _ = qed_goal "ipo_01" ipodef.thy
  "ipo sig S crel B = ctxt (sig Un ipo1 sig S crel B)"
  (fn _ => [ Safe_tac, (dtac (red_cases' RS equalityD1') 2),
    (fast_tac (ces ((nured_mono' RS ipo_ipo1.pctxtI) :: ipo_ipo1.intros)
      addSss esimps [nured_Un]) 2),
    (etac ipo.induct 1),
    (TRYALL (rtac (UnI2 RS ctxt.red_cutI) THEN' 
      (fast_tac (ces ipo_ipo1.intros)))),
    (etac (UnI1 RS ctxt.red_cutI) 1), (dtac nured_mono' 1),
    Simp_tac 1, (rtac Int_lower2 1),
    (dtac (mk_mono' red_nured_sub) 1), Full_simp_tac 1 ]) ;
    
val _ = qed_goal "ipo1_notin" ipodef.thy
  "ipo1 sig S crel B <= hds_notin S"
  (fn _ => [ (safe_tac (ces [ipo.ipo1_elim])) ]) ;

(** ipo - monotonic in r **)
val _ = qed_goal_spec_mp "ipo_mono" ipodef.thy 
  "A <= B --> ipo sig S crel A <= ipo sig S crel B"
  (fn _ => [ Safe_tac, (etac ipo.induct 1),
    (TRYALL (eresolve_tac ipo.intros)), (TRYALL atac),
    (ALLGOALS Clarsimp_tac), 
    (rtac ipo.pctxtI 2), (etac nured_mono' 2), 
    (rtac ipo.fgI 1), Auto_tac ]) ;

(** ipo - closed under context, and transitive **)
(* not true
val _ = qed_goal_spec_mp "red_ipo" ipodef.thy 
  "onerel_corl crel --> ctxt (ipo sig S crel r) <= ipo sig S crel r"
  (fn _ => [Safe_tac, (etac ctxt.induct 1), atac 2, 
    (etac oneup.elims 1), Safe_tac, (rtac ipo.corlI 1), 
    (rtac order_refl 2), 
    (clarsimp_tac (cesimps [onerel_corl_def]) 1),
    (etac allE 1), (Clarify_tac 1), (etac subsetD 1),
    (etac onerel_mono' 1), Safe_tac,
    (datac in_onerel 1 1), Safe_tac, (eatac ipo.esubtI 1 1) ]) ;

val _ = qed_goal_spec_mp "red_ipo_eq'" ipodef.thy 
  "onerel_corl crel --> ctxt (ipo sig S crel r) = ipo sig S crel r"
  (fn _ => [ (rtac impI 1), (rtac equalityI 1),
    (etac red_ipo 1), Auto_tac]) ;
    
val _ = qed_goal_spec_mp "isubt_ipo" ipodef.thy 
  "(Node f ts, s) : ipo cr r --> ti : set ts --> (ti, s) : ipo cr r" 
  (fn _ => [ (res_inst_tac [("rtree1", "s")] rtree_induct 1),
    Safe_tac, (etac ipo.elims 1), Safe_tac, Fast_tac 2, Fast_tac 1,
    (etac ipo.esubtI 1), (etac ipo.subtI 1), 
    (datac bspec 1 1), (REPEAT (mp_tac 1)), 
    (eatac ipo.esubtI 1 1)]) ; 

val _ = qed_goalw_spec_mp "subt_ipo" ipodef.thy [subt_def, psubt_def]
  "(ti, t) : subt --> (t, s) : ipo cr r --> (ti, s) : ipo cr r"
  (fn _ => [ (rtac impI 1), (etac UnE 1), Fast_tac 2,
    (etac trancl_induct 1),
    (ALLGOALS (etac isubt.elims)), Safe_tac,
    (ALLGOALS (datac isubt_ipo 1)), Safe_tac]) ;
*)

val rc3nE = rel_comp3I RSN (2, notE) ;

val itacs = [ (etac (subt_def RS def_imp_eq RS equalityD1' RS UnE)), 
  (full_simp_tac (esimps [sub1t_psubt RS sym])),
  (etac sub1t.elims), Clarify_tac, (REPEAT1 o datac bspec 1),
  (REPEAT1 o (etac allE ORELSE' mp_tac)), Force_tac ] ;

val _ = qed_goalw_spec_mp "ipo_red_props_crel" ipodef.thy 
  [red_props_crel_def'] "sigma = ipo (subs r0s) S crel symo --> \
    \ mono crel --> r0s <= rule0_proph S --> \
    \ red_props_crel sigma (-S) crel \
      \ (hpocfg (-S) symo Un subs (cut0 S r0s))"
  (fn _ => [ (REPEAT (rtac impI 1)),
    hyp_subst_tac 1, (rtac allI 1), (rtac allI 1), 
    (res_inst_tac [("rtree1", "dtn")] rtree_induct 1),
    Safe_tac, (etac ipo.elims 1), Safe_tac, 
    (* ipo.subtI *) (etac rc3nE 3), (rtac subt_refl 3),
    (rtac rtrancl_refl 3), (etac subt_thms.sip 3), Fast_tac 3,
    (* ipo.esubtI *) (eatac rc3nE 1 3), 
    (etac (ctxt.red_cutI RS r_into_rtrancl) 3),
    (rtac isubt_psubt 3), Simp_tac 3,
    (* ipo.fgI *) (EVERY' itacs 2), Fast_tac 2, 
    (* ipo.corlI *) (EVERY' itacs 1), Safe_tac, (etac (monoD RS subsetD) 1), 
    atac 2, (etac order_trans 1), (rtac r_into_red 1),
    (* ipo.hierI *) (dtac rp_pc_cut0 1), (rewtac red_props_pc_def),
    (etac allE3 1), mp_tac 1, mp_tac 1, Clarify_tac 1, 
    (etac rc3nE 1), atac 3, (rtac subt_refl 1), (rtac rtrancl_refl 1),
    (* ipo.pctxtI *) (hd itacs 1), Fast_tac 2,
    (datac (rel_compI RS (nured_psubt RS subsetD)) 1 1),
    (dtac rel_comp3_mono' 1), (contr_tac 4),
    (auto_tac (cesimps [psubt_def])) ]) ;

val _ = bind_thm ("ipo_red_props_dtp",
  ipo_red_props_crel RSN (2, red_props_dtp_lemh)) ;

val ipo_red_props_dtp' = meta_std (rewrite_rule [prp_def] (
  rewrite_rule [red_props_dt_def] (ipo_red_props_dtp) 
    RS rel_subsetD)) ;

val _ = qed_goal "hcut_notS" ipodef.thy
  "hpocfg (-S) so Un hpocl (-S) crel ro <= hds_notin S"
  (fn _ => [ (safe_tac (ces [hpocfg.elims, hpocl.elims])) ]) ;

val wf_shc = [hcut_notS, transfer ipodef.thy hpowfcut] MRS wf_cuth ;
val wf_shc' = rewrite_rule [cuth_def] wf_shc ;

val wf_ps = [refl RSN (5, wfh_lem3), wf_cut0, wf_subset] MRS wfUn_movr ;
val u3 = [subset_refl, hpocl2_ge, wfh_lem5'] MRS
  transfer ipodef.thy (Un_mono RS Un_mono) ;
val wf_ps' = [asm_rl, hcut_notS, asm_rl, refl, asm_rl, hpowf2dt, u3] MRS wf_ps ;

val hrpc = 
  [asm_rl, ipo_01 RS sym RS ipo_red_props_crel, wf_subset] MRS all_sn3_crel' ;
val hrpc' = full_simplify (esimps []) (rotate_prems ~1 (wf_ps' RSN (4, hrpc))) ;

val wf_ipo' = tacsthm [
  (SELECT_GOAL (Safe_tac THEN TRYALL Fast_tac) 1),
  (dtac (sn12o RS subsetD) 1), (dtac (mk_mono' wfh_lem2) 1), 
  Fast_tac 2, (REPEAT (etac thin_rl 1)), Simp_tac 1,
  (FIRSTGOAL (match_tac [ipo1_notin])),
  (TRYALL (resolve_tac (msc (corl_props_def RS defD1))))] hrpc' ; 

val _ = bind_thm ("wf_ipo", fold_rule [mk_eq ipo_01] (rdp wf_ipo')) ;


