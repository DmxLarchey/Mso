
structure orders = struct val thy = theory "orders" end ;
use_legacy_bindings orders.thy ;
fun u _ = use_thy "orders" ;

(** class rewr_ok_jgl **)

(** use of abstract reduction system results **)
val _ = bind_thm ("nr_gbscf", [wf_psubt, nr_nra] MRS nra_gbscf) ;
(* note - this result gives dt : wfp rho, not dt : wfp (ctxt rho) *)
val all_wf_nr = [wfp_psubt, nr_gbscf, wf_gjgl] MRS all_wf_gbsn ;
val dtjgl_def' = rewrite_rule [snHered_gindy'] dtjgl_def ;

(* note distinction between definition of red_props_dt and
  Condition 2 of CSL'05 paper: 
  red_props_dt depends only on immediate subterms being in SN *)

val () = qed_goalw_spec_mp "dt_abs" orders.thy 
  [red_props_dtaf_def, red_props_dt_def']
  "red_props_dt sigma cuto --> \
    \ All (red_props_dtaf (ctxt sigma) isubt \
      \ ((cuto Un sn1order sigma)^+) (wfp (ctxt sigma)))"
  (fn _ => [ (safe_tac (ces [ron.elim])), 
    (fold_tac [subt_def']),
    (REPEAT1 (eresolve_tac [allE, allE2] 2 THEN mp_tac 2)),
    (clarsimp_tac (cesimps [isubts_iff]) 2),
    (* reduction is in ctxt sigma \ sigma *)
    (etac thin_rl 1), (rewtac subt_def), (etac UnE 1), 
    (* subterm is term itself *)
    etac notE 2, (etac oneup.elims 2), Clarify_tac 2,
    (simp_tac (esimps [sn1order_def']) 2), 
    (rtac r_into_trancl 2), (rtac UnI2 2), (rtac oneup.ouI 2),
    (etac (onerel_sn RS conjunct2) 2), Fast_tac 2,
    (* subterm is proper subterm *)
    (rewtac (mk_eq (p_iOs RS sym))), Clarify_tac 1,
    (rtac subt_sn 1), atac 2,
    (etac oneup.elims 1), Clarify_tac 1,
    (datac in_onerel 1 1), Safe_tac, (etac wfpRed 1), TRYALL Fast_tac ]) ;

val () = qed_goal_spec_mp "dt_gindy" orders.thy 
  "red_props_dt rho cuto --> \
    \ dt : gindy ((cuto Un sn1order rho)^+) (gindy isubt (wfp (ctxt rho)))"
  (fn _ => [(safe_tac (cis [gindy.I])), rtac wfp.wfpI 1, strip_tac 1,
    (dtac dt_abs 1), (rewtac red_props_dtaf_def), 
    mp_tac 1, (etac allE 1 THEN mp_tac 1),
    (rtac gindy_all 1), (rtac wfp_isubt 1),
    (etac all_forward 1 THEN etac imp_forward 1), Fast_tac 1 ]) ;
    
val () = qed_goalw_spec_mp "all_sn3" orders.thy [dtjgl_def']
  "red_props_dt rho cuto --> dtjgl rho cuto --> dt : wfp (ctxt rho)"
  (fn _ => [strip_tac 1, rtac gindy_wf 1, (rtac wf_isubt 1),
    (etac allE 1), (etac gindy_bars 1), (etac dt_gindy 1) ]) ;

val () = qed_goal_spec_mp "all_sn3'" orders.thy 
  "red_props_dt rho cuto --> dtjgl rho cuto --> wf (ctxt rho)"
  (fn _ => [strip_tac 1, rtac wfp_wfI 1, datac all_sn3 1 1,
    (Full_simp_tac 1) ]) ;

val _ = bind_thm ("all_sn3_dt", wf_dtjgl RSN (2, all_sn3)) ;
val _ = bind_thm ("all_sn3_c", rpcdt' RS all_sn3_dt) ;
val _ = bind_thm ("all_sn3_pc", rp_pc_dt RS all_sn3_dt) ;

(** class rewr_ok_dt' **)

(* every derivation tree dt is snHered,
  depending only on dt being barred by snHered in dtorder,
  for dt whose proper subtrees are sn *)

(* trivially, ctxt isubt is well-founded *)
val () = qed_goalw "rpc_isubt" orders.thy [red_props_pc_def]
  "red_props_pc isubt {}"
  (fn _ => [ Safe_tac, (eatac subt_thms.sip 1 1) ]) ;

val () = qed_goalw "dtjgl_empty" orders.thy [dtjgl_def] "dtjgl r {}"
  (fn _ => [ (clarsimp_tac (cis [wf_bars, wf_trancl], esimps []) 1)]) ;

val wf_red_isubt = [rpc_isubt RS rpcc' RS rpcdt', dtjgl_empty] MRS all_sn3' ;

(** class rewr_ok_dt **)

(* alternative proof, using sntr directly,
  proof requires condition red_props_pc, stronger than red_props *)

val () = qed_goal_spec_mp "pc_gindy" orders.thy 
  "sn1order rho O cuto <= cuto --> red_props_pc rho cuto --> \
    \ dt : gindy cuto (gindy isubt (wfp (ctxt rho)))"
  (fn _ => [ (safe_tac (cis [gindy.I])),
    (rtac (notI RS notnotD) 1), (dtac dth1_lem 1),
    (force_tac (cesimps [isubts_iff]) 1),
    Safe_tac, (ftac sn1_sn 1), 
    (force_tac (cesimps [isubts_iff]) 1), (etac notE 1), 

    (* ptr cutReduces to ptc, need to show ptc is sn *)
    (rtac gindy_all 1), (rtac wfp_isubt 1), strip_tac 1, 
    (rewtac red_props_pc_def), (etac allE3 1), 
    (rewtac subt_def'), mp_tac 1, mp_tac 1, (etac disjE 1),

    (* show any subtree dts of ptc is snHered *)
    (rtac UnI2 1), (rewtac psubt_def), 
    (dtac converse_tranclD 1), 
    (clarsimp_tac (cesimps [isubts_iff]) 1),
    (fold_goals_tac [subt_def']), (rtac subt_sn 1),
    (EVERY [atac 2, etac subsetD 1, MSSG Simp_tac 1]),

    (* dts is cutorder-smaller than ptr, and therefore then dt *)
    (rtac UnI1 1), (dtac absorb_l_rtrancl 1), (Fast_tac 1) ]) ;

val () = qed_goal_spec_mp "all_sn_pc" orders.thy 
  "sn1order rho O cuto <= cuto --> red_props_pc rho cuto --> \
    \ wf cuto --> dt : wfp (ctxt rho)"
  (fn _ => [ Safe_tac, (rtac gindy_wf 1), (rtac wf_isubt 1), 
    (etac gindy_wf 1), (eatac pc_gindy 1 1) ]) ;

(* if ruleredn satisfies red_props_c2 conditions, then so does ruleredn^+,
  for same cutorder (and dtorder^+ is the same anyway) *)

val _ = qed_goal_spec_mp "prp2all_subt" orders.thy 
  "(dtm, dt) : prp2all rho cuto --> (dts, dtm) : subt --> \
    \ (dts, dt) : prp2all rho cuto"
  (fn _ => [ (auto_tac
    (ces [prp2allE] addSIs [prp2all.intros], esimps [subt_def'])),
    (datac rtrancl_trans 1 1), Fast_tac 1]) ;

val _ = qed_goal_spec_mp "rpt_lem" orders.thy 
  "(dtm, dt) : prs rho --> (dtn, dtm) : (ctxt rho)^* --> \
    \ (dts, dtn) : subt --> (dts, dt) : prs rho"
  (fn _ => [ (safe_tac (ces [prsE] addSIs [prs.intros])), 
    (subgoal_tac "?P" 1),
    (rtac (subt_redn RS move_r_rtrancl RS subsetD) 2),
    (eatac rel_compI 1 2), (Clarify_tac 1), (rewtac subt_def'),
    (REPEAT (datac rtrancl_trans 1 1)), Fast_tac 1 ]) ; 

Delrules [rel_compE] ; 

(* following lemma shows that if reduction ruleredn satisfies condition 2
  of the paper then so does its transitive closure *)
val _ = qed_goal_spec_mp "rpt_lem2" orders.thy 
  "wf (ctxt rho) --> ctxt rho <= prp2all rho cuto --> \
    \ (ALL dt dtm. (dtm, dt) : (ctxt rho)^+ --> \
    \ (dtm, dt) : prp2all rho cuto)"
  (fn _ => [ (REPEAT (rtac impI 1)), 
    (dtac (wf_psubt_redn RS wf_trancl) 1), (rewtac wf_def), 
    (etac allE 1), (etac mp 1), 
    strip_tac 1, (etac tranclE 1), Fast_tac 1,
    (subgoal_tac "(dtm, b) : prp2all rho cuto" 1), Fast_tac 2,
    (subgoal_tac "(b, x) : prp2all rho cuto" 1), Fast_tac 2,
    (subgoal_tac "(b, x) : ctxt rho O subt" 1), Fast_tac 2,
    (thin_tac "(b, x) : ctxt rho" 1),
    (REPEAT (eres_inst_tac [("P", "?p : ?S")] rev_mp 1)),
    (res_inst_tac [("x", "dtm")] spec 1),
    (cut_facts_tac [wf_psubt] 1),
    (dtac (wf_def RS defD1 RS spec) 1), (dtac mp 1),
    (eres_inst_tac [("x", "b")] spec 2), 
    (safe_tac (cis [prp2all.intros])),
    (ftac prp2allD 1),
    (etac allE 1 THEN etac impE 1 THEN rtac subt_refl 1),
    (etac prp2E 1), (dtac trancl_into_rtrancl 1),
    (datac rpt_lem 2 1), (etac prp2.prsI 1),
    (datac (prp2allD RS spec RS mp) 1 1), (etac prp2E 1),
    (rtac prp2.dtI 2), (eatac trancl_trans 1 2),
    (etac prsE 1), (REPEAT (etac rel_compEpair 1)),
    (dtac rtranclD 1), (etac disjE 1),
    (etac prp2allE 1), (etac allE 1 THEN etac mp 1),
    (clarsimp_tac (cds [trancl_into_rtrancl],
      esimps [subt_def', psubt_def]) 1),
    (eatac rtrancl_trans 1 1),
    (etac allE 1), (etac impE 1),
    (etac allE 2 THEN etac impE 2 THEN etac conjunct2 2),
    (resolve_tac transitive_closure_trans 1), Fast_tac 2,
    (clarsimp_tac (cesimps [subt_def', psubt_def]) 1), 
    (dresolve_tac transitive_closure_trans 1 THEN atac 1 THEN contr_tac 1),

    (etac allE 1), (eatac impE 1 1),
    (etac allE 1), (REPEAT (SOMEGOAL (etac impE))),
    Fast_tac 4, atac 3, 
    (rtac rel_compI 1), atac 2, 
    (clarsimp_tac (cis [trancl_into_rtrancl], 
      esimps [subt_def', psubt_def]) 1), 
    (eresolve_tac transitive_closure_trans 1 THEN atac 1),
    (etac prp2all_subt 1), (etac psubt_subt 1),
    (etac prp2allE 1 THEN etac allE 1 THEN eatac mp 1 1) ]) ;

val _ = qed_goal_spec_mp "prp2all_trans" orders.thy 
  "wf (ctxt rho) --> ctxt rho <= prp2all rho cuto --> \
    \ (ctxt rho)^+ <= prp2all rho cuto"
  (fn _ => [ (safe_tac (ces [rpt_lem2])) ]) ;

(* this result (actually, slightly stronger) is proved in a more
  elementary way in redn.ML as wfp_constrict *)
val _ = qed_goal_spec_mp "wf_constrict" orders.thy
  "wf (ctxt (constrict rho)) --> wf (ctxt rho)"
  (fn _ => [ (rtac impI 1), (rtac (wf_wfp RS iffD2) 1), Auto_tac, 
    (rtac all_sn3 1), (rtac wfc_dt 1), (rewtac (mk_eq dtjgl_gjgl)),
    (rtac wf_gjgl 1), (rtac wf_trancl 1), (etac wfc_dtwf 1)]) ;

(* this result is also proved in redn.ML, see wf_chain *)
val _ = qed_goal_spec_mp "wf_chain_sub" orders.thy
  "wf (constrict rho O subt O (sn1order rho)^*) --> wf (ctxt rho)"
  (fn _ => [ (rtac impI 1),
    (full_simp_tac (esimps [O_assoc RS sym]) 1),
    (dtac (wf_sn1order RS wf_comp_Unr RS iffD1) 1),
    (dtac (Un_commute RS arg_cong RS iffD1) 1),
    (rtac all_sn3' 1), (rewrite_tac [dtjgl_def, red_props_dt_def]),
    (rtac allI 2), (etac (wf_trancl RS wf_bars) 2),
    (clarify_tac (cis [prp.prpI]) 1),
    (subgoal_tac "?p : constrict rho" 1), Fast_tac 1, 
    (asm_simp_tac (esimps [constrict_def]) 1) ]) ;

val _ = qed_goal_spec_mp "asalem" orders.thy "dt : wfp (ctxt rho) --> \
    \ dt : wfp (constrict rho O subt O (sn1order rho)^*)"
  (fn _ => [ (rtac impI 1), 
    (dtac (wfp_O_subt_redn RS equalityD2') 1),
    (dtac (wfp_trancl RS equalityD2') 1),
    (etac wfp_mono' 1), (simp_tac (esimps [O_assoc RS sym]) 1),
    (rtac subsetI 1), (etac rel_compE 1), (hyp_subst_tac 1),
    (rtac (nth (transitive_closure_trans, 7)) 1),
    (etac rtrancl_mono' 1), (fast_tac (cds [sn1o_red]) 1),
    (rtac r_into_trancl 1), (force_tac (cesimps [constrict_def]) 1) ]) ;

val _ = qed_goal_spec_mp "scslem" orders.thy "dt : wfp (ctxt rho) --> \
    \ dt : wfp (sn1order rho Un (constrict rho O subt))"
  (fn _ => [ (rtac impI 1), 
    (dtac (wfp_O_subt_redn RS equalityD2') 1),
    (dtac (wfp_trancl RS equalityD2') 1),
    (etac wfp_mono' 1), Safe_tac,
    (dtac sn1o_red 1), (ALLGOALS (rtac r_into_trancl)), Fast_tac 1,
    (force_tac (cesimps [constrict_def]) 1) ]) ;

val _ = qed_goal_spec_mp "sulem" orders.thy 
  " ~ (set (isubts dt) <= wfp (ctxt rho)) --> \
    \ dt : wfp (constrict rho O subt O (sn1order rho)^*)"
  (fn _ => [ (rtac impI 1), (rtac wfp.wfpI 1),
    (strip_tac 1), rewtac constrict_def, Force_tac 1]) ;

val _ = qed_goalw_spec_mp "dt_constrict" orders.thy 
  [red_props_dt_def', constrict_def, meta_eq_def]
  "red_props_dt rho cuto == \
    \ (ALL t s. (t, s) : constrict rho O subt --> \
    \ t : wfp (ctxt rho) | (t, s) : (cuto Un sn1order rho)^+)"
  (fn _ => [ Safe_tac, (REPEAT (etac allE 1 ORELSE (mp_tac 1))), 
    (etac allE2 2), (etac impE 2), Auto_tac ]) ;
    
val clem = tacsthm [etac sulem 2, etac asalem 2] disjE ;

(* and we can conversely use this result to prove our main result *)
val _ = qed_goalw_spec_mp "all_sn3'_alt" orders.thy [dtjgl_def]
  "red_props_dt rho cuto --> dtjgl rho cuto --> wf (ctxt rho)"
  (fn _ => [ Safe_tac, (rtac wf_chain_sub 1), (rtac wfp_wfI 1),
    (eres_inst_tac [("x", "x")] allE 1),

    (etac bars.induct 1), 
    (force_tac (cis [clem], esimps [snHered_def]) 2),
    (rtac wfp.wfpI 1), Safe_tac, 
    (rewtac red_props_dt_def), (dtac (constrict_iff RS iffD1) 1),
    (etac conjE 1), (datac subsetD 1 1),
    (etac prpE 1), (etac allE 1 THEN REPEAT1 (mp_tac 1)),
    Safe_tac, (dtac (sn1o_red_sub RS rtrancl_mono RS subsetD) 1),
    (datac sn_red 1 1), (etac asalem 1),
    (dtac (mk_mono UnI2 RS rtrancl_mono RS subsetD) 1),
    (etac allE 1), (etac impE 1), 
    (eresolve_tac transitive_closure_trans 1 THEN atac 1), Clarify_tac 1]) ;

(* or doing the proof to follow that in RTA'05 paper *)

val _ = qed_goal_spec_mp "all_sn3'_alt2" orders.thy 
  "red_props_dt rho cuto --> wf (cuto Un sn1order rho) --> wf (ctxt rho)"
  (fn _ => [ Safe_tac, (rtac wf_chain_sub 1),
    (simp_tac (esimps [O_assoc RS sym, wf_sn1order RS wf_comp_Unr]) 1),
    (full_simp_tac (esimps [dt_constrict]) 1),
    (rtac wfp_wfI 1), (rtac (bars_wfp RS equalityD1') 1), 
    (dres_inst_tac [("x", "x")] wf_ssI 1),
    (dtac (wfp_trancl RS equalityD2') 1), (etac wfp.induct 1),
    (rtac bars.barsI 1), Clarify_tac 1, (etac UnE 1),
    (etac allE2 2), mp_tac 2, Safe_tac, Fast_tac 3, 
    (rtac bars.inI 2), (etac scslem 2), Fast_tac 1]) ;
    
    

