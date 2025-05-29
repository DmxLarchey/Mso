
structure redn = struct val thy = the_context () end ;
val _ = use_legacy_bindings redn.thy ;

val cut1_dvk_prop_def' = rewrite_rule [dvk_cond_def] cut1_dvk_prop_def ;    
val cut1_gip_prop_def' = rewrite_rule [gip_cond_def] cut1_gip_prop_def ;    
val cut1_gip_propa_def' = rewrite_rule [gip_cond_def] cut1_gip_propa_def ;    
val cut1_prop_def = rewrite_rule [cut1_propa_def] cut1_prop_def' ;    
val cut1_propaI = cut1_prop_def' RS defD1 RS spec ;
val _ = qed_goalw_spec_mp "cut1_gip_propaI" redn.thy 
  [cut1_gip_prop_def, cut1_gip_propa_def]
  "cut1_gip_prop c1 --> cut1_gip_propa c1 x" fn_at ;

val _ = qed_goal "fwf_redn" redn.thy "fwf (ctxt r) <= ctxt (fwf r)"
  (fn _ => [ Safe_tac, (chop_tac 1 (etac rev_mp 1)),
    (etac ron.induct 1), (clarify_tac (cis [ron.red_cutI]) 2),
    (etac rev_subsetD 2), (rtac wfp_mono 2), Fast_tac 2,
    (etac oneup.elims 1), (Clarsimp_tac 1),
    (rtac ro_intr 1), (dtac snUp' 1),
    (chop_tac 1 (etac rev_mp 1)),
    (etac onerel.induct 1), (dtac IntD2 1), (Auto_tac)]) ;

val _ = qed_goal_spec_mp "rfr_eq" redn.thy 
  "((a, b) : ctxt (fwf (ctxt r))) = \
  \ ((a, b) : nured (fwf (ctxt r)) | (a, b) : r & b : wfp (ctxt r))" 
  (fn _ => [ (rtac iffI 1), (etac ron.elims 1), 
    (auto_tac (cesimps [nured_def])),
    (etac ron.elims 1), (etac notE 1),
    (auto_tac (cesimps [nured_def])),
    (rtac (fwf_redn RS onerel_mono RS oneup_mono RS subsetD) 1), 
    (rtac (onerel_fwf_sub RS oneup_mono RS subsetD) 1), 
    (clarsimp_tac (cesimps [fwf_oneup RS sym]) 1),
    (rtac (wfp_mono RS subsetD) 1), atac 2, Fast_tac 1,
    (rtac ron.red_cutI 1), Safe_tac ]) ;

val _ = bind_thm ("rfrE", 
  tacthm (etac conjE 3) (rewrite_rule [nured_def] (rfr_eq RS iffD1 RS disjE))) ;
val _ = bind_thm ("rfrI", ron.red_cutI RS fwf.fwfI RS ron.red_cutI) ; 

val _ = qed_goal "rfr_le" redn.thy 
  "ctxt (fwf (ctxt r)) <= ctxt r"
  (fn _ => [ (rtac order_trans 1), (rtac (red_idemp RS equalityD1) 2),
    (rtac red_mono 1), Fast_tac 1]) ;

val _ = qed_goalw "cfc_lem" redn.thy [wfpc_def]
  "ctxt (fwf (ctxt r)) = ctxt (r Int wfpc r)"
  (fn _ => [ Safe_tac, (etac red_mono' 2), Force_tac 2, 
    (etac ctxt.induct 1), 
    (rtac ctxt.red_nuI 1), (etac oo_mono' 1), Force_tac 1,
    
    Clarify_tac 1, (chop_tac 1 (etac rev_mp 1)), (etac ctxt.induct 1), 
    (fast_tac (cis [ctxt.red_cutI]) 2), 
    (etac oneup.elims 1), (safe_tac (cds [snUp])),
    (rtac ctxt.red_nuI 1), (dtac onerel_inst 1), Clarify_tac 1, 
    (ftac onerel_in 1), (etac onerel_mono' 1), Fast_tac 1 ]) ;

val _ = qed_goalw "nfc_lem" redn.thy [nured_def]
  "nured (fwf (ctxt r)) = nured (r Int wfpc r)"
  (fn _ => [ (simp_tac (esimps [cfc_lem]) 1) ]) ;

val () = qed_goalw "wf_sn1order" redn.thy [sn1order_def'] "wf (sn1order r)"
  (fn _ => [ (simp_tac (esimps [wf1up, wf_sn1red]) 1)]) ;

val () = qed_goalw_spec_mp "sn1_sn" redn.thy [sn1order_def']
  "(dtn, dt) : (sn1order r)^* --> set (isubts dt) <= wfp (ctxt r) --> \
    \ set (isubts dtn) <= wfp (ctxt r)"
  (fn _ => [ (rtac impI 1), (etac rtrancl_induct 1),
    (etac oneup.elims 2), (ALLGOALS Asm_full_simp_tac),
    (rtac impI 1), (etac mp 1), (eatac onered_allsn 1 1)]) ;

val sn1r_onered' = (rewrite_rule [onered_def] sn1r_onered) ;

val () = qed_goalw "sn1o_nured" redn.thy [sn1order_def, mk_eq nured_def]
  "sn1order r <= nured r"
  (fn _ => [ (rtac oneup_mono 1), (rtac sn1r_onered' 1)]) ;

val () = bind_thm ("sn1o_nured'", sn1o_nured RS subsetD) ; 
val () = bind_thm ("sn1o_red", sn1o_nured' RS red_nured) ;
val () = bind_thm ("sn1o_red_sub", mk_mono sn1o_red) ;
val () = bind_thm ("nured_mono", 
  fold_rule [nured_def] (red_mono RS onerel_mono RS oneup_mono)) ;
val nured_mono' = mk_mono' nured_mono ;

val () = qed_goalw_spec_mp "nured_sn" redn.thy [sn1order_def', nured_def]
  "(ptr, pt) : nured r --> set (isubts pt) <= wfp (ctxt r) --> \ 
    \ set (isubts ptr) <= wfp (ctxt r) & (ptr, pt) : sn1order r"
  (fn _ => [(rtac impI 1), (etac oneup.elims 1), Safe_tac,
    (dtac snOnerel 1), (dtac (onerel_fwf RS oneup.ouI) 3), Auto_tac]) ;

val () = qed_goalw_spec_mp "nured_sn" redn.thy [sn1order_def', nured_def]
  "(ptr, pt) : nured r --> set (isubts pt) <= wfp (ctxt r) --> \ 
    \ set (isubts ptr) <= wfp (ctxt r) & (ptr, pt) : sn1order r"
  (fn _ => [(Clarify_tac 1), (dtac r_wf 1), 
    (auto_tac (ces [oneup.elims, onerel_fwf], 
      esimps [wfp_oneup, wfp_onered]))]) ;

val () = qed_goal_spec_mp "nuredtc_sn" redn.thy 
  "(ptr, pt) : (nured r)^+ --> set (isubts pt) <= wfp (ctxt r) --> \ 
    \ set (isubts ptr) <= wfp (ctxt r) & (ptr, pt) : (sn1order r)^+"
  (fn _ => [rtac impI 1, (etac trancl_induct 1), 
    (rtac impI 1), (datac nured_sn 1 1), Fast_tac 1,
    (rtac impI 1), (datac nured_sn 1 1), Safe_tac,
    (eatac (trancl_into_rtrancl RS rtrancl_into_trancl1) 1 1)]) ; 

val () = qed_goal_spec_mp "nuredrtc_sn" redn.thy 
  "(ptr, pt) : (nured r)^* --> set (isubts pt) <= wfp (ctxt r) --> \ 
    \ set (isubts ptr) <= wfp (ctxt r) & (ptr, pt) : (sn1order r)^*"
  (fn _ => [rtac impI 1, (etac rtrancl_induct 1), Fast_tac 1, 
    (rtac impI 1), (datac nured_sn 1 1), Safe_tac,
    (eatac rtrancl_into_rtrancl 1 1)]) ; 

val () = qed_goal_spec_mp "dth1_lem" redn.thy
  "pt ~: wfp (ctxt r) --> set (isubts pt) <= wfp (ctxt r) --> \
    \ (EX ptr ptc. (ptr, pt) : (sn1order r)^* & \
      \ (ptc, ptr) : r & ptc ~: wfp (ctxt r))"
  (fn _ => [ (strip_tac 1),
    (ftac (dth_lemg RSN (2, thin_rl)) 1), (Full_simp_tac 1),
    (full_simp_tac (esimps [wfp_nured' RS sym]) 1), (Safe_tac), 
    (subgoal_tac "(ptc, ptr) : r" 1), 
    (rtac exI 1), (rtac exI 1), (Safe_tac), atac 2, 
    ((etac ron.elims THEN_ALL_NEW Asm_full_simp_tac) 3), 
    (Asm_full_simp_tac 2),
    (full_simp_tac (HOL_ss addsimps [reflcl_trancl RS sym]) 1),
    Safe_tac, (datac nuredtc_sn 1 1), 
    (auto_tac (cesimps [nured_def]))]) ;

(* not wanted 
val _ = bind_thm ("lower_reds", prove_goal redn.thy 
  "(ALL y.  (y, z) : isubt^+ --> (ALL b. (y, b) : s --> (y, b) : t)) --> \
    \ (ALL y.  (y, z) : isubt^+ --> \
      \ (ALL b. (y, b) : ctxt s --> (y, b) : ctxt t))"
  (fn _ => [ Safe_tac, (chop_tac 1 (etac rev_mp 1)),
    (etac ron.induct 1), (Fast_tac 2), 
    (etac oneup.elims 1), (safe_tac (cis [ron.red_nuI])), 
    (chop_tac 2 (etac rev_mp 1)), (etac onerel.induct 1), Safe_tac, 
    (etac onerel_mono_ss1 2), (Clarsimp_tac 2), 
    (REPEAT (EVERY [(REPEAT (etac notE 1)),
      (rtac trancl_into_trancl2 1), atac 2, Force_tac 1])) ]) RS mp) ;
*)
val () = qed_goal_spec_mp "wfp_rfr'" redn.thy 
  "dt : wfp (ctxt (fwf (ctxt r))) & set dts <= wfp (ctxt (fwf (ctxt r)))"
  (fn _ => [ (induct_tac "dt dts" 1), (ALLGOALS Asm_simp_tac),
    (dtac (wfp_onerel' RS iffD2) 1), (etac wfp_wk_induct 1),
    (rtac wfp.wfpI 1), Safe_tac, (etac ctxt.elims 1), Safe_tac,
    (datac wfpRed 1 2), (etac wfp_mono' 2), (rtac rfr_le 2),
    (etac oneup.elims 1), Fast_tac 1 ]) ;

val _ = bind_thm ("wf_rfr", wfp_rfr' RS conjunct1 RS wfp_wfI) ;

val () = qed_goalw "wf_nfr" redn.thy [nured_def, mk_eq wf1up] 
  "wf (nured (fwf (ctxt r)))"
  (fn _ => [ (rtac wf_onerel 1), (rtac wf_rfr 1)]) ;

AddIffs [wf_rfr, wf_nfr] ;

val () = qed_goalw "nfr_sn1" redn.thy [nured_def, sn1order_def'] 
  "sn1order r <= nured (fwf (ctxt r))"
  (fn _ => [ (rtac oneup_mono 1), (rtac onerel_mono 1), Fast_tac 1]) ;

(** sn2order **)

val () = qed_goalw "wf_sn2order" redn.thy [sn2order_def'] "wf (sn2order r)"
  (fn _ => [ (simp_tac (esimps [wf1up]) 1), 
    (rtac wf_onerel 1), (rtac wf_rfr 1)]) ;

AddIffs [wf_sn1order, wf_sn2order] ;

val () = qed_goal "sn12o" redn.thy "sn1order r <= sn2order r"
  (fn _ => [ (simp_tac (esimps [sn1order_def', sn2order_def']) 1),
    (rtac oneup_mono 1), (rtac onerel_mono 1), (rtac r_into_red 1)]) ;

val dt12' = [order_refl, sn12o] MRS Un_mono ;
val wf_cus12 = dt12' RSN (2, wf_subset) ;

val _ = bind_thm ("sn2o_defh",
  [sn2order_defn, mk_eq nfc_lem] MRS transitive_thm) ;

val _ = qed_goalw_spec_mp "c1p_wfdt" redn.thy [cut1_prop_def]
  "wf cuto --> cut1_prop cuto --> wf (cuto Un sn1order any)"
  (fn _ => [ Safe_tac, (rtac wf_cus12 1), (rtac wfUn_movr 1),
    (rtac wf_sn2order 3), (atac 2),
    (rewtac sn2order_defn), (etac spec 1) ]) ;

(** constrict **)

val () = qed_goal "fwf_constrict" redn.thy 
  "fwf (ctxt rho) <= fwf (ctxt (constrict rho))"
  (fn _ => [ Safe_tac, 
    (etac wfp_mono' 2), (rtac red_mono 2),
    (clarsimp_tac (cesimps [constrict_def]) 2),
    (chop_tac 1 (etac rev_mp 1)), (etac ron.induct 1),
    (clarsimp_tac (cis [ron.red_cutI] addSEs [subt_sn],
      esimps [constrict_def]) 2),
    (etac oneup.elims 1), Safe_tac, (dtac snUp 1), (rtac ro_intr 1), 
    (chop_tac 1 (etac rev_mp 1)), (etac onerel.induct 1), 
    (clarsimp_tac (cis [ro_intr], esimps []) 1), 
    (clarsimp_tac (ces [subt_sn] addSIs [isubt_subt], esimps []) 1)]) ;

val () = qed_goalw "sn1_constrict" redn.thy [sn1order_def']
  "sn1order rho <= sn1order (constrict rho)"
  (fn _ => [rtac oneup_mono 1, rtac onerel_mono 1, rtac fwf_constrict 1]) ;

val _ = qed_goalw "constrict_redn" redn.thy [constrict_def]
  "constrict (ctxt r) <= ctxt (constrict r)"
  (fn _ => [ Safe_tac, (chop_tac 1 (etac rev_mp 1)), (etac ron.induct 1), 
    (clarsimp_tac (cis [ron.red_cutI], esimps []) 2),
    (clarsimp_tac (cis [ron.red_nuI] addSEs [oneup.elims], esimps []) 1),
    (etac onerel.elim 1), Safe_tac,
    (clarsimp_tac (ces [subt_sn], esimps []) 1),
    (etac rev_mp 1), (etac onerel.induct 1), (ALLGOALS Clarsimp_tac),
    (eatac (isubt_subt RS subt_snr) 1 1)]) ;

val constrict_redn' = constrict_redn RS subsetD ;

val _ = qed_goal_spec_mp "wfp_subt_O_constrict" redn.thy
  "wfp (subt O constrict (ctxt rho)) <= wfp (ctxt rho)"
  (fn _ => [ Safe_tac, (etac wfp.induct 1), (etac rev_mp 1), 
    (res_inst_tac [("a", "dt")] (wf_isubt RS wf_induct) 1), (Clarify_tac 1),
    (case_tac "ALL y. (y, xa) : isubt --> y : wfp (ctxt rho)" 1),
    (etac thin_rl 1), (rtac wfp.wfpI 1), (etac all_forward 1), 
    (rtac impI 1), (etac impE 1), 
    (rtac rel_compI 1), (rtac subt_refl 2),
    (clarsimp_tac (cesimps [constrict_def]) 1),
    (etac conjunct2 1), Clarify_tac 1, (etac allE 1 THEN mp_tac 1),
    (etac mp 1), (etac isubt.elims 1), Clarify_tac 1, 
    (subgoal_tac "(ya, Node a sts) : subt" 1), (etac subt_thms.sis 2),
    Simp_tac 2, (etac allE 1), (etac impE 1), (TRYALL Fast_tac) ]) ;

val _ = qed_goal_spec_mp "wfp_constrict" redn.thy
  "wfp (ctxt (constrict rho)) <= wfp (ctxt rho)"
  (fn _ => [ (rtac order_trans 1), (rtac order_trans 1),
    (rtac ([wfp_psubt_subt, wfp_psubt_redn] MRS trans RS equalityD2) 1),
    (rtac ([order_refl, constrict_redn] MRS rel_comp_mono RS wfp_mono) 1),
    (rtac wfp_subt_O_constrict 1) ]) ;

(* Thm 6 of Arts & Giesl, 
  Termination of Term Rewriting Using Dependency Pairs
  Theoretical Computer Science 236 (2000), 133-178, 2000,
  since rho O subt approximates to the set of dependency pairs, 
  extension to nured as per Juergen's email, then to sn1order;
  from this, trivial to get Lemma 1 of 
  N. Hirokawa & A. Middeldorp, Dependency Pairs Revisited, RTA-04, LNCS 3091.
  *)

val _ = qed_goal "wfp_subt_O_tcl_sub" redn.thy
  "wfp (subt O (sn1order rho)^* O constrict rho) <= wfp (ctxt rho)"
  (fn _ => [ Safe_tac, (etac wfp.induct 1), (etac rev_mp 1), 
    (res_inst_tac [("a", "dt")] (wf_isubt RS wf_induct) 1), (Clarify_tac 1),
    (case_tac "ALL y. (y, xa) : isubt --> y : wfp (ctxt rho)" 1),

    (etac thin_rl 1), (subgoal_tac "xa : wfp (nured rho)" 1),
    (clarsimp_tac (cesimps [wfp_nured]) 2),
    (subgoal_tac "ALL dtn. (dtn, xa) : (sn1order rho)^* O constrict rho --> \
      \ dtn : wfp (ctxt rho)" 1), 
    (etac all_forward 2), Fast_tac 2, 
    (etac thin_rl 1), (etac rev_mp 1), 
    (chop_tac 1 (etac rev_mp 1)), (etac wfp.induct 1),
    (strip_tac 1), (rtac wfp.wfpI 1), 
    (SELECT_GOAL (safe_tac (cds [red_cases RS iffD1])) 1), 
    (subgoal_tac "(dtn, dta) : constrict rho" 2), Fast_tac 2,
    (simp_tac (esimps [constrict_def]) 2), Force_tac 2,
    (etac allE 1 THEN mp_tac 1), 
    (subgoal_tac "(dtn, dta) : sn1order rho" 1), 
    (etac conjE 1), (etac impE 1 THEN etac mp 2),
    (fast_tac (ces [nth (transitive_closure_trans, 5), all_forward, mp]) 1), 
    (TRYALL (dtac nured_sn THEN_ALL_NEW 
      (force_tac (cds [subsetD], esimps [])))),
    
    Safe_tac, (etac allE 1 THEN mp_tac 1),
    (etac mp 1), (etac isubt.elims 1), Clarify_tac 1, 
    (subgoal_tac "(ya, Node a sts) : subt" 1), (etac subt_thms.sis 2), 
    Simp_tac 2, (etac allE 1), (etac impE 1), (TRYALL Fast_tac) ]) ;
    
val _ = qed_goal "wfp_subt_O_tcl_sup" redn.thy
  "wfp (ctxt rho) <= wfp (subt O (ctxt rho)^* O rho)"
  (fn _ => [ (rtac order_trans 1), (rtac equalityD1 1),
    (rtac (order_refl RS rel_comp_mono RS wfp_mono) 2), 
    (rtac ([order_refl, r_into_red] MRS rel_comp_mono) 2), 
    (Simp_tac 1), (res_inst_tac 
      [("s", "wfp (subt O ctxt ((ctxt rho)^+))")] trans 1),
    (simp_tac (esimps [wfp_subt_O_redn]) 1),
    (ALLGOALS (simp_tac (esimps [rtr]))) ]) ;

val _ = bind_thm ("wfp_subt_O_tcl", tacsthm
  [ (rtac wfp_subt_O_tcl_sub 1), (rtac order_trans 1),
    (rtac wfp_subt_O_tcl_sup 1),
    (REPEAT (resolve_tac [order_refl, wfp_mono, rel_comp_mono, 
      rtrancl_mono, mk_mono (sn1o_nured' RS red_nured), rel_subsetI] 1)),
    rewtac constrict_def, (Clarsimp_tac 1)] equalityI) ;

val _ = qed_goal "wf_chain" redn.thy
  "wf (constrict rho O subt O (sn1order rho)^*) = wf (ctxt rho)"
  (fn _ => [ (rtac trans 1), (rtac wf_rev_comp_eq 1),
    (rtac wf_wfp_eq 1), (simp_tac (esimps [O_assoc, wfp_subt_O_tcl]) 1) ]) ;

(* useful tactics *)

(* artac : int -> tactic
  deal with subgoal whose premise gives a reduction 
  and whose conclusion is the corresponding reduction in a larger tree *)
fun artac sg st = (atac ORELSE' 
  (resolve_tac (ron.red_nuI :: oneup.ouI :: onerel.intrs) THEN' artac)) sg st ;

val _ = qed_goalw_spec_mp "ii_maptr1'" redn.thy [inv_image_def]
  "inj f --> (ae, be) : ctxt q --> \
    \ (ALL a b. (ae, be) = (maptree f a, maptree f b) --> \
    \ (a, b) : ctxt (inv_image q (maptree f)))"
  (fn _ => [ (rtac impI 1), (rtac impI 1), (etac ron.induct 1),
    (clarsimp_tac (cis [ron.red_cutI], esimps []) 2), Clarify_tac 1, 
    (case_tac "a" 1), (case_tac "b" 1), (etac oneup.elims 1),
    (clarsimp_tac (cis [ron.red_nuI], esimps [maptrees_def]) 1),
    (datac rev_injD 1 1), (Clarify_tac 1),
    (fatac (inj_maptree RS onerel_ii_map) 1 1), (etac onerel_mono' 1), 
    (clarsimp_tac (cesimps [inv_image_def]) 1) ]) ;
    
val _ = qed_goal_spec_mp "ii_maptr1" redn.thy "inj f --> \
  \ inv_image (ctxt q) (maptree f) <= ctxt (inv_image q (maptree f))"
  (fn _ => [ (Safe_tac), (etac (refl RSN (3, ii_maptr1')) 1),
    (full_simp_tac (esimps [inv_image_def]) 1)]) ;
    
val _ = qed_goal_spec_mp "ii_maptr2" redn.thy 
  "ctxt (inv_image q (maptree f)) <= inv_image (ctxt q) (maptree f)"
  (fn _ => [ Safe_tac, (etac ron.induct 1),
    (etac (mk_mono' (r_into_red RS inv_image_mono)) 2),
    (etac oneup.elims 1),
    (clarsimp_tac (cis [ron.red_nuI], esimps [inv_image_def]) 1),
    (etac onerel.induct 1),
    (REPEAT (force_tac (cesimps [inv_image_def]) 1))]) ;

val _ = qed_goal_spec_mp "fi_red1'" redn.thy 
  "(t, s) : ctxt q --> \
    \ (maptree f t, maptree f s) : ctxt (fwd_image q (maptree f))" 
  (fn _ => [ Safe_tac, (etac ron.induct 1), 
    (rtac (mk_mono' r_into_red) 2), Clarify_tac 2, 
    (rtac ron.red_nuI 1), (etac oneup.elims 1), Clarsimp_tac 1, 
    (etac onerel.induct 1), (TRYALL Force_tac)]) ;

val rimD = inj_maptree RSN (2, rev_injD) ;

val _ = qed_goal_spec_mp "fi_red1" redn.thy 
  "fwd_image (ctxt q) (maptree f) <= ctxt (fwd_image q (maptree f))" 
  (fn _ => [ (fast_tac (ces [fwd_image.elim, fi_red1']) 1) ]) ;

val _ = bind_thm ("wfp_mf",
  fi_red1 RS wfp_mono RS subsetD RS wfp_fwd_image);

val _ = qed_goal_spec_mp "fi_red2_ex'" redn.thy 
  "inj f --> (mft, mfs) : ctxt (fwd_image q (maptree f)) --> \
    \ (ALL s. mfs = maptree f s --> \
    \ (EX t. mft = maptree f t & (t, s) : ctxt q))"
  (fn _ => [ (rtac impI 1), (rtac impI 1), (etac ron.induct 1), 
    (fast_tac (ces fwd_image.elims addSD2 ("rimD", rimD)) 2),
    (etac oneup.elims 1), Clarify_tac 1, (case_tac "s" 1), 
    (clarsimp_tac (cis [ron.red_nuI], esimps [maptrees_def]) 1), 
    (dtac (inj_maptree RS onerel_map_fi_ex2) 1),
    (etac onerel_mono' 1), (rtac Int_lower2 1),
    (force_tac (cesimps [maptrees_def]) 1) ]) ;
   
val _ = qed_goal_spec_mp "fi_red2'" redn.thy 
  "inj f --> (mft, mfs) : ctxt (fwd_image q (maptree f)) --> \
    \ (ALL t s. (mft, mfs) = (maptree f t, maptree f s) --> \
      \ (t, s) : ctxt q)"
  (fn _ => [ (rtac impI 1), (rtac impI 1), (etac ron.induct 1), 
    (clarify_tac (ces fwd_image.elims addSD2 ("rimD", rimD)) 2),
    (clarify_tac (ces [oneup.elims]) 1), (case_tac "t" 1), (case_tac "s" 1), 
    (clarsimp_tac (cis [ron.red_nuI], esimps [maptrees_def]) 1), 
    (datac rev_injD 1 1), Clarify_tac 1, 
    (rtac onerel_map_fi_ex 1), (etac inj_maptree 1), 
    (etac onerel_mono' 1), (rtac Int_lower2 1) ]) ;

val [fi_red2_ex, fi_red2] = map remeqs [fi_red2_ex', fi_red2'] ;

(* note - this result doesn't hold although fi_red2' does
val _ = qed_goal_spec_mp "fi_red2" redn.thy "inj f --> \
  \ ctxt (fwd_image q (maptree f)) <= fwd_image (ctxt q) (maptree f)" 
  *)

val _ = qed_goal_spec_mp "wfp_fi" base.thy 
  "inj f --> (t : wfp r) = (maptree f t : wfp (fwd_image r (maptree f)))"
  (fn _ => [ Safe_tac, (etac wfp_fwd_image 2),
    (rtac wfp_fwd_image_sub 1), atac 2, (etac inj_maptree 1)]) ;

val _ = qed_goal_spec_mp "wfp_red_fi1" redn.thy 
  "inj f --> (t : wfp (ctxt r)) --> \
    \ (maptree f t : wfp (ctxt (fwd_image r (maptree f))))"
  (fn _ => [ Safe_tac, (etac wfp.induct 1), (rtac wfp.wfpI 1), 
    (fast_tac (cds [fi_red2_ex]) 1) ]) ;

val _ = qed_goal_spec_mp "wfp_red_fi" redn.thy 
  "inj f --> (t : wfp (ctxt r)) = (maptree f t : ?P)"
  (fn _ => [ Safe_tac, (etac wfp_mf 2), (eatac wfp_red_fi1 1 1) ]) ;

val _ = qed_goalw_spec_mp "fi_sn1" redn.thy [sn1order_def', fwf_def]
  "inj f --> fwd_image (sn1order q) (maptree f) \
    \ <= sn1order (fwd_image q (maptree f))"
  (fn _ => [ (clarsimp_tac (ces [fwd_image.elim, oneup.elims], esimps []) 1),
    (etac onerel.induct 1), 
    (auto_tac (ces [wfp_red_fi1, fi_red1'], esimps [])) ]) ;

val fi_sn1' = tacthm (rtac fwd_image.I 2) (fi_sn1 RS subsetD) ;

(* example of use of commuting reductions *)
val _ = qed_goal_spec_mp "nu_comm'" redn.thy
  "wf r --> r O nured r <= nured r O (ctxt r)^* --> \
    \ dt : wfp (ctxt r) & set dts <= wfp (ctxt r)"
  (fn _ => [ (strip_tac 1), (induct_tac "dt dts" 1),
    (dtac (reop rev wfUn_movl_dvk') 1),
    (full_simp_tac (esimps [red_cases']) 1),
    (full_simp_tac (esimps [red_cases' RS sym]) 1),
    (asm_simp_tac (esimps [wfp_nured']) 1), Auto_tac ]) ;

val nu_comm = zero_var_indexes (rewrite_rule [triv_forall_equality]
  (nu_comm' RS conjunct1 RS wfp_wfI)) ;

(* now, suppose we have the converse reordering, 
  ie "nured r O r <= r O (nured r)^*", and r is wf.
  Then should be able to reorder an infinite sequence of reductions as
  r^* O (nured r)^*,
  finitely many r since r is wf, then deal with instances of nured r
  in each subterm separately, ie, have instances of ctxt r in each subterm,
  and proceed the same way.
  This should work unless the term becomes of unbounded depth, as in
  r : a --> f(a), then nured r O r <= r,
  sequence a, f(a), f(f(a)), ... becomes of unbounded depth
  and does not terminate ;
  but what follows is a variation on that theme *)

val _ = qed_goal "nctxt_Suc'" redn.thy 
  "nctxt r (Suc n) = nctxt (oneup (onerel r)) n" (indAu "n") ;

val _ = qed_goal "ltnctxt_Suc'" redn.thy 
  "ltnctxt r (Suc n) = (oneup (onerel (ltnctxt r n)) Un r)"
  (fn _ => [ (induct_tac "n" 1), Simp_tac 1,
    (rtac trans 1), (rtac ltnctxt.ltnctxt_Suc 1), (rtac trans 1),
    (safe_asm_full_simp_tac (HOL_ss addsimps nctxt.simps) 1),
    (etac thin_rl 2), 
    (safe_asm_full_simp_tac (esimps [onerel_Un, oneup_Un]) 2), Auto_tac ]) ;

val _ = qed_goal_spec_mp "oucomm1" redn.thy 
  "(ALL n. nctxt r n O r <= r O (nctxt r n)^*) --> \
    \ nctxt r n O ltnctxt r n <= ltnctxt r n O (nctxt r n)^*"
  (fn _ => [ (rtac impI 1), (induct_tac "n" 1), (Force_tac 1), 
    (simp_tac (HOL_ss addsimps [ltnctxt_Suc', O_Un, Un_O]) 1),
    (rtac Un_mono 1), (asm_simp_tac HOL_ss 2),
    (simp_tac (HOL_ss addsimps 
      (([oneup_comp, oneup_rtrancl] RL [sym]) @ nctxt.simps)) 1),
    (rtac oneup_mono 1), 
    (rtac order_trans 1), (rtac comp_onerel 1), 
    (dtac onerel_mono 1), Auto_tac, 
    (datac subsetD 1 1), (REPEAT (dtac (onerel_comp RS subsetD) 1)),
    (fast_tac (cds [onerel_rtrancl RS rel_subsetD]) 1) ]) ;

(* or a corresponding result using wfUn_movr *)
val _ = qed_goal_spec_mp "oucomm" redn.thy 
  "(ALL n. nctxt r n O ltnctxt r n <= ltnctxt r n O (nctxt r n)^*) --> \
    \ (ALL n. wf (nctxt r n)) --> wf (ltnctxt r n)"
  (fn _ => [ Safe_tac, (induct_tac "n" 1), (ALLGOALS Simp_tac), 
    (REPEAT (etac allE 1)), (eatac wfUn_movl 2 1), Auto_tac ]) ;

val oucomm' = oucomm1 RS allI RS oucomm ;

val _ = qed_goal "wf_nctxt" redn.thy "wf (nctxt r n) = wf r"
  (fn _ => [ (induct_tac "n" 1), 
    (ALLGOALS (simp_tac (esimps [wf1up, wf_onerel_eq]))) ]) ;

(* cut1_gip_prop and cut1_prop *)
val _ = qed_goalw_spec_mp "movr_cond_gip" redn.thy [gip_cond_def]
  "r O s <= s^* O r --> gip_cond r s"
  (fn _ => [ (rtac impI 1), (etac subset_trans 1), (rtac movr_gip 1) ]) ;

val _ = qed_goalw_spec_mp "cut1_prop_gip" redn.thy
  [cut1_gip_prop_def, cut1_prop_def] "cut1_prop c --> cut1_gip_prop c"
  (fn _ => [ (rtac impI 1), (etac all_forward 1), (etac movr_cond_gip 1) ]) ;

(* cut1_dvk_prop and cut1_prop, I think not needed *)
val _ = qed_goalw_spec_mp "movr_cond_dvk" redn.thy [dvk_cond_def]
  "r O s <= s^* O r --> dvk_cond r s"
  (fn _ => [ (rtac impI 1), (etac subset_trans 1), (rtac movr_dvk 1) ]) ;

val _ = qed_goalw_spec_mp "cut1_prop_dvk" redn.thy
  [cut1_dvk_prop_def, cut1_prop_def] "cut1_prop c --> cut1_dvk_prop c"
  (fn _ => [ (rtac impI 1), (etac all_forward 1), (etac movr_cond_dvk 1) ]) ;

