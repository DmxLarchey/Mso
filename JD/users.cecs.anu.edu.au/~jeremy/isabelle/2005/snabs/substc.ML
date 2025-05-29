
structure substc = struct val thy = theory "substc" ;
  val ipt_mk_cases = InductivePackage.the_mk_cases thy ; end ;
use_legacy_bindings substc.thy ;
fun u _ = use_thy "substc" ; 

AddSIs [subs.intros] ; (* not quite safe *)
AddSEs ctxt_S.intros ;

val cut0_def = rewrite_rule [lfp_const] cut0.defs ;

val _ = qed_goal "subs_hd_S" substc.thy 
  "subs (rule0_hd_S S) <= hds_notin (-S)"
  (fn _ => [ (auto_tac (ces [subs.elims, rule0_hd_S.elims], esimps [])) ]) ;

val _ = qed_goal_spec_mp "subs_mono" substc.thy 
  "r <= s --> subs r <= subs s"
  (fn _ => [ (fast_tac (ces [subs.elims]) 1) ]) ;

val _ = qed_goal_spec_mp "sc_inS" substc.thy 
  "r0s <= rule0_hd_S S --> subs (cut0 S r0s) <= symbs_in S"
  (fn _ => [ (safe_tac (ces 
      [subs.elims, cut0.elims, ctxt_S.elims, oneup_S.elims])),
    (datac subsetD 1 2), (etac rule0_hd_S.elims 2), Auto_tac ]) ;

val rStacs = [ Safe_tac, (etac ctxt_S.induct 1), 
  (fast_tac (cis [ctxt_S.cutI]) 2), 
  (etac oneup_S.elims 1), Safe_tac, (etac onerel.induct 1),
  (ALLGOALS (rtac ctxt_S.nuI)), Auto_tac,
  (etac rev_subsetD 1), (rtac onerel_mono 1), Auto_tac] ;

val () = qed_goal_spec_mp "ctxt_S_mono" substc.thy 
  "r <= s --> (ctxt_S S r <= ctxt_S S s)" (fn _ => rStacs) ;

val ctxt_S_mono' = mk_mono' ctxt_S_mono ;

val () = qed_goal "ctxt_S_idemp" substc.thy 
  "ctxt_S S (ctxt_S S r) = ctxt_S S r" (fn _ => rStacs) ;

val () = bind_thm ("ctxt_S_clos",  
  [ctxt_S_mono, ctxt_S_idemp RS order_eq_refl] MRS order_trans) ;

val _ = qed_goal "ctxt_S_Un1" substc.thy "ctxt_S S r = (UN p:r. ctxt_S S {p})"
  (fn _ => [ Safe_tac, 
    (etac ctxt_S.induct 1), (fast_tac (cis [ctxt_S.cutI]) 2),
    (dtac oo_S_inst 1), Safe_tac, (etac UN_I 1),
    (etac (oo_S_mono' RS ctxt_S.nuI) 1), 
    (etac ctxt_S_mono' 2), Auto_tac ]) ;

val _ = qed_goalw_spec_mp "subst_ctxt_S'" substc.thy [ctxt1_def]
  "(t, s) : ctxt_S S {(tb, sb)} --> \
    \ (subst f t, subst f s) : ctxt1 (subst f tb, subst f sb)"
  (fn _ => [ (rtac impI 1), (etac ctxt_S.induct 1),
    (rtac ctxt.red_cutI 2), (Fast_tac 2),
    (dtac oo_S_mono' 1), (rtac Int_lower2 1),
    (etac oneup_S.elims 1), Clarsimp_tac 1,
    (rtac ro_intr 1), (etac onerel.induct 1), Auto_tac ]) ;

val _ = qed_goal_spec_mp "subst_ctxt_S" substc.thy 
  "(t, s) : ctxt_S S r --> (subst f t, subst f s) : ctxt (subs r)"
  (fn _ => [ (stac ctxt_S_Un1 1), Clarify_tac 1, 
    (dtac subst_ctxt_S' 1), rewtac ctxt1_def,
    (etac red_mono' 1), Fast_tac 1 ]) ;

val _ = qed_goalw "cut0_r0p" substc.thy [cut0_def]
  "cut0 S r <= rule0_prop S" 
  (fn _ => [ Clarsimp_tac 1, (eatac r0p_subt 1 1) ]) ;

val _ = qed_goalw_spec_mp "cut0_r0ph" substc.thy [rule0_proph_def]
  "r0s <= rule0_hd_S S --> cut0 S r0s <= rule0_proph S"
  (fn _ => [ Safe_tac, (ftac (cut0_r0p RS subsetD) 1),
    (etac cut0.elims 1), (etac ctxt_S.elims 1), (etac oneup_S.elims 1), 
    (auto_tac (ces [rule0_hd_S.elims], esimps [])) ]) ;

val _ = qed_goal_spec_mp "subs0_nured" substc.thy
  "X <= hds_notin S --> sr0s <= rule0_proph S --> \
    \ subs sr0s O nured X <= (nured X)^* O subs sr0s"
  (fn _ => [ Safe_tac, (dtac nured_inst 1), 
    (rewtac nured1_def), (etac subs.elims 1), Safe_tac,
    (REPEAT (datac subsetD 1 1)), (etac hds_notin.elims 1), 
    (dtac (red_nured_sub RS subsetD) 1), (fold_tac [ctxt1_def]),
    (dtac hier_lemh 1), atac 2, Force_tac 1, Safe_tac, 
    (rtac rel_compI 1), (etac rtrancl_mono' 2), 
    (rtac nured_mono 2), Fast_tac 2, (etac subs.I 1) ]) ;

val _ = bind_thm ("sc_nured", cut0_r0ph RSN (2, subs0_nured)) ;
val _ = bind_thm ("sc_nured_dvk", sc_nured RS movr_cond_dvk) ;

val _ = qed_goal_spec_mp "sc_chn" substc.thy "X <= hds_notin S --> \
    \ subs (cut0 S r0s) O ctxt X <= subs (cut0 S r0s) O nured X"
  (fn _ => [ (clarsimp_tac (cesimps [red_cases']) 1), 
    (etac disjE 1), Fast_tac 1, (rewtac cut0_def),
    (auto_tac (ces [subs.elims], esimps [])) ]) ;

(* taking S-ctxt preserves rule0_prop *)
(* not true, must look at other branches involved in context
val _ = qed_goal "S_ctxt_pres_r0p" substc.thy 
  "rule0_prop S (t, s) --> (t', s') : ctxt_S S {(t, s)} --> \
    \ rule0_prop S (t', s')"
  (fn _ => [ (Clarsimp_tac 1), (etac ctxt_S.induct 1), Fast_tac 2,
    (dtac oo_S_inst 1), Clarify_tac 1, 
*)

val ec2r = tacsthm [etac conj_forward 2, TRYALL (etac sym)] ex_forward ; 
val ex_substr = zero_var_indexes (simplify (esimps []) ex_subst' RS ec2r) ;
val ex_subst'' = tacthm (rtac exI 1) ex_substr ;
val ex_subst'3 = (full_simplify (esimps []) o tacthm (rtac exI 2) o
  read_instantiate [("s", "SVar ?n")]) ex_substr ;

val ecc_tacs = [ (subgoal_tac "Ex ?P" 2), (etac ex_forward 2),
  (rtac conjI 2), (rtac conjI 3), atac 4, 
  (SOMEGOAL (eresolve_tac conjuncts)), 
  (force_tac (ces [rule0_prop.elims], esimps subst_sames) 2) ] ; 

val _ = qed_goal_spec_mp "sctxt_onerel" substc.thy
  "(t0, s0) : rule0_prop S --> aa : S --> \
    \ (dtl1, dtl2) : onerel {(subst f t0, subst f s0)} --> \
    \ (EX t0l s0l.  (SNode aa t0l, SNode aa s0l) : rule0_prop S & \
    \ (t0l, s0l) : onerel {(t0, s0)} & \
    \ (EX f'.  dtl1 = substs f' t0l & dtl2 = substs f' s0l))"
  (fn _ => [ (strip_tac 1), (etac onerel.induct 1),
    (res_inst_tac [("x", 
      "t0 # map SVar (newvars (vars_of s0) (length t))")] exI 1),
    (rtac exI 1), (rtac conjI 1), (rtac conjI 2), 
    (rtac onerel.onerelI1 2), Fast_tac 2, Simp_tac 2, 
    EVERY ecc_tacs, (rtac ex_subst'' 2), Fast_tac 2, 
    Simp_tac 3, (simp_tac (esimps [substs_map_SVar]) 2),
    (rtac ex_mapfun 2), Simp_tac 3, Simp_tac 2, 
    (SELECT_GOAL (auto_tac (cesimps [rule0_prop_def])) 1), 
    (dtac (tacthm (etac notin_newvars 2) contrapos_pn) 1), Fast_tac 1, 

    Clarify_tac 1, 
    (res_inst_tac [("x", "SVar (newvar (varss_of s0l)) # t0l")] exI 1),
    (rtac exI 1), (rtac conjI 1), (rtac conjI 2), 
    (etac onerel.onerelI2 2), Simp_tac 2, 
    EVERY ecc_tacs, (rtac ex_subst'3 2), (rtac refl 3), Fast_tac 3,
    (auto_tac (cesimps [rule0_prop_def])) ]) ;

val _ = qed_goal_spec_mp "sctxt_oo" substc.thy 
  "(t0, s0) : rule0_prop S --> (t, s) = (subst f t0, subst f s0) --> \
    \ (tc, sc) : oneup (onerel {(t, s)}) --> \
    \ (EX t0c s0c. (t0c, s0c) : rule0_prop S & \
      \ (t0c, s0c) : oneup_S S (onerel {(t0, s0)}) & \
      \ (EX f'. tc = subst f' t0c & sc = subst f' s0c)) | \
    \ (tc, sc) : hds_notin S"
  (fn _ => [ (strip_tac 1), (etac oneup.elims 1),
    (case_tac "a : S" 1), Fast_tac 2, 
    (rtac disjI1 1), Safe_tac, 
    (datac sctxt_onerel 2 1), Clarify_tac 1,
    (REPEAT_SOME (resolve_tac [exI, conjI, subst_substs.subst_SNode RS sym])),
    atac 1, (eatac oneup_S.ouI 1 1) ]) ;
    
(*
set show_sorts ;
reset show_sorts ;
*)

val _ = qed_goalw_spec_mp "sctxt_lem" substc.thy [ctxt1_def]
  "(t0, s0) : rule0_prop S --> (t, s) = (subst f t0, subst f s0) --> \
    \ (tc, sc) : ctxt1 (t, s) --> (EX t0c s0c. \
      \ (t0c, s0c) : rule0_prop S & (t0c, s0c) : ctxt_S S {(t0, s0)} & \
      \ (EX f'. tc = subst f' t0c & sc = subst f' s0c)) | \
    \ (EX t1 s1. symb_of s1 ~: S & (tc, sc) : ctxt1 (t1, s1) & \
      \ (t1, s1) : ctxt1 (t, s))"
  (fn _ => [ (strip_tac 1), (etac ctxt.induct 1),
    (rtac disjI1 2), (force_tac (cis [ctxt_S.cutI], esimps []) 2),
    (dtac oo_inst 1), (Full_simp_tac 1), (safe_tac csp), 
    (rtac disjI2 2), (REPEAT1 (rtac exI 2)), 
    (REPEAT_SOME (ares_tac [conjI])),
    (rtac ctxt.red_nuI 2), (etac oo_mono' 2), Fast_tac 2, 

    (datac (refl RSN (2, sctxt_oo)) 1 1), (etac disj_forward 1), 
    (REPEAT_FIRST (eresolve_tac [ex_forward, conj_forward, asm_rl])),
    (rtac ctxt_S.nuI 1), (etac oo_S_mono' 1), (etac singleton_subsetI 1),
    (REPEAT_FIRST (resolve_tac [exI, conjI])),
    (rtac (singletonI RS ctxt.red_cutI) 2),
    (etac hds_notin.elims 1), Force_tac 1, 
    (rtac ctxt.red_nuI 1), (etac oo_mono' 1), (etac singleton_subsetI 1) ]) ;

val () = qed_goal "nured_S_alt1" substc.thy 
  "ctxt_S S (oneup_S S (onerel r)) <= oneup_S S (onerel (ctxt_S S r))"
  (fn _ => [ Safe_tac, (etac ctxt_S.induct 1),
    (etac oo_S_mono' 2), (etac oo_S_mono' 1), Auto_tac ]) ;
    
val _ = qed_goal_spec_mp "ctxt_subs" substc.thy "r0s <= rule0_proph S --> \
    \ ctxt (subs r0s) <= ctxt (hds_notin S) Un (subs (cut0 S r0s) Un psubt)"
  (fn _ => [ (safe_tac (csp addSDs [ctxt_inst] addSEs [subs.elims])), 
    (datac subsetD 1 1), (ftac r0phD1 1),
    (datac (refl RSN (2, sctxt_lem)) 1 1), (safe_tac csp),
    (rtac UnI1 2), (rewtac ctxt1_def), (case_tac "s1" 2), 
    (EVERY [(etac red_mono' 2), Force_tac 2]),
    (case_tac "t0c" 1), (case_tac "ab : S" 1),
    (force_tac (cesimps [rule0_prop_def]) 2), 
    (rtac (UnI1 RS UnI2) 1), (rtac subs.I 1), Clarify_tac 1,
    (rtac cut0.I 1), atac 3, atac 2, 
    (etac ctxt_S_mono' 1), Fast_tac 1, 
    (simp_tac (esimps [subt_S_def]) 1),
    (rtac (UnI2 RS UnI2) 1), (Clarsimp_tac 1), (rtac r0ph_lem1 1),
    (simp_tac (esimps [r0ph_def]) 1), (etac conjI 1),
    (etac ctxt_S.elims 1), (etac oneup_S.elims 1), Force_tac 1,
    (clarsimp_tac (cesimps [r0ph_def]) 1) ]) ;
    
val _ = qed_goal_spec_mp "nured_subs" substc.thy 
  "r0s <= rule0_proph S --> sr <= subs r0s --> nured sr <= \
    \ ctxt (hds_notin S Int nured sr) Un subs (cut0 S r0s)"
  (fn _ => [ (rewtac nured_alt), (safe_tac (csp addSDs [ctxt_inst])), 
    (dtac oo_inst 1), (safe_tac csp), 
    (datac subsetD 1 1), (safe_tac (csp addSEs [subs.elims])), 
    (datac subsetD 1 1), (dtac r0phD1 1),

    (datac (refl RSN (2, sctxt_oo)) 1 1), (safe_tac csp),
    (rtac UnI1 2), (etac ctxt1D 2), (etac IntI 2), 
    (rtac ctxt.red_cutI 2), (etac oo_mono' 2), Fast_tac 2,

    (datac (refl RSN (2, sctxt_lem)) 1 1), (safe_tac csp),
    (rtac UnI1 2), (case_tac "s1" 2),
    (EVERY [(etac ctxt1D 2), (rtac IntI 2), Force_tac 2]),
    (etac ctxt1D 2), (etac oo_mono' 2), Fast_tac 2,

    (dtac ctxt_S_mono' 1), 
    (etac singleton_subsetI 1 THEN dtac (nured_S_alt1 RS subsetD) 1),
    (case_tac "t0ca" 1), (rtac UnI1 2),
    (fast_tac (ces [oneup_S.elims]) 2),
    (case_tac "ac : S" 1), (rtac UnI1 2),
    (fast_tac (ces [oneup_S.elims]) 2),

    (rtac UnI2 1), (rtac subs.I 1), Clarify_tac 1,
    (rtac cut0.I 1), atac 3, atac 2, 
    (simp_tac (esimps [subt_S_def]) 2),
    (eatac ([ctxt_S.nuI, singleton_subsetI] MRS ctxt_S_mono') 1 1) ]) ;

(* key theorems so far:
[subs0_nured, r0ph_sub, nured_subs] ;
*)

