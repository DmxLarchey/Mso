
structure base = struct val thy = theory "base" ;
  val ipt_mk_cases = InductivePackage.the_mk_cases thy ; end ;
use_legacy_bindings base.thy ;
fun u _ = use_thy "base" ; 

val oneup_mk_cases = base.ipt_mk_cases "base.oneup" ;
val oneupS_mk_cases = base.ipt_mk_cases "base.oneupS" ;
val isubt_mk_cases = base.ipt_mk_cases "base.isubt" ;

AddSEs [NilE, ConsE] ; 
AddSIs [symbs_in.I] ; 

val rtree_induct = tacsthm [ (eatac (conjI RS (Ball_set_Cons RS iffD2)) 1 3),
  Simp_tac 2] rtree.induct RS conjunct1 ;

val _ = qed_goal "maptrees_def" base.thy "maptrees f ts = map (maptree f) ts"
  (indAu "ts") ;

val _ = qed_goal_spec_mp "inj_maptree'" base.thy 
  "xxs = x # xs --> inj f --> (ALL y. maptree f x = maptree f y --> x = y) & \
    \ (ALL ys. maptrees f xs = maptrees f ys --> xs = ys)"
  (fn _ => [ (Clarify_tac 1), (induct_tac "x xs" 1), (ALLGOALS Clarsimp_tac),
    (case_tac "y" 1), (clarsimp_tac (ces [injD], esimps []) 1),
    (TRYALL (case_tac "ys")), Auto_tac]) ;

val _ = qed_goal_spec_mp "inj_maptree" base.thy 
  "inj f --> inj (maptree f)"  
  (fn _ => [ (fast_tac (ces (msc (refl RS inj_maptree')) addSIs [injI]) 1) ]) ; 
  
(** oneup **)
AddSIs [oneup.intros, oneupS.intros] ;
val oneup_elim = oneup_mk_cases "(Node a dtl1, Node b dtl2) : oneup r" ;
val oneupS_elim = oneupS_mk_cases "(Node a dtl1, Node b dtl2) : oneupS S r" ;
AddSEs [oneup_elim, oneupS_elim] ;

val _ = bind_thm ("oneup_iff", 
  tacsthm [(etac oneup.ouI 2), (etac oneup_elim 1), atac 1 ] iffI) ;

val _ = qed_goal_spec_mp "oneupS_mono" base.thy 
  "A <= B --> oneupS S A <= oneupS S B"
  (fn _ => [ (fast_tac (ces [oneupS.elims]) 1) ]) ; 

val _ = qed_goal_spec_mp "oneup_mono" base.thy "A <= B --> oneup A <= oneup B"
  (fn _ => [ (fast_tac (ces [oneup.elims]) 1) ]) ; 

val _ = qed_goal "oneup_Id" base.thy "oneup Id = Id"
  (fn _ => [ (auto_tac (ces [oneup.elims], esimps [])),
    (case_tac "b" 1), Auto_tac ]) ; 

val _ = qed_goal "oneup_empty" base.thy "oneup {} = {}"
  (fn _ => [ (fast_tac (ces [oneup.elims]) 1) ]) ; 
Addsimps [oneup_empty, oneup_Id] ;

val _ = qed_goal "oneup_comp" base.thy "oneup (r O s) = oneup r O oneup s"
  (fn _ => [ (fast_tac (ces [oneup.elims]) 1) ]) ; 

val _ = qed_goal "oneup_Un" base.thy "oneup (r Un s) = oneup r Un oneup s"
  (fn _ => [ (fast_tac (ces [oneup.elims]) 1) ]) ; 

val _ = bind_thm ("oo_mono", onerel_mono RS oneup_mono) ;
val [oo_mono', oneup_mono', oneupS_mono'] = 
  map mk_mono' [oo_mono, oneup_mono, oneupS_mono] ;

val oo_elims = [oneup.elims, onerelE1', onerelE2']; (* these are safe *)

val _ = qed_goal_spec_mp "oo_inst" base.thy 
  "(x, y) : oneup (onerel r) --> (EX z. z : r & (x, y) : oneup (onerel {z}))"
  (fn _ => [ (clarify_tac (ces [oneup.elims]) 1),
    (dtac onerel_inst 1), Auto_tac ]) ;

val _ = qed_goal "oneup_trancl" base.thy "oneup (r^+) = (oneup r)^+"
  (fn _ => [ (safe_tac (ces [oneup.elims])),
    (ALLGOALS (etac trancl_induct)),
    (rtac r_into_trancl 1), (etac trancl_into_trancl 2),
    (etac oneup_mono' 3), (REPEAT (etac oneup.elims 4)), Auto_tac ]) ; 

val _ = qed_goal "oneup_rtrancl" base.thy "oneup (r^*) = (oneup r)^*"
  (fn _ => [ (auto_tac (claset (), HOL_ss addsimps
      [reflcl_trancl RS sym, oneup_trancl, oneup_Un])), Auto_tac ]) ;

(** subt **)

val isubtE = isubt_mk_cases "(sdt, Node a sts) : isubt" ;
val isubtD = tacthm (atac 2) isubtE ;
val isubt_iff = tacsthm [etac isubtD 1, etac isubt.isubtI 1] iffI ;
AddSEs [isubtE] ;
Addsimps [isubt_iff] ;

val isubt_tranclE = tacthm (TRYALL (etac isubtE)) tranclE ;
val isubt_tranclI = isubt.isubtI RSN (2, rtrancl_into_trancl1) ;

val () = bind_thm ("subt_def'",
  rewrite_rule [psubt_def, mk_eq reflcl_trancl] subt_def) ;

fun mk_subt th = fold_rule [subt_def', psubt_def]
  (read_instantiate_sg (sign_of base.thy) [("r", "isubt")] th) ;

val _ = ListPair.app bind_thm 
  (["subt_refl", "p_iOs", "p_sOi", "isubt_psubt", "isubt_subt", "psubt_subt",
    "psubt_rtrancl"],
    map mk_subt [rtrancl_refl, O_rtc, rtc_O, r_into_trancl, r_into_rtrancl,
      trancl_into_rtrancl, rtrancl_trancl]) ; 

structure subt_thms = struct 
  val [ppp, sss, pip, ipp, sis, iss, spp, psp] = 
    map mk_subt (tl transitive_closure_trans) ;
  val [pps, pis, ips, sps, pss] = [ppp, pip, ipp, spp, psp] RL [psubt_subt] ; 
  val [ipp, iip, isp, iis] = [isubt_psubt] RL [ppp, pip, psp, pis] ;
  val sip = isubt_psubt RSN (2, spp) ;
  end ; (* structure subt_thms *) 

val () = qed_goal_spec_mp "sub1t_psubt" base.thy
  "((dt, dtl) : sub1t) = ((dt, Node a dtl) : psubt)"
  (fn _ => [ (auto_tac (cesimps [p_iOs RS sym, sub1t.defs])) ]) ;

val _ = bind_thm ("sub1tI1", consI1 RS sub1t.sub1tI) ;
val _ = bind_thm ("sub1tI2",
  tacthm (eatac (consI2 RS sub1t.sub1tI) 1 2) (mkpE sub1t.elims)) ;
AddSEs [sub1tI1, sub1tI2] ;

val _ = qed_goal "isubts_isubt" base.thy 
  "((x, y) : isubt) = (x : set (isubts y))"
  (fn _ => [ (case_tac "y" 1), Auto_tac]) ;

val _ = qed_goal_spec_mp "wfp_isubt'" base.thy 
  "dtdts = dt # dts --> dt : wfp isubt & set dts <= wfp isubt"
  (fn _ => [ Clarify_tac 1, (induct_tac "dt dts" 1),
    (rtac wfp.wfpI 1), Auto_tac]) ;
val wfp_isubt = refl RS wfp_isubt' RS conjunct1 ;

val wf_isubt = wfp_isubt RS wfp_wfI ;
val wf_psubt = fold_rule [psubt_def] (wf_isubt RS wf_trancl) ;
val wf_psubt' = wf_psubt RS (wf_def RS defD1) RS spec RS mp RS spec ; 
val wfp_psubt = wf_psubt RS wf_ssI ;

AddSIs [isubt.isubtI] ;
AddSEs [isubt_psubt, isubt_subt, psubt_subt] ; 
AddIffs [subt_refl, wf_isubt, wf_psubt, wfp_psubt, wfp_isubt] ;
Addsimps [isubts_isubt RS sym] ; 

val _ = qed_goal "isubts_iff" base.thy 
  "set (isubts y) = {x. (x, y) : isubt}" fn_at ;

(** depth **)
val _ = qed_goal_spec_mp "depths_in" base.thy 
  "dts : set sts --> depth dts <= depths sts" (indAu "sts") ;

val _ = qed_goalw_spec_mp "psubt_depth" base.thy [psubt_def]
  "(dts, dt) : psubt --> depth dts < depth dt"
  (fn _ => [ (rtac impI 1), (etac trancl_induct 1),
    (safe_tac (ces [isubt.elims])),
    (auto_tac (cds [depths_in], simpset ())) ]) ;

val _ = qed_goal "depth_treel" base.thy 
  "depth (tree xs t) = (length xs + depth t)" (indAu "xs") ;

val _ = qed_goal "depths_trees" base.thy 
  "depths (trees xs) = (length xs)" (indAu "xs") ;

(* useful tactics *)

(* disjs_tac : tactic -> int -> tactic
  select disjunct of subgoal i and apply tactic 
  (which may affect other subgoals)  *)
fun disjs_tac tac i st = FIRST [rtac disjI1 i THEN disjs_tac tac i,
  rtac disjI2 i THEN disjs_tac tac i, tac] st ;

(* istc_tac, isrtc_tac : int -> tactic 
  handle subgoals (x, y) : isubt^+ or (x, y) : isubt^* respectively *)
fun istc_tac i st = (atac i ORELSE EVERY [(rtac isubt_tranclI i), 
  (safe_asm_full_simp_tac (init_ss) (i+1)), 
  (disjs_tac (rtac refl (i+1) THEN isrtc_tac i) (i+1))]) st 

and isrtc_tac i st = ((rtac rtrancl_refl i) ORELSE EVERY
  [(rtac trancl_into_rtrancl i), istc_tac i]) st ; 
  
val trancl_isubtE = tacthm (etac isubtE 3) tranclE ;
val trancl_isubtI = isubt.isubtI RSN (2, trancl_into_trancl) ;
val consIs = [consI1, consI1 RS consI2, consI1 RS consI2 RS consI2] ;
val tic1s as tic1 :: _ = consIs RL [isubt.isubtI RS r_into_trancl] ;
val tic2s as tic2 :: _ = (consIs RLN (2, [trancl_isubtI])) ;
val tic3 = tacsthm [(dtac consI2 3), (eatac trancl_isubtI 1 3),
  (rtac r_into_trancl 2), (clarsimp_tac (cesimps [isubt.defs]) 2)]
  trancl_isubtE ;

(* tranclI_tac : int -> tactic
  an alternative tactic to handle goals x : isubt^+
  seems faster but less powerful than istc_tac *)
  
fun tranclI_tac sg st = (ares_tac [tic1] ORELSE' 
  (resolve_tac [tic2, tic3] THEN' tranclI_tac)) sg st ;
  
(* characterizations of sn_set *)

(*
val () = qed_goal "sn1upn" redn.thy 
  "(Node a dtl : wfp (oneup r)) = (dtl : wfp r)"
  (fn _ => [rtac iffI 1, 
    (dres_inst_tac [("P", "%t. (isubts t) : wfp r")] wfp.induct 1),
    (case_tac "dt" 1), (ALLGOALS Asm_full_simp_tac), 
    Safe_tac, (rtac wfp.wfpI 1), (strip_tac 1),
    (etac allE 1), (etac impE 1), 
    (etac oneup.ouI 1), Asm_full_simp_tac 1,
    (etac wfp.induct 1), (rtac wfp.wfpI 1), (strip_tac 1),
    (etac oneup.elims 1), Force_tac 1 ]) ;
*)

val () = qed_goal_spec_mp "wfp_oneup1" base.thy 
  "(dt : wfp (oneup r)) --> (isubts dt : wfp r)"
  (fn _ => [ (rtac impI 1), (etac wfp_wk_induct 1),
    (case_tac "dt" 1), (rtac wfp.wfpI 1), (Auto_tac) ]) ;  

val () = qed_goal_spec_mp "wfp_oneup2" base.thy 
  "(dtl : wfp r) --> (Node a dtl : wfp (oneup r))"
  (fn _ => [ (rtac impI 1), (etac wfp_wk_induct 1),
    (rtac wfp.wfpI 1), (Clarsimp_tac 1), (etac oneup.elims 1), Auto_tac ]) ;  

val () = qed_goal "wfp_oneup" base.thy
  "(dt : wfp (oneup r)) = (isubts dt : wfp r)"
  (fn _ => [ (safe_tac (ces [wfp_oneup1])),
    (case_tac "dt" 1), (auto_tac (ces [wfp_oneup2], esimps [])) ]) ;

val () = qed_goal "sn1upn" base.thy 
  "(Node a dtl : wfp (oneup r)) = (dtl : wfp r)"
  (fn _ => [ (simp_tac (esimps [wfp_oneup]) 1) ]) ;

val () = qed_goalw "wf1up" base.thy [mk_eq wf_wfp] "wf (oneup r) = wf r" 
  (fn _ => [ Safe_tac, (TRYALL (rtac UNIV_I)),
    (case_tac "x" 2), (force_tac (cesimps [sn1upn]) 2),
    (rtac (sn1upn RS iffD1) 1), Force_tac 1]) ;

val snUpn = sn1upn RS iffD1 ;
    
val _ = qed_goalw_spec_mp "wfp_isubt_subt" base.thy [subt_def']
  "wfp (subt O r) = wfp (r Un isubt)"
  (fn _ => [ (simp_tac (esimps [Un_commute,
    wf_isubt RS wf_comp_Unl']) 1) ]) ;

val _ = qed_goalw_spec_mp "wfp_psubt_subt" base.thy 
  [mk_eq (psubt_rtrancl RS sym)]
  "wfp (subt O r) = wfp (r Un psubt)"
  (fn _ => [ (simp_tac (esimps [Un_commute,
    wf_psubt RS wf_comp_Unl']) 1) ]) ;

val _ = qed_goalw_spec_mp "wf_isubt_subt" base.thy [subt_def']
  "wf (r O subt) = wf (r Un isubt)"
  (fn _ => [ (simp_tac (esimps [Un_commute,
    wf_isubt RS wf_comp_Unr]) 1) ]) ;

val _ = qed_goalw_spec_mp "wf_psubt_subt" base.thy 
  [mk_eq (psubt_rtrancl RS sym)]
  "wf (r O subt) = wf (r Un psubt)"
  (fn _ => [ (simp_tac (esimps [Un_commute,
    wf_psubt RS wf_comp_Unr]) 1) ]) ;

