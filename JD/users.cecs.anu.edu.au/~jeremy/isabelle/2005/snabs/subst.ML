
structure subst = struct val thy = theory "subst" ;
  val ipt_mk_cases = InductivePackage.the_mk_cases thy ; end ;
use_legacy_bindings subst.thy ;
fun u _ = use_thy "subst" ; 

AddIffs [singletonI RS ctxt.red_cutI] ; (* could go to clcon.ML *)
val hds_notinE =
  subst.ipt_mk_cases "subst.hds_notin" "(t, Node a ss) : hds_notin S" ;
val hds_notinD = tacthm (atac 2) hds_notinE ;
val hds_notin_eq = tacsthm [etac hds_notin.I 2, etac hds_notinD 1] iffI ;
AddSIs [hds_notin.I] ; 
AddSEs [hds_notinE] ; 
Addsimps [hds_notin_eq] ; 

val stree_induct = tacsthm [ (eatac (conjI RS (Ball_set_Cons RS iffD2)) 1 4),
  Simp_tac 3] stree.induct RS conjunct1 ;

val rule0_prophE = tacsthm
  [chop_tac 1 (etac rule0_prop.elims 2), Safe_tac] rule0_proph.elims ;

val rule0_prop_def = rewrite_rule [lfp_const] rule0_prop.defs ;
val rule0_proph_def = rewrite_rule [lfp_const] rule0_proph.defs ;
val rule0_hd_S_def = rewrite_rule [lfp_const] rule0_hd_S.defs ;

val _ = qed_goalw "r0ph_def" subst.thy 
  [rule0_proph_def, rule0_prop_def, rule0_hd_S_def]
  "rule0_proph S = rule0_prop S Int rule0_hd_S S" fn_at ;
  
val r0ph_def' = [r0ph_def RS set_cong, Int_iff] MRS trans ;

val r0phDs as [r0phD1, r0phD2] = ([r0ph_def' RS iffD1] RL conjuncts) ;
AddSEs r0phDs ;

(** newvars **)
val _ = qed_goal_spec_mp "length_newvars" subst.thy 
  "ALL l. length (newvars l n) = n" (indAu "n") ;
Addsimps [length_newvars] ;

val _ = qed_goal_spec_mp "nv_larger" subst.thy "x : set l --> x <= (maxl l)"
  (fn _ => [ (induct_tac "l" 1), (auto_tac (cesimps [le_max_iff_disj])) ]) ;
  
val _ = qed_goalw "nv_notin" subst.thy [newvar_def] "newvar l ~: set l"
  (fn _ => [ (auto_tac (cds [nv_larger], esimps [])) ]) ;
AddIffs [nv_notin] ;
   
val [distinct_Nil, distinct_Cons] = thms "distinct.simps" ;

val distinct_nv = nv_notin RS conjI RS (distinct_Cons RS iffD2) ;

val _ = qed_goal_spec_mp "newvars_disjoint" subst.thy 
  "ALL xs. set xs Int set (newvars xs n) = {}" 
  (fn _ => [ (induct_tac "n" 1), (ALLGOALS Clarsimp_tac), 
    (eres_inst_tac [("x", "newvar xs # xs")] allE 1), Auto_tac ]) ;
Addsimps [newvars_disjoint] ;

val _ = qed_goal_spec_mp "notin_newvars" subst.thy 
  "x : set xs --> x ~: set (newvars xs n)" 
  (fn _ => [ Clarify_tac 1, (datac IntI 1 1), Clarsimp_tac 1 ]) ;

val _ = qed_goal_spec_mp "newvars_distinct" subst.thy 
  "ALL l. distinct (newvars l n)" 
  (fn _ => [ (induct_tac "n" 1), (ALLGOALS Clarsimp_tac), 
    (full_simp_tac (esimps [notin_newvars]) 1) ]) ;
AddIffs [newvars_distinct] ;

val () = bind_thm ("subt_S_def'",
  rewrite_rule [psubt_S_def, mk_eq reflcl_trancl] subt_S_def) ;

fun mk_subt_S th = fold_rule [subt_S_def', psubt_S_def]
  (read_instantiate_sg (sign_of subst.thy) [("r", "isubt_S ?S")] th) ;

structure subt_S_thms = struct 
  val [subt_S_refl, p_iOs, p_sOi, isubt_S_psubt_S, isubt_S_subt_S,
      psubt_S_subt_S, psubt_S_rtrancl] = 
    map mk_subt_S [rtrancl_refl, O_rtc, rtc_O, r_into_trancl, r_into_rtrancl,
      trancl_into_rtrancl, rtrancl_trancl] ; 
  val [ppp, sss, pip, ipp, sis, iss, spp, psp] = 
    map mk_subt_S (tl transitive_closure_trans) ;
  val [pps, pis, ips, sps, pss] = 
    [ppp, pip, ipp, spp, psp] RL [psubt_S_subt_S] ; 
  val [ipp, iip, isp, iis] = [isubt_S_psubt_S] RL [ppp, pip, psp, pis] ;
  val sip = isubt_S_psubt_S RSN (2, spp) ;
  end ; (* structure subt_S_thms *) 

val _ = qed_goal "substs_map" subst.thy 
  "substs f ss = map (subst f) ss" (indAu "ss") ;

val _ = qed_goal "substs_map_SVar" subst.thy 
  "substs f (map SVar ns) = map f ns" (indAu "ns") ;

val _ = qed_goal "s_ss_of_map_SVar" subst.thy 
  "s_ss_of (map SVar ns) = []" (indAu "ns") ;
Addsimps [s_ss_of_map_SVar] ;

val _ = qed_goalw_spec_mp "isubt_S_mono" subst.thy [isubt_S.defs]
  "A <= B --> isubt_S A <= isubt_S B" fn_at ;
 
val _ = bind_thm ("subt_S_mono", 
   fold_rule [subt_S_def'] (isubt_S_mono RS rtrancl_mono)) ;

val _ = qed_goal_spec_mp "subst_isubt_S" subst.thy 
  "(t, s) : isubt_S S --> (subst f t, subst f s) : isubt"
  (fn _ => [ (auto_tac (ces [isubt_S.elims], esimps [substs_map])) ]) ;

val _ = qed_goalw_spec_mp "subst_subt_S" subst.thy [subt_S_def', subt_def']
  "(t, s) : subt_S S --> (subst f t, subst f s) : subt"
  (fn _ => [ (rtac impI 1), (etac rtrancl_induct 1), Fast_tac 1,
    (etac (nth (transitive_closure_trans, 5)) 1), (etac subst_isubt_S 1) ]) ;

val _= qed_goal "nslem'" subst.thy 
  "(n ~: set (vars_of s) --> subst (f(n := t)) s = subst f s) & \
    \ (n ~: set (varss_of ss) --> substs (f(n := t)) ss = substs f ss)"
  (indAu "s ss") ;
  
val nslems as [nslem, nsleml] = msc nslem' ;

val _ = qed_goalw_spec_mp "var_sub'" subst.thy []
  "X = s # ss --> (n : set (vars_of s) --> (f n, subst f s) : subt) & \
    \ (n : set (varss_of ss) --> (f n, substs f ss) : sub1t)"
  (fn _ => [ Clarify_tac 1, (induct_tac "s ss" 1), ALLGOALS Simp_tac,
    Safe_tac, (rtac psubt_subt 1), (etac (sub1t_psubt RS iffD1) 1) ]) ;
    
val var_subs as [var_sub, var_subl] = msc (refl RS var_sub') ;

val _ = qed_goal_spec_mp "subst_same'" subst.thy
  "((ALL n : set (vars_of s). f n = g n) --> subst f s = subst g s) & \
    \ ((ALL n : set (varss_of ss). f n = g n) --> substs f ss = substs g ss)"
  (indAu "s ss") ;

val _ = qed_goal_spec_mp "subst_same'" subst.thy
  "((subst f s = subst g s) = (ALL n : set (vars_of s). f n = g n)) & \
    \ ((substs f ss = substs g ss) = (ALL n : set (varss_of ss). f n = g n))"
  (indAu "s ss") ;

val subst_sames as [subst_same, subst_samel] = msc subst_same' ;

val _ = qed_goal_spec_mp "varss_of_map" subst.thy
  "varss_of (map SVar xs) = xs" (indAu "xs") ;
Addsimps [varss_of_map] ;

val _ = qed_goal_spec_mp "ex_subst'" subst.thy
  "(EX f. subst f s = t) --> (EX g. substs g ss = ts) --> \
    \ set (vars_of s) Int set (varss_of ss) = {} --> \
    \ (EX h. substs h (s # ss) = t # ts)"
  (fn _ => [ (Clarify_tac 1), 
    (res_inst_tac [("x", 
      "%n. if n : set (vars_of s) then f n else g n")] exI 1),
    (force_tac (cesimps subst_sames) 1) ]) ;

(** oneup_S **)
val oneup_S_mk_cases = subst.ipt_mk_cases "subst.oneup_S" ;
AddSIs [oneup_S.intros] ;
val oneup_S_elim = oneup_S_mk_cases 
  "(SNode a dtl1, SNode b dtl2) : oneup_S S r" ;
AddSEs [oneup_S_elim] ;

val _ = qed_goal_spec_mp "oneup_S_mono" subst.thy
  "A <= B --> oneup_S S A <= oneup_S S B"
  (fn _ => [ (fast_tac (ces [oneup_S.elims]) 1) ]) ; 

val _ = bind_thm ("oo_S_mono", onerel_mono RS oneup_S_mono) ;
val [oo_S_mono', oneup_S_mono'] = map mk_mono' [oo_S_mono, oneup_S_mono] ;

val _ = qed_goal_spec_mp "oo_S_inst" subst.thy 
  "(x, y) : oneup_S S (onerel r) --> \
    \ (EX z. z : r & (x, y) : oneup_S S (onerel {z}))"
  (fn _ => [ (clarify_tac (ces [oneup_S.elims]) 1),
    (dtac onerel_inst 1), Auto_tac ]) ;

val _ = qed_goal "v1lem'" subst.thy 
  "(n : set (vars_of s) & n ~: duplicates (vars_of s) --> \
    \ (subst (f(n := t)) s, subst f s) : ctxt {(t, f n)}) & \
    \ (n : set (varss_of ss) & n ~: duplicates (varss_of ss) --> \
    \ (substs (f(n := t)) ss, substs f ss) : onerel (ctxt {(t, f n)}))"
  (fn _ => [ (induct_tac "s ss" 1), (ALLGOALS Clarsimp_tac), (etac disjE 1),
    (ALLGOALS (clarsimp_tac (cesimps [duplicates_append]))),
    (ALLGOALS (resolve_tac [onerelI1_eq, onerelI2_eq] THEN' (atac o incr))),
    (ALLGOALS (dresolve_tac nslems)), (auto_tac (cesimps [fun_upd_def])) ]) ;

val v1lems as [v1lem, v1leml] = [conjI] RL msc v1lem' ;

(* doubt if we want this
val _ = qed_goal "v1lemtc'" subst.thy 
  "(n : set (vars_of s) --> \
    \ (subst (f(n := t)) s, subst f s) : (ctxt {(t, f n)})^+) & \
    \ (n : set (varss_of ss) --> \
    \ (substs (f(n := t)) ss, substs f ss) : (onerel (ctxt {(t, f n)}))^+)"
  (fn _ => [ (induct_tac "s ss" 1), (ALLGOALS Clarsimp_tac),
    (rtac (singletonI RS ctxt.red_cutI RS r_into_trancl 2),
    (dtac oneup.ouI 1), (dtac (oneup_trancl RS equalityD1') 1),
    (etac trancl_mono 1), Fast_tac 1, Safe_tac, ]) ;
    *)

val _ = qed_goal "v1lemg'" subst.thy 
  "(subst (f(n := t)) s, subst f s) : (ctxt {(t, f n)})^* & \
    \ (substs (f(n := t)) ss, substs f ss) : (onerel (ctxt {(t, f n)}))^*"
  (fn _ => [ (induct_tac "s ss" 1), (ALLGOALS Clarsimp_tac),
    (rtac (singletonI RS ctxt.red_cutI RS r_into_rtrancl) 2),
    (dtac oneup.ouI 1), (dtac (oneup_rtrancl RS equalityD1') 1),
    (etac rtrancl_mono' 1), Fast_tac 1, (rtac rtrancl_trans 1),
    (etac onerelI2_rtc 1), (etac onerelI1_rtc 1)]) ;

val v1lemgs as [v1lemg, v1lemgl] = msc v1lemg' ;

val _ = qed_goal_spec_mp "sinvlem'" subst.thy 
  "symb_of s ~: S --> s ~= t --> \
    \ (set (s_symbols_of tb) <= S --> \
    \ (subst (f(n := tr)) tb, subst f tb) : ctxt1 (t, s) --> \
    \ (tr, f n) : ctxt1 (t, s)) & \
    \ (set (s_ss_of tbs) <= S --> \
    \ (substs (f(n := tr)) tbs, substs f tbs) : onerel (ctxt1 (t, s)) --> \
    \ (tr, f n) : ctxt1 (t, s))"
  (fn _ => [ (strip_tac 1), (induct_tac "tb tbs" 1),
    (Conv.CONV_TAC (SOME o eta_conversion)), 
    (ALLGOALS Clarsimp_tac), (fast_tac (cds [ctxt_IdI]) 2),
    (rewtac ctxt1_def), (etac onerelE 2), (etac ctxt.elims 1), Auto_tac ]) ;

val sinvlems as [sinvlem, sinvleml] = msc sinvlem' ;

val _ = qed_goalw_spec_mp "rewr_in_var'" subst.thy [ctxt1_def]
  "symb_of s ~: S --> (c, b) : ctxt1 (t, s) --> \
    \ (ALL tb. b = subst f tb --> distinct (vars_of tb) --> \
    \ set (s_symbols_of tb) <= S --> \
    \ (EX nat tr. nat : set (vars_of tb) & c = subst (f (nat := tr)) tb))"
  
  (fn _ => [ (rtac impI 1), (rtac impI 1), 
    (etac ctxt.induct 1), Clarify_tac 2,
    (case_tac "tb" 2), Force_tac 2, Force_tac 2, 

    Safe_tac, (case_tac "tb" 1), Force_tac 2,
    (dtac oo_inst 1), (Conv.CONV_TAC (SOME o eta_conversion)), 
    Clarsimp_tac 1, (etac oneup.elims 1), Clarsimp_tac 1,

    (chop_tac 1 (etac rev_mp 1)),
    (chop_tac 2 (etac rev_mp 1)),
    (chop_tac 4 (etac rev_mp 1)),
    (res_inst_tac [("x", "dtl1")] spec 1),
    (induct_tac "list" 1), Force_tac 1, 
    (Conv.CONV_TAC (SOME o eta_conversion)),
    Clarsimp_tac 1, (etac onerel.elim 1),
    Clarsimp_tac 2, (etac allE 2 THEN mp_tac 2),
    (force_tac (ces [ex_forward] addSIs (nslems RL [sym]) delrules [exE],
      esimps []) 2),

    Clarsimp_tac 1, (EVERY [etac allE 1, etac impE 1, rtac refl 1]),
    (force_tac (ces [ex_forward] addSIs (nslems RL [sym]) delrules [exE],
      esimps []) 1) ]) ;

val rewr_in_var = refl RSN (3, rewr_in_var') ;

(* apply rule (tb, sb) in R0 (substituted), taking a to b,
  then ctxt (rule (t, s)), rule (t, s) in R1, taking b to c *)

val _ = qed_goal_spec_mp "hier_lem'" subst.thy 
  "a = subst f sb --> symb_of s ~: S --> (c, b) : ctxt1 (t, s) --> \
    \ (ALL tb. b = subst f tb --> distinct (vars_of tb) --> \
    \ set (vars_of tb) <= set (vars_of sb) --> \
    \ set (s_symbols_of tb) <= S --> \
    \ (EX f'. (subst f' sb, a) : (ctxt1 (t, s))^* & \
      \ (c = subst f' tb)))"
  (fn _ => [ Safe_tac, (case_tac "s = t" 1), 
    (force_tac (cds [ctxt_IdE], esimps [ctxt1_def]) 1),
    (fatac rewr_in_var 3 1), Safe_tac, 
    (rtac exI 1), (rtac conjI 1), (rtac refl 2),
    (fatac sinvlem 3 1), 
    (rtac (rtrancl_mono RS (v1lemg RS rev_subsetD)) 1),
    (rewtac ctxt1_def), (rtac ctxt_clos 1), Fast_tac 1 ]) ;

val hier_lem'' = tacthm (TRYALL (rtac refl)) hier_lem' ;

val _ = qed_goalw_spec_mp "hier_lem" subst.thy [rule0_prop_def]
  "(tb, sb) : rule0_prop S --> symb_of s ~: S --> \
    \ (c, subst f tb) : ctxt1 (t, s) --> (EX f'. \
      \ (subst f' sb, subst f sb) : (ctxt1 (t, s))^* & (c = subst f' tb))"
  (fn _ => [ (clarsimp_tac (init_css) 1), (etac hier_lem'' 1), Auto_tac ]) ;

val _ = qed_goal_spec_mp "nured_hlem" clcon.thy 
  "(x, y) : (ctxt1 (t, s))^* --> symb_of y ~= symb_of s --> \
    \ (x, y) : (nured {(t, s)})^*"
  (fn _ => [ (rtac impI 1), (etac rtrancl_induct 1), Simp_tac 1,
    (rewtac ctxt1_def), (etac ctxt.elims 1), Force_tac 2,
    (etac oneup.elims 1), Clarsimp_tac 1, 
    (etac (nth (transitive_closure_trans, 5)) 1), 
    (rewtac nured_def), (etac oneup.ouI 1) ]) ;
    
val _ = qed_goalw_spec_mp "hier_lemh" subst.thy [rule0_proph_def]
  "(tb, sb) : rule0_proph S --> symb_of s ~: S --> \
    \ (c, subst f tb) : ctxt1 (t, s) --> (EX f'. \
      \ (subst f' sb, subst f sb) : (nured {(t, s)})^* & (c = subst f' tb))"
  (fn _ => [ (clarsimp_tac (init_css) 1), (datac hier_lem 2 1),
    (etac ex_forward 1), Auto_tac, (etac nured_hlem 1), Force_tac 1 ]) ;

val _ = qed_goal_spec_mp "r0p_isubt" subst.thy 
  "(SNode a ts, s) : rule0_prop S --> t : set ts --> (t, s) : rule0_prop S"
  (fn _ => [ (induct_tac "ts" 1), (auto_tac (cesimps [rule0_prop_def])) ]) ;

val _ = qed_goalw_spec_mp "r0ph_isubt" subst.thy [rule0_proph_def]
  "(SNode a ts, s) : rule0_proph S --> t : set ts --> (t, s) : rule0_proph S"
  (fn _ => [ Safe_tac, (datac r0p_isubt 1 1), Fast_tac 1 ]) ;

val _ = qed_goalw_spec_mp "r0p_subt" subst.thy [subt_S_def']
  "(t', t) : subt_S S' --> (t, s) : rule0_prop S --> (t', s) : rule0_prop S"
  (fn _ => [ (rtac impI 1), (etac rtrancl_induct 1), 
    (safe_tac (ces [isubt_S.elims])),
    (datac r0p_isubt 1 1), contr_tac 1 ]) ;

val _ = qed_goalw_spec_mp "r0ph_subt" subst.thy [rule0_proph_def]
  "(t', t) : subt_S S' --> (t, s) : rule0_proph S --> (t', s) : rule0_proph S"
  (fn _ => [ Safe_tac, (datac r0p_subt 1 1), Fast_tac 1 ]) ;

val _ = qed_goal_spec_mp "r0ph_lem1" subst.thy 
  "(SVar n, s) : rule0_proph S --> (f n, subst f s) : psubt"
  (fn _ => [ (clarsimp_tac (ces [rule0_prophE, var_subl], 
      esimps [sub1t_psubt RS sym]) 1) ]) ; 

val _ = qed_goalw_spec_mp "r0ph_sub" subst.thy [subt_def']
  "(t0, s0) : rule0_proph S --> s = subst f s0 --> (t', t) : subt --> \
    \ (t = subst f t0 --> \
    \ (t', s) : psubt | (EX t0'. (t0', t0) : subt_S S & \
      \ is_SNode t0' & t' = subst f t0' & (t0', s0) : rule0_proph S))"
  (fn _ => [ (rtac impI 1), (rtac impI 1), (rtac impI 1), 
    (etac converse_rtrancl_induct 1), (case_tac "t0" 1),
    (Clarsimp_tac 2), (etac r0ph_lem1 2),
    (strip_tac 1), (rtac disjI2 1), (rtac exI 1), 
    (SELECT_GOAL ((REPEAT_FIRST (ares_tac [conjI])) THEN
      (auto_tac (cesimps [subt_S_def]))) 1),
    Safe_tac, (eatac subt_thms.ipp 1 1), 
    (case_tac "t0'" 1), Force_tac 2,
    (clarsimp_tac (cesimps [substs_map, in_map]) 1),
    (datac r0ph_isubt 1 1), (etac allE 1), (etac impE 1),
    (rtac refl 1), (subgoal_tac "a : S" 1),
    (datac isubt_S.I 1 1), (datac subt_S_thms.iss 1 1),
    (case_tac "x" 1), Clarsimp_tac 1, Clarsimp_tac 1,
    (etac r0ph_lem1 1), (datac r0ph_subt 1 1), 
    (auto_tac (ces [rule0_prophE], esimps [])) ]) ;
    
val r0ph_sub' = tacthm (TRYALL (rtac refl)) r0ph_sub ;


