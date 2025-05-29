

structure clcon = struct val thy = the_context () end ;
val _ = use_legacy_bindings clcon.thy ;

structure sn1order = struct (* imitating old definitions *)
val sn1I = prove_goalw clcon.thy [sn1order_def] "?P --> ?x : sn1order r"
  (fn _ => [ (rtac impI 1), (etac oneup.ouI 1)]) RS mp ;
val intrs = [sn1I] ;
end ;

val sn1order_def' = rewrite_rule [sn1red_def] sn1order_def ;
val sn2order_def' = rewrite_rule [sn2red_def] sn2order_def ;

val _ = bind_thm ("sn2order_defn",
  [sn2order_def', symmetric nured_def] MRS transitive_thm) ;

val [sn1order_eq, sn2order_eq] = store_thms ("snxorder_eqs",
  map zero_var_indexes ([sn1order_def, sn2order_def] RL 
  [[def_imp_eq RS set_cong, oneup_iff] MRS trans])) ;

val _ = ListPair.app bind_thm (["nuredE", "sn2orderE"], 
  [nured_def, sn2order_def] RL [def_imp_eq RS equalityD1' RS oneup.elims]) ;

val wfpc_def = [wfpc.defs, lfp_const] MRS transitive_thm ;

fun mksns wfpth = zero_var_indexes 
  (read_instantiate_sg clcon.thy [("r", "ctxt ?s")] wfpth) ;

val [snwf, _, sn_red] = map mksns [snwfp, wfpRed, wfp_red] ;

val _ = bind_thm ("sn_red", sn_red) ;

val _ = bind_thm ("constrict_iff", 
  simplify (esimps []) (constrict_def RS def_imp_eq RS set_cong_pair)) ;

(** ctxt **)

structure ron = struct
open ctxt ;
fun frn rl = fold_rule [nured_def] rl ;
val red_nuI' = frn red_nuI ;
val elim = elims ;
val intrs = intros ;
val elim' = frn elims ;
val mk_cases = InductivePackage.the_mk_cases clcon.thy "clcon.ctxt" ;
val E = mk_cases "(a, b) : ctxt r" ;
val E' = frn E ;
end ;

open ron ;
val ro_intr = oneup.ouI RS red_nuI ;
val ro_elim = tacthm (etac oneup.elims 2 THEN Safe_tac) ron.elims ;
val ro_elim' = tacthm (etac oneup_elim 2) ron.E ;
AddSEs [ro_intr, red_cutI, red_nuI] ;
val sn1_defs = [sn1red_def, sn1order_def] ;
val sn1Ds = sn1_defs RL [set_defD1] ;
val sn1Is = sn1_defs RL [set_defD2] ;
val sn1_cs = (ces oo_elims addSIs sn1Is addSDs sn1Ds) ;

val sn_red' = ron.red_cutI RS r_into_rtrancl RS sn_red ;

structure redn = clcon ; (* TEMPORARY *)
val _ = qed_goal_spec_mp "ro_intr_tc" redn.thy
  "(l1, l2) : (onerel (ctxt r))^+ --> \
    \ (Node a l1, Node a l2) : (ctxt r)^+"
  (fn _ => [ (rtac impI 1), (etac trancl_induct 1), 
    (etac trancl_into_trancl 2), Auto_tac]) ;

val _ = qed_goalw_spec_mp "ro_intr_rtc" redn.thy [mk_eq (reflcl_trancl RS sym)]
  "(l1, l2) : (onerel (ctxt r))^* --> \
    \ (Node a l1, Node a l2) : (ctxt r)^*"
  (fn _ => [ (fast_tac (cds [ro_intr_tc]) 1) ]) ;

val () = qed_goalw "red_cases'" redn.thy [nured_def]
  "ctxt r = (nured r Un r)"
  (fn _ => [(safe_tac (ces [ron.elims])) ]) ;

val () = qed_goal "red_cases" redn.thy 
  "(dtr, dt) : ctxt r = ((dtr, dt) : nured r | (dtr, dt) : r)"
  (fn _ => [ (simp_tac (esimps [red_cases']) 1) ]) ;

val _ = bind_thm ("red_nured", disjI1 RS (red_cases RS iffD2)) ;
val _ = bind_thm ("red_nured_sub", mk_mono red_nured) ;
val () = qed_goal "r_into_red" redn.thy "r <= ctxt r" fn_at ;
AddIffs [red_nured_sub, r_into_red] ; AddSEs[red_nured] ;

val () = qed_goal_spec_mp "nured_alt_lem" redn.thy "(a, b) : ctxt r --> \
    \ (ALL x : oneup (onerel {(a, b)}). x : ctxt (oneup (onerel r)))"
  (fn _ => [ (rtac impI 1), (etac ctxt.induct 1), Safe_tac, 
    (rtac ctxt.red_cutI 2), (etac oo_mono' 2), Fast_tac 2,
    (dtac oo_mono' 1), (rtac Int_lower2 1),
    (chop_tac 1 (dtac oo_inst 1)), Safe_tac, 
    (datac bspec 1 1), (rtac ctxt.red_nuI 1), 
    (etac oo_mono' 1), Fast_tac 1 ]) ;

val () = qed_goalw "nured_alt" redn.thy [nured_def, meta_eq_def]
  "nured r == ctxt (oneup (onerel r))"
  (fn _ => [ Safe_tac,
    (etac ctxt.induct 2), (etac oo_mono' 3), (rtac r_into_red 3),
    (etac oo_mono' 2), Fast_tac 2,
    (dtac oo_inst 1), Safe_tac, (eatac nured_alt_lem 1 1) ]) ;

val rtacs = [ Safe_tac, (etac ron.induct 1), 
  (fast_tac (cis [ron.red_cutI]) 2), 
  (etac oneup.elims 1), Safe_tac, (etac onerel.induct 1),
  (ALLGOALS (rtac ron.red_nuI)), Auto_tac,
  (etac rev_subsetD 1), (rtac onerel_mono 1), Auto_tac] ;

val () = qed_goal_spec_mp "red_mono" redn.thy 
  "r <= s --> (ctxt r <= ctxt s)" (fn _ => rtacs) ;

val red_mono' = mk_mono' red_mono ;

val () = qed_goal "red_idemp" redn.thy 
  "ctxt (ctxt r) = ctxt r" (fn _ => rtacs) ;

val () = bind_thm ("ctxt_clos",  
  [red_mono, red_idemp RS order_eq_refl] MRS order_trans) ;

val _ = bind_thm ("ctxt1D", 
  [ctxt1_def RS def_imp_eq RS equalityD1', singleton_subsetI] MRS red_mono') ;

val _ = qed_goalw "ctxt_Un1" clcon.thy [ctxt1_def] "ctxt r = (UN p:r. ctxt1 p)"
  (fn _ => [ Safe_tac, 
    (etac ctxt.induct 1), (fast_tac (cis [ron.red_cutI]) 2),
    (dtac oo_inst 1), Safe_tac, (etac UN_I 1),
    (etac (oo_mono' RS ctxt.red_nuI) 1), 
    (etac red_mono' 2), Auto_tac ]) ;

val _ = qed_goalw "nured_Un1" clcon.thy [nured1_def, nured_def] 
  "nured r = (UN p:r. nured1 p)"
  (fn _ => [ Safe_tac, (etac oo_mono' 2), (rtac red_mono 2),
    Fast_tac 2, (dtac oo_inst 1), 
    (auto_tac (ces [oo_mono'], esimps [ctxt_Un1])) ]) ;

val _ = ListPair.app bind_thm (["nured_inst", "ctxt_inst"], 
  map (simplify (esimps [])) ([nured_Un1, ctxt_Un1] RL [equalityD1'])) ;

fun mk1 th = fold_rule [ctxt1_def, nured1_def] 
  (read_instantiate [("r", "{?p}")] th) ;

val _ = ListPair.app bind_thm (["ctxt1_nured1", "nured1_def'"], 
  map mk1 [red_nured, nured_def]) ;

val _ = qed_goal "red_Un" redn.thy
  "ctxt (r Un s) = ctxt r Un ctxt s"
  (fn _ => [ (force_tac (cesimps [ctxt_Un1]) 1) ]) ;

val _ = qed_goal "nured_Un" redn.thy
  "nured (r Un s) = nured r Un nured s"
  (fn _ => [ (force_tac (cesimps [nured_Un1]) 1) ]) ;

(*
val _ = qed_goal "red_Un" redn.thy
  "ctxt (r Un s) = ctxt r Un ctxt s"
  (fn _ => [ (safe_tac csp), (TRYALL (etac red_mono')),
    (etac ron.induct 1), (fast_tac (cis [ron.red_cutI]) 2),
    (safe_tac (ces oo_elims addSIs [ron.red_nuI])),
    (full_simp_tac (esimps [symmetric Un_def]) 1),
    (dtac onerel_mono' 1), (rtac Int_lower2 1),
    (clarsimp_tac (cesimps [onerel_Un]) 1)]) ;
*)

val () = qed_goalw "sn1ord_red" redn.thy [sn1order_def', mk_eq red_idemp]
  "sn1order (ctxt r) = sn1order r" (fn _ => [(rtac refl 1)]) ;

Addsimps [red_idemp, sn1ord_red] ;

val _ = qed_goal "red_comp" redn.thy
  "ctxt (r O s) <= ctxt r O ctxt s" 
  (fn _ => [ Safe_tac, (etac ron.induct 1), 
    (etac rel_compE 2), (rtac rel_compI 2), Fast_tac 2, Fast_tac 2,
    (etac oneup.elims 1), (Clarsimp_tac 1),
    (dtac (Int_lower2 RS onerel_mono RS subsetD) 1),
    (dtac (onerel_comp RS subsetD) 1),
    Safe_tac, (rtac rel_compI 1), Auto_tac]) ;

val _ = qed_goalw_spec_mp "ctxt_IdI" clcon.thy [ctxt1_def]
  "(c, b) : ctxt1 (t, s) --> c = b --> t = s"
  (fn _ => [ (rtac impI 1), (etac ctxt.induct 1), Fast_tac 2,
    (dtac oo_inst 1), Safe_tac, (etac oneup.elims 1),
    Safe_tac, (dtac onerel_IdI 1), Auto_tac ]) ;

val _ = qed_goal_spec_mp "ctxt_IdE" clcon.thy
  "(c, b) : ctxt r --> r <= Id --> c = b"
  (fn _ => [ (rtac impI 1), (etac ctxt.induct 1), Fast_tac 2,
    (dtac oo_inst 1), Safe_tac, (etac oneup.elims 1),
    Safe_tac, (etac onerel.induct 1), Auto_tac ]) ;

(* ctxt is of "finite character" *)
    
val _ = qed_goal_spec_mp "red_finchar" redn.thy 
  "(x, y) : ctxt r --> \
    \ (EX s. finite s & s <= r & (x, y) : ctxt s)" 
  (fn _ => [ (rtac impI 1), (etac ron.induct 1), 
    (etac oneup.elims 1), (Clarsimp_tac 1), 
    (res_inst_tac [("x", "{(dtr, dt)}")] exI 2),
    (clarsimp_tac (cis [ron.red_cutI], esimps []) 2),
    (dtac (Int_lower2 RS onerel_mono RS subsetD) 1),
    (subgoal_tac 
      "EX s. finite s & s <= r & (dtl1, dtl2) : onerel (ctxt s)" 1),
    (etac ex_match 1), (Clarsimp_tac 1), 
    (etac onerel.induct 1), Auto_tac]) ;

val _ = qed_goal "redn_trancl" redn.thy "ctxt (r^+) <= (ctxt r)^+" 
  (fn _ => [ Safe_tac, (etac ron.induct 1), 
    (etac trancl_mono 2), Fast_tac 2,
    (etac oneup.elims 1), (Clarsimp_tac 1),
    (dtac (Int_lower2 RS onerel_mono RS subsetD) 1),
    (dtac (onerel_trancl RS subsetD) 1),
    (etac trancl_induct 1), Fast_tac 1,
    (etac trancl_into_trancl 1), Fast_tac 1]) ;

val _ = qed_goal "rtr" redn.thy "ctxt ((ctxt r)^+) = (ctxt r)^+" 
  (fn _ => [ (rtac equalityI 1), (rtac order_trans 1), 
    (rtac redn_trancl 1), Auto_tac]) ;

val _ = qed_goal "trt" redn.thy "(ctxt (r^+))^+ = (ctxt r)^+" 
  (fn _ => [ (rtac equalityI 1),
    (rtac trancl_mono' 2), (rtac red_mono 2), 
    (rtac order_trans 1), (rtac trancl_mono' 1),
    (rtac redn_trancl 1), Auto_tac]) ;

val _ = qed_goal "isubt_redn'" redn.thy 
  "isubt O ctxt r <= nured r O isubt"
  (fn _ => [ Safe_tac, (etac isubt.elims 1),
    (res_inst_tac [("b", "Node aa (repfst sts sdt a)")] rel_compI 1), 
    (Clarify_tac 1), (etac in_repfst 1), 
    (rewtac nured_def), (Clarify_tac 1),
    (eatac onerel_repfst 1 1) ]) ;

val _ = qed_goal "isubt_redn" redn.thy 
  "isubt O ctxt r <= ctxt r O isubt"
  (fn _ => [ (rtac order_trans 1), (rtac isubt_redn' 1),
    (rtac rel_comp_mono 1), Safe_tac ]) ;

val isubt_rtc_redn = isubt_redn RS move_l_rtrancl ;
val _ = bind_thm ("psubt_redn",
  fold_rule [psubt_def] (isubt_redn RS move_l_trancl)) ;
val _ = bind_thm ("subt_redn", fold_rule [subt_def'] isubt_rtc_redn) ;

val _ = qed_goalw "psubt_nuredn" redn.thy [psubt_def]
  "psubt O ctxt r <= nured r O psubt"
  (fn _ => [ Safe_tac, (dtac converse_tranclD 1), Safe_tac, 
    (ftac (thin_rl RS (isubt_rtc_redn RS subsetD)) 1),
    Fast_tac 1, (etac rel_compE 1), 
    (ftac (thin_rl RS (isubt_redn' RS subsetD)) 1),
    Fast_tac 1, (etac rel_compE 1), Safe_tac, 
    (REPEAT (datac rtrancl_into_trancl1 1 1)), Fast_tac 1]) ;

val _ = qed_goalw "nured_isubt" redn.thy [nured_def]
  "nured r O isubt <= isubt O (ctxt r)^="
  (fn _ => [ (safe_tac (ces [oneup.elims, converse_tranclD RS exE])),
    (rotate_tac ~1 1), (etac rev_mp 1), (etac onerel.induct 1), Safe_tac,
    (TRYALL (EVERY' [ (rtac rel_compI), 
      (etac UnI1 ORELSE' rtac (IdI RS UnI2)),
      (rtac isubt.isubtI),
      (etac consI2 ORELSE' rtac consI1) ]))]) ;

val _ = qed_goalw "nured_psubt" redn.thy [mk_eq (p_iOs RS sym)]
  "nured r O psubt <= isubt O (ctxt r)^= O subt"
  (fn _ => [ (simp_tac (esimps [O_assoc RS sym]) 1),
    (rtac rel_comp_mono 1), (rtac nured_isubt 1), (rtac order_refl 1) ]) ;

val nured_psubt' = 
  rel_compI RS (rewrite_rule [nured_def] nured_psubt RS subsetD) ;

val _ = qed_goal_spec_mp "wfp_isubt_redn" redn.thy 
  "wfp (ctxt r Un isubt) = wfp (ctxt r)"
  (fn _ => [ (rtac wfUn_movl' 1), (rtac wf_isubt 2), 
    (rtac order_trans 1), (rtac isubt_redn 1),
    (rtac rel_comp_mono 1), Auto_tac]) ;

val _ = qed_goal_spec_mp "wfp_psubt_redn" redn.thy 
  "wfp (ctxt r Un psubt) = wfp (ctxt r)"
  (fn _ => [ (rtac wfUn_movl' 1), (rtac wf_psubt 2), 
    (rtac order_trans 1), (rtac psubt_redn 1),
    (rtac rel_comp_mono 1), Auto_tac]) ;

val subOtacs = [ (rtac equalityI 1), (rtac wfp_mono 1), Fast_tac 1,
    (rtac order_trans 1), (rtac 
      ([wfp_trancl, wfp_psubt_redn] MRS trans RS sym RS order_eq_refl) 1),
    (rtac wfp_mono 1), 
    (auto_tac (cds [rtranclD], esimps [subt_def', psubt_def])),
    (rtac (hd transitive_closure_trans) 1), Auto_tac] ;

val _ = qed_goal_spec_mp "wfp_O_subt_redn" redn.thy 
  "wfp (ctxt r O subt) = wfp (ctxt r)" (fn _ => subOtacs) ;

val _ = qed_goal_spec_mp "wfp_subt_O_redn" redn.thy 
  "wfp (subt O ctxt r) = wfp (ctxt r)" (fn _ => subOtacs) ;

val _ = bind_thm ("wf_psubt_redn", wfp_psubt_redn RS wf_wfp_eq RS iffD2) ;
val _ = bind_thm ("wf_O_subt_redn", wfp_O_subt_redn RS wf_wfp_eq RS iffD2) ;
val _ = bind_thm ("wf_subt_O_redn", wfp_subt_O_redn RS wf_wfp_eq RS iffD2) ;

(* using new formulation of sn_set, prove old one *)

val () = qed_goalw "sn1r_onered" redn.thy [onered_def, sn1red_def]
  "sn1red r <= onered r"
  (fn _ => [ (rtac onerel_mono 1), Fast_tac 1]) ;

val () = qed_goalw "wfp_nured'" redn.thy [mk_eq nured_def]
  "dt : wfp (nured r) = (set (isubts dt) <= wfp (ctxt r))"
  (fn _ => [ (simp_tac (esimps [wfp_onerel, wfp_oneup]) 1) ]) ;

val wfp_nured = prove_goal redn.thy 
  "wfp (nured r) = {dt. set (isubts dt) <= wfp (ctxt r)}"
  (fn _ => [ (simp_tac (esimps [wfp_nured' RS sym]) 1) ]) ;

val ro1I = rewrite_rule [mk_eq nured_def] ron.red_nuI ;

val () = qed_goal_spec_mp "snUp" redn.thy 
  "Node a dtl : wfp (ctxt r) --> set dtl <= wfp (ctxt r)"
  (fn _ => [rtac impI 1, 
    (dtac (rev_subsetD) 1), (rtac (wfp_mono) 1), (dtac snUpn 2), 
    Clarify_tac 1, (etac ro1I 1),
    (full_simp_tac (esimps [wfp_onered]) 1)]) ;
    
val () = qed_goal "fwf_oneup" redn.thy "fwf (oneup r) = oneup (fwf r)"
  (fn _ => [ Safe_tac, (ALLGOALS (etac oneup.elims)), 
    (auto_tac (cesimps [sn1upn]))]) ;

val () = bind_thm ("subt_sn", reop rev (
  meta_std (prove_goalw redn.thy [subt_def'] 
  "(dts, dt) : subt --> dt : wfp (ctxt r) --> dts : wfp (ctxt r)" 
  (fn _ => [ (rtac impI 1), (etac converse_rtrancl_induct 1),
    (case_tac "z" 2), (Safe_tac), (dtac snUp 1), Auto_tac])))) ;

val _ = bind_thm ("subt_snr", rotate_prems 1 subt_sn) ;
 
val _ = qed_goalw_spec_mp "isubts_sn" redn.thy [psubt_def]
  "set (isubts dt) <= wfp (ctxt r) --> (dt', dt) : psubt --> dt' : wfp (ctxt r)"
  (fn _ => [
    (clarsimp_tac (cesimps [subset_def, Ball_def, subt_def']) 1),
    (dtac converse_tranclD 1),
    (force_tac (ces [subt_sn], esimps [subt_def']) 1)]) ;

val _ = ListPair.app bind_thm (["snUp'", "subt_sn'"], [snUp, subt_sn]) ;

