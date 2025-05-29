
structure pmsdef = struct val thy = theory "pmsdef" ;
  val ipt_mk_cases = InductivePackage.the_mk_cases thy ; end ;
use_legacy_bindings pmsdef.thy ;
fun u _ = use_thy "pmsdef" ;

val pmci_mk_cases = pmsdef.ipt_mk_cases "pmsdef.pmci" ;

val pm_intrs = [pmcc.I, pmc1.I, pmc2.I] ;
val pm_elims = [pmcc.elims, pmci.elims, pmc1.elims, pmc2.elims] ;
val pm_cs = (ces pm_elims addSIs pm_intrs) ;
val pm_css = (pm_cs, simpset ()) ;
AddSIs (pmr1.I :: pmci.I :: coll1s.intros) ; AddIffs [coll1.I] ;
val pmci_elim = pmci_mk_cases "(Node a xs, Node a ys) : pmci" ;
AddSEs [pmci_elim] ;

val _ = qed_goal "rtree_list_size_append" pmsdef.thy 
  "rtree_list_size (xs @ ys) = rtree_list_size xs + rtree_list_size ys"
  (indAu "xs") ;

val _ = qed_goal_spec_mp "size_coll" pmsdef.thy
  "(collapses xs) ~= xs --> \
    \ rtree_list_size (collapses xs) < rtree_list_size xs"
  (fn _ => [ (induct_tac "xs" 1), 
    (ALLGOALS (simp_tac (esimps [rtree_list_size_append]))),
    (case_tac "a" 1), (case_tac "aa" 1), Auto_tac]) ;

val _ = qed_goal_spec_mp "size_coll1" pmsdef.thy
  "(ys, xs) : coll1s --> rtree_list_size ys < rtree_list_size xs"
  (fn _ => [ (rtac impI 1), (etac coll1s.induct 1), 
    (ALLGOALS (simp_tac (esimps [rtree_list_size_append]))),
    (etac coll1.elims 1), Auto_tac]) ;

val _ = qed_goal "wf_pmcc" pmsdef.thy "wf pmcc"
  (fn _ => [ (rtac wf_subset 1), 
    (res_inst_tac [("f", "size")] wf_measure 1), 
    (rewrite_goals_tac [measure_def, inv_image_def, less_than_def,
      symmetric less_def]),
    (clarsimp_tac (ces [pmcc.elims, size_coll], simpset ()) 1)]) ;

val _ = qed_goal "wf_pmci" pmsdef.thy "wf pmci"
  (fn _ => [ (rtac wf_subset 1), 
    (res_inst_tac [("f", "size")] wf_measure 1), 
    (rewrite_goals_tac [measure_def, inv_image_def, less_than_def,
      symmetric less_def]),
    (force_tac (ces [coll1s.elims, pmci.elims, size_coll1],
      simpset ()) 1)]) ;

val _ = qed_goal "pmswfc12" pmsdef.thy "wf (pmc1 Un pmc2)"
  (fn _ => [ (rtac wfUn_absr 1), (safe_tac pm_cs),
    (cut_facts_tac [wf_symborder] 1), 
    (full_simp_tac (esimps [wf_eq_minimal]) 1), Safe_tac,
    (case_tac "x" 1), (case_tac "a" 1),
    (rtac bexI 2), atac 3, (safe_tac pm_cs),
    (eres_inst_tac [("x", "{aa. EX list. Node (Leaf aa) list : Q}")] allE 1),
    (etac impE 1), Fast_tac 1,
    (etac thin_rl 1), Safe_tac,
    (rtac bexI 1), atac 2, (fast_tac pm_cs 1),
    (res_inst_tac [("n", "Suc (Suc 0)")] wf_lim_comp 1),
    (force_tac pm_css 1) ]) ;
  
val _ = qed_goal "pmswfc12c" pmsdef.thy "wf ((pmc1 Un pmc2) Un pmcc)"
  (fn _ => [ (rtac wfUn_absr 1),
    (rtac pmswfc12 3), (rtac wf_pmcc 2), (safe_tac pm_cs)]) ;

val _ = qed_goal "pmswfc12i" pmsdef.thy "wf ((pmc1 Un pmc2) Un pmci)"
  (fn _ => [ (rtac wfUn_absr 1),
    (rtac pmswfc12 3), (rtac wf_pmci 2), (safe_tac pm_cs)]) ;

val _ = bind_thm ("pmswfcut", fold_rule [pmscdef] pmswfc12) ;

(*
val _ = qed_goalw_spec_mp "pmssntr" pmsdef.thy [pmscdef]
  "(dt, Node a dtl1) : cutorder --> (dtl1, dtl2) : r --> \
    \ (dt, Node a dtl2) : (cutorder :: (spms rtree * spms rtree) set)"
  (fn _ => [ (safe_tac pm_cs)]) ;
*)

val _ = qed_goal_spec_mp "coll_subt" pmsdef.thy
  "y : set (collapses xs) --> (EX x : set xs. (y, x) : isubt^*)"
  (fn _ => [ (induct_tac "xs" 1), 
    (case_tac "a" 2), (case_tac "aa" 2), Auto_tac]) ;

val _ = qed_goal_spec_mp "coll1_subt" pmsdef.thy
  "(ys, xs) : coll1s --> y : set ys --> \
    \ (EX x : set xs. (y, x) : isubt^*)"
  (fn _ => [ (rtac impI 1), (etac coll1s.induct 1), 
    (etac coll1.elims 1), Auto_tac ]) ;

val _ = qed_goalw_spec_mp "pms_red_props_pc'" pmsdef.thy 
  [subt_def, psubt_def, pmscdef]
  "(dtn, dt) : pmr1 Un pmci --> (dts, dtn) : subt --> \
    \ (dts, dt) : psubt | (dts, dt) : pms_cutorder"
  (fn _ => [ 
    (safe_tac (ces [pmr1.elims, pmci.elims])), 
    (safe_tac (cis pm_intrs)), 
    (* case - subtree of collapsed tree *)
    (dtac converse_tranclD 2), (Clarify_tac 2), 
    (datac coll1_subt 1 2), (Clarify_tac 2), 
    (etac notE 2), (rtac rtrancl_into_trancl1 2),
    (etac isubt.isubtI 3), (eatac rtrancl_trans 1 2),
    (* case of subtree of new Inner node *)
    (safe_tac (ces [isubt_tranclE])), 
    (dtac converse_tranclD 2), 
    (force_tac (cesimps [leaf_def]) 2), 
    (force_tac (cis pm_intrs, esimps [leaf_def]) 1)]) ;

val pms_red_props_pc'' = fold_rule [pmsrdef] pms_red_props_pc' ;

val _ = qed_goal_spec_mp "onerel_coll1" pmsdef.thy
  "(ys, zs) : coll1s --> (ALL xs. (xs, ys) : onerel (ctxt r) --> \
    \ (xs, zs) : onerel (ctxt r) O coll1s)"
  (fn _ => [ (rtac impI 1), (etac coll1s.induct 1), 
    (etac coll1.elims 1), Safe_tac,
    (dtac onerel_appendD 1), (etac onerel.elim 2), 
    (etac allE 3), (Clarify_tac 3), mp_tac 3, Safe_tac,
    (res_inst_tac [("b", "h # ?ss")] rel_compI 4),
    (res_inst_tac [("b", "a # zs")] rel_compI 3),
    (res_inst_tac [("b", "Node Inner ts # W")] rel_compI 2),
    (res_inst_tac [("b", "Node Inner V # xs")] rel_compI 1), Auto_tac ]) ;

val _ = qed_goal "pmswfdt'" pmsdef.thy 
  "wf (pmc1 Un pmc2 Un pmci Un nured (fwf (ctxt r)))"
  (fn _ => [ (rtac wfUn_movr 1), (rtac pmswfc12i 2), (rtac wf_nfr 2),
    (rewtac nured_def), 
    (safe_tac (ces (oneup.elims :: pm_elims))), 
    (TRYALL (EVERY' [rtac rel_compI, 
      rtac rtrancl_refl o incr, fast_tac (cis pm_intrs)])),
    (datac onerel_coll1 1 1), Safe_tac, (rtac rel_compI 1), 
    (rtac r_into_rtrancl 2), (rtac UnI2 1), Auto_tac]) ;

val _ = qed_goalw "pmswfdt" pmsdef.thy [pmscdef]
  "wf (pms_cutorder Un sn1order pms_ruleredn)"
  (fn _ => [ (rtac wf_subset 1), (rtac pmswfdt' 1),
    (rtac Un_mono 1), (rtac nfr_sn1 2), (rtac order_refl 1)]) ;

val _ = qed_goalw "pms_red_props_pc" pmsdef.thy [red_props_pc_def]
  "red_props_pc pms_ruleredn ?cuto"
  (fn _ => [ (strip_tac 1), (eatac pms_red_props_pc'' 1 1) ]) ;

val pmssn = [pms_red_props_pc, pmswfdt] MRS all_sn3_pc ;
val pmswf = pmssn RS wfp_wfI ;

