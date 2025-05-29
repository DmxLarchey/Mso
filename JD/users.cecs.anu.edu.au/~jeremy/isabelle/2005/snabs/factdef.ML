
structure factdef = struct val thy = theory "factdef" end ;
use_legacy_bindings factdef.thy ;
fun u _ = use_thy "factdef" ;

(* fact example - note - needs to use wfUn_movl_dvk *)
val fcis = fc1.intros @ fcsymb.intros ; 
val fces = [fc1.elims, fcsymb.elims] ; 
AddIffs (fcis @ fact_ruleredn.intros) ;
val fact_cs = cis [equals0I] addSEs fces ;
val fact_css = (fact_cs, esimps [inv_image_def]) ;

val _ = qed_goal "wf_fcsymb" factdef.thy "wf fcsymb"
  (fn _ => [
    (res_inst_tac [("n", "Suc (Suc (Suc (Suc 0)))")] wf_lim_comp 1),
    (Auto_tac), 
    (REPEAT (EVERY [sg_tac 1, ALLGOALS (etac fcsymb.elims), Auto_tac])) ]) ;

val _ = qed_goal "wf_fc1" factdef.thy "wf fc1"
  (fn _ => [ (res_inst_tac [("n", "Suc (Suc 0)")] wf_lim_comp 1),
    (auto_tac fact_css) ]) ;

AddIffs [wf_fcsymb, wf_fc1] ;

val _ = qed_goalw "factwfcut" factdef.thy [factcdef] "wf fact_cutorder"
  (fn _ => [ (rtac wfUn_absr 1), Safe_tac, (auto_tac fact_css) ]) ;

val sntc_tacs1 = [ (simp_tac (esimps [gip_rel_alt])),
    (REPEAT o rtac disjI1), (etac wfpc.elims), Clarsimp_tac,
    (dtac (isubt.isubtI RS isubt_subt RSN (2, subt_sn))), (Force_tac) ] ;

val sntc_tacs2 = [ (rtac r_into_trancl), 
  (rtac (onerel.onerelI1 RS oneup.intros)),
  (REPEAT o (rtac (onerel.onerelI1 RS oneup.intros RS ctxt.red_nuI))),
  (rtac ctxt.red_cutI), (fast_tac (cis [wfpc.I])) ] ;

fun sntc_tacs3 th = [ (rtac (mov_gip RS subsetD)),
  (rtac rel_compI), (rtac UnI2), (rtac th),
  (rtac (onerel.onerelI1 RS oneup.intros)),
  (rtac (onerel.onerelI1 RS oneup.intros RS ctxt.red_nuI)), atac ] ;

val _ = qed_goalw "fact_c1ge" factdef.thy [cut1_gip_epr_def']
  "cut1_gip_epr fact_cutorder fact_ruleredn (range F0)" 
  (fn _ => [ Safe_tac, (rewrite_goals_tac [factcdef]),
    (safe_tac (fact_cs addSEs (rfrE :: oo_elims))),
    (* deal with cases where cutorder O sn2order <= cutorder *)
    (TRYALL (EVERY' [ (rtac (movr_gip RS subsetD)), 
      (rtac ([UnI1, rtrancl_refl] MRS rel_compI)),
      (etac sn2orderE), (MSSG Clarsimp_tac)])),
      
    (rewrite_goals_tac [sn2o_defh, nured_def]),
    (auto_tac (ces oo_elims, esimps [])),
    (auto_tac (ces [ctxt.elims, fact_ruleredn.elims], esimps [])),
    (* level 7, 4 subgoals *)
    (EVERY' sntc_tacs1 2), (EVERY' sntc_tacs1 4), (rtac trancl_trans 4),
    (EVERY' sntc_tacs2 2), (EVERY' sntc_tacs2 3), (EVERY' sntc_tacs2 3), 
    (* level 13, 2 subgoals *)
    (auto_tac (ces oo_elims, esimps [])),
    (EVERY' (sntc_tacs3 fc1.I2) 2), 
    (etac ctxt.elims 1), Safe_tac, 
    (datac subsetD 1 2), Force_tac 2,
    (etac fact_ruleredn.elims 2), Auto_tac, 
    (MSSG (simp_tac (esimps [gip_rel_alt])) 2),
    (auto_tac (ces oo_elims, esimps [])),
    (EVERY' (sntc_tacs3 fc1.I1) 1) ]) ; 

val fact_c1de = fact_c1ge RS cut1_gip_dvk_epr ;

val _ = bind_thm ("fact_c1ge'", simplify (esimps [gip_cond_def])
([rewrite_rule [cut1_gip_epr_def] fact_c1ge RS spec, empty_subsetI] MRS mp)) ;

val _ = bind_thm ("factwfdt", 
  [fact_c1ge', wf_sn2order, factwfcut] MRS wfUn_gip RS wf_cus12') ;

(*
val _ = qed_goal "factwfdt" factdef.thy 
  "wf (fact_cutorder Un sn1order fact_ruleredn)" 
  (fn _ => [ (rtac wf_cus12' 1), (rtac wfUn_movl_dvk 1),
    (rtac wf_sn2order 2), (rtac factwfcut 2),
    (rewrite_goals_tac [factcdef, sn2order_def']),
    (safe_tac (fact_cs addSEs (rfrE :: oo_elims))),
    (* deal with cases where sn2order O cutorder <= cutorder O sn2order *)
    (TRYALL (EVERY' [ (etac notE), (TRY o datac rfrI 1), (rtac rel_compI),
      (rtac r_into_rtrancl), (rtac UnI2), (artac o incr), Fast_tac])),
    (safe_tac (ces [fact_ruleredn.elims])), Auto_tac, 
    (* remaining cases are where  sn2order O cutorder <= sn2order^+ *)
    (ALLGOALS (EVERY' [(etac notE), 
      (subgoal_tac "Node S [xa] : wfp (ctxt fact_ruleredn)"),
      (etac subt_sn' o incr), (force_tac (cesimps [subt_def']) o incr),
      (rtac rel_compI)] )), 
    (rtac rtrancl_refl 1), (fast_tac (cis [rfrI]) 1),
    (rtac r_into_rtrancl 1), (rtac UnI1 1), 
    (fast_tac (cis [rfrI]) 1), Clarify_tac 1,
    (rtac ron.red_nuI 1), (fast_tac (cis [rfrI]) 1)]) ;
*)

val _ = qed_goalw_spec_mp "fact_red_props" factdef.thy 
  [subt_def, psubt_def, factcdef]
  "(dtn, dt) : fact_ruleredn --> (dts, dtn) : subt --> \
    \ (dts, dt) : psubt Un fact_cutorder Un (nured fact_ruleredn)^+"
  (fn _ => [ strip_tac 1, (etac fact_ruleredn.elims 1),
    (safe_tac (ces [trancl_isubtE])),
    (* deal with cases involving isubt^+ *) 
    (TRYALL ((DETERM o chop_tac 1 o etac notE) THEN' tranclI_tac)),
    (* now using nured ruleredn, using psubt rules for ruleredn *)
    (TRYALL (EVERY' [ (DETERM o etac notE), 
      (rtac r_into_trancl), (SELECT_GOAL (rewtac nured_def)),
      (rtac oneup.ouI), Clarify_tac, (rtac ron.red_cutI), 
      (resolve_tac fact_ruleredn.intros)])) ]) ;

val _ = qed_goalw_spec_mp "fact_red_props_c" factdef.thy [red_props_c_def]
  "red_props_c fact_ruleredn fact_cutorder"
  (fn _ => [ (fast_tac (cds [fact_red_props RS UnI1]) 1) ]) ;

val factsn = [fact_red_props_c, factwfdt] MRS all_sn3_c ;

(* for incremental proof of termination *)

val _ = qed_goal "factr_notin" factdef.thy 
  "fact_ruleredn <= hds_notin (range F0)"
  (fn _ => [ (auto_tac (ces [fact_ruleredn.elims], esimps [])) ]) ;

val _ = qed_goalw "factc_notin" factdef.thy [factcdef]
  "fact_cutorder <= hds_notin (range F0)"
  (fn _ => [ (auto_tac (ces [fcsymb.elims, fc1.elims], esimps [])) ]) ;

val factisn = tacthm (TRYALL (resolve_tac [fact_red_props_c,
    factr_notin, factc_notin, fact_c1de, factwfcut])) rp_c_epr ;

val 2 = nprems_of factisn ;

