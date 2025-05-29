
structure d31def = struct val thy = theory "d31def" ;
  val ipt_mk_cases = InductivePackage.the_mk_cases thy ; end ;
use_legacy_bindings d31def.thy ;
fun u _ = use_thy "d31def" ;

val d31_ruleredn_mk_cases = d31def.ipt_mk_cases "d31def.d31_ruleredn" ;

(* proof of termination of Dershowitz, 33 Examples, example 31 *)

(* d31 example *)
val dcis = dc2.intros :: dc3.intros :: dc1.intros ; 
val dces = [dc1.elims, dc2.elims, dc3.elims] ; 
AddIffs (dcis @ d31_ruleredn.intros) ;
val d31_cs = cis [equals0I] addSEs dces ;
val d31_css = (d31_cs, esimps [inv_image_def]) ;
val d31rGE = d31_ruleredn_mk_cases "(ab, Node G a) : d31_ruleredn" ;
val d31rAE = d31_ruleredn_mk_cases "(ab, Node A a) : d31_ruleredn" ;
val d31rPE = d31_ruleredn_mk_cases "(ab, Node P a) : d31_ruleredn" ;
AddSEs [d31rGE, d31rPE, d31rAE] ;

val _ = qed_goal "wf_dc3" d31def.thy "wf dc3"
  (fn _ => [
    (subgoal_tac "dc3 <= inv_image isubt (hd o tl o isubts)" 1),
    (rtac wf_subset 1), atac 2, (rtac wf_inv_image 1), (rtac wf_isubt 1),
    (clarsimp_tac d31_css 1)]) ;

val _ = qed_goal "wf_dc2" d31def.thy "wf dc2"
  (fn _ => [
    (subgoal_tac "dc2 <= inv_image isubt (hd o isubts)" 1),
    (rtac wf_subset 1), atac 2, (rtac wf_inv_image 1), (rtac wf_isubt 1),
    (clarsimp_tac d31_css 1)]) ;

val _ = qed_goal "wf_dc1" d31def.thy "wf dc1"
  (fn _ => [ (res_inst_tac [("n", "Suc (Suc (Suc 0))")] wf_lim_comp 1),
    (auto_tac d31_css) ]) ;

AddIffs [wf_dc2, wf_dc3, wf_dc1] ;

val _ = qed_goalw "d31wfcut" d31def.thy [d31cdef] "wf d31_cutorder"
  (fn _ => [ (rtac wfUn_absr 1), (rtac wfUn_absl 2), Safe_tac, 
    (safe_tac d31_cs) ]) ;

val _ = qed_goal "d31wfdt" d31def.thy 
  "wf (d31_cutorder Un sn1order d31_ruleredn)"
  (fn _ => [ (rtac wf_cus12 1), (rtac wfUn_movr 1),
    (rtac wf_sn2order 3), (rtac d31wfcut 2),
    (rewrite_goals_tac [d31cdef, sn2order_def']),
    (safe_tac (d31_cs addSEs (rfrE :: oo_elims))),
    (* deal with cases where cutorder O sn2order <= cutorder *)
    (TRYALL (EVERY' [ (rtac rel_compI), 
      (rtac rtrancl_refl o incr), Fast_tac])),
    (* deal with cases where cutorder O sn2order <= sn2order O cutorder *)
    (TRYALL (EVERY' [ (TRY o datac rfrI 1), (rtac rel_compI),
      (rtac r_into_rtrancl o incr), (fast_tac d31_cs), artac]))]) ;

val _ = qed_goalw_spec_mp "d31_red_props" d31def.thy 
  [subt_def, psubt_def, d31cdef]
  "(dtn, dt) : d31_ruleredn --> (dts, dtn) : subt --> \
    \ (dts, dt) : psubt Un d31_cutorder Un (nured d31_ruleredn)^+"
  (fn _ => [ strip_tac 1, (etac d31_ruleredn.elims 1),
    (safe_tac (ces [trancl_isubtE])),
    (* deal with cases involving isubt^+ *) 
    (TRYALL ((DETERM o chop_tac 1 o etac notE) THEN' tranclI_tac)),
    (* now using nured ruleredn, using psubt rules for ruleredn *)
    (TRYALL (EVERY' [ (DETERM o etac notE), 
      (rtac r_into_trancl), (SELECT_GOAL (rewtac nured_def)),
      (rtac oneup.ouI), Clarify_tac, (rtac ron.red_cutI), 
      (resolve_tac d31_ruleredn.intros)])) ]) ;

val _ = qed_goalw_spec_mp "d31_red_props_c" d31def.thy [red_props_c_def]
  "red_props_c d31_ruleredn d31_cutorder"
  (fn _ => [ (fast_tac (cds [d31_red_props RS UnI1]) 1) ]) ;

val d31sn = [d31_red_props_c, d31wfdt] MRS all_sn3_c ;


    

