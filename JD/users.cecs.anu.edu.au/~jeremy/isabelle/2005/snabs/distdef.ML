
structure distdef = struct val thy = theory "distdef" end ;
use_legacy_bindings distdef.thy ;
fun u _ = use_thy "distdef" ;

structure drn = dist_ruleredn ;
AddSEs [dcofg.elims] ; AddSIs dcofg.intros ;
AddSEs [dcoaT.elims] ; AddSIs [dcoaT.intros] ;
AddSEs [dcoaP.elims] ; AddSIs [dcoaP.intros] ;

val _ = qed_goal "distwfcut'" distdef.thy "wf (dcofg Un (dcoaP Un dcoaT))"
  (fn _ => [ (rtac wfUn_absl 1), (rtac wfUn_absl 3), 
    (res_inst_tac [("n", "Suc (Suc (Suc 0))")] wf_lim_comp 2), Auto_tac,
    (REPEAT (EVERY [
      (subgoal_tac "?r <= inv_image isubt (hd o isubts)" 1),
      (rtac wf_subset 1), atac 2, 
      (rtac wf_inv_image 1), (rtac wf_isubt 1),
      (force_tac (cesimps [inv_image_def]) 1)])) ]) ;

val distwfcut = fold_rule [distcdef] distwfcut' ;

val _ = qed_goalw "dist_c1p" distdef.thy [distcdef, nured_def, cut1_prop_def]
  "cut1_prop dist_cutorder"
  (fn _ => [ (safe_tac (ces oo_elims)), 
    (REPEAT1 (EVERY [ (rtac rel_compI 1),
      (rtac rtrancl_refl 2), Fast_tac 1])),
    (Fast_tac 4), (Fast_tac 2),
    (REPEAT1 (EVERY [ (etac isubt.elims 1), Clarify_tac 1, 
      (fatac onerel_repfst 1 1), 
      (rtac rel_compI 1), (rtac r_into_rtrancl 2), 
      (artac 2), (fast_tac (ces [in_repfst]) 1)])) ]) ;

val distwfdt = [distwfcut, dist_c1p] MRS c1p_wfdt ;

val _ = qed_goalw_spec_mp "dist_red_props" distdef.thy 
  [subt_def, psubt_def, distcdef]
  "(dtn, dt) : dist_ruleredn --> (dts, dtn) : subt --> \
    \ (dts, dt) : psubt Un dist_cutorder Un (nured dist_ruleredn)^+"
  (fn _ => [ strip_tac 1, (etac drn.elims 1),

    (REPEAT (EVERY [ (SELECT_GOAL (rewtac (mk_eq reflcl_trancl)) 1),
      (rtac (UnI1 RS UnI1) 1),
      (etac rtrancl_into_trancl1 1), Force_tac 1])),

    (safe_tac (ces [trancl_isubtE])),
    (* deal with cases involving isubt^+ *) 
    (TRYALL ((DETERM o chop_tac 1 o etac notE) THEN' tranclI_tac)),

    (* cases arising from associativity *)
    (ALLGOALS Simp_tac),

    (* now using nured ruleredn, using psubt rules for ruleredn *)
    (TRYALL (EVERY' [ (etac notE), (etac thin_rl),
      (rtac r_into_trancl), (SELECT_GOAL (rewtac nured_def)),
      (rtac oneup.ouI), Clarify_tac, (rtac ron.red_cutI), 
      (resolve_tac dist_ruleredn.intros)])) ]) ;

val _ = qed_goalw_spec_mp "dist_red_props_c" distdef.thy [red_props_c_def]
  "red_props_c dist_ruleredn dist_cutorder"
  (fn _ => [ (fast_tac (cds [dist_red_props RS UnI1]) 1) ]) ;

val distsn = [dist_red_props_c, distwfdt] MRS all_sn3_c ;


    


    

