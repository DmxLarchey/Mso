
structure fgdef = struct val thy = theory "fgdef" ;
  val ipt_mk_cases = InductivePackage.the_mk_cases thy ; end ;
use_legacy_bindings fgdef.thy ;
fun u _ = use_thy "fgdef" ;

structure fgrn = fg_ruleredn ;
structure fgc = fg_cutorder ;
structure fgcn = fg_cutorder_n ;
val fgcn_mk_cases = fgdef.ipt_mk_cases "fgdef.fg_cutorder_n" ;
val fgc_mk_cases = fgdef.ipt_mk_cases "fgdef.fg_cutorder" ;
val fgcn_elim_Suc = fgcn_mk_cases " ((y, z), Suc n) : fg_cutorder_n" ;
val fgcn_elim_0 = fgcn_mk_cases " ((y, z), 0) : fg_cutorder_n" ;
val fgc_fgI = fgcn.fgI RS fgc.I ;
AddSEs [fgcn_elim_Suc, fgcn_elim_0] ;
val red_elim = tacsthm [etac oneup.elims 2, etac fgrn.elims 3] ron.elim ;
val fgc_elim' = (fgc_mk_cases "(a, b) : fg_cutorder") ;
val fgc_subI = tacthm (etac (fgcn.subI RS fgc.I) 2) fgc_elim' ;
AddSIs [fgc_fgI, fgc_subI] ;

val _ = qed_goal_spec_mp "colem" fgdef.thy 
  "ALL m x y z. ((y, z), n) : fg_cutorder_n --> \
    \ ((x, y), m) : fg_cutorder_n --> m < n"
  (fn _ => [ (induct_tac "n" 1), Safe_tac,
    (etac fgcn.elims 1), Safe_tac,
    (case_tac "m" 1), Safe_tac, Fast_tac 1 ]) ;

val _ = qed_goal_spec_mp "colem2'" fgdef.thy 
  "ALL j z m. m <= n --> ((f j, z), m) : fg_cutorder_n --> \
    \ (EX i. (f (Suc i), f i) ~: fg_cutorder)"
  (fn _ => [ (induct_tac "n" 1), Safe_tac,
    (res_inst_tac [("x", "j")] exI 1),
    Clarify_tac 1, (etac fgc.elims 1), (etac fgcn.elims 1), 
    Force_tac 1, Force_tac 1, 
    (case_tac "(f (Suc j), f j) : fg_cutorder" 1), (etac exI 2),
    (etac fgc.elims 1), (dtac colem 1), Fast_tac 1, 
    (subgoal_tac "na <= n" 1), Asm_simp_tac 2, Fast_tac 1]) ;

val colem2 = order_refl RS colem2' ;

val _ = qed_goal "fgwfcut" fgdef.thy "wf (fg_cutorder)"
  (fn _ => [
    (simp_tac (esimps [wf_iff_no_infinite_down_chain]) 1), Safe_tac, 
    (case_tac "(f (Suc 0), f 0) : fg_cutorder" 1), Fast_tac 2,
    (etac fgc.elims 1), (rtac colem2 1), Fast_tac 1]) ;

val _ = qed_goal_spec_mp "fgslem'" fgdef.thy 
  "ALL m dt dt1 dt2. m <= n --> ((dt, dt1), m) : fg_cutorder_n --> \
    \ (dt1, dt2) : ctxt fg_ruleredn --> (dt, dt2) : fg_cutorder"
  (fn _ => [ (induct_tac "n" 1), Safe_tac,
    (etac red_elim 1), Safe_tac,
    (case_tac "m" 1), (Clarify_tac 1), 
    (etac red_elim 1), Safe_tac,
    
    (etac red_elim 1), (etac fgcn.elims 2), Safe_tac,
    (fast_tac (ces onerel.elims) 1)]) ;

val fgslem = order_refl RS fgslem' ;
val fgslem2 = tacthm (etac fgslem 2) fgc_elim' ;

val _ = qed_goal_spec_mp "fgsntr" fgdef.thy
  "(dt, Node a dtl1) : fg_cutorder --> (dtl1, dtl2) : sn1red fg_ruleredn --> \
    \ (dt, Node a dtl2) : (fg_cutorder :: (fg rtree * fg rtree) set)"
  (fn _ => [ Safe_tac, (etac fgslem2 1), 
    (resolve_tac ([oneup.intros] RL ron.intrs) 1),
    (etac (sn1r_onered' RS subsetD) 1)]) ;

val _ = qed_goalw "fg_absl" fgdef.thy [sn1order_def]
  "sn1order fg_ruleredn O fg_cutorder <= fg_cutorder"
  (fn _ => [ (safe_tac (ces [oneup.elims])), (eatac fgsntr 1 1) ]) ;

val fgwf = [fg_absl, fgwfcut, wf_sn1order] MRS wfUn_absl ;

val _ = qed_goalw_spec_mp "fg_red_props" fgdef.thy [subt_def, psubt_def]
  "(dtn, dt) : fg_ruleredn --> (dts, dtn) : subt --> \
    \ (dts, dt) : psubt Un fg_cutorder"
  (fn _ => [ strip_tac 1, (etac fgrn.elims 1), (etac UnE 1), 
    (rtac UnI2 2), Fast_tac 2, 
    (etac tranclE 1), (etac isubt.elims 1), Force_tac 1,
    (rtac UnI1 1), (etac tranclE 1),
    (REPEAT_SOME (etac isubt.elims)), Auto_tac,
    (etac trancl_into_trancl 1), Force_tac 1]) ;

val _ = qed_goalw_spec_mp "fg_red_props_pc" fgdef.thy [red_props_pc_def]
  "red_props_pc fg_ruleredn fg_cutorder"
  (fn _ => [ (fast_tac (cds [fg_red_props]) 1) ]) ;

val fgsn = [fg_red_props_pc, fgwf] MRS all_sn3_pc ;

