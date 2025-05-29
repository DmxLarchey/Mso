
structure horders = struct val thy = theory "horders" ;
  val ipt_mk_cases = InductivePackage.the_mk_cases thy ; end ;
use_legacy_bindings horders.thy ;
fun u _ = use_thy "horders" ; 

val _ = qed_goalw_spec_mp "rp_pc_cut0" horders.thy [red_props_pc_def]
  "r0s <= rule0_proph S --> red_props_pc (subs r0s) (subs (cut0 S r0s))"
  (fn _ => [ (safe_tac (csp addSEs [subs.elims])),
    (datac subsetD 1 1), (fatac r0ph_sub' 1 1), 
    (etac disj_forward 1), atac 1, Safe_tac, 
    (simp_tac (esimps [cut0_def]) 1), (case_tac "t0'" 1), Force_tac 2,
    (REPEAT_FIRST (resolve_tac [exI, conjI])), atac 1,
    (etac ctxt_S.cutI 1), Fast_tac 1, 
    (auto_tac (ces [rule0_prophE], esimps [])) ]) ;

val rp_c_cut0 = rp_pc_cut0 RS rpcc' ;

(* simple case - suppose system 2 satisfies red_props_c also *)
val _ = qed_goalw_spec_mp "rp_c_hier'" horders.thy [cuth_def]
  "r0s <= rule0_proph S --> red_props_c r1s c1 --> \
    \ wf (cuth S r0s c1 Un ?s) --> dt : wfp (ctxt (subs r0s Un r1s))"
  (fn _ => [ Safe_tac, (datac (rp_c_cut0 RS rp_c_Un) 1 1), 
    (etac all_sn3_c 1), atac 1 ]) ;
    
val rph = mkss r0phD2 RSN (2, subset_trans) ;

val rp_c_epr2 = wfh_epr1 RSN (3, rp_c_hier') ;
val rp_c_epr3 = tacthm (TRYALL (rtac rph)) rp_c_epr2 ;
val _ = bind_thm ("rp_c_epr", rem_dup_prems rp_c_epr3) ;


