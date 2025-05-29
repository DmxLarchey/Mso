
structure zan15def = struct val thy = theory "zan15def" end ;
use_legacy_bindings zan15def.thy ;

(* proof of termination of example on 
  Zantema, The Termination Hierarchy for Term Rewriting, Prop'n 15 *)

structure z15rn = struct
  open zan15_ruleredn ;
  val intros' = map (simplify (esimps [])) intros ;
  end ;

structure z15c = struct
  open zan15_cut ;
  val intros' = map (simplify (esimps [])) intros ;
  val elims' = full_simplify (esimps []) elims ;
  end ;

val z15_cs = claset () addSIs z15c.intros' addSEs [z15c.elims'] ;

AddIffs (z15c.intros' @ z15rn.intros') ;

val _ = qed_goal "zan15wfcut" zan15def.thy "wf (zan15_cut)"
  (fn _ => [
    (res_inst_tac [("n", "Suc (Suc (Suc 0))")] wf_lim_comp 1),
    (clarsimp_tac (cis [equals0I], simpset ()) 1),
    (auto_tac (ces [zan15_cut.elims], simpset ()))]) ;

val _ = qed_goal "zan15wfdt" zan15def.thy 
  "wf (zan15_cut Un sn1order zan15_ruleredn)"
  (fn _ => [ (rtac wfUn_absr 1), 
    (rtac wf_sn1order 2), (rtac zan15wfcut 2), Safe_tac, 
    (dtac (sn1o_nured') 1), 
    (rewrite_goals_tac [nured_def]),
    (safe_tac (z15_cs addSEs oo_elims)),
    (safe_tac (z15_cs addSEs (z15rn.elims :: ron.elim :: oo_elims))),
    Auto_tac]) ;

val _ = qed_goalw_spec_mp "zan15_red_props'" zan15def.thy [subt_def, psubt_def]
  "(dtn, dt) : zan15_ruleredn --> (dts, dtn) : subt --> \
    \ (dts, dt) : psubt | (dts, dt) : zan15_cut"
  (fn _ => [ strip_tac 1, (etac zan15_ruleredn.elims 1),
    (safe_tac csp), (ALLGOALS Full_simp_tac),
    (safe_tac (ces [isubt_tranclE])), (ALLGOALS tranclI_tac) ]) ;

val _ = qed_goalw_spec_mp "zan15_red_props_pc" zan15def.thy [red_props_pc_def]
  "red_props_pc zan15_ruleredn zan15_cut"
  (fn _ => [ (fast_tac (cds [zan15_red_props']) 1) ]) ;

val zan15sn = [zan15_red_props_pc, zan15wfdt] MRS all_sn3_pc ;

