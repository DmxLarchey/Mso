
structure zan8edef = struct val thy = theory "zan8edef" end ;
use_legacy_bindings zan8edef.thy ;

(* proof of termination of second example on 
  Zantema, The Termination Hierarchy for Term Rewriting, p8 *)

structure z8ern = struct
  open zan8e_ruleredn ;
  val intros' = map (simplify (esimps [])) intros ;
  end ;

structure z8ec = struct
  open zan8e_cut ;
  val intros' = map (simplify (esimps [])) intros ;
  val elims' = full_simplify (esimps []) elims ;
  end ;

val z8e_cs = claset () addSIs z8ec.intros' addSEs [z8ec.elims'] ;

AddIffs (z8ec.intros' @ z8ern.intros') ;

val _ = qed_goal "zan8ewfcut" zan8edef.thy "wf (zan8e_cut)"
  (fn _ => [
    (res_inst_tac [("n", "Suc (Suc (Suc 0))")] wf_lim_comp 1),
    (clarsimp_tac (cis [equals0I], simpset ()) 1),
    (auto_tac (ces [zan8e_cut.elims], simpset ()))]) ;

val _ = qed_goal "zan8ewfdt" zan8edef.thy 
  "wf (zan8e_cut Un sn1order zan8e_ruleredn)"
  (fn _ => [ (rtac wfUn_absr 1), 
    (rtac wf_sn1order 2), (rtac zan8ewfcut 2), Safe_tac, 
    (dtac (sn1o_nured') 1), 
    (rewrite_goals_tac [nured_def]),
    (safe_tac (z8e_cs addSEs oo_elims)),
    (safe_tac (z8e_cs addSEs (z8ern.elims :: ron.elim :: oo_elims))),
    Auto_tac]) ;

val _ = qed_goalw_spec_mp "zan8e_red_props'" zan8edef.thy 
  [subt_def, psubt_def]
  "(dtn, dt) : zan8e_ruleredn --> (dts, dtn) : subt --> \
    \ (dts, dt) : psubt | (dts, dt) : zan8e_cut"
  (fn _ => [ strip_tac 1, (etac z8ern.elims 1), 
    (safe_tac csp), (ALLGOALS Full_simp_tac),
    (safe_tac (ces [isubt_tranclE])), (TRYALL tranclI_tac) ]) ;

val _ = qed_goalw_spec_mp "zan8e_red_props_pc" zan8edef.thy [red_props_pc_def]
  "red_props_pc zan8e_ruleredn zan8e_cut"
  (fn _ => [ (fast_tac (cds [zan8e_red_props']) 1) ]) ;

val zan8esn = [zan8e_red_props_pc, zan8ewfdt] MRS all_sn3_pc ;

