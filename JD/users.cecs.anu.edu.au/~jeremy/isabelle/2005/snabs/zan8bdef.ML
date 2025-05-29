
structure zan8bdef = struct val thy = theory "zan8bdef" end ;
use_legacy_bindings zan8bdef.thy ;

(* proof of termination of second example on 
  Zantema, The Termination Hierarchy for Term Rewriting, p8 *)

val z8b_cs = claset () addSIs zan8b_cut.intros addSEs [zan8b_cut.elims] ;

structure z8brn = struct
  open zan8b_ruleredn ;
  val intros' = map (simplify (esimps [])) intros ;
  end ;

AddIffs (zan8b_cut.intros @ z8brn.intros') ;

val _ = qed_goal "zan8bwfcut" zan8bdef.thy "wf (zan8b_cut)"
  (fn _ => [
    (res_inst_tac [("n", "Suc (Suc (Suc (Suc 0)))")] wf_lim_comp 1),
    (clarsimp_tac (cis [equals0I], simpset ()) 1),
    (auto_tac (ces [zan8b_cut.elims], simpset ()))]) ;

val _ = qed_goal "zan8bwfdt" zan8bdef.thy 
  "wf (zan8b_cut Un sn1order zan8b_ruleredn)"
  (fn _ => [ (rtac wfUn_absr 1), 
    (rtac wf_sn1order 2), (rtac zan8bwfcut 2), Safe_tac, 
    (dtac (sn1o_nured') 1), 
    (rewrite_goals_tac [nured_def]),
    (safe_tac (z8b_cs addSEs oo_elims)),
    (safe_tac (z8b_cs addSEs [z8brn.elims, oneup.elims, ron.elim])),
    Auto_tac]) ;

(* this examples requires the most general form of red_props *)
val _ = qed_goalw_spec_mp "zan8b_red_props" zan8bdef.thy [subt_def, psubt_def]
  "(dtn, dt) : zan8b_ruleredn --> (dts, dtn) : subt --> \
    \ (dts, dt) : psubt Un zan8b_cut Un (nured zan8b_ruleredn)^+ Un X"
  (fn _ => [ strip_tac 1, (etac z8brn.elims 1),
    (safe_tac csp), (ALLGOALS Full_simp_tac),
    (safe_tac (ces [isubt_tranclE])),
    (rewrite_goals_tac [nured_def]),
    (fast_tac (cis [r_into_trancl, ron.red_cutI]) 1),
    (TRYALL (tranclI_tac)),  (* for mosml *)
    (TRYALL (etac notE THEN' tranclI_tac)) ]) ;
    
val _ = qed_goalw_spec_mp "zan8b_red_props_c" zan8bdef.thy [red_props_c_def]
  "red_props_c zan8b_ruleredn zan8b_cut"
  (fn _ => [ (fast_tac (cds [zan8b_red_props]) 1) ]) ;

val zan8bsn = [zan8b_red_props_c, zan8bwfdt] MRS all_sn3_c ;

    
