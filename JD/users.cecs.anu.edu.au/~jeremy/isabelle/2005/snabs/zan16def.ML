
structure zan16def = struct val thy = theory "zan16def" end ;
use_legacy_bindings zan16def.thy ;

(* proof of termination of example on 
  Zantema, The Termination Hierarchy for Term Rewriting, Prop'n 16 *)

structure z16rn = struct
  open zan16_ruleredn ;
  val intros' = map (simplify (esimps [])) intros ;
  end ;

structure z16c = struct
  open zan16_cut ;
  val intros' = map (simplify (esimps [])) intros ;
  val elims' = full_simplify (esimps []) elims ;
  end ;

val z16_cs = claset () addSIs z16c.intros' addSEs [z16c.elims'] ;

AddIffs (z16c.intros' @ z16rn.intros') ;

val _ = qed_goal "zan16wfcut" zan16def.thy "wf (zan16_cut)"
  (fn _ => [
    (res_inst_tac [("n", "Suc (Suc (Suc (Suc 0)))")] wf_lim_comp 1),
    (clarsimp_tac (cis [equals0I], simpset ()) 1),
    (safe_tac (ces [z16c.elims']))]) ;

val _ = qed_goal "zan16wfdt" zan16def.thy 
  "wf (zan16_cut Un sn1order zan16_ruleredn)"
  (fn _ => [ (rtac wfUn_absr 1), 
    (rtac wf_sn1order 2), (rtac zan16wfcut 2), Safe_tac, 
    (dtac (sn1o_nured') 1), 
    (rewrite_goals_tac [nured_def]),
    (safe_tac (z16_cs addSEs oo_elims)),
    (safe_tac (z16_cs addSEs (z16rn.elims :: ron.elim :: oo_elims))),
    Auto_tac]) ;

val _ = qed_goalw_spec_mp "zan16_red_props" zan16def.thy [subt_def, psubt_def]
  "(dtn, dt) : zan16_ruleredn --> (dts, dtn) : subt --> \
    \ (dts, dt) : psubt Un zan16_cut Un (nured zan16_ruleredn)^+"
  (fn _ => [ strip_tac 1, (etac zan16_ruleredn.elims 1),
    (safe_tac csp), (ALLGOALS Full_simp_tac),
    (safe_tac (ces [isubt_tranclE])), 
    (* deal with cases involving isubt^+ *) 
    (TRYALL (tranclI_tac)), (* for mosml *)
    (TRYALL ((DETERM o etac notE) THEN' tranclI_tac)),
    (* now using nured ruleredn, using psubt rules for ruleredn *)
    (* mosml version first *)
    (TRYALL (EVERY' [ (DETERM o etac notE), 
      (rtac r_into_trancl), (SELECT_GOAL (rewtac nured_def)),
      (rtac oneup.ouI), Clarify_tac, (rtac ron.red_cutI), 
      (resolve_tac z16rn.intros')])),
    (TRYALL (EVERY' [ (DETERM o chop_tac 1 o etac notE), 
      (rtac r_into_trancl), (SELECT_GOAL (rewtac nured_def)),
      (rtac oneup.ouI), Clarify_tac, (rtac ron.red_cutI), 
      (resolve_tac z16rn.intros')])) ]) ;

val _ = qed_goalw_spec_mp "zan16_red_props_c" zan16def.thy [red_props_c_def]
  "red_props_c zan16_ruleredn zan16_cut"
  (fn _ => [ (fast_tac (cds [zan16_red_props RS UnI1]) 1) ]) ;

val zan16sn = [zan16_red_props_c, zan16wfdt] MRS all_sn3_c ;

