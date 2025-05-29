
structure gpodef = struct val thy = the_context () end ;
val _ = use_legacy_bindings gpodef.thy ;
AddSEs [gpo_gpo2.subtI] ;
val [gpocI] = gpo_gpo2.intros RL [gpo_gpo2.gpo2I] ;
val gpo_elim = tacthm (eresolve_tac gpo_gpo2.elims 2) (hd gpo_gpo2.elims) ;
val gpo_induct = rotate_prems ~1 
  (tacthm (chop_tac 1 (atac 2)) gpo_gpo2.induct RS conjunct1 RS mp) ;

val _ = qed_goal_spec_mp "isubt_gpo" gpodef.thy "s : wfp vtl --> \
    \ (t, s) : gpo vtl crel --> (ti, t) : vtl --> (ti, s) : gpo vtl crel" 
  (fn _ => [ (rtac impI 1), (etac wfp.induct 1), Safe_tac,
    (etac gpo_elim 1), Safe_tac, Fast_tac 1, 
    (etac gpo_gpo2.esubtI 1), (etac gpo_gpo2.subtI 1), 
    (etac allE 1), mp_tac 1, Clarify_tac 1,
    (eatac gpo_gpo2.esubtI 1 1)]) ; 

val _ = qed_goal_spec_mp "subt_gpo" gpodef.thy "s : wfp vtl --> \
    \ (ti, t) : vtl^* --> (t, s) : gpo vtl crel --> (ti, s) : gpo vtl crel"
  (fn _ => [ Safe_tac, (etac converse_rtrancl_induct 1),
    atac 1, (eatac isubt_gpo 2 1) ]) ;

(* lemmas for alternative proof *)

val _ = qed_goal_spec_mp "subt_gpo'" gpodef.thy 
  "(si, s) : vtl^* --> (t, si) : gpo vtl crel --> (t, s) : gpo vtl crel"
  (fn _ => [ Safe_tac, (etac rtrancl_induct 1),
    atac 1, (eatac gpo_gpo2.esubtI 1 1) ]) ;

val _ = qed_goal_spec_mp "psubt_gpo" gpodef.thy 
  "(si, s) : vtl^+ --> (si, s) : gpo vtl crel"
  (fn _ => [ (rtac impI 1), (etac trancl_induct 1),
    (etac gpo_gpo2.subtI 1), (eatac gpo_gpo2.esubtI 1 1) ]) ;
  
AddSEs [psubt_gpo] ;

val _ = qed_goalw_spec_mp "gpo_red_props_nrp" gpodef.thy [red_props_nra_def']
  "wf vtl --> mono crel --> wf_gpoc_fwf vtl crel --> \
    \ red_props_nra vtl (gpo vtl crel) (crel (fwf (gpo vtl crel)))"
  (fn _ => [ (Clarify_tac 1), (dtac wf_ssI 1), (datac subt_gpo 2 1), 
    (thin_tac "(dtn, dt) : gpo vtl ?c" 1), 
    (etac gpo_elim 1), (dtac monoD 1), (datac subsetD 1 2), atac 1,
    Safe_tac, (force_tac (cesimps [wf_gpoc_fwf_def]) 1),
    (ALLGOALS (rtac rel_compI)), Auto_tac ]) ;

val _ = qed_goal_spec_mp "gpocwf" gpodef.thy 
  "wf vtl --> gpoc_props vtl crel --> dt : wfp (gpo vtl crel)"
  (fn _ => [ (Clarify_tac 1), (rtac all_gjgl_nra 1), atac 1,
    (rtac gpo_red_props_nrp 1), (rtac wf_gjgl 4), (rtac wf_der_fwf 4),
    (rewtac gpoc_props_def), Auto_tac]) ; 


(* 
set show_sorts ;
reset show_sorts ;
*)




