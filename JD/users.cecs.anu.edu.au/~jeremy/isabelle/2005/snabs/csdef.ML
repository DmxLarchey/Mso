
(* use results on spo ordering to prove wf of cpo ordering *)

structure csdef = struct val thy = the_context () end ;
val _ = use_legacy_bindings csdef.thy ;

AddIffs [qord_of.ffI] ;
AddSEs [qord_of.fgI] ;

val _ = qed_goalw_spec_mp "trans_qord_of" csdef.thy [trans_def]
  "trans symo --> trans (qord_of symo)"
  (fn _ => [ (fast_tac (ces [qord_of.elims]) 1) ]) ;

val _ = qed_goal_spec_mp "in_pq" csdef.thy "wf symo --> \
  \ ((Node g ts, Node f ss) : pord_of (qord_of symo)) = ((g, f) : symo)"
  (fn _ => [ (Safe_tac), (etac pord_of.elims 1), 
    (TRYALL (etac qord_of.elims)), Safe_tac, 
    (etac wf_irrefl 1), 
    (etac (wf_trancl RS wf_irrefl) 2),
    (TRYALL (fast_tac (cis [hd transitive_closure_trans]))) ]) ;

val _ = qed_goalw_spec_mp "in_pq1" csdef.thy [inv_image_def] "wf symo --> \
  \ pord_of (qord_of symo) = inv_image symo symb_of"
  (fn _ => [ (Safe_tac), (etac pord_of.elims 1), 
    (TRYALL (etac qord_of.elims)), Auto_tac, 
    (etac (wf_trancl RS wf_irrefl) 2),
    (fast_tac (cis [hd transitive_closure_trans]) 2),
    (case_tac "a" 1), (case_tac "b" 1), Auto_tac ]) ;

val _ = qed_goal_spec_mp "s_g_poc" csdef.thy 
  "wf symo --> cpoc symo screl r = s_gpoc screl (qord_of symo) r"
  (fn _ => [ (Safe_tac), (etac cpocE 1), (etac s_gpocE 3),
    (etac pord_of.elims 3), 
    (TRYALL (etac qord_of.elims)), Safe_tac, 
    (fast_tac (cis [s_gpoc.r3I]) 1), 
    (rtac s_gpoc.r2I 1), (asm_simp_tac (esimps [in_pq]) 1) ]) ;

val _ = qed_goal_spec_mp "cpo_spo" csdef.thy 
  "wf symo --> cpo crel symo = spo crel (qord_of symo)"
  (fn _ => [ Safe_tac, (etac cpo.induct 1),
    (TRYALL (eresolve_tac spo_spo2.intros THEN_ALL_NEW atac)),
    (TRYALL (rtac spo_spo2.spo2I)),
    (rtac spo_spo2.r2I 2), Fast_tac 3, 
    (asm_simp_tac (esimps [in_pq]) 2),
    (rtac spo_spo2.r3I 1), atac 2, TRYALL Fast_tac,
    (etac spo_induct 1), 
    (etac pord_of.elims 1), 
    (TRYALL (etac qord_of.elims)), Safe_tac, 
    (TRYALL (eresolve_tac cpo.intros THEN_ALL_NEW Fast_tac)) ]) ;

val _ = qed_goal_spec_mp "cpocwf'" csdef.thy 
  "spoc_props crel --> wf symo --> dt : wfp (cpo crel (symo^+))"
  (fn _ => [ Safe_tac, (dtac wf_trancl 1),
    (asm_simp_tac (esimps [cpo_spo]) 1),
    (rtac spocwf 1), (asm_simp_tac (esimps [in_pq1]) 1), atac 2, 
    (rtac trans_qord_of 1), (rtac trans_trancl 1) ]) ;

(* strong norm result for cpo got using spo *)
val _ = bind_thm ("cpocwf", cpocwf' RS mk_mono'
  (tacthm (etac r_into_trancl 1) rel_subsetI RS cpo_mono RS wfp_mono)) ;



