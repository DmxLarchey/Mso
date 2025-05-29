
(*
set show_sorts ;
reset show_sorts ;
*)

structure cgdef = struct val thy = the_context () end ;
val _ = use_legacy_bindings cgdef.thy ;

val cpocE = tacsthm [etac cpoc2.elims 2, etac cpocfg.elims 3,
  ALLGOALS (safe_asm_full_simp_tac (simpset ())), Safe_tac] cpoc.elims ;

val cpoc_intrs as [cpoc_crelI, cpoc_symI] = 
  [cpocfg.intros, cpoc2.intros] RL cpoc.intros ;

AddSIs [cpoc2.intros] ;
AddSIs [cpoc_crelI] ; (* safe if symo irreflexive *)
AddSEs [cpoc_symI] ; 
AddSEs cpoc.intros ;

val _ = qed_goalw_spec_mp "cpoc_mono" cgdef.thy [mono_def] 
  "mono crel --> mono (cpoc symo crel)"
  (fn _ => [ Safe_tac, (etac cpocE 1), Auto_tac ]) ;

val _ = qed_goal "cpoc2_oneup" cgdef.thy 
  "cpoc2 crel r = oneup (crel r)" 
  (fn _ => [ (force_tac (ces [cpoc2.elims, oneup.elims], simpset ()) 1)]) ;

val _ = qed_goalw_spec_mp "wf_cpoc2" cgdef.thy [wf_der_def]
  "wf r --> wf_der crel --> wf (cpoc2 crel r)"
  (fn _ => [ (strip_tac 1), (force_tac (cesimps [cpoc2_oneup, wf1up]) 1) ]) ;

val _ = qed_goal "cpoc_eq" cgdef.thy 
  "cpoc symo crel r = (cpocfg symo Un cpoc2 crel r)"
  (fn _ => [ (safe_tac (ces [cpoc.elims]))]) ;

val _ = qed_goal_spec_mp "wf_cpoc" cgdef.thy 
  "wf r --> wf_der crel --> wf symo --> wf (cpoc symo crel r)"
  (fn _ => [ (clarsimp_tac (cesimps [cpoc_eq]) 1),
    (rtac wfUn_absl 1), Clarify_tac 1, 
    (etac cpocfg.elims 1), (etac cpoc2.elims 1), Clarify_tac 1, 
    (etac wf_cpocfg 1), (eatac wf_cpoc2 1 1)]) ; 

val _ = qed_goal "gpo_cpo" cgdef.thy 
  "gpo isubt (cpoc symo crel) = cpo crel symo"
  (fn _ => [Safe_tac, 
    (etac gpo_induct 1), (etac cpocE 1),
    (ALLGOALS Clarsimp_tac), 
    (TRYALL (eresolve_tac (cpo_isubt :: cpo_eisubt :: cpo.intros)
      THEN_ALL_NEW Fast_tac)), 
    (etac cpo.induct 1), (TRYALL (dtac isubt.isubtI)),
    (TRYALL (eresolve_tac gpo_gpo2.intros THEN_ALL_NEW Fast_tac)), 
    (ALLGOALS (rtac gpocI)), (TRYALL (etac ball_match THEN' etac conjunct2)),
    (TRYALL (eresolve_tac cpoc_intrs)), (TRYALL Fast_tac) ]) ;

val _ = qed_goalw_spec_mp "gpoc_fwfN" cgdef.thy
  [wf_gpoc_fwf_def, wf_derl_fwf_def] 
  "wf_derl_fwf crel --> wf_gpoc_fwf isubt (cpoc symo crel)"
  (fn _ => [ Safe_tac, (etac cpocE 1),
    (Clarsimp_tac 1), (etac allE3 1), (etac impE 1), mp_tac 2, 
    (atac 2), (fast_tac (cis [isubt_psubt]) 1), (Clarsimp_tac 1) ]) ;
  
val _ = qed_goal_spec_mp "all_wf_cpop" cgdef.thy 
  "corl_props crel --> wf symo --> dt : wfp (cpo crel symo)"
  (fn _ => [ (strip_tac 1), (rtac all_wf_nra 1),
    (rewtac (mk_eq (gpo_cpo RS sym))),
    (rtac gpo_red_props_nrp 2), (rtac cpoc_mono 3),
    (rtac gpoc_fwfN 4), (rtac wf_cpoc 5),
    (auto_tac (cesimps [corl_props_def])) ]) ;

(* same as cpocsn, but got using results about gpo *) 
val _ = qed_goal_spec_mp "cpo_gpo_sn" cgdef.thy 
  "corl_props crel --> wf symo --> dt : wfp (ctxt (cpo crel symo))"
  (fn _ => [ (strip_tac 1), 
    (forw_inst_tac [("r", "symo")] (thin_rl RS red_cpo_eq') 1),
    (fast_simp_tac (cesimps [corl_props_def]) 1),
    (Asm_simp_tac 1), (eatac all_wf_cpop 1 1) ]) ;

