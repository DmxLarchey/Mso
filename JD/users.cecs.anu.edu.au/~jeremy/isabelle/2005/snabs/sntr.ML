
structure sntr = struct val thy = theory "sntr" ;
  val ipt_mk_cases = InductivePackage.the_mk_cases thy ; end ;
use_legacy_bindings sntr.thy ;
fun u _ = use_thy "sntr" ;

open symbwf_class ; (* for wf_symborder *)

val prp_mk_cases = sntr.ipt_mk_cases "sntr.prp" ;

val prp2allE = mkpE prp2all.elims ;
val prp2allD = tacthm (atac 2) prp2allE ;
val prp2E = mkpE prp2.elims ;
val prp2all_spec = subt_refl RSN (2, prp2allD RS spec RS mp) ;
val prsE = mkpE prs.elims ;
val prpE = mkpE prp.elims ;
val prp2E' = tacthm (etac prsE 2) prp2E ;

val () = qed_goal "dtorder_def'" sntr.thy 
  "dtorder = cutorder Un sn1order ruleredn"
  (fn _ => [ (auto_tac (cesimps [dtorder.defs]))]) ;

val dtorder_def = mk_eq dtorder_def' ;

val _ = qed_goalw "dtjgl_gjgl" sntr.thy [gjgl_def', dtjgl_def]
  "dtjgl rho cuto = gjgl isubt ((cuto Un sn1order rho)^+) (wfp (ctxt rho))"
  (fn _ => [ (cong_tac 1), (rtac ext 1), (cong_tac 1), (rtac set_ext 1), 
    (auto_tac (cesimps [snHered_def, isubts_iff, gindy_def]))]) ;

val _ = bind_thm ("wf_dtjgl", wf_trancl RS wf_gjgl RS (dtjgl_gjgl RS iffD2)) ;

(** red_props - if red_props holds, ie ruleredn implies prp,
  then ctxt ruleredn implies prp - specifically, this depends
  on ruleredn implying prp for all subtrees **)

val prpD = meta_std (tacthm (atac 2) 
  (prp_mk_cases "(dtn, dt) : prp rho cuto")) ;

val prp_def = mk_eq (tacsthm [etac prp.prpI 2, fast_tac (cds [prpD]) 1] iffI) ;

val _ = qed_goalw_spec_mp "prp_psubt" sntr.thy [psubt_def]
  "(dtn, dt) : psubt O ctxt rho --> (dtn, dt) : prp rho cuto"
  (fn _ => [ Safe_tac, (dtac converse_tranclD 1), (Clarify_tac 1),
    (rtac prp.prpI 1), Safe_tac, 
    (full_simp_tac (esimps [symmetric subt_def']) 1),
    (dtac subsetD 1), (Simp_tac 1), (datac subt_sn 1 1),
    (datac (r_into_rtrancl RS sn_red) 1 1), (eatac subt_sn 1 1)]) ;

val _ = qed_goal_spec_mp "prp_subt" sntr.thy 
  "(dtn, dt) : prp rho cuto --> (dts, dtn) : subt --> (dts, dt) : prp rho cuto"
  (fn _ => [Safe_tac, (etac prp.elims 1), (rtac prp.prpI 1),
    (safe_tac csp), (etac allE 1), (etac impE 1), (eatac mp 1 2),
    (rewtac subt_def'), (eatac rtrancl_trans 1 1)]) ;

val _ = qed_goal_spec_mp "prp_red'" sntr.thy 
  "(ALL dt' dtn'. (dt', dt) : subt --> (dtn', dtn) : subt --> \
    \ (dtn', dt') : rho --> (dtn', dt') : prp rho cuto) --> \
    \ (dtn, dt) : ctxt rho --> (dtn, dt) : prp rho cuto"
  (fn _ => [ strip_tac 1, 
    (etac ron.elim' 1), Fast_tac 2, 
    (rtac prp.prpI 1), (safe_tac csp), (etac thin_rl 1), 
    (datac nured_sn 1 1), (rewtac subt_def), (safe_tac csp), (Force_tac 2),
    (dtac (sn1o_nured') 1), (rewtac nured_def),
    (etac oneup.elims 1), (rewtac psubt_def),
    (dtac converse_tranclD 1), (Clarify_tac 1), (rtac subt_sn 1),
    (simp_tac (esimps [subt_def']) 2), Force_tac 1]) ;

val _ = qed_goalw_spec_mp "prp_red2" sntr.thy [subt_def]
  "?P --> (dtn, dt) : subt O ctxt rho --> (dtn, dt) : prp rho cuto"
  (fn _ => [ Safe_tac, (rtac prp_psubt 1), 
    (eatac prp_red' 1 2), Fast_tac 1]) ;

val _ = qed_goal_spec_mp "prp_red3" sntr.thy 
  "rho <= prp rho cuto --> ctxt rho <= prp rho cuto"
  (fn _ => [ Safe_tac, (rtac prp_red2 1), Auto_tac]) ;

val _ = qed_goal_spec_mp "prp_red_same" sntr.thy 
  "prp (ctxt rho) cuto = prp rho cuto"
  (fn _ => [ Safe_tac, rewtac prp_def, Auto_tac]) ;

(* if ruleredn satisfies the conditions for rewr_ok_dt_alt,
  then so does ctxt ruleredn *)
val _ = qed_goal_spec_mp "prp_red" sntr.thy 
  "rho <= prp rho cuto --> ctxt rho <= prp (ctxt rho) cuto"
  (fn _ => [ (auto_tac (cds [prp_red3], esimps [prp_red_same])) ]) ;

(* setting cuto to rho O subt automatically satisfies the prp reqt *)
val _ = qed_goal_spec_mp "prp_rho_subt" sntr.thy 
  "rho <= prp rho (rho O subt)" 
  (fn _ => [ Safe_tac, rewtac prp_def, Auto_tac]) ;

(* link between Conditions 1 and 2 of paper *)
val _ = qed_goal "prp2all_prp" sntr.thy "prp2all rho cuto <= prp rho cuto"
  (fn _ => [ (safe_tac (ces [prp2allE])), (rtac prp.prpI 1),
    (etac all_match 1), (safe_tac (ces [prp2E, prsE])),
    (etac subt_snr 1 THEN etac sn_red 1),
    (force_tac (ces [subt_snr], esimps [p_iOs RS sym]) 1)]) ;

val _ = qed_goalw "dt12" sntr.thy [dtorder_def]
  "dtorder <= cutorder Un sn2order ruleredn" (fn _ => [ rtac dt12' 1 ]) ;
val wf_dt12 = dt12 RSN (2, wf_subset) ;
val wf_dt12' = Conv.rewr [Un_commute] wf_dt12 ;
val SOME wf_cus12' = let open Conv in 
  CONV_RULE (PREMS_CONV (TDSTOP_CONV (eqc [Un_commute]))) wf_cus12 end ;

(* snHered *)
val _ = qed_goalw "snHered_gindy" sntr.thy [snHered_def, meta_eq_def, gindy_def]
  "snHered r dt == (dt : gindy isubt (wfp (ctxt r)))" fn_at ;

val _ = qed_goalw "snHered_gindy'" sntr.thy [meta_eq_def]
  "Collect (snHered r) == gindy isubt (wfp (ctxt r))" 
  (fn _ => [ (auto_tac (cesimps [snHered_gindy])) ]) ;

val () = qed_goalw_spec_mp "sn_snH" sntr.thy [snHered_def]
  "dt : wfp (ctxt r) --> snHered r dt" (fn _ => [Auto_tac]) ;

val () = qed_goalw_spec_mp "hereds_sn" sntr.thy [snHered_gindy]
  "(ALL dts. (dts, dt) : subt --> snHered r dts) = (dt : wfp (ctxt r))"
  (fn _ => [ rtac iffI 1, 
    (rtac (transfer sntr.thy wfp_isubt RS gindy_all) 1), 
    (force_tac (cesimps [subt_def']) 1),
    (safe_tac (cis [gindy.intros])), (eatac subt_sn 1 1) ]) ;

val hereds_sn' = hereds_sn RS iffD1 ;

