
structure bag = struct val thy = theory "bag" end ;
use_legacy_bindings bag.thy ;
fun u _ = use_thy "bag" ;

val colordE = mkpE colord.elims ;
val rp_exscf_def' = rewrite_rule [rp_exsf_def] rp_exscf_def;

val _ = qed_goal_spec_mp "gg_ext1" redn.thy
  "dt : gindy cuto (gindy isub sn) --> dt : gindy \
    \ (cuto Int {(t, s). ALL u. (u, t) : isub --> u : sn}) (gindy isub sn)" 
  (fn _ => [ (rtac impI 1), (rtac gindy.I 1), 
   (rtac impI 1), (etac gindyE 1), (etac mp 1), (etac all_match 1),
   Safe_tac, (fast_tac (cis [gindy.I]) 1)]) ;

val _ = qed_goal_spec_mp "gg_ext2" redn.thy
  "dt : gindy cuto (gindy isub sn) --> dt : gindy \
    \ (cuto Int {(t, s). ALL u. (u, s) : isub --> u : sn}) (gindy isub sn)" 
  (fn _ => [ (rtac impI 1), (rtac gindy.I 1), 
   (rtac impI 1), (etac gindyE 1), (rtac gindy_Ialt 1), (strip_tac 1),
   (etac mp 1), (etac all_match 1), Safe_tac]) ;

(* would like to use the above to get
  x : gbars (isub^* O cuto) (gindy isub (wfp rho))
  to use in conjunction with below *)

val () = qed_goalw_spec_mp "col_colord" bag.thy [trans_def]
  "trans col --> colord to col O col <= colord to col"
  (fn _ => [ Safe_tac, (etac colordE 1), (rtac colord.I 1), Fast_tac 1]) ;

val () = qed_goal_spec_mp "dth_dti_col" bag.thy 
  "trans col --> rp_exscf isub rho to col dt --> \
    \ dt : gindy (colord to col) (gindy isub (wfp rho))" 
  (fn _ => [ (strip_tac 1), (rtac dth_dti_gbsnf 1),
    (rewrite_goals_tac [rp_exscf_def', red_props_gbscf_def']),
    (REPEAT (eresolve_tac [all_forward, imp_forward] 1)),
    (safe_tac (ces [gbars_mono'] addSIs [colord.I])), 
    (datac transD 2 1), Fast_tac 1]) ;

(*
val _ = qed_goal_spec_mp "glues_all" bag.thy
  "wf so --> wf isub --> All (rp_gluescf rho isub so) --> \
    \ glues isub (wfp rho) {y. (y, x) : isub^*}"
  (fn _ => [ (strip_tac 1), 
    (eres_inst_tac [("P", "glues isub (wfp rho)")] wf_induct 1),
    (simp_tac (esimps [glues_def]) 1), (strip_tac 1), 
    (res_inst_tac [("r", "isub")] gindy_gbars' 1),
    (etac gbars_mono' 1), Safe_tac, 
    (rtac gindy.I 1), (rewtac rp_gluescf_def),
    (etac allE 1 THEN rtac impI 1 THEN mp_tac 1),
    (rtac wfp.wfpI 1), (strip_tac 1), 
    (rewtac rp_gluesf_def),
    (etac allE 1 THEN mp_tac 1), Safe_tac, 
    (* unfortunately this does not follow *)
    (subgoal_tac "glues isub (wfp rho) G" 1),
    (rewtac glues_def),
    (etac allE 1 THEN eatac mp 1 1) ]) ;
*)


