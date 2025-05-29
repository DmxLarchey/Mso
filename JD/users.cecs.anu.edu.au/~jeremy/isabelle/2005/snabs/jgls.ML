
structure jgls = struct val thy = theory "jgls" end ;
use_legacy_bindings jgls.thy ;
fun u _ = use_thy "jgls" ;

val phisigE = mkpE phisig.elims ;

(* use dth_dti_jglh_sn unchanged from jglns.ML *)

val jgl4sfD = meta_std (jgl4sf_def RS def_imp_eq RS fun_cong RS iffD1) ;

val _ = qed_goal_spec_mp "gindy_some" jgls.thy
  "?P --> ?Q --> ?R --> ?S --> ?T --> ?U --> \
    \ (ALL t.  (t :: 'a, s :: 'a) : sig --> \
      \ t : (gindy (isub Un trio) (wfp (rho Un trio))))"
  (fn _ => [ (strip_tac 1), (rtac gindy_bars' 1),
    (eatac jgl4sfD 2 1), (eatac dth_dti_jglh_sn_all 3 1)]) ;

(* analogous to bars_ext13 in case without substitutions *)
val _ = qed_goalw_spec_mp "ext13sub" jgls.thy [jgl13sf_def]
  "(jgl13sf sig isub trio rho s) --> \
    \ t : gindy (isub Un trio) (wfp rho) --> (t, s) : sig --> \
    \ (ALL v. (v, s) : isub O sig --> v : wfp rho) --> t : wfp rho"
  (fn _ => [ (Safe_tac), (etac gindyE 1), 
    (etac allE 1 THEN mp_tac 1), (etac disjE 1 THEN atac 1),
    (etac mp 1), (etac all_match 1 THEN rtac impI 1 THEN mp_tac 1),
    (etac disjE 1 THEN atac 1), (etac rel_compEpair 1),
    (etac allE 1 THEN mp_tac 1), (eatac wfp_red 1 1)]) ;

val _ = qed_goal_spec_mp "ext13_subs_wf" jgls.thy 
  "(jgl13sf sig isub trio rho s) --> \
    \ (ALL t. (t, s) : sig --> t : gindy (isub Un trio) (wfp rho)) --> \
    \ s : gindy isub (subs_wf sig rho)"
  (fn _ => [ (safe_tac (cis [gindy.I, subs_wf.I])), 
    (etac allE 1), mp_tac 1,
    (eatac ext13sub 2 1), (force_tac (cesimps [subs_wf_def]) 1) ]) ;

val _ = qed_goal_spec_mp "gindy_subs_wf" jgls.thy 
  "?P --> ?Q --> ?R --> ?S --> ?T --> ?U --> \
    \ s : gindy isub (subs_wf sig (rho Un trio))"
  (fn _ => [ Safe_tac, (rtac gindy_Ialt 1), (rtac impI 1), 
    (etac ext13_subs_wf 1), Safe_tac, 
    (etac gindy_some 1), (REPEAT (atac 2)), 
    (force_tac (cesimps [subs_wf_def]) 1) ]) ;

(* old version 
val _ = qed_goal_spec_mp "gindy_subs_wf" jgls.thy 
  "?P --> ?Q --> ?R --> ?S --> ?T --> ?U --> \
    \ s : gindy isub (subs_wf sig (rho Un trio))"
  (fn _ => [ (safe_tac (cis [gindy.I, subs_wf.I])), 
    (subgoal_tac "ALL v. (v, s) : isub O sig --> v : wfp (rho Un trio)" 1), 
    (etac ext13sub 1), atac 2, 
    (etac gindy_some 1), (REPEAT (atac 2)), (atac 1), 
    (Clarify_tac 1), (etac allE 1 THEN mp_tac 1),
    (etac subs_wfE 1), (etac allE 1 THEN mp_tac 1), atac 1]) ;
*)

val _ = qed_goal_spec_mp "sub_wfp" jgls.thy 
  "?P --> ?Q --> ?R --> ?S --> ?T --> ?U --> \
    \ Id <= (sig :: 'a relation) --> s : wfp (rho Un trio :: 'a relation)"
  (fn _ => [ Safe_tac, 
    (subgoal_tac "s : subs_wf sig (rho Un trio)" 1),
    (rtac gindy_wfp' 2), (rtac gindy_subs_wf 3),
    (REPEAT (atac 3 ORELSE eres_inst_tac [("x", "dts")] spec 3)),
    (etac wf_ssI 2), (etac subs_wfE 1), (dtac subsetD 1), (rtac IdI 1),
    (etac allE 1 THEN eatac mp 1 1)]) ;


