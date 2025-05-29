
structure jglns = struct val thy = theory "jglns" end ;
use_legacy_bindings jglns.thy ;
fun u _ = use_thy "jglns" ;

val red_props_jglh_def' =
  rewrite_rule [red_props_jglhf_def] red_props_jglh_def;

(* wlog brti contains tri Un trio *)

val _ = qed_goalw_spec_mp "jgl15f_mono" jglns.thy [jgl15f_def]
  "jgl15f btri1 sub1 sn dt --> \
    \ sub1 <= sub2 --> btri2 <= btri1 --> \
    \ jgl15f btri2 sub2 sn dt"
  (fn _ => [ Clarify_tac 1, etac impE 1, Auto_tac]) ;

val _ = qed_goalw_spec_mp "jgl14f_mono" jglns.thy [jgl14f_def]
  "jgl14f cuto1 trio isub1 rho1 dt --> \
    \ cuto2 <= cuto1 --> isub1 <= isub2 --> rho1 <= rho2 --> \
    \ jgl14f cuto2 trio isub2 rho2 dt"
  (fn _ => [ (REPEAT (rtac impI 1 ORELSE etac all_match 1)),
    (REPEAT (etac impE 1 THEN Fast_tac 1)),
    (etac disj_forward 1), (etac (mk_mono' rel_comp_mono) 2),
    (TRYALL (resolve_tac [Un_mono, rtrancl_mono])), Auto_tac]) ;

val _ = qed_goalw_spec_mp "jgl15_ext" jglns.thy [jgl15f_def]
  "jgl15f btri sub sn dt --> jgl15f (btri Un sub) sub sn dt" fn_ft1 ;

val _ = qed_goalw_spec_mp "gbs_Un" jglns.thy [red_props_gbsf_def]
  "red_props_gbsf (rho1 Un rho2) isub cuto S dt = \
    \(red_props_gbsf rho1 isub cuto S dt & red_props_gbsf rho2 isub cuto S dt)"
  fn_ft1 ;
  
val _ = bind_thm ("gbs_mono", prove_goalw jglns.thy [red_props_gbsf_def]
  "r2 <= r1 --> s2 <= s1 --> c1 <= c2 --> S1 <= S2 --> \
    \ red_props_gbsf r1 s1 c1 S1 dt --> red_props_gbsf r2 s2 c2 S2 dt"
  (fn _ => [ Safe_tac, (etac allE 1), (etac impE 1), 
    (etac gbars_mono' 2), Auto_tac]) RS mp RS mp RS mp RS mp) ;

val gbs_mono' = mk_mono' gbs_mono ;

val () = qed_goal_spec_mp "jglhf_gbs" jglns.thy 
  "(ALL u. (u, dt) : btri --> u : wfp rho1) --> \
    \ red_props_gbsf rho2 isub cuto {dts. (dts, dt) : btri O rho1^*} dt --> \
    \ red_props_gbsf rho2 isub cuto (wfp rho1) dt"
  (fn _ => [ (fast_tac (ces [gbs_mono', wfp_red]) 1) ]) ;

val () = qed_goalw_spec_mp "gbs_triv" jglns.thy [red_props_gbsf_def]
  "(ALL u. (u, dt) : trio --> u : S) --> \
    \ red_props_gbsf trio isub cuto S dt" fn_ft1 ;

val () = qed_goal_spec_mp "jglhf_gbs_ext'" jglns.thy 
  "(ALL u. (u, dt) : (btri Un trio) --> u : wfp (rho Un trio)) --> \
    \ red_props_gbsf rho isub cuto {dts. (dts, dt) : btri O rho^*} dt --> \
    \ red_props_gbsf (rho Un trio) isub cuto (wfp (rho Un trio)) dt"
  (fn _ => [ (safe_tac (cis [gbs_Un RS iffD2])), 
    (rtac gbs_triv 2), (rtac jglhf_gbs 1), (etac gbs_mono' 2),
    (TRYALL (fast_tac 
      (claset_of Set.thy addSEs [rel_comp_mono', rtrancl_mono']))) ]) ;

val jglhf_gbs_ext = full_simplify (HOL_ss addsimps [Un_assoc]) 
  (read_instantiate [("btri", "btri Un isub")] jglhf_gbs_ext') ;
    
val jglh_btlem = prove_goalw jglns.thy [jgl15f_def]
  "(ALL u. (u, dt) : isub --> u : wfp rho) --> \
    \ jgl15f btri isub (wfp rho) dt --> \
    \ (ALL u. (u, dt) : btri Un isub --> u : wfp rho)" fn_ft1 RS mp RS mp ;

val jglh_btlem1 = jglh_btlem RS (jglhf_gbars RSN (2, jglhf_gbs_ext)) ;

val gbarsI' = tacsthm [etac asm_rl 3, 
  etac conjE 2, eatac gbars.gbarsI 1 2] disjE ;

val _ = qed_goalw_spec_mp "jglh_btlem2" jglns.thy 
  [red_props_gbsf_def, jgl14f_def]
  "(ALL u. (u, dt) : isub Un trio --> u : wfp rho) --> \
    \ (jgl14f cuto trio isub rho dt) --> \
    \ red_props_gbsf rho isub cuto (wfp rho) dt --> \
    \ red_props_gbsf rho (isub Un trio) cuto (wfp rho) dt"
  (fn _ => [ (REPEAT (rtac impI 1)), 
    (etac all_match 1 THEN rtac impI 1 THEN mp_tac 1),
    (etac gbars.induct 1), (etac gbars.inI 2),
    (rtac gbarsI' 1), Safe_tac, Fast_tac 1,
    (etac allE2 1), (REPEAT (mp_tac 1)), (etac disjE 1), Fast_tac 1,
    (etac rel_compEpair 1), (etac allE 1 THEN mp_tac 1),
    (datac wfp_red 1 1), (etac notE 1), (etac gbars.inI 1) ]) ;

val jstm = "wf isub --> \
    \ (ALL dt. red_props_jglh isub {dts. (dts, dt) : (btri Un isub O rho^*)} \
      \ rho cuto dt) --> \
    \ (jgl14f cuto trio isub rho s) --> \
    \ (jgl15f btri (isub Un trio) (wfp (rho Un trio)) s) --> \
  \ red_props_gbscf (rho Un trio) (isub Un trio) cuto (wfp (rho Un trio)) s" ;

val _ = bind_thm ("jglh_sn", 
  prove_goalw jglns.thy [red_props_gbscf_def] jstm
  (fn _ => [ (strip_tac 1), (rtac jglh_btlem2 1), 
    (rtac jglh_btlem1 3), (TRYALL atac), (etac jgl14f_mono 1), 
    (rewtac red_props_jglh_def), (dtac spec 4 THEN etac mp 4), 
    (etac all_match 4 THEN fast_tac (ces [wfp_mono']) 4), 
    (TRYALL Fast_tac) ])) ;

val jsth1 = read_instantiate_sg (sign_of jglns.thy) [("P", "%s. "^jstm)] allI ;
val jsth2 = tacthm (rtac jglh_sn 1) jsth1 ;
val all_dist = rewrite_rule [atomize_all] (transfer jglns.thy all_mono) ;

fun f th = 
  let val thn = th RS mp handle _ => th RS all_dist ;
  in f thn end 
  handle _ => th ;

val jsth3 = standard (full_simplify (simpset ()) (f jsth2)) ;

(* in the following, our rho is > Un |>o of the paper *)
  
val dth_dti_jglh_sn = standard (meta_std jglh_sn RS dth_dti_gbsnf) ;

val _ = qed_goal_spec_mp "dth_dti_jglh_sn_all" jglns.thy 
  "?P --> ?Q --> ?R --> ?S --> (ALL dt. dt : ?T)"
  (fn _ => [ (REPEAT (rtac impI 1)), 
    (eatac all_match2 1 1), (etac thin_rl 1),
    (etac dth_dti_jglh_sn 1), (REPEAT (atac 1)) ]) ;

val jglh_gindy_all = jsth3 RS all_gindy_gbsnf ;
val jglh_gindy_all_check = rewrite_rule [red_props_jglh_def',
  jgl14f_def, jgl15f_def, gjglf_def] jglh_gindy_all ;

val _ = qed_goalw_spec_mp "bars_ext13" jglns.thy [jgl13f_def]
  "s : gindy (isub Un trio) (wfp rho) --> \
    \ (jgl13f isub trio rho s) --> s : gindy isub (wfp rho)"
  (fn _ => [ (Safe_tac), (etac gindyE 1), (rtac gindy.I 1),
    (rtac impI 1), (etac mp 1), (eatac all_match2 1 1),
    (Clarify_tac 1), (etac wfp_red 1), Fast_tac 1]) ;

val _ = qed_goalw "wfhns" jglns.thy [gjglf_def] "wf isub --> \
    \ (ALL dt. red_props_jglh isub {dts. (dts, dt) : (btri Un isub O rho^*)} \
      \ rho cuto dt) --> \
    \ (ALL s. jgl14f cuto trio isub rho s) --> \
    \ (ALL s. jgl15f btri (isub Un trio) (wfp (rho Un trio)) s) --> \
    \ (ALL s. jgl13f isub trio (rho Un trio) s) --> \
    \ (ALL s. gjglf (isub Un trio) cuto (wfp (rho Un trio)) s) --> \
    \ s : wfp (rho Un trio)"
  (fn _ => [ Safe_tac, (rtac gindy_bars' 1), 
    (rtac wfp_le_bars' 1), (etac wf_ssI 1),
    (rtac (jglh_gindy_all RS bars_ext13) 1),
    (TRYALL (etac spec ORELSE' atac)) ]) ;

val wfhns_check' = meta_std (rewrite_rule [red_props_jglh_def',
  jgl13f_def, jgl14f_def, jgl15f_def, gjglf_def] wfhns) ;

val wfhns_check = tacsthm [ (rtac (impI RS all_mono RS mp) 6), 
  (etac (Un_upper1 RS bars_redundant) 6) ] wfhns_check' ;

