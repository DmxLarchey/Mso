
structure gensubs = struct val thy = theory "gensubs" end ;
use_legacy_bindings gensubs.thy ;
fun u _ = use_thy "gensubs" ;

val exsubE = mkpE exsub.elims ;
val allsubsE = mkpE allsubs.elims ;
val exsub_O = tacthm (eatac rel_compI 1 2) exsubE ;
val allsubs_def = rewrite_rule [mk_eq lfp_const] allsubs.defs ;
val exsub_def = rewrite_rule [mk_eq lfp_const] exsub.defs ;

val _ = qed_goal "exsub_eqO" gensubs.thy "exsub sub r = sub O r"
  (fn _ => [ Safe_tac, (eatac exsub.I 1 2), (etac exsubE 1), Fast_tac 1]) ;

(*
val _ = bind_thm ("allsubs_def", mk_eq (prove_goal gensubs.thy
  "((r, l) : allsubs sub rho) = ?P"
  (fn _ => [ (rtac iffI 1), 
    etac allsubs.I 2, etac allsubs.elims 1, Auto_tac]))) ;
*)

val _ = qed_goalw_spec_mp "allsubs_mono" gensubs.thy [allsubs_def] 
  "subb <= suba --> r <= s --> allsubs suba r <= allsubs subb s"
  (fn _ => [Auto_tac, (TRYALL (fast_tac (cds [subsetD])))]) ;

val _ = qed_goalw_spec_mp "allsubs_Int" gensubs.thy [allsubs_def] 
  "allsubs sub (r Int s) = allsubs sub r Int allsubs sub s" 
  (fn _ => [Auto_tac]) ;

val _ = qed_goalw_spec_mp "allsubs_le" gensubs.thy [allsubs_def] 
  "allsubs (subt) r <= r" (fn _ => [Auto_tac]) ;

val _ = qed_goalw_spec_mp "allsubs_subt" gensubs.thy [allsubs_def] 
  "allsubs subt subt = subt" (fn _ => [Auto_tac, (eatac subt_thms.sss 1 1)]) ;

val _ = qed_goalw_spec_mp "allsubs_psubt" gensubs.thy [allsubs_def] 
  "allsubs subt psubt = psubt" (fn _ => [Auto_tac, (eatac subt_thms.spp 1 1)]) ;

val _ = qed_goalw "allsubs_O_subt" gensubs.thy [allsubs_def] 
  "allsubs subt rho O subt <= allsubs subt rho"
  (fn _ => [ Auto_tac, (datac subt_thms.sss 1 1), Fast_tac 1]) ;

val _ = qed_goalw "allsubs_O_psubt" gensubs.thy [allsubs_def] 
  "allsubs subt rho O psubt <= allsubs subt rho"
  (fn _ => [ Auto_tac, (datac subt_thms.sps 1 1), Fast_tac 1]) ;

val _ = qed_goal "allsubs_union" gensubs.thy
  "allsubs subt (r Un s) <= \
    \ r Int allsubs subt (r Un s) Un s Int allsubs subt (r Un s)"
  (fn _ => [ Safe_tac, rewtac allsubs_def, Fast_tac 1]) ;

val _ = qed_goal_spec_mp "wf_all_lem" gensubs.thy
  "wf r --> wf s --> a O s <= a --> a <= r Un s --> wf a"
  (fn _ => [ Safe_tac, 
    (subgoal_tac "a <= r Int a Un s Int a" 1), Fast_tac 2,
    (rtac wf_subset 1), (chop_tac 1 (atac 2)),
    (rtac wfUn_Un' 1),
    (TRYALL (rtac wf_subset THEN' 
      (rtac Int_lower1 o incr) THEN' Clarify_tac)),
    (rtac order_trans 1), (atac 2),
    (rtac order_trans 1), (atac 2), Fast_tac 1]) ; 

val _ = bind_thm ("wf_allsubs", 
  [asm_rl, wf_psubt, allsubs_O_psubt, allsubs_le] MRS wf_all_lem) ;
    
val _ = qed_goalw_spec_mp "exsub_mono" gensubs.thy [exsub_def] 
  "suba <= subb --> r <= s --> exsub suba r <= exsub subb s" 
  (fn _ => [Auto_tac, (TRYALL (fast_tac (cds [subsetD])))]) ;

val _ = qed_goalw_spec_mp "exsub_Un" gensubs.thy [exsub_def] 
  "exsub sub (r Un s) = exsub sub r Un exsub sub s" (fn _ => [Auto_tac]) ;

val _ = qed_goalw_spec_mp "exsub_ge" gensubs.thy [exsub_def] 
  "r <= exsub subt r" (fn _ => [Auto_tac]) ;

val _ = qed_goalw_spec_mp "exsub_subt" gensubs.thy [exsub_def] 
  "exsub subt subt = subt" (fn _ => [Auto_tac, (eatac subt_thms.sss 1 1)]) ;

val _ = qed_goalw_spec_mp "exsub_psubt" gensubs.thy [exsub_def] 
  "exsub subt psubt = psubt" (fn _ => [Auto_tac, (eatac subt_thms.psp 1 1)]) ;

AddIffs [allsubs_le, allsubs_psubt, allsubs_subt,
  exsub_ge, exsub_psubt, exsub_subt] ; 

(* possibly useful lemmas *)
val _ = qed_goal_spec_mp "bdlem2" gensubs.thy 
  "r O r <= r O s --> nrel_comp r (Suc n) <= r O nrel_comp s n"
  (fn _ => [ (rtac impI 1), 
    (induct_tac "n" 1), (Simp_tac 1),
    (rtac order_trans 1), (simp_tac (esimps [O_assoc RS sym]) 2),
    (etac rel_comp_mono 2), (rtac order_refl 2),
    (simp_tac (esimps [O_assoc]) 1),
    (rtac rel_comp_mono 1), (atac 2), (rtac order_refl 1) ]) ;

val bdlem2' = rewrite_rule [mk_eq nrel_comp_Suc'] bdlem2 ;

val _ = qed_goal_spec_mp "bdlem1" gensubs.thy 
  "r O r <= r O s --> (ALL a x. (a, x) : r --> \
    \ (ALL y. (y, x) : r --> (y, m) : ubsl s) --> (a, m) : ubsl r)"
  (fn _ => [ (rtac impI 1), (simp_tac (HOL_ss addsimps [ubsl_nrel_comp]) 1),
    (dtac bdlem2' 1), Fast_tac 1]) ;
   
val _ = qed_goal_spec_mp "bdlem" gensubs.thy 
  "r O r <= r O s --> fb r --> fb s --> wf s --> wf r"
  (fn _ => [ (safe_tac (cis [wf_wfp' RS iffD2])), 
    (rtac (mk_mono' bd_wfp) 1),
    (subgoal_tac "EX m. ALL y. (y, x) : r --> (y, m) : ubsl s" 1),
    (dtac (fb_def RS defD1) 2),
    (eres_inst_tac [("x", "x")] allE 2),
    (dtac finite_list 2), (Clarify_tac 2),
    (res_inst_tac [("x", "(maxl (map (bd_of s) l))")] exI 2),
    (Clarify_tac 2), (res_inst_tac [("m", "bd_of s y")] ubsl_mono' 2),
    (rtac bded_bd 2), (etac (wf_ssI RS mk_mono' fb_wfp_bd) 2), 
    (REPEAT (force_tac (cis [maxlG], simpset ()) 2)),
    (etac exE 1), 
    (res_inst_tac [("n", "Suc m")] bded.I 1),
    (rtac ubsl.SucI 1), Clarify_tac 1,
    (eatac bdlem1 2 1) ]) ;

val _ = qed_goal_spec_mp "all_O_ex" gensubs.thy 
  "allsubs subt p O exsub subt q <= allsubs subt p O q"
  (fn _ => [ Safe_tac, (etac exsubE 1), 
    (datac (rel_compI RS mk_mono' allsubs_O_subt) 1 1), Fast_tac 1]) ;

val _ = qed_goal_spec_mp "aeOae" gensubs.thy 
  "allsubs subt (exsub subt q) O allsubs subt (exsub subt q) <= \
    \ allsubs subt (exsub subt q) O q"
  (fn _ => [ (rtac order_trans 1), (rtac all_O_ex 2),
    (rtac rel_comp_mono 1), Auto_tac]) ;

val _ = qed_goalw_spec_mp "fb_subt" gensubs.thy [subt_def'] "fb subt"
  (fn _ => [ (rtac fb_rtrancl 1),
    (auto_tac (claset (), init_ss addsimps [fb_def, isubts_isubt]))]) ;

val _ = bind_thm ("fb_exsub", fold_rule [mk_eq exsub_eqO] (fb_subt RS fb_O)) ;

val _ = qed_goal_spec_mp "wfae" gensubs.thy 
  "fb s --> wf s --> wf (allsubs subt (exsub subt s))"
  (fn _ => [ Safe_tac, (rtac (aeOae RS bdlem) 1), 
    (dtac fb_exsub 1), (rtac fb_mono 1), (rtac allsubs_le 1), Safe_tac]) ;


    

