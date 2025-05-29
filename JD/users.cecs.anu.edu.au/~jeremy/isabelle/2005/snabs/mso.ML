
structure mso = struct val thy = theory "mso" ;
  val ipt_mk_cases = InductivePackage.the_mk_cases thy ; end ;
use_legacy_bindings mso.thy ;
fun u _ = use_thy "mso" ;

val smso_mk_cases = mso.ipt_mk_cases "mso.smso" ;

val mult1_def = thm "mult1_def" ;
val mult_def = thm "mult_def" ;
val wf_mult = thm "wf_mult" ;
val wf_mult1 = thm "wf_mult1" ;
val multiset_induct = thm "multiset_induct" ;
val single_is_union = thm "single_is_union" ;
val union_is_single = thm "union_is_single" ;
val mem_set_of_iff = thm "mem_set_of_iff" ;
val multiset_eq_conv_count_eq = thm "multiset_eq_conv_count_eq" ;
val elem_imp_eq_diff_union = thm "elem_imp_eq_diff_union" ;
val union_ac = thms "union_ac" ;

val smsoE = smso_mk_cases "(Ma, M) : smso r" ;

val _ = qed_goalw_spec_mp "mult1_mono" mso.thy [mult1_def]
  "r <= s --> mult1 r <= mult1 s" (fn _ => [ Force_tac 1]) ;

val _ = bind_thm ("mult_mono", 
  fold_rule [mult_def] (mult1_mono RS trancl_mono')) ;

val _ = qed_goalw_spec_mp "msol_mono" mso.thy [msol_def]
  "r <= s --> msol r <= msol s" 
  (fn _ => [ (rtac impI 1), (rtac inv_image_mono 1), 
    (rtac mult_mono 1), (rtac trancl_mono' 1), atac 1]) ;

(* won't hold because of transitivity built into the definition of msol
val msol_mono_ss1 = prove_goal mso.thy 
  "(al, bl) : msol A --> A Int set al <*> UNIV <= B --> (al, bl) : msol B"
  *)

(** mset_of **)

val _ = qed_goal_spec_mp "ex_mset" mso.thy "EX l. mset_of l = s"
  (fn _ => [(res_inst_tac [("M", "s")] multiset_induct 1),
    (rtac exI 1), (rtac mset_of.Nil 1),
    Safe_tac, (rtac exI 1), (rtac mset_of.Cons 1)]) ;

val _ = qed_goal "set_mset" mso.thy "set_of (mset_of l) = set l" (indAu "l") ;
val _ = qed_goal "mset_set" mso.thy "(x :# mset_of l) = (x : set l)" 
  (indAu "l") ;

val _ = qed_goal_spec_mp "mset_append" mso.thy 
  "ALL ys. mset_of (xs @ ys) = mset_of xs + mset_of ys"
  (fn _ => [ (induct_tac "xs" 1), (auto_tac (cesimps union_ac))]) ;

val _ = qed_goalw "surj_mset" mso.thy [surj_def] "surj mset_of"
  (fn _ => [ (rtac allI 1), 
    (res_inst_tac [("M", "y")] multiset_induct 1), Safe_tac,
    (res_inst_tac [("x", "[]")] exI 1),
    (res_inst_tac [("x", "x # xa")] exI 2), Auto_tac]) ;

val less_add = thm "less_add" ;
(*
val mult1D = mult1_def RS def_imp_eq RSN (2, mem_same) ;
*)
val _ = qed_goalw_spec_mp  "mult1_plus" mso.thy [mult1_def]
  "(Ma, M) : (mult1 r) --> (X + Ma, X + M) : (mult1 r)"
  (fn _ => [ Safe_tac, (REPEAT (rtac exI 1)),
    (REPEAT_FIRST (rtac conjI)), atac 3, 
    (REPEAT (rtac (assoc RS sym) 1))]) ;

val SOME mult1_plus' = Conv.CONV_RULE (Conv.TDSTOP_CONV 
  (Conv.EQ_CONV (false, false) (mk_eq commute))) mult1_plus ;

fun ext_r_tc_tacs th _ = [ (rtac impI 1), (etac trancl_induct 1), 
    (rtac r_into_trancl 1), (etac th 1),
    (etac trancl_into_trancl 1), (etac th 1)] ;

val mult1_plus_tc = prove_goal mso.thy 
  "(Ma, M) : (mult1 r)^+ --> (X + Ma, X + M) : (mult1 r)^+"
  (ext_r_tc_tacs mult1_plus) RS mp ;

val mult1_plus'_tc = prove_goal mso.thy 
  "(Ma, M) : (mult1 r)^+ --> (Ma + X, M + X) : (mult1 r)^+"
  (ext_r_tc_tacs mult1_plus') RS mp ;

val _ = ListPair.app bind_thm (["mult_plus", "mult_plus'"],
  map (fold_rule [mult_def]) [mult1_plus_tc, mult1_plus'_tc]) ;

val _ = qed_goalw "mult1_def1" mso.thy [mult1_def]
  "((K, {#a#}) : mult1 r) = (ALL b. b :# K --> (b, a) : r)"
  (fn _ => [ Safe_tac,
    (forw_inst_tac [("f", "size")] arg_cong 1),
    (Full_simp_tac 1), (Force_tac 1), 
    (res_inst_tac [("x", "a")] exI 1),
    (res_inst_tac [("x", "{#}")] exI 1), Force_tac 1]) ;

val _ = qed_goalw_spec_mp "in_mult1" mso.thy [mult1_def]
  "(N, M) : mult1 r --> a :# N --> (EX b. b :# M & (a, b) : r^=)"
  (fn _ => [Force_tac 1]) ;

val _ = qed_goalw_spec_mp "in_mult" mso.thy [mult_def]
  "(N, M) : mult r --> (ALL a. a :# N --> (EX b. b :# M & (a, b) : r^*))"
  (fn _ => [ (rtac impI 1), (etac trancl_induct 1),
    (fast_tac (cds [in_mult1]) 1), (etac all_match 1), Safe_tac,
    (datac in_mult1 1 1), (etac ex_match 1), Safe_tac,
    (eatac rtrancl_into_rtrancl 1 1)]) ;

(*
val _ = qed_goal "mult1_trancl" mso.thy 
  "ALL x. (x, y) : mult1 (r^+) --> (x, y) : (mult1 r)^+"
  (fn _ => [ (res_inst_tac [("M", "y")] multiset_induct 1), 
    (simp_tac (esimps [mult1_def]) 1), Safe_tac, 
    (dtac less_add 1), Safe_tac, 
    (etac allE 1), (eatac impE 1 1),
    (etac mult1_plus'_tc 1), 
    (etac thin_rl 1), (etac rev_mp 1), 
    (* following step wrong *)
    (res_inst_tac [("M", "K")] multiset_induct 1), 
    (rtac impI 1), (rtac r_into_trancl 1), (rtac mult1_plus 1),
    (simp_tac (esimps [mult1_def1]) 1),
    (rtac impI 1), (etac impE 1), Force_tac 1,
  ]) ;
  *)

val _ = qed_goalw "trancl_msol" mso.thy [msol_def]
  "(msol ?r)^+ = msol (?r^+)"
  (fn _ => [ (rtac equalityI 1), 
    (ALLGOALS (rtac order_trans)),
    (rtac trancl_inv_image 1), 
    (rtac (surj_mset RS trancl_inv_image_surj) 3),
    (ALLGOALS (simp_tac (esimps [mult_def])))]) ;

(** smso **)

val SOME smso_plusI' = Conv.CONV_RULE (Conv.TDSTOP_CONV 
  (Conv.EQ_CONV (false, false) (mk_eq commute))) smso.plusI ;

AddSIs [smso_plusI', smso.plusI] ;

val _ = qed_goalw "mult1_smso" mso.thy [mult1_def] "mult1 r <= smso r"
  (fn _ => [ (safe_tac (cds [smso.singleI])) ]) ;

val _ = qed_goal "smso_mult1_tc" mso.thy "smso r <= (mult1 r)^+"
  (fn _ => [ Safe_tac, (etac smso.induct 1),
    (rtac r_into_trancl 1),
    (force_tac (cesimps [mult1_def, single_is_union]) 1),
    (etac mult1_plus'_tc 1), 
    (dtac mult1_plus'_tc 1), (dtac mult1_plus_tc 1),
    (eatac trancl_trans 1 1) ]) ;

val _ = qed_goalw "smso_tc_mult" mso.thy [mult_def] "(smso r)^+ = mult r"
  (fn _ => [ (rtac equalityI 1),
    (rtac trancl_mono' 2), (rtac mult1_smso 2), 
    (rtac order_trans 1),
    (rtac trancl_mono' 1), (rtac smso_mult1_tc 1), Simp_tac 1]) ;

val _ = qed_goal_spec_mp "wf_smso" mso.thy "wf r --> wf (smso r)"
  (fn _ => [ Safe_tac, (rtac (wf_trancl_iff RS iffD1) 1),
    (asm_simp_tac (esimps [smso_tc_mult, wf_mult]) 1)]) ;

val _ = qed_goalw_spec_mp "wf_smsol" mso.thy [smsol_def]
  "wf r --> wf (smsol r)"
  (fn _ => [ (rtac impI 1), (rtac wf_inv_image 1), (etac wf_smso 1) ]) ;

val _ = qed_goal_spec_mp "smso_nonempty'" mso.thy 
  "(N, M) : smso r --> M ~= {#}"
  (fn _ => [ (rtac impI 1), (etac smso.induct 1), Auto_tac]) ;

val _ = qed_goal "smso_nonempty" mso.thy "(N, {#}) ~: smso r"
  (fn _ => [ (safe_tac (cds [smso_nonempty']))]) ;

AddIffs [smso_nonempty] ;

val _ = qed_goal_spec_mp "smso_single'" mso.thy 
  "((N, S) : smso r) --> (S = {#m#}) --> n :# N --> (n, m) : r"
  (fn _ => [ (rtac impI 1), (etac smso.induct 1), 
    (auto_tac (claset(), esimps [union_is_single] addsplits [split_if_asm]))]) ;

val _ = qed_goal "smso_single" mso.thy 
  "((N, {#m#}) : smso r) = (ALL n. n :# N --> (n, m) : r)"
  (fn _ => [ (rtac iffI 1), (etac smso.singleI 2), Safe_tac,
    (rtac smso_single' 1), Auto_tac]) ;

Addsimps [smso_single] ;

val _ = qed_goal_spec_mp "smso_mono" mso.thy 
  "r <= s --> smso r <= smso s" 
  (fn _ => [ Safe_tac, (etac smso.induct 1), Force_tac 1,
    (etac smso.plusI 1), (eatac smso.addI 1 1)]) ; 

val _ = qed_goal_spec_mp "in_smso" mso.thy 
  "(N, M) : smso r --> a :# N --> (EX b. b :# M & (a, b) : r^=)"
  (fn _ => [ (rtac impI 1), (etac smso.induct 1), 
   (auto_tac (claset(), esimps [union_is_single] addsplits [split_if_asm]))]) ;

val _ = qed_goal_spec_mp "smso_fwfI" mso.thy 
  "(ts, ss) : smso r --> set_of ss <= wfp r --> (ts, ss) : smso (fwf r)"
  (fn _ => [ (rtac impI 1), (etac smso.induct 1), 
    (force_tac (cis [smso.addI], simpset ()) 3), Auto_tac]) ;

val _ = qed_goalw_spec_mp "smsol_fwfI" mso.thy [smsol_def, inv_image_def]
  "(ts, ss) : smsol r --> set ss <= wfp r --> (ts, ss) : smsol (fwf r)"
  (fn _ => [ (fast_simp_tac (ces [smso_fwfI], esimps [set_mset]) 1) ]) ;

val _ = qed_goalw "onerel_smsol" mso.thy [smsol_def, inv_image_def]
  "onerel r <= smsol r"
  (fn _ => [ (Clarify_tac 1), (etac onerel.induct 1), Auto_tac]) ;
    
val _ = qed_goalw_spec_mp "smsol_mono" mso.thy [smsol_def]
  "r <= s --> smsol r <= smsol s" 
  (fn _ => [ (rtac impI 1), (rtac inv_image_mono 1), (etac smso_mono 1) ]) ;

(* true but hard to prove
val _ = qed_goal "smso_plus" mso.thy 
  "((Ma + X, M + X) : smso r) = ((Ma, M) : smso r)"
  (fn _ => [ (rtac iffI 1), (etac smso.plusI 2), Safe_tac,
  ]) 
*)

(* using former definition of smso 
val _ = qed_goal_spec_mp "smsoD" mso.thy 
  "(N, M) : smso r --> (ALL n. n :# N --> (EX m. m :# M & (n, m) : r^=))"
  (fn _ => [ Safe_tac, (etac smso.elim 1), (Clarsimp_tac 1), 
    (eres_inst_tac [("x", "n")] allE 1), (etac impCE 1), 
    (etac ex_match 2), (TRYALL Force_tac)]) ;

val _ = qed_goal_spec_mp "smso_mono" mso.thy 
  "r <= s --> smso r <= smso s" 
  (fn _ => [ (simp_tac (init_ss addsimps [smso.unfold]) 1), Force_tac 1]) ;

val _ = qed_goal_spec_mp "smso_plus" mso.thy 
  "(Ma, M) : smso r --> (Ma + X, M + X) : smso r"
  (fn _ => [ (rtac impI 1), (etac smsoE 1), (rtac smso.I 1), 
    Force_tac 1, (etac all_match 1), Simp_tac 1]) ;

val SOME smso_plus' = Conv.CONV_RULE (Conv.TDSTOP_CONV 
  (Conv.EQ_CONV (false, false) (mk_eq commute))) smso_plus ;

val _ = qed_goal "trancl_smso" mso.thy "(smso r)^+ = smso (r^+)"
  (fn _ => [ Safe_tac, (etac trancl_induct 1),
    (etac rev_subsetD 1), (rtac smso_mono 1), Fast_tac 1,
    (etac thin_rl 1), (rtac smso.I 1), (Clarify_tac 2),
    (* rather than next line, need to compare counts of n in a, y, z *)
    (case_tac "n :# y" 2), (etac smso.elim 2), 
    (eres_inst_tac [("x", "n")] allE 2), (Clarsimp_tac 2)
  ]) ;
*)

