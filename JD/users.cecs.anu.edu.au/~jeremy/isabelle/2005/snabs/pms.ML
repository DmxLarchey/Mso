
structure pms = struct val thy = theory "pms" end ;
use_legacy_bindings pms.thy ;
fun u _ = use_thy "pms" ; 

(* now to show the link between this and the multiset ordering *)

val _ = qed_goalw "leaves_leaf" pms.thy [leaf_def]
  "leaves (leaf a) = [a]" fn_at ;
val _ = qed_goal "leavess_map_leaf" pms.thy 
  "leavess (map leaf l) = l"
  (fn _ => [ (induct_tac "l" 1), (auto_tac (cesimps [leaves_leaf]))]) ;

Addsimps [leaves_leaf, leavess_map_leaf] ;

val _ = qed_goal_spec_mp "mult1_rtree" pms.thy 
  "ALL s s'. mset_of (leaves t) = s --> (s', s) : mult1 symborder --> \
    \ (EX t'. (t', t) : ctxt pms_ruleredn & mset_of (leaves t') = s')"
  (fn _ => [(res_inst_tac [("rtree1", "t")] rtree_induct 1), Safe_tac,
    (full_simp_tac (esimps [mult1_def, single_is_union] 
      addsplits [spms.split_asm]) 1),
    (cut_inst_tac [("s", "s'")] ex_mset 1), Safe_tac, 
    (res_inst_tac [("x", "Node Inner (map leaf l)")] exI 1), 
    (full_simp_tac (esimps [pmsrdef, mset_set]) 1),
    (rtac ron.red_cutI 1), (rtac (pmr1.I RS UnI1) 1), Fast_tac 1, (* level 10 *)
    (subgoal_tac "EX tl'. (tl', list) : onerel (ctxt pms_ruleredn) & \
      \ mset_of (leavess tl') = M0 + K" 1),
    (etac thin_rl 1), (Clarsimp_tac 1), 
    (res_inst_tac [("x", "Node Inner tl'")] exI 1), (Force_tac 1),
    (etac rev_mp 1), (etac rev_mp 1),
    (res_inst_tac [("x", "M0")] spec 1), (* level 18 *)
    (induct_tac "list" 1), 
    Simp_tac 1, Clarsimp_tac 1, 
    (case_tac "aa :# mset_of (leaves ab)" 1), 
    (eres_inst_tac [("x", "mset_of (leavess lista) - {#aa#}")] allE 2),
    (REPEAT (thin_tac "All ?P" 2)), (thin_tac "Ball ?S ?P" 2),
    (etac impE 2), (rtac elem_imp_eq_diff_union 2),
    (dres_inst_tac [("f", "%s. aa :# s")] arg_cong 2), 
    (asm_full_simp_tac (esimps [mset_append]) 2),
    (Clarify_tac 2), (* level 30 *)
    (res_inst_tac [("x", "ab # tl'")] exI 2), Safe_tac,
    (full_simp_tac (esimps [mset_append, multiset_eq_conv_count_eq]) 2), 
    (eatac all_match2 1 2), Force_tac 2,
    (rotate_tac 1 1), (thin_tac "All ?P" 1), (thin_tac "Ball ?S ?P" 1),
    (etac allE 1), (etac impE 1), (rtac exI 1), (rtac exI 1), 
    (rtac conjI 1), (etac elem_imp_eq_diff_union 1),
    (rtac exI 1), (rtac conjI 1), (rtac refl 1), (atac 1),
    Safe_tac, (res_inst_tac [("x", "t' # lista")] exI 1), Safe_tac,
    (full_simp_tac (esimps [mset_append, multiset_eq_conv_count_eq]) 1), 
    (etac all_match2 1), (chop_tac 1 (atac 1)),
    (full_simp_tac (esimps [] addsplits [split_if_asm]) 1), 
    Safe_tac, TRYALL arith_tac ]) ;
    
val _ = qed_goal_spec_mp "mult1_list" pms.thy 
  "ALL s s'. mset_of l = s --> (s', s) : mult1 symborder --> \
    \ (EX l'. (map leaf l', map leaf l) : onerel pmr1 O coll1s & \
      \ mset_of l' = s')"
  (fn _ => [(induct_tac "l" 1), (ALLGOALS Clarsimp_tac),
    (dtac less_add 1), Safe_tac, (etac thin_rl 2),
    (cut_inst_tac [("s", "K")] ex_mset 2), (Clarify_tac 2), 
    (res_inst_tac [("x", "l @ list")] exI 2), 
    (simp_tac (esimps (mset_append :: union_ac)) 2),
    (res_inst_tac [("b", "?t # map leaf list")] rel_compI 2), 
    (etac allE 1), mp_tac 1, (Clarify_tac 1),
    (res_inst_tac [("x", "a # l'")] exI 1), Simp_tac 1,
    (res_inst_tac [("b", "leaf a # y")] rel_compI 1), 
    (auto_tac (cesimps [leaf_def, mset_set])) ]) ;

val _ = qed_goal_spec_mp "mult1_list'" pms.thy 
  "mset_of l = s --> (s', s) : mult1 symborder --> \
    \ (EX l'. (Node Inner (map leaf l'), Node Inner (map leaf l)) : \
      \ (ctxt pms_ruleredn)^+ & mset_of l' = s')"
  (fn _ => [ strip_tac 1, (datac mult1_list 1 1), Safe_tac,
    (res_inst_tac [("x", "l'")] exI 1), Simp_tac 1,
    (res_inst_tac [("b", "Node Inner y")] rtrancl_into_trancl1 1), 
    (rewtac pmsrdef), 
    (rtac r_into_rtrancl 1), (rtac ron.red_cutI 1), Fast_tac 1,
    (rtac ron.red_nuI 1), Clarify_tac 1,
    (etac rev_subsetD 1), (rtac onerel_mono 1),
    (rtac order_trans 1), (rtac r_into_red 2), (rtac Un_upper1 1)]) ;

val _ = qed_goal "wf_m1'" pms.thy "wf (mult1 (symborder :: (symb * symb) set))"
  (fn _ => [ (cut_facts_tac [pmswf] 1), (dtac wf_trancl 1),
    (full_simp_tac (esimps [wf_eq_minimal]) 1), Safe_tac,
    (eres_inst_tac [("x", 
      "{Node Inner (map leaf l) | l. mset_of l : Q}")] allE 1),
    (etac impE 1), (cut_inst_tac [("s", "x")] ex_mset 1), Force_tac 1,
    Safe_tac, (etac thin_rl 1), (rtac bexI 1), atac 2, Safe_tac,
    (dtac (refl RS mult1_list') 1), Auto_tac]) ;

val _ = qed_goal "ex_rtree" pms.thy "EX t. mset_of (leaves t) = s"
  (fn _ => [ (cut_inst_tac [("s", "s")] ex_mset 1), Safe_tac,
    (res_inst_tac [("x", "Node Inner (map leaf l)")] exI 1), Simp_tac 1]) ;

val _ = qed_goal "wf_m1" pms.thy "wf (mult1 (symborder :: (symb * symb) set))"
  (fn _ => [ (cut_facts_tac [pmswf] 1),
    (full_simp_tac (esimps [wf_eq_minimal]) 1), Safe_tac,
    (eres_inst_tac [("x", "{t. mset_of (leaves t) : Q}")] allE 1),
    (etac impE 1), (cut_inst_tac [("s", "x")] ex_rtree 1), Force_tac 1,
    Safe_tac, (etac thin_rl 1), (rtac bexI 1), atac 2, Safe_tac,
    (dtac (refl RS mult1_rtree) 1), Auto_tac]) ;

