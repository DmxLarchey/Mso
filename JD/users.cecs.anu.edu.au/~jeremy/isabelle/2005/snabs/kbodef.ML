
structure kbodef = struct val thy = the_context () end ;
val _ = use_legacy_bindings kbodef.thy ;
AddSIs [kbocfg.intros, kbocl.intros] ;

val _ = qed_goal "hns" kbodef.thy "(h, f) ~: symborder"
  (fn _ => [ (case_tac "f = h" 1), (dtac hmin 2),
    (forw_inst_tac [("Q", "{h, f}")] 
      (thin_rl RS (wf_symborder RS wf_eq_minD)) 2),
    (forw_inst_tac [("Q", "{h}")] 
      (thin_rl RS (wf_symborder RS wf_eq_minD)) 1),
    (REPEAT (Fast_tac 1))]) ;

val _ = qed_goal "tw_gt_0" kbodef.thy "0 < tw t"
  (fn _ => [ (rtac rtree_induct 1), (case_tac "list" 1), Auto_tac]) ;

AddIffs [hns, tw_gt_0] ;

val _ = qed_goal_spec_mp "tw_in" kbodef.thy 
  "sdt : set sts --> tw sdt <= tws sts" (indAu "sts") ;

val _ = qed_goalw_spec_mp "subt_tw" kbodef.thy [subt_def']
  "(t, s) : subt --> tw t <= tw s"
  (fn _ => [ Safe_tac, (etac rtrancl_induct 1),
    (etac isubt.elims 2), (dtac tw_in 2), Auto_tac]) ;

val _ = qed_goal_spec_mp "kbo_tw" kbodef.thy 
  "(t, s) : kbo --> tw t <= tw s"
  (fn _ => [ (auto_tac (ces [kbo.elims], simpset ()))]) ;

val _ = qed_goal_spec_mp "red_kbo_tw" kbodef.thy 
  "(t, s) : ctxt kbo --> tw t <= tw s"
  (fn _ => [Safe_tac, (etac ctxt.induct 1), etac kbo_tw 2, 
    (etac oneup.elims 1), Safe_tac, (etac onerel.induct 1), Auto_tac, 
    (etac onerel.elim 1), Auto_tac]) ;

(** kbo - closed under context, and transitive **)
val _ = qed_goal "red_kbo" kbodef.thy "ctxt (kbo) <= kbo"
  (fn _ => [Safe_tac, (ftac red_kbo_tw 1),
    (chop_tac 1 (etac rev_mp 1)), (etac ctxt.induct 1), 
    (etac oneup.elims 1), Safe_tac, (etac kbo.lexI 1), 
    (rtac (onerel_lex RS subsetD) 1), 
    (etac (onerel_mono RSN (2, rev_subsetD)) 1), 
    Safe_tac, (dtac red_kbo_tw 1), Fast_tac 1]) ;

val _ = qed_goal "red_kbo_eq" kbodef.thy "ctxt (kbo) = kbo"
  (fn _ => [ (rtac equalityI 1), (rtac red_kbo 1), Auto_tac]) ;
    
val _ = qed_goal_spec_mp "tws" kbodef.thy 
  "sdt : set sts --> tw sdt = tws sts --> sts = [sdt]"
  (fn _ => [ (case_tac "sts" 1), (case_tac "list" 2), Auto_tac,
    (dtac tw_in 1), (cut_inst_tac [("t", "a")] tw_gt_0 1), arith_tac 1]) ;

val _ = qed_goal_spec_mp "sw0" kbodef.thy 
  "sdt : set sts --> tw (Node f sts) = tw sdt --> f = h & sts = [sdt]"
  (fn _ => [ Clarsimp_tac 1, (ftac tw_in 1),
    (dtac tws 1), Auto_tac, (etac h_uniq_0 1)]) ;

val stacs = [ (etac ex_match), (clarsimp_tac (cesimps [subt_def'])),
  (rtac rtrancl_into_rtrancl), atac, Force_tac] ;

val _ = qed_goal_spec_mp "kbo_red_props_lem" kbodef.thy 
  "ALL dtn. (dtn, dt) : kbo --> (dts, dtn) : subt --> \ 
    \ (EX dt'. (dt', dt) : subt & (dts, dt') : kbo)"
  (fn _ => [ (res_inst_tac [("rtree1", "dt")] rtree_induct 1),
    (strip_tac 1), (ftac kbo_tw 1), (ftac subt_tw 1),
    (case_tac "tw dts = tw (Node a list)" 1), 
    (rtac exI 2), (force_tac (cis [kbo.wltI], simpset ()) 2),
    (ftac (subt_def RS def_imp_eq RS equalityD1 RS subsetD) 1),
    Safe_tac, (rtac exI 2), (Force_tac 2),
    (rewtac psubt_def), (dtac converse_tranclD 1), Safe_tac,
    (etac isubt.elims 1), Safe_tac,
    (ftac (rewrite_rule [subt_def'] subt_tw) 1),
    (forw_inst_tac [("f", "aa")] sw0 1),
    (dtac tw_in 1), Force_tac 1,

    (etac kbo.elims 1), (Clarsimp_tac 4), (Clarify_tac 2), 

    (* the case where (r, l) : kbo by rule kbo.usubtI *)
    (Clarify_tac 2), 
    (subgoal_tac "f = h" 2), (rtac h_uniq_0 3), (Force_tac 3),
    (Clarsimp_tac 2), (etac allE 2), 
    (etac impE 2), (rtac kbo.usubtI 2),
    (fold_tac [subt_def']), (eatac impE 1 2), EVERY' stacs 2,

    (* the case where (r, l) : kbo by rule kbo.lexI *)
    (etac lex.elim 1), (etac lex.elim 1), Auto_tac,
    (etac allE 1), (eatac impE 1 1), (eatac impE 1 1), EVERY' stacs 1]) ;

val _ = qed_goalw_spec_mp "kbo_red_props_lem2" kbodef.thy [kbocdef]
  "(dtn, dt) : kbo --> set (isubts dt) <= wfp (ctxt kbo) --> \
    \ (dtn, dt) : psubt | (dtn, dt) : kbo_cutorder"
  (fn _ => [ strip_tac 1, (etac kbo.elims 1),
    (clarsimp_tac (cesimps [inv_image_def]) 4),
    (clarsimp_tac (cis [r_into_trancl], esimps [psubt_def]) 3),
    Clarsimp_tac 2, (dtac wf_lex_fwf 1),
    (auto_tac (cesimps [red_kbo_eq]))]) ;

val _ = qed_goal_spec_mp "kbo_red_props_dt'" kbodef.thy 
  "(dtn, dt) : kbo --> (dts, dtn) : subt --> \
       \ set (isubts dt) <= wfp (ctxt kbo) -->  \
       \ dts : wfp (ctxt kbo) | (dts, dt) : (kbo_cutorder Un sn1order kbo)^+"
  (fn _ => [ Safe_tac, (datac kbo_red_props_lem 1 1), Safe_tac, 
    (ftac kbo_red_props_lem2 1), 
    (clarsimp_tac (cesimps [subset_def, Ball_def, subt_def']) 1),
    (etac thin_rl 1), (etac rtranclE 1), Fast_tac 1,
    (etac allE 1), (eatac impE 1 1), (etac subt_sn 1),
    (clarsimp_tac (cesimps [subt_def']) 1), 
    (eatac converse_rtrancl_into_rtrancl 1 1),
    (etac thin_rl 1), (rewtac subt_def), (etac UnE 1),
    (datac isubts_sn 1 1), (eatac sn_red' 1 1),
    Safe_tac, (eatac isubts_sn 1 1), (Force_tac 1)]) ;

val _ = qed_goalw "kbocfg_symb_of" kbodef.thy [inv_image_def]
  "kbocfg <= inv_image symborder symb_of"
  (fn _ => [ Safe_tac, (etac kbocfg.elims 1), Auto_tac]) ;

val _ = qed_goal_spec_mp "wf_kbocfg" kbodef.thy "wf (kbocfg)"
  (fn _ => [ (rtac wf_subset 1), (rtac kbocfg_symb_of 2), 
    (clarsimp_tac (cesimps [wf_symborder]) 1)]) ;

val _ = qed_goal "kbocl_oneup" kbodef.thy 
  "kbocl <= oneup (lex (fwf (ctxt (kbo))))" 
  (fn _ => [ (clarsimp_tac
    (ces [oneup.elims, kbocl.elims], esimps [red_kbo_eq]) 1)]) ;

val _ = qed_goal "wf_kbocl" kbodef.thy "wf (kbocl)"
  (fn _ => [ (rtac wf_subset 1), (rtac kbocl_oneup 2), 
    (simp_tac (esimps [wf1up]) 1),
    (rtac wf_lex 1), (rtac wf_fwf 1) ]) ;

AddIffs [wf_kbocfg, wf_kbocl] ;

val _ = qed_goalw "kbowfcut" kbodef.thy [kbocdef] "wf kbo_cutorder"
  (fn _ => [ (rtac wfUn_absl 1), (rtac wfUn_absl 3),
    (safe_tac (ces [kbocfg.elims, kbocl.elims])),
    (auto_tac (cesimps [inv_image_def]))]) ;

val _ = qed_goal "sn1cut" kbodef.thy 
  "sn1order (kbo) <= kbocl"
  (fn _ => [ Safe_tac, (ftac (sn1o_nured') 1), 
    (dtac (red_nured RS red_kbo_tw) 1),
    (rewrite_goals_tac [sn1order_def, sn1red_def]),
    (etac oneup.elims 1), Safe_tac,
    (clarsimp_tac (ces [onerel_lex RS subsetD], (esimps [red_kbo_eq])) 1)]) ;

val _ = qed_goal "kbowfdt" kbodef.thy 
  "wf (kbo_cutorder Un sn1order kbo)"
  (fn _ => [ (rtac wf_subset 1), (rtac kbowfcut 1), 
    (simp_tac (esimps [kbocdef, Un_subset_iff]) 1),
    (rtac order_trans 1), (rtac sn1cut 1), Fast_tac 1]) ;

val _ = qed_goalw "kbo_red_props_dt" kbodef.thy [red_props_dt_def']
  "red_props_dt kbo ?cuto"
  (fn _ => [ (strip_tac 1), (eatac kbo_red_props_dt' 2 1) ]) ;

val kbosn = [kbo_red_props_dt, kbowfdt] MRS all_sn3_dt ;



