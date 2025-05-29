
structure ackdef = struct val thy = theory "ackdef" end ;
use_legacy_bindings ackdef.thy ;
fun u _ = use_thy "ackdef" ;

structure ackrn = ack_ruleredn ;

val ack_cs = (ces [acr1.elims, acr2.elims, acr0.elims]) ;
val ack_css = (ack_cs, esimps [inv_image_def, measure_def]) ;
val ack_intrs = [acr1.I, acr2.I, acr0.I] ;

val _ = qed_goalw "ackwfcut" ackdef.thy [ackcdef] "wf (ack_cutorder)"
  (fn _ => [
    (subgoal_tac "wf acr1" 1), (rtac wf_subset 2),
    (res_inst_tac [("f", "size o hd o isubts")] wf_measure 2),
    (force_tac ack_css 2),
    (subgoal_tac "wf acr2" 1), (rtac wf_subset 2),
    (res_inst_tac [("f", "size")] wf_measure 2),
    (force_tac ack_css 2),
    (subgoal_tac "wf (acr1 Un acr2)" 1), (rtac wfUn_absr 2),
    (* could have equally used wfUn_absl *)
    (safe_tac ack_cs), (rtac acr1.I 2),
    (subgoal_tac "wf acr0" 1), 
    (res_inst_tac [("n", "Suc (Suc 0)")] wf_lim_comp 2),
    (Simp_tac 2), (safe_tac (ces [acr0.elims])),
    (forw_inst_tac [("r", "acr0"), ("s", "acr1 Un acr2")] 
      (thin_rl RS wfUn_absr) 1),
    (safe_tac ack_cs), (simp_tac (esimps [Un_assoc]) 1)]) ;

val _ = qed_goalw "ack_c1p" ackdef.thy [ackcdef, nured_def, cut1_prop_def]
  "cut1_prop ack_cutorder"
  (fn _ => [ (safe_tac (ack_cs addSEs oo_elims)),
    (rtac rel_compI 1), (rtac rtrancl_refl 2), 
    (clarify_tac (cis ack_intrs) 1),

    (rtac rel_compI 2), (rtac rtrancl_refl 3), 
    (clarify_tac (cis ack_intrs) 2),
    
    (REPEAT1 (EVERY [
      (rtac rel_compI 1), (rtac r_into_rtrancl 2), 
      (artac 2), (clarify_tac (cis ack_intrs) 1)])) ]) ;

val ackwfdt = [ackwfcut, ack_c1p] MRS c1p_wfdt ;

val swap_tcl = 
  read_instantiate_sg (sign_of Main.thy) [("Pa", "?x : ?r^+")] swap ;

val _ = qed_goalw_spec_mp "ack_red_props_pc'" ackdef.thy 
  [subt_def, psubt_def, ackcdef]
  "(dtn, dt) : ack_ruleredn --> (dts, dtn) : subt --> \
    \ (dts, dt) : psubt | (dts, dt) : ack_cutorder"
  (fn _ => [ strip_tac 1, (etac ackrn.elims 1), 
    (safe_tac (cis ack_intrs)), 
    (safe_tac (ces [isubt_tranclE])), 
    (safe_tac (cis ack_intrs)), 
    (TRYALL (etac swap_tcl)), (TRYALL tranclI_tac)]) ;
    
val _ = qed_goalw "ack_red_props_pc" ackdef.thy [red_props_pc_def]
  "red_props_pc ack_ruleredn ?cuto"
  (fn _ => [ (strip_tac 1), (eatac ack_red_props_pc' 1 1) ]) ;

val acksn = [ack_red_props_pc, ackwfdt] MRS all_sn3_pc ;
    

(* problem - can't prove sntr' or its counterpart 
eg
have A (S (A x), z) >cut A (A x, y) >sn1 A (w, y) for some w,
  but A (S (A x), z) not >cut A (w, y)
and A (A (0, z), y) >sn1 A (S z, y) >cut A (z, w)
  but A (A (0, z), y) not >cut A (z, w)
*)
