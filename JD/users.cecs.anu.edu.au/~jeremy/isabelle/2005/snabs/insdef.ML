
structure insdef = struct val thy = theory "insdef" end ;
use_legacy_bindings insdef.thy ;
fun u _ = use_thy "insdef" ;

(* to help in understanding *)
local nonfix ins in
fun sort [] = []
  | sort (x :: y) = op ins (x, sort y)

and ins (x, []) = [x]
  | ins (x, v :: w) = choose (x, v :: w, x, v)

and choose (x, v :: w, y, z) = 
  if y < z then v :: ins (x, w) else x :: v :: w ;
end ;

val icis = [ic1.intros, ic2.intros, ic3.intros, ic12.intros] @ icsymb.intros ; 
val ices = [ic1.elims, ic2.elims, ic3.elims, ic12.elims, icsymb.elims] ; 
AddIffs (icis @ ins_ruleredn.intros) ;
val ins_cs = cis [equals0I] addSEs ices ;
val ins_css = (ins_cs, esimps [inv_image_def]) ;

val _ = qed_goal "wf_icsymb" insdef.thy "wf icsymb"
  (fn _ => [
    (res_inst_tac [("n", "Suc (Suc (Suc 0))")] wf_lim_comp 1),
    (force_tac ins_css 1) ]) ; 

val _ = qed_goal "wf_ic3" insdef.thy "wf ic3"
  (fn _ => [ (rtac wf_subset 1), 
    (res_inst_tac [("f", "%t. isubts t ! Suc (Suc 0)")] wf_inv_image 1), 
    (rtac wf_isubt 1), (force_tac ins_css 1) ]) ;

val _ = qed_goal "wf_ic12a" insdef.thy "wf ic12"
  (fn _ => [ (rtac wf_subset 1), 
    (res_inst_tac [("f", "%t. isubts t ! Suc 0")] wf_inv_image 1), 
    (rtac wf_isubt 1), 
    (force_tac ins_css 1) ]) ;

val _ = qed_goal "wf_ic12b" insdef.thy "wf (ic12 Un ic1)"
  (fn _ => [ (rtac wfUn_absr 1), (rtac wf_ic12a 3),
    (res_inst_tac [("n", "Suc (Suc 0)")] wf_lim_comp 2),
    (auto_tac ins_css) ]) ;

val _ = qed_goal "wf_ic12c" insdef.thy "wf ((ic12 Un ic1) Un ic2)"
  (fn _ => [ (rtac wfUn_absl 1), (rtac wf_ic12b 2),
    (res_inst_tac [("n", "Suc (Suc 0)")] wf_lim_comp 2),
    (auto_tac ins_css) ]) ;

val _ = qed_goal "wf_ic12" insdef.thy "wf (ic1 Un ic2)"
  (fn _ => [ (rtac wf_subset 1), (rtac wf_ic12c 1), Fast_tac 1]) ;

val _ = qed_goal "wf_ic123" insdef.thy "wf ((ic1 Un ic2) Un ic3)"
  (fn _ => [ (rtac wfUn_absl 1),
    (rtac wf_ic12 2), (rtac wf_ic3 2), (safe_tac ins_cs)]) ;

val _ = qed_goalw "inswfcut" insdef.thy [inscdef] "wf ins_cutorder"
  (fn _ => [ (rtac wfUn_absl 1), 
    (rtac wf_icsymb 2), (rtac wf_ic123 2), (auto_tac ins_css) ]) ;

val _ = qed_goalw "ins_c1p" insdef.thy [inscdef, nured_def, cut1_prop_def]
  "cut1_prop ins_cutorder"
  (fn _ => [ (safe_tac (ins_cs addSEs oo_elims)),
    (* deal with goals not using sn2order^* *)
    (TRYALL (EVERY' [ (rtac rev_subsetD), (resolve_tac icis), Fast_tac])),
    (TRYALL (SELECT_GOAL (EVERY [ (rtac rel_compI 1),
      (rtac r_into_rtrancl 2), (artac 2), 
      (REPEAT (resolve_tac [UnI1, UnI2] 1)), (resolve_tac icis 1)] ))) ]) ;

val inswfdt = [inswfcut, ins_c1p] MRS c1p_wfdt ;

val _ = qed_goalw_spec_mp "ins_red_props" insdef.thy 
  [subt_def, psubt_def, inscdef]
  "(dtn, dt) : ins_ruleredn --> (dts, dtn) : subt --> \
    \ (dts, dt) : psubt Un ins_cutorder Un (nured ins_ruleredn)^+"
  (fn _ => [ strip_tac 1, (etac ins_ruleredn.elims 1),
    (safe_tac (ces [trancl_isubtE])),
    (* deal with cases involving isubt^+ *) 
    (TRYALL ((DETERM o chop_tac 1 o etac notE) THEN' tranclI_tac)),
    (* now using nured ruleredn, using psubt rules for ruleredn *)
    (TRYALL (EVERY' [ (DETERM o etac notE), 
      (rtac r_into_trancl), (SELECT_GOAL (rewtac nured_def)),
      (rtac oneup.ouI), Clarify_tac, (rtac ron.red_cutI), 
      (resolve_tac ins_ruleredn.intros)])) ]) ;

val _ = qed_goalw_spec_mp "ins_red_props_c" insdef.thy [red_props_c_def]
  "red_props_c ins_ruleredn ins_cutorder"
  (fn _ => [ (fast_tac (cds [ins_red_props RS UnI1]) 1) ]) ;

val inssn = [ins_red_props_c, inswfdt] MRS all_sn3_c ;


    
