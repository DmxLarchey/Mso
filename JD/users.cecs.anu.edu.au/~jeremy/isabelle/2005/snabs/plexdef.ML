
structure plexdef = struct val thy = theory "plexdef" end ;
use_legacy_bindings plexdef.thy ;
fun u _ = use_thy "plexdef" ;

val pl_intrs = [plc1.I, plc2.I] ;
val pl_elims = [plc1.elims, plc2.elims] ;
val pl_cs = (ces pl_elims addSIs pl_intrs) ;
val pl_css = (pl_cs, simpset ()) ;

val _ = qed_goalw "plc1_ii" plexdef.thy [inv_image_def] 
  "plc1 = inv_image less_than depth"
  (fn _ => [ (force_tac pl_css 1) ]) ;

val _ = qed_goal "wf_plc1" plexdef.thy "wf plc1"
  (fn _ => [(simp_tac (esimps [plc1_ii]) 1)]) ;
  
val _ = qed_goalw "plc2_ii" plexdef.thy [inv_image_def] 
  "plc2 <= inv_image symborder symb_of" 
  (fn _ => [ (force_tac pl_css 1) ]) ;

val _ = qed_goal "wf_plc2" plexdef.thy "wf plc2"
  (fn _ => [ (rtac wf_subset 1), (rtac plc2_ii 2),
    (rtac wf_inv_image 1), (rtac wf_symborder 1) ]) ;

val _ = qed_goal "plexwfc12" plexdef.thy "wf (plc1 Un plc2)"
  (fn _ => [ (rtac wfUn_absr 1), (safe_tac pl_cs),
    Force_tac 1, (rtac wf_plc2 1), (rtac wf_plc1 1) ]) ;

val _ = bind_thm ("plexwfcut", fold_rule [plexcdef] plexwfc12) ;

val _ = qed_goalw_spec_mp "plex_red_props_pc'" plexdef.thy 
  [subt_def, plexcdef]
  "(dtn, dt) : plc2 --> (dts, dtn) : subt --> \
    \ (dts, dt) : psubt | (dts, dt) : plex_cutorder"
  (fn _ => [ 
    (safe_tac (ces [plc2.elims] addSDs [psubt_depth])), 
    (auto_tac (cis pl_intrs, simpset ())) ]) ; 

val plex_red_props_pc'' = fold_rule [plexrdef] plex_red_props_pc' ;

val _ = qed_goal_spec_mp "red2_depth" plexdef.thy 
  "(dts, dt) : ctxt plc2 --> depth dts <= depth dt"
  (fn _ => [ (safe_tac (ces [ron.induct, oneup.elims, plc2.elims])),
    (etac onerel.induct 1), ALLGOALS Asm_full_simp_tac ]) ; 

val _ = qed_goal "plexwfdt'" plexdef.thy 
  "wf (plex_cutorder Un sn1order plc2)"
  (fn _ => [ (rtac wfUn_absr 1), (rtac plexwfcut 3), 
    (rtac wf_sn1order 2), (rewtac plexcdef),
    (safe_tac (pl_cs addSDs [sn1o_nured'])),
    (dtac red_nured 1), (dtac red2_depth 1), arith_tac 1,
    (case_tac "a" 1), (safe_tac pl_cs),
    (dtac red_nured 2), (dtac red2_depth 2), arith_tac 2,
    (rewtac nured_def), (etac oneup.elims 1), Asm_full_simp_tac 1 ]) ;

val _ = qed_goalw "plexwfdt" plexdef.thy [plexrdef]
  "wf (plex_cutorder Un sn1order plex_ruleredn)"
  (fn _ => [ (rtac plexwfdt' 1) ]) ;

val _ = qed_goalw "plex_red_props_pc" plexdef.thy [red_props_pc_def]
  "red_props_pc plex_ruleredn ?cuto"
  (fn _ => [ (strip_tac 1), (eatac plex_red_props_pc'' 1 1) ]) ;

val plexsn = [plex_red_props_pc, plexwfdt] MRS all_sn3_pc ;
val plexwf = plexsn RS wfp_wfI ;


