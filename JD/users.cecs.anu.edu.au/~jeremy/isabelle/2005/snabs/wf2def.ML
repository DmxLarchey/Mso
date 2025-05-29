
structure wf2def = struct val thy = theory "wf2def" end ;
use_legacy_bindings wf2def.thy ;
fun u _ = use_thy "wf2def" ;

val wf_tpcr = wf_cr RS wf_psubt_redn RS wf_trancl ;

val _ = qed_goalw "wf2wfdt" wf2def.thy [wf2cdef]
  "wf (wf2_cutorder Un sn1order wf2_ruleredn)"
  (fn _ => [ (rtac (wf_cr RS wf_dtwf) 1)]) ;

val _ = qed_goalw_spec_mp "wf2_red_props" wf2def.thy [wf2cdef, subt_def]
  "(dtn, dt) : wf2_ruleredn --> (dts, dtn) : subt --> \
    \ (dts, dt) : psubt | (dts, dt) : wf2_cutorder" (fn _ => [ Fast_tac 1 ]) ;

val _ = qed_goalw_spec_mp "wf2_red_props_pc" wf2def.thy [red_props_pc_def]
  "red_props_pc wf2_ruleredn wf2_cutorder"
  (fn _ => [ (fast_tac (cds [wf2_red_props]) 1) ]) ;

val wf2sn = [wf2_red_props_pc, wf2wfdt] MRS all_sn3_pc ;

    

