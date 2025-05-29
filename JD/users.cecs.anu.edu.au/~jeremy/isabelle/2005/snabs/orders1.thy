
theory orders1 imports sntr WfUn begin 
 
consts
  red_props_c :: "'a rtree relation => 'a rtree relation => bool"
  red_props_pc :: "'a rtree relation => 'a rtree relation => bool"
  red_props_crel :: " 'a rtree relation => 'a set => 
    ('a rtree relation => 'a rtree list relation) =>'a rtree relation => bool"
  red_props_g :: "'a rtree relation => 'a rtree relation => bool"
  red_props_dt :: "'a rtree relation => 'a rtree relation => bool"
  red_props_c2 :: "'a rtree relation => 'a rtree relation => bool"
  red_props_nr :: "'a rtree relation => 'a rtree relation => bool"
  red_props_c2f :: 
    "'a rtree relation => 'a rtree relation => 'a rtree => bool"
  red_props_nrf :: 
    "'a rtree relation => 'a rtree relation => 'a rtree => bool"

defs
  red_props_nrf_def : "red_props_nrf rho cuto dt == ALL dtn dts. 
    (dtn, dt) : rho --> (dts, dtn) : subt --> 
	    (dts, dt) : psubt O rho^* | (dts, dt) : cuto"

  (* using psubts dt would be enough in this condition *)
  red_props_nr_def : "red_props_nr rho cuto == ALL dt.
     set (isubts dt) <= wfp rho --> red_props_nrf rho cuto dt"

  red_props_dt_def : "red_props_dt rho cuto == rho <= prp rho cuto"
  red_props_c2f_def : "red_props_c2f rho cuto dt == 
    ALL dtn. (dtn, dt) : rho --> (dtn, dt) : prp2all rho cuto"
  red_props_c2_def : "red_props_c2 rho cuto == 
    ALL dt. set (isubts dt) <= wfp (ctxt rho) --> red_props_c2f rho cuto dt" 

  red_props_g_def : "red_props_g rho S == ALL dt dtn dts.
    (dtn, dt) : rho --> (dts, dtn) : subt --> (dts, dt) : S"

  red_props_pc_defg : "red_props_pc rho cuto == red_props_g rho (psubt Un cuto)"

  red_props_c_defg : "red_props_c rho cuto == red_props_g rho 
    (psubt Un cuto Un (nured rho)^+ Un ((nured rho)^* O cuto))"

  red_props_crel_def : "red_props_crel rho S crel cuto == red_props_g rho 
     ((psubt O (ctxt rho)^* O subt) Un cuto Un (nured rho)^+ Un
       oneupS S (crel (ctxt rho)))"

(* note - Dershowitz & Hoot's proof of wf of gpo relies on slightly
  stronger conditions, namely that gpo O subt <= gpo, gpo <= subt O gpo2,
  and that gpo2 is wf on terms whose proper subterms are wf *)

end



