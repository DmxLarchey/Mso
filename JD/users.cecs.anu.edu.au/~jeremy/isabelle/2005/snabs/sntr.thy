
theory sntr imports redn rewr begin 
 
axclass rewr < type (* for which rewrite relation exists *)

consts
  (* these now parameterized by "primitive" reduction *)
  snHered :: "('a rtree * 'a rtree) set => 'a rtree => bool"

defs
  snHered_def : "snHered r dt == 
    set (isubts dt) <= wfp (ctxt r) --> dt : wfp (ctxt r)"

(* symbol type, not further specified, with a well-founded ordering,
  used in several subsequent cases *)
consts symborder :: "('a * 'a) set" 

axclass symbwf < rewr
  wf_symborder : "wf symborder"

typedecl symb
arities symb :: symbwf

consts 
  ruleredn    :: "('a::rewr rtree * 'a::rewr rtree) set"
  cutorder    :: "('a::rewr rtree * 'a::rewr rtree) set"
  dtorder    :: "('a::rewr rtree * 'a::rewr rtree) set"

inductive "dtorder" (* order based on ... *)
  intros
    dtc : "dts : cutorder ==> dts : dtorder"
    snr : "dts : sn1order ruleredn ==> dts : dtorder"

consts
  prs :: "('a rtree * 'a rtree) set => ('a rtree * 'a rtree) set"
  prp2 :: "('a rtree * 'a rtree) set =>
    ('a rtree * 'a rtree) set => ('a rtree * 'a rtree) set"
  prp2all :: "('a rtree * 'a rtree) set =>
    ('a rtree * 'a rtree) set => ('a rtree * 'a rtree) set"
  prp :: "('a rtree * 'a rtree) set =>
    ('a rtree * 'a rtree) set => ('a rtree * 'a rtree) set"

inductive "prp rho cuto"
  intros
    prpI : "ALL dts. (dts, dtn) : subt --> set (isubts dt) <= wfp (ctxt rho) -->
	   dts : wfp (ctxt rho) | (dts, dt) : (cuto Un sn1order rho)^+ ==> 
	  (dtn, dt) : prp rho cuto"

inductive "prs rho"
  intros
    prsI : "(dts, dt) : psubt O (ctxt rho)^* O subt ==>
      (dts, dt) : prs rho" 

inductive "prp2 rho cuto"
  intros
    prsI : "(dts, dt) : prs rho ==> (dts, dt) : prp2 rho cuto" 
    dtI : "(dts, dt) : (cuto Un sn1order rho)^+ ==>
      (dts, dt) : prp2 rho cuto" 

inductive "prp2all rho cuto"
  intros
    I : "ALL dts. (dts, dtn) : subt --> (dts, dt) : prp2 rho cuto ==>
        (dtn, dt) : prp2all rho cuto"

(* class incorporating requirement derived from Thm 1, cond'n (iv) of 
  Jean Goubault-Larrecq.  Well-founded recursive relations. (CSL'2001) *)

consts
  dtjgl :: "'a rtree relation => 'a rtree relation => bool"

defs
  dtjgl_def : "dtjgl rho cuto == ALL dt. 
    dt : bars ((cuto Un sn1order rho)^+) (Collect (snHered rho))"

end


