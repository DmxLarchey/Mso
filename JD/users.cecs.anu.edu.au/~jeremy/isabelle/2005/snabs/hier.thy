

(* getting a reduction relation for rtrees by 
  formalising substitution for variables *)

theory hier imports substc begin 

typedecl symb

arities
  symb :: type

consts
  S0 :: "symb set"
  rules0 :: "(symb stree * symb stree) set"
  rho1 :: "(symb rtree * symb rtree) set"
  cut1 :: "(symb rtree * symb rtree) set"
  cuth :: "'a set => 'a srule set => 'a rule set => 'a rule set"
  cuth_alt :: "'a set => 'a srule set => 'a rule set => 'a rule set"
  cutd :: "'a set => ('a rtree * 'a rtree) set"
  rhier :: "(symb rtree * symb rtree) set"
  sn2_alt :: "'a set => 'a srule set => 'a rule set => 'a rule set"
  cut1_gip_epr :: "'a rule set => 'a rule set => 'a set => bool"
  cut1_dvk_epr :: "'a rule set => 'a rule set => 'a set => bool"

defs
  rhier_def : "rhier == subs rules0 Un rho1"

inductive "cutd S"
  intros
    I : "a : S ==> b ~: S ==> (Node a ts, Node b ss) : cutd S"

defs
  cuth_def : "cuth S rs0 c1 == subs (cut0 S rs0) Un c1"
  cuth_alt_def : "cuth_alt == cuth"
  (* $<'_{sn2}$ of paper *)
  sn2_alt_def : "sn2_alt S r0s r1s == 
    (ctxt (hds_notin S Int nured (subs r0s Int wfpc (subs r0s Un r1s))) Un
      nured (r1s Int wfpc (subs r0s Un r1s)))"
  cut1_gip_epr_def : "cut1_gip_epr c1 r1s S == 
    ALL X. X <= hds_notin (-S) --> gip_cond c1 (sn2order (X Un r1s))"
  cut1_dvk_epr_def : "cut1_dvk_epr c1 r1s S == 
    ALL X. X <= hds_notin (-S) --> dvk_cond c1 (sn2order (X Un r1s))"

axioms
  wf0 : "wf (ctxt (subs rules0))"
  rules0_proph : "rules0 <= (rule0_proph S0)"
  cut1_symb : "(t, s) : cut1 ==> symb_of s ~: S0"

end

