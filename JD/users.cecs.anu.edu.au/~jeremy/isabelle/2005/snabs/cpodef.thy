
(* common to lpo and mpo *)

theory cpodef imports orders begin

consts
  corl :: "('a relation) => ('a list relation)"

consts 
  cpo :: "('a rtree relation => 'a rtree list relation) => 
      'a relation => 'a rtree relation"
  cpocl :: "('a rtree relation => 'a rtree list relation) => 
      'a rtree relation => 'a rtree relation"
  cpocfg :: "'a relation => 'a rtree relation" 
  (* hpocl and hpocl2 have similar relation to sn1order and sn2order *)
  hpocl :: "'a set => ('a rtree relation => 'a rtree list relation) => 
      'a rtree relation => 'a rtree relation"
  hpocl2 :: "'a set => ('a rtree relation => 'a rtree list relation) => 
      'a rtree relation => 'a rtree relation"
  hpocfg :: "'a set => 'a relation => 'a rtree relation" 

inductive "cpo crel r"
  intros (* note order *)
    (* will want crel monotonic, but doing it this way avoids the
      need for yet another type class *)
    corlI : "(ts, ss) : crel (cpor) ==> cpor <= cpo crel r ==> 
      ALL t: set ts. (t, Node f ss) : cpo crel r ==> 
      (Node f ts, Node f ss) : cpo crel r"
    fgI : "(g, f) : r ==> 
        ALL t: set ts. (t, Node f ss) : cpo crel r ==> 
	(Node g ts, Node f ss) : cpo crel r"
    subtI : "si : set ss ==> (si, Node f ss) : cpo crel r"
    esubtI : "si : set ss ==> (t, si) : cpo crel r ==> 
      (t, Node f ss) : cpo crel r"
  monos ctns_mono

inductive "hpocfg S r"
  intros
    I : "(g, f) : r ==> f : S ==> (Node g ts, Node f ss) : hpocfg S r"

inductive "cpocfg r"
  intros
    I : "(g, f) : r ==> (Node g ts, Node f ss) : cpocfg r"

inductive "cpocl crel ro"
  intros
    I : "(ts, ss) : crel (fwf (ctxt ro)) ==> 
      (Node f ts, Node f ss) : cpocl crel ro"

inductive "hpocl S crel ro"
  intros
    I : "(ts, ss) : crel (fwf (ctxt ro)) ==> f : S ==> 
      (Node f ts, Node f ss) : hpocl S crel ro"

inductive "hpocl2 S crel ro"
  intros
    I : "(ts, ss) : crel (ctxt (fwf (ctxt ro))) ==> f : S ==> 
      (Node f ts, Node f ss) : hpocl2 S crel ro"

consts
  corl_props :: "('a relation => 'a list relation) => bool"
  onerel_corl :: "('a relation => 'a list relation) => bool"

defs
  onerel_corl_def : "onerel_corl crel == ALL r. onerel r <= crel r"

  corl_props_def : "corl_props crel == mono crel & onerel_corl crel &
    wf_der crel & wf_derl_fwf crel" 

end 



