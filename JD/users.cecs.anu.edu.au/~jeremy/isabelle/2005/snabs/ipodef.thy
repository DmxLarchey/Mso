


(* hierarchical (incremental) rpo *)

theory ipodef imports horders cpodef begin

consts 
  ipo :: "'a rtree relation => 'a set => 
    ('a rtree relation => 'a rtree list relation) => 
      'a relation => 'a rtree relation"
  ipo1 :: "'a rtree relation => 'a set => 
    ('a rtree relation => 'a rtree list relation) => 
      'a relation => 'a rtree relation"

(* NOTE - hpocl and hpocfg in cpodef *)

inductive "ipo sig S crel r" "ipo1 sig S crel r"
  intros (* note order *)
    (* will want crel monotonic, but doing it this way avoids the
      need for yet another type class *)
    corlI : "(ts, ss) : crel (ipor) ==> ipor <= ipo sig S crel r ==> 
      ALL t: set ts. (t, Node f ss) : ipo sig S crel r ==> f ~: S ==> 
      (Node f ts, Node f ss) : ipo1 sig S crel r"
    fgI : "(g, f) : r ==> f ~: S ==> 
        ALL t: set ts. (t, Node f ss) : ipo sig S crel r ==> 
	(Node g ts, Node f ss) : ipo1 sig S crel r"
    subtI : "si : set ss ==> f ~: S ==> (si, Node f ss) : ipo1 sig S crel r"
    esubtI : "si : set ss ==> f ~: S ==> (t, si) : ipo sig S crel r ==> 
      (t, Node f ss) : ipo1 sig S crel r"
    ipo1I : "(t, s) : ipo1 sig S crel r ==> (t, s) : ipo sig S crel r"
    hierI : "(t, s) : sig ==> (t, s) : ipo sig S crel r"
    pctxtI : "(t, s) : nured (ipo sig S crel r) ==> (t, s) : ipo sig S crel r"
  monos ctns_mono nured_mono

end 




