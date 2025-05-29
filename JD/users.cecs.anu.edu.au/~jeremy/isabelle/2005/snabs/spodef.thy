
(* semantic path ordering, see
  Cristina Borralleras, Maria Ferreira and Albert Rubio.
  Complete Monotonic Semantic Path Orderings,
  17th (CADE).  LNCS (LNAI) 1831.
  proved well-founded using gpo *)

theory spodef imports orders gpodef begin

(** the well-founded quasi-order **)
consts
  pord_of :: "'a relation => 'a relation"

inductive "pord_of qord"
  intros
    I : "(t, s) : qord ==> (s, t) ~: qord ==> (t, s) : pord_of qord"

consts 
  spo :: " ('a rtree relation => 'a rtree list relation) =>
    'a rtree relation => 'a rtree relation"
  spo2 :: " ('a rtree relation => 'a rtree list relation) =>
    'a rtree relation => 'a rtree relation"

(* note - in r3I, the condition ALL t: set ts. (t, Node f ss) : spo crel qord
  is not included in the paper, but holds anyway when crel is the 
  derived multiset ordering *)
inductive "spo crel qord" "spo2 crel qord"
  intros (* note order *)
    r2I : "(Node g ts, s) : pord_of qord ==> ALL t: set ts.
      (t, s) : spo crel qord ==> (Node g ts, s) : spo2 crel qord"
    r3I : "(Node g ts, Node f ss) : qord ==>
      (ts, ss) : crel spot ==> spot <= (spo crel qord) ==>
      ALL t: set ts. (t, Node f ss) : spo crel qord ==> 
      (Node g ts, Node f ss) : spo2 crel qord"
    spo2I : "(t, s) : spo2 crel qord ==> (t, s) : spo crel qord"
    subtI : "si : set ss ==> (si, Node f ss) : spo crel qord"
    esubtI : "si : set ss ==> (t, si) : spo crel qord ==> 
      (t, Node f ss) : spo crel qord"
  monos ctns_mono
  
consts 
  s_gpoc :: "('a rtree relation => 'a rtree list relation) =>
    'a rtree relation => 'a rtree relation => 'a rtree relation"

inductive "s_gpoc screl qord r"
  intros 
    r2I : "(t, s) : pord_of qord ==> (t, s) : s_gpoc screl qord r"
    r3I : "(Node g ts, Node f ss) : qord ==> 
      (ts, ss) : screl r ==> (Node g ts, Node f ss) : s_gpoc screl qord r" 

consts
  spoc_props :: "('a relation => 'a list relation) => bool"

defs
  spoc_props_def : "spoc_props crel == mono crel & 
    wf_der crel & wf_derl_fwf crel" 

end 



