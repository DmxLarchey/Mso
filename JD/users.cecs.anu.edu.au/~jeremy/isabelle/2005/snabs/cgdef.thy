
(* try to do cpo using our gpo stuff *)

theory cgdef imports cpodef gpodef begin

consts 
  cpoc :: "('a * 'a) set => 
    ('a rtree relation => 'a rtree list relation) => 
     'a rtree relation => 'a rtree relation"
  cpoc2 :: "('a rtree relation => 'a rtree list relation) => 
     'a rtree relation => 'a rtree relation"

inductive "cpoc2 crel r"
  intros
    corlI : "(ts, ss) : crel r ==> (Node f ts, Node f ss) : cpoc2 crel r"

inductive "cpoc symo crel r"
  intros (* note order *)
    corlI : "(t, s) : cpoc2 crel r ==> (t, s) : cpoc symo crel r"
    fgI : "(t, s) : cpocfg symo ==> (t, s) : cpoc symo crel r"
    
end 


