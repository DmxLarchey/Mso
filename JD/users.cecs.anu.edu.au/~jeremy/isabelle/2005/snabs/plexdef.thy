
(* proof of well-foundedness of lexicographic order *)

theory plexdef imports orders begin 

consts
  plc1 :: "(symb rtree * symb rtree) set"
  plc2 :: "(symb rtree * symb rtree) set"
  plex_ruleredn :: "(symb rtree * symb rtree) set"
  plex_cutorder :: "(symb rtree * symb rtree) set"

inductive "plc1"
  intros
    I : "depth t < depth u ==> (t, u) : plc1"

inductive "plc2"
  intros
    I : "(x, y) : symborder ==> depth (Node x ls) <= depth (Node y ms) ==>
	(Node x ls, Node y ms) : plc2"

defs
  plexrdef : "plex_ruleredn == plc2"
  plexcdef : "plex_cutorder == plc1 Un plc2"

end 



