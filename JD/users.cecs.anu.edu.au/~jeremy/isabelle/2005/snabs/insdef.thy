
(* proof of termination of insertion sort,
  Dershowitz, 33 Examples, example 32, and 
  Dershowitz, Natural Termination, pg 16-17 *)

theory insdef imports orders_c begin 

datatype ins = Sort | Ins | Ch | S | Z | N | C 

arities ins :: rewr

consts
  ins_ruleredn :: "(ins rtree * ins rtree) set"
  ins_cutorder :: "(ins rtree * ins rtree) set"
  icsymb :: "(ins rtree * ins rtree) set"
  ic1 :: "(ins rtree * ins rtree) set"
  ic2 :: "(ins rtree * ins rtree) set"
  ic3 :: "(ins rtree * ins rtree) set"
  ic12 :: "(ins rtree * ins rtree) set"

inductive "ins_ruleredn"
  intros
    r0 : "(Node N [], Node Sort [Node N []]) : ins_ruleredn"
    r1 : "(Node Ins [x, Node Sort [y]], Node Sort [Node C [x,y]]) :
      ins_ruleredn"
    r2 : "(Node C [x, Node N []], Node Ins [x, Node N []]) : ins_ruleredn"
    r3 : "(Node Ch [x, Node C [v,w], x, v], 
      Node Ins [x, Node C [v,w]]) : ins_ruleredn"
    r4 : "(Node C [x, Node C [v,w]], 
      Node Ch [x, Node C [v,w], y, Node Z []]) : ins_ruleredn"
    r5 : "(Node C [v, Node Ins [x,w]], 
      Node Ch [x, Node C [v,w], Node Z [], Node S [z]]) : ins_ruleredn"
    r6 : "(Node Ch [x, Node C [v,w], y, z],
      Node Ch [x, Node C [v,w], Node S [y], Node S [z]]) : ins_ruleredn"
    (* additional rules *)
    simpC : "(y, Node C [x,y]) : ins_ruleredn"
    
inductive "icsymb"
  intros
    CS : "(Node C x, Node Sort y) : icsymb"
    CI : "(Node C x, Node Ins y) : icsymb"
    CC : "(Node C x, Node Ch y) : icsymb"
    SI : "(Node Ins x, Node Sort y) : icsymb"
    
inductive "ic1"
  intros
    ChI : "(Node Ch [y,w,a,b], Node Ins [x,w]) : ic1"
    
inductive "ic2"
  intros
    ICh : "(Node Ins [x,w], Node Ch [y, Node C [z,w], a,b]) : ic2"
    
inductive "ic12"
  intros
    I : "(Node Ch [y,w,a,b], Node Ch [y', Node C [z,w], a',b']) : ic12"
    
inductive "ic3"
  intros
    r6 : "(Node Ch [x, w, y, z], Node Ch [x, w, Node S [y], z']) : ic3"

defs
  inscdef : "ins_cutorder == icsymb Un ((ic1 Un ic2) Un ic3)"

end 


