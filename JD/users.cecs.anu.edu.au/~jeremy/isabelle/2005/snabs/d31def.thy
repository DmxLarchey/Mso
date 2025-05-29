
(* proof of termination of Dershowitz, 33 Examples, example 31 *)

theory d31def imports orders_c begin 

datatype d31 = F | G | A | T | P 

arities d31 :: rewr

consts
  d31_ruleredn :: "(d31 rtree * d31 rtree) set"
  d31_cutorder :: "(d31 rtree * d31 rtree) set"
  dc1  :: "(d31 rtree * d31 rtree) set"
  dc2  :: "(d31 rtree * d31 rtree) set"
  dc3  :: "(d31 rtree * d31 rtree) set"

inductive "d31_ruleredn"
  intros
    assocTI : "(Node T [x, Node T [y, z]],
      Node T [Node T [x, y], z]) : d31_ruleredn" 
    (*
    distI : "(Node P [Node T [x, y], Node T [x, z]], 
      Node T [x, Node P [y, z]]) : d31_ruleredn"
      *)
    rdistI : "(Node P [Node T [x, z], Node T [y, z]], 
      Node T [Node P [x, y], z]) : d31_ruleredn"
    specI : "(Node T [Node G [z,y], Node P [x, Node A []]],
      Node T [z, Node P [x, Node F [y]]]) : d31_ruleredn"
    (* additional rules *)
    leftTI : "(x, Node T [x, y]) : d31_ruleredn"
    rightTI : "(y, Node T [x, y]) : d31_ruleredn"
    leftPI : "(x, Node P [x, y]) : d31_ruleredn"
    rightPI : "(y, Node P [x, y]) : d31_ruleredn"
    FA : "(Node A [], Node F y) : d31_ruleredn"
    
inductive "dc1"
  intros
    FA : "(Node A x, Node F y) : dc1"
    TA : "(Node A x, Node T y) : dc1"
    TG : "(Node G x, Node T y) : dc1"
    TP : "(Node P x, Node T y) : dc1"
    specI : "(Node T [Node G [z',y'], Node P [x, Node A []]],
      Node T [z, Node P [x, Node F [y]]]) : dc1"
    specaI : "(Node T [Node G [z',y'], Node A []],
      Node T [z, Node P [x, Node F [y]]]) : dc1"
    
inductive "dc2"
  intros
    I : "(Node T [x, y'], Node T [Node T [x, z], y]) : dc2"

inductive "dc3"
  intros
    specxI : "(Node T [Node G [z',y'], x],
      Node T [z, Node P [x, Node F [y]]]) : dc3"

defs
  d31cdef : "d31_cutorder == dc1 Un (dc2 Un dc3)"

end 



