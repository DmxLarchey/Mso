
(* proof of termination of distributive rule, and differentiation *)

theory distdef imports orders_c begin 

datatype dist = P | T | D

arities dist :: rewr

consts
  dist_ruleredn :: "(dist rtree * dist rtree) set"
  dist_cutorder :: "(dist rtree * dist rtree) set"
  dcofg :: "(dist rtree * dist rtree) set"
  dcoaT :: "(dist rtree * dist rtree) set"
  dcoaP :: "(dist rtree * dist rtree) set"

inductive "dist_ruleredn"
  intros
    leftPI : "(x, Node P [x, y]) : dist_ruleredn"
    rightPI : "(y, Node P [x, y]) : dist_ruleredn"
    leftTI : "(x, Node T [x, y]) : dist_ruleredn"
    rightTI : "(y, Node T [x, y]) : dist_ruleredn"
    distI : "(Node P [Node T [x, y], Node T [x, z]], 
      Node T [x, Node P [y, z]]) : dist_ruleredn"
    diffTI : "(Node P [Node T [x, Node D [y]],
      Node T [Node D [x], y]], Node D [Node T [x, y]]) : dist_ruleredn"
    rdistI : "(Node P [Node T [y, x], Node T [z, x]], 
      Node T [Node P [y, z], x]) : dist_ruleredn"
    diffPI : "(Node P [Node D [y], Node D [z]], 
      Node D [Node P [y, z]]) : dist_ruleredn"
    (* to include 
      *)
    assocTI : "(Node T [x, Node T [y, z]],
      Node T [Node T [x, y], z]) : dist_ruleredn" 
    assocPI : "(Node P [x, Node P [y, z]],
      Node P [Node P [x, y], z]) : dist_ruleredn" 
    
inductive "dcofg"
  intros
    PTI : "(Node P x, Node T y) : dcofg"
    PDI : "(Node P x, Node D y) : dcofg"
    TDI : "(Node T x, Node D y) : dcofg"

inductive "dcoaT"
  intros
    I : "(x', x) : isubt ==> (Node T [x', y'], Node T [x, y]) : dcoaT"

inductive "dcoaP"
  intros
    I : "(x', x) : isubt ==> (Node P [x', y'], Node P [x, y]) : dcoaP" 

defs
  distcdef : "dist_cutorder == dcofg Un (dcoaP Un dcoaT)"

end 



