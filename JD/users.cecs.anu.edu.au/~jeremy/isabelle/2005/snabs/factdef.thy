
(* proof of termination of factorial example,
  Dershowitz, 33 Examples, example 21, and 
  Dershowitz, Natural Termination, pg 3 *)

theory factdef imports orders_c horders begin 

datatype fact = F | P | Pl | T | S | Z | F0 nat

arities fact :: rewr

consts
  fact_ruleredn :: "fact rule set"
  fact_cutorder :: "fact rule set"
  fcsymb  :: "fact rule set"
  fc1  :: "fact rule set"

inductive "fact_ruleredn"
  intros
    r0 : "(x, Node P [Node S [x]]) : fact_ruleredn"
    r1 : "(Node Z [], Node F [Node Z []]) : fact_ruleredn"
    r2 : "(Node T [Node S [x], Node F [Node P [Node S [x]]]],
      Node F [Node S [x]]) : fact_ruleredn"
    r3 : "(Node Z [], Node T [Node Z [], y]) : fact_ruleredn"
    r4 : "(Node Pl [Node T [x,y], y], Node T [Node S [x], y]) : fact_ruleredn"
    r5 : "(x, Node Pl [x, Node Z []]) : fact_ruleredn"
    r6 : "(Node S [Node Pl [x,y]], Node Pl [x, Node S [y]]) : fact_ruleredn"
    (* additional rules *)
    simpS : "(y, Node S [y]) : fact_ruleredn"
    
inductive "fcsymb"
  intros
    SF : "(Node S x, Node F y) : fcsymb"
    TF : "(Node T x, Node F y) : fcsymb"
    ST : "(Node S x, Node T y) : fcsymb"
    PlT : "(Node Pl x, Node T y) : fcsymb"
    SPl : "(Node S x, Node Pl y) : fcsymb"
    PF : "(Node P x, Node F y) : fcsymb"
    
inductive "fc1"
  intros
    I1 : "(Node F [Node P [Node S [x]]], Node F [Node S [x]]) : fc1"
    I2 : "(Node F [Node P [x]], Node F [Node S [x]]) : fc1"
    
defs
  factcdef : "fact_cutorder == fcsymb Un fc1"

end 


