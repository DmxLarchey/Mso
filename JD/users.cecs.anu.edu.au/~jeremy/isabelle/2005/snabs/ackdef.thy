
(* proof of termination of evaluation of Ackerman's function,
  Dershowitz, 33 Examples of Termination, example 29 *)

theory ackdef imports orders_c begin 

datatype ack = A | S | Z 

arities ack :: rewr

consts
  ack_ruleredn :: "(ack rtree * ack rtree) set"
  ack_cutorder :: "(ack rtree * ack rtree) set"
  acr0 :: "(ack rtree * ack rtree) set"
  acr1 :: "(ack rtree * ack rtree) set"
  acr2 :: "(ack rtree * ack rtree) set"

inductive "ack_ruleredn"
  intros
    r0 : "(Node S [y], Node A [Node Z [], y]) : ack_ruleredn"
    r1 : "(Node A [x, Node S [Node Z []]],
      Node A [Node S [x], Node Z []]) : ack_ruleredn"
    r2 : "(Node A [x, Node A [Node S [x], y]],
      Node A [Node S [x], Node S [y]]) : ack_ruleredn"
    
inductive "acr0"
  intros
    I : "(Node S w, Node A z) : acr0"
inductive "acr1"
  intros
    I : "(Node A [x, y], Node A [Node S [x], z]) : acr1"
inductive "acr2"
  intros
    I : "(Node A [x, y], Node A [x, Node S [y]]) : acr2"

defs
  ackcdef : "ack_cutorder == acr0 Un acr1 Un acr2"

end 

