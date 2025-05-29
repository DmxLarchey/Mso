
(* proof of termination of example on 
  Zantema, The Termination Hierarchy for Term Rewriting, Prop'n 15 *)

theory zan15def imports orders_c begin 

datatype zan15 = F | G | H 

arities zan15 :: rewr

consts
  zan15_ruleredn :: "(zan15 rtree * zan15 rtree) set"
  zan15_cut :: "(zan15 rtree * zan15 rtree) set"

inductive "zan15_ruleredn"
  intros
    r0 : "(tree [G,F] x, tree [F,F] x) : zan15_ruleredn"
    r1 : "(tree [F,G,H] x, tree [G,G] x) : zan15_ruleredn"
    
inductive "zan15_cut"
  intros
    F : "(Node G x, tree [F,F] y) : zan15_cut"
    G3 : "(tree [F,G,H] x, tree [G,G] y) : zan15_cut"
    G2 : "(tree [G,H] x, tree [G,G] y) : zan15_cut"
    G1 : "(Node H x, tree [G,G] y) : zan15_cut"

end 


