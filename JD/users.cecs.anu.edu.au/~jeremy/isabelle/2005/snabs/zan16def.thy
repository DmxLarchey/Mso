
(* proof of termination of example on 
  Zantema, The Termination Hierarchy for Term Rewriting, Prop'n 16 *)

theory zan16def imports orders_c begin 

datatype zan16 = F | G | H | I

arities zan16 :: rewr

consts
  zan16_ruleredn :: "(zan16 rtree * zan16 rtree) set"
  zan16_cut :: "(zan16 rtree * zan16 rtree) set"

inductive "zan16_ruleredn"
  intros
    r0 : "(tree [G,G,F] x, tree [F,G] x) : zan16_ruleredn"
    r1 : "(tree [F,F,H] x, tree [H,F] x) : zan16_ruleredn"
    r2 : "(tree [H,I] x, tree [G,H] x) : zan16_ruleredn"
    simpF : "(x, Node F [x]) : zan16_ruleredn"
    simpG : "(x, Node G [x]) : zan16_ruleredn"
    
inductive "zan16_cut"
  intros
    FHF : "(Node F x, tree [H,F] y) : zan16_cut"
    IG : "(tree [I] x, tree [G] y) : zan16_cut"
    HIG : "(tree [H,I] x, tree [G] y) : zan16_cut"
    GF : "(Node G x, tree [F] y) : zan16_cut"

end 


