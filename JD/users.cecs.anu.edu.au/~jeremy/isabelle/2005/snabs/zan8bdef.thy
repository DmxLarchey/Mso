
(* proof of termination of second example on 
  Zantema, The Termination Hierarchy for Term Rewriting, p8 *)

theory zan8bdef imports orders_c begin 

datatype zan8b = F | G | H 

arities zan8b :: rewr

consts
  zan8b_ruleredn :: "(zan8b rtree * zan8b rtree) set"
  zan8b_cut :: "(zan8b rtree * zan8b rtree) set"

inductive "zan8b_ruleredn"
  intros
    r0 : "(tree [G,F,F,H] x, tree [F,G,F] x) : zan8b_ruleredn"
    r1 : "(tree [F,H] x, tree [G,F] x) : zan8b_ruleredn"
    
inductive "zan8b_cut"
  intros
    HF : "(Node H x, Node F y) : zan8b_cut"
    HG : "(Node H x, Node G y) : zan8b_cut"
    FHG : "(Node F [Node H x], Node G y) : zan8b_cut"
    FHFG : "(Node F [Node H x], Node F [Node G y]) : zan8b_cut"
    GFG : "(Node G x, Node F [Node G y]) : zan8b_cut"

end 


