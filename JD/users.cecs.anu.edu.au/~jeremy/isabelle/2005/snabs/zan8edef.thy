
(* proof of termination of second and fifth example on 
  Zantema, The Termination Hierarchy for Term Rewriting, p8 *)

theory zan8edef imports orders_c begin 

datatype zan8e = F | G | H 

arities zan8e :: rewr

consts
  zan8e_ruleredn :: "(zan8e rtree * zan8e rtree) set"
  zan8e_cut :: "(zan8e rtree * zan8e rtree) set"

inductive "zan8e_ruleredn"
  intros
    (* first rule is from (b) *)
    r0 : "(tree [G,F,F,H] x, tree [F,G,F] x) : zan8e_ruleredn"
    r1 : "(tree [H,G,G,F,F,H] x, tree [F,G] x) : zan8e_ruleredn"
    (* this rule is from (d), with strings reversed, and F <-> H *)
    r2 : "(tree [G,G,F,F,H] x, tree [F,G,H] x) : zan8e_ruleredn"
    
inductive "zan8e_cut"
  intros
    HF : "(Node H x, Node F y) : zan8e_cut"
    HG : "(Node G x, Node F y) : zan8e_cut"
    FHFG : "(tree [F,H] x, tree [F,G] y) : zan8e_cut"
    FFHFG : "(tree [F,F,H] x, tree [F,G] y) : zan8e_cut"

end 


