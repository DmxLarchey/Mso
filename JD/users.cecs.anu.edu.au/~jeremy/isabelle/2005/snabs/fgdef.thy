
(* proof of termination of f(f(x)) --> f(g(f(x))),
  Dershowitz, 33 Examples of Termination, example 5 *)

theory fgdef imports orders begin 

datatype fg = F | G

arities fg :: rewr

consts
  fg_ruleredn :: "(fg rtree * fg rtree) set"
  fg_cutorder :: "(fg rtree * fg rtree) set"
  fg_cutorder_n :: "((fg rtree * fg rtree) * nat) set"

inductive "fg_ruleredn"
  intros
    I : "(Node F [Node G [Node F y]], Node F [Node F y]) : fg_ruleredn"
    
inductive "fg_cutorder_n"
  intros
    (* integer indicates location of difference *)
    fgI : "((Node G w, Node F z), 0) : fg_cutorder_n"
    subI : "((w, z), n) : fg_cutorder_n ==> 
      ((Node F [w], Node F [z]), Suc n) : fg_cutorder_n"

inductive "fg_cutorder"
  intros
    I : "(x, n) : fg_cutorder_n ==> x : fg_cutorder"

(* can't do this
datatype 'a chain = Cn "'a" "'a chain"
Nonemptiness check failed for datatype fgdef.chain
*)

end 


