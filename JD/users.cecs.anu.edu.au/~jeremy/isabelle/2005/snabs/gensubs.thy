
(* additional stuff, to try to extend results *)

theory gensubs imports orders bdrel begin 

consts 
  allsubs :: "'a relation => 'a relation => 'a relation"
  exsub :: "'a relation => 'a relation => 'a relation"

inductive "allsubs sub rho"
  intros
    I : "(ALL r'. (r', r) : sub --> (r', l) : rho) ==>
      ((r, l) : allsubs sub rho)"

inductive "exsub sub rho"
  intros
    I : "(l', l) : sub ==> (r, l') : rho ==> ((r, l) : exsub sub rho)"

end

