
(* proof of termination of an arbitrary terminating system using our theorem *)

theory wf2def imports orders begin 

typedecl symb

arities symb :: rewr

consts
  wf2_cutorder :: "(symb rtree * symb rtree) set"
  wf2_ruleredn :: "(symb rtree * symb rtree) set"

axioms
  wf_cr : "wf (ctxt wf2_ruleredn)"
  
defs
  wf2cdef : "wf2_cutorder == wf2_ruleredn O subt"

end 


