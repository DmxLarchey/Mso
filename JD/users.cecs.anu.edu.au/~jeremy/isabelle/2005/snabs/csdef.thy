
(* use results on spo ordering to prove wf of cpo ordering *)

theory csdef 
imports cgdef spodef 
begin
  
consts
  qord_of :: "'a relation => 'a rtree relation"

inductive "qord_of symo"
  intros
    ffI : "(Node f ts, Node f ss) : qord_of symo"
    fgI : "(g, f) : symo ==> (Node g ts, Node f ss) : qord_of symo"
   
end

