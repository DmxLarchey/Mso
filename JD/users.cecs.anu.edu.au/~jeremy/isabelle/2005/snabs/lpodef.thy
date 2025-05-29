
(* try to do lpo same as mpo *)

theory lpodef 
imports cpodef 
begin

consts 
  lpo :: "('a * 'a) set => 'a rule set"

inductive "lpo r"
  intros (* note order *)
    lexI : "(ts, ss) : lex (lpo r) ==>
      ALL t: set ts. (t, Node f ss) : lpo r ==> 
      (Node f ts, Node f ss) : lpo r"
    fgI : "(g, f) : r ==> 
        ALL t: set ts. (t, Node f ss) : lpo r ==> 
	(Node g ts, Node f ss) : lpo r"
    subtI : "si : set ss ==> (si, Node f ss) : lpo r"
    esubtI : "si : set ss ==> (t, si) : lpo r ==> (t, Node f ss) : lpo r"
  monos lex_mono

end 


