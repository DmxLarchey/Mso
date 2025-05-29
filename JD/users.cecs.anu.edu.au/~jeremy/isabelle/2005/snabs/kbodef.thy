
theory kbodef imports orders_c begin

consts 
  h :: "symb" (* the symbol with weight 0, if any *)
  sw :: "symb => nat" (* symbol weight *)
  tw :: "symb rtree => nat" (* term weight *)
  tws :: "symb rtree list => nat" (* weight of list of terms *)
  kbo :: "symb rule set"
  kbo_cutorder :: "symb rule set"

primrec
  tws_Cons : "tws (t # ts) = tw t + tws ts"
  tws_Nil : "tws [] = 0"

  (* note that actual Knuth-Bendix definition allow symbol weight 0
    only for a unary symbol *)
  tw_def : "tw (Node f ts) = 
    sw f + tws ts + (if ts = [] & sw f = 0 then Suc 0 else 0)"

inductive "kbo"
  intros (* note order *)
    lexI : "tw (Node f ts) <= tw (Node f ss) ==> 
      (ts, ss) : lex (kbo) ==> (Node f ts, Node f ss) : kbo"
    fgI : "(g, f) : symborder ==> tw (Node g ts) <= tw (Node f ss) ==> 
	(Node g ts, Node f ss) : kbo"
    usubtI : "(si, Node f [si]) : kbo"
    wltI : "tw t < tw s ==> (t, s) : kbo"
  monos lex_mono

consts
  kbocfg :: "symb rule set"
  kbocl :: "symb rule set"

inductive "kbocfg"
  intros
    fgI : "(g, f) : symborder ==> tw (Node g ts) <= tw (Node f ss) ==> 
	(Node g ts, Node f ss) : kbocfg"

inductive "kbocl"
  intros
    lexI : "tw (Node f ts) <= tw (Node f ss) ==> 
      (ts, ss) : lex (fwf kbo) ==> (Node f ts, Node f ss) : kbocl"

axioms
  w0h : "sw h = 0" 
  hmin : "g ~= h ==> (g, h) : symborder"
  h_uniq_0 : "sw g = 0 ==> g = h"

defs
  kbocdef : "kbo_cutorder == inv_image less_than tw Un (kbocfg Un kbocl)"

end 



