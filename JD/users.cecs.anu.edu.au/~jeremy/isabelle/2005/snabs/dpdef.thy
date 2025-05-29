
theory dpdef imports orders_c begin

datatype esymb = Sharp symb | Nat symb

consts
  porder :: "(esymb rtree * esymb rtree) set"
  qorder :: "(esymb rtree * esymb rtree) set"
  rres :: "(esymb rtree * esymb rtree) set"
  defsyms :: "symb set"
  mk_sharp_s :: "esymb => esymb"
  mk_nat_s :: "esymb => esymb"
  mk_sharp_t :: "esymb rtree => esymb rtree"
  mk_nat_t :: "esymb rtree => esymb rtree"
  mk_es :: "symb rtree => esymb rtree"
  mk_ess :: "symb rtree list => esymb rtree list"
  dpcs :: "(symb rtree * symb rtree) set"
  dpccd :: "(symb rtree * symb rtree) set"
  depprs :: "(symb rtree * symb rtree) set"
  dp_cutorder :: "(symb rtree * symb rtree) set"
  dp_ruleredn :: "(symb rtree * symb rtree) set"

(* terms headed by defined symbols > terms headed by constructor symbols *)
inductive "dpccd" 
  intros
    I : "d : defsyms ==> c ~: defsyms ==> (Node c ss, Node d ts) : dpccd"

inductive "rres" (* the rewrite rules, with Nat applied to every symbol *)
  intros
    I : "(t, s) : dp_ruleredn ==> (mk_es t, mk_es s) : rres"

inductive "dpcs" (* we limit the porder given to exclude cases where
  t < s and t[s] headed by defined[constructor] symbol *)
  intros
    I : "(mk_sharp_t (mk_es t), mk_sharp_t (mk_es s)) : porder ==>
       t = Node x ts ==> s = Node y ss ==> 
       (x : defsyms --> y : defsyms) ==> (t, s) : dpcs"

inductive "defsyms" (* defined symbols *)
  intros
    I : "(x, Node d ts) : dp_ruleredn ==> d : defsyms" 

(* dependency pairs, defined in terms of original symbols,
  but note, this is in terms of rules after substitution *)
inductive "depprs" 
  intros
    I : "d : defsyms ==> (Node d ul, r) : subt ==> (r, l) : dp_ruleredn ==> 
      (Node d ul, l) : depprs"

(* the following enable poq to be deduced, not needed otherwise
inductive "porder"
  intros
    I : "(t, s) : qorder ==> (s, t) ~: qorder ==> (t, s) : porder"

rules
  qorder_trans "trans qorder"
*)

(* modifications to take into account s 4 of 
  N. Hirokawa & A. Middeldorp, Dependency Pairs Revisited, RTA-04, LNCS 3091.
  and various by Giesl et al incl
  J~Giesl, T~Arts, and E~Ohlebusch.
  Modular Termination Proofs for Rewriting Using Dependency Pairs.
  Journal of Symbolic Computation 34(1):21-58, 2002.
  porder not necessarily the partial order of preorder qorder,
  rather they form a reduction pair *)
axioms
  poq : "porder O qorder <= porder | qorder O porder <= porder"
  wfpsq : "wf (porder Un sn1order qorder)"
  wfpsr : "wf (porder Un sn1order rres)"

primrec (* apply Nat to every symbol in a tree *)
  mk_es_def : "mk_es (Node s ts) = Node (Nat s) (mk_ess ts)"

  mk_ess_Nil : "mk_ess [] = []"
  mk_ess_Cons : "mk_ess (t # ts) = mk_es t # mk_ess ts"

primrec
  "mk_nat_s (Sharp s) = Nat s"
  "mk_nat_s (Nat s) = Nat s"

primrec
  "mk_sharp_s (Sharp s) = Sharp s"
  "mk_sharp_s (Nat s) = Sharp s"

(* change head symbol from Nat to Sharp, and vv *)
primrec
  "mk_nat_t (Node es ts) = (Node (mk_nat_s es) ts)"

primrec
  "mk_sharp_t (Node es ts) = (Node (mk_sharp_s es) ts)"

axioms
  (* qorder closed under context *)
  qorder_ctxt : "ctxt qorder <= qorder"
  (* porder well-founded *)
  wf_porder : "wf porder"
  (* qorder contains the rewrite rules *)
  pqa : "(r, l) : dp_ruleredn ==> (mk_es r, mk_es l) : qorder"
  (* dependency pairs s > t (our definition, after substitution):
    sharped versions in porder OR t proper subterm of lhs 
    (this is the case where t was in a variable in the rhs of the rule,
    which got instantiated) *)
  pqb : "(t, s) : depprs ==> 
    (mk_sharp_t (mk_es t), mk_sharp_t (mk_es s)) : porder | (t, s) : psubt" 

defs
  dpcdef : "dp_cutorder == dpccd Un dpcs"

end 



