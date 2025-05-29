
(* stuff to do with closure under context *)

theory ctxt imports base begin  

consts
  (* these now parameterized by "primitive" reduction *)

  ctxt :: "('a rtree * 'a rtree) set => ('a rtree * 'a rtree) set"
  nctxt :: "('a rtree * 'a rtree) set => nat => ('a rtree * 'a rtree) set"
  ltnctxt :: "('a rtree * 'a rtree) set => nat => ('a rtree * 'a rtree) set"
  nured :: "('a rtree * 'a rtree) set => ('a rtree * 'a rtree) set"
  sn1order :: "('a rtree * 'a rtree) set => ('a rtree * 'a rtree) set"
  sn2order :: "('a rtree * 'a rtree) set => ('a rtree * 'a rtree) set"
  constrict :: "('a rtree * 'a rtree) set => ('a rtree * 'a rtree) set"
  onered :: "('a rtree * 'a rtree) set => ('a rtree list * 'a rtree list) set"
  sn1red :: "('a rtree * 'a rtree) set => ('a rtree list * 'a rtree list) set"
  sn2red :: "('a rtree * 'a rtree) set => ('a rtree list * 'a rtree list) set"

inductive "ctxt r" 
  intros
    red_nuI : "(dtr, dt) : oneup (onerel (ctxt r)) ==>
      (dtr, dt) : ctxt r"
    red_cutI :  "(dtr, dt) : r ==> (dtr, dt) : ctxt r"
  monos oo_mono

(* context, but at a specific or limited depth in the tree *)
primrec 
  nctxt_0 : "nctxt r 0 = r"
  nctxt_Suc : "nctxt r (Suc n) = oneup (onerel (nctxt r n))"

primrec 
  ltnctxt_0 : "ltnctxt r 0 = {}"
  ltnctxt_Suc : "ltnctxt r (Suc n) = (ltnctxt r n Un nctxt r n)"

defs
  nured_def : "nured r == oneup (onerel (ctxt r))"
  onered_def : "onered r == onerel (ctxt r)"
  sn1red_def : "sn1red r == onerel (fwf (ctxt r))"
  sn2red_def : "sn2red r == onerel (ctxt (fwf (ctxt r)))"

defs 
  sn1order_def : "sn1order r == oneup (sn1red r)"
  sn2order_def : "sn2order r == oneup (sn2red r)"

defs
  (* constricting derivations, in the sense of
  Nachum Dershowitz. Termination Dependencies.  Extended Abstract.
  www.cs.tau.ac.il/~nachumd/papers/depend.pdf 
  see also (which differ)
  Femke van Raamsdonk, Paula Severi, Morten Heine Sørensen and Hongwei Xi
  Perpetual Reductions in Lambda Calculus
  Information and Computation 149(2):173--225, March 1999,
  http://www.cs.vu.nl/~femke/ps/jic98.ps, page 25,
  David Plaisted, RTA-93, LNCS 690, 405-420 *)

  constrict_def : "constrict r == 
    {(dtn, dt). (dtn, dt) : r & set (isubts dt) <= wfp (ctxt r)}"

end

