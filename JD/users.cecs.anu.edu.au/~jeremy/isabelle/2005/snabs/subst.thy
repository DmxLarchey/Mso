
(* getting a reduction relation for rtrees by 
  formalising substitution for variables *)

theory subst imports redn begin 
  
datatype 'a stree = SNode "'a" "'a stree list"
                  | SVar nat 

types
  'a rule = "('a rtree * 'a rtree)"
  'a srule = "('a stree * 'a stree)"

consts 
  (* when we substitute, we get a tree without variables *)
  subst :: "(nat => 'a rtree) => 'a stree => 'a rtree"
  substs :: "(nat => 'a rtree) => 'a stree list => 'a rtree list"

  s_symb_of :: "'a stree => 'a"
  s_symbols_of :: "'a stree => 'a list"
  s_ss_of :: "'a stree list => 'a list"
  vars_of :: "'a stree => nat list"
  varss_of :: "'a stree list => nat list"
  rule0_prop :: "'a set => 'a srule set"
  rule0_hd_S :: "'a set => 'a srule set"
  rule0_proph :: "'a set => 'a srule set"
  hds_notin :: "'a set => 'a rule set"
  is_SNode :: "'a stree => bool"
  is_SVar :: "'a stree => bool"
  newvar :: "nat list => nat"
  newvars :: "nat list => nat => nat list"

(* of $\mathcal{R}_0$-property in paper, 
  (i), (iii), (iv) are rule0_prop, (ii) is rule0_hd_S, 
  (i) to (iv) are rule0_proph *) 
inductive "rule0_prop S"
  intros 
    I : "[| set (s_symbols_of t) <= S ; 
	  set (vars_of t) <= set (vars_of s) ;
	  distinct (vars_of t) |] ==>
	(t, s) : rule0_prop S"

inductive "rule0_hd_S S"
  intros 
    I : "a : S  ==> (t, SNode a ss) : rule0_hd_S S"

inductive "rule0_proph S"
  intros 
    I : "[| a : S ; (t, SNode a ss) : rule0_prop S |] ==>
      (t, SNode a ss) : rule0_proph S"

inductive "hds_notin S"
  intros 
    I : "a ~: S ==> (t, Node a ss) : hds_notin S"

primrec 
  SVar : "is_SVar (SVar n) = True"
  SNode : "is_SVar (SNode a ts) = False"

primrec 
  SVar : "is_SNode (SVar n) = False"
  SNode : "is_SNode (SNode a ts) = True"

primrec 
  subst_SVar : "subst f (SVar n) = f n"
  subst_SNode : "subst f (SNode a ts) = Node a (substs f ts)"

  substs_Nil : "substs f [] = []"
  substs_Cons : "substs f (t # ts) = subst f t # substs f ts"

primrec 
  s_symb_of_def : "s_symb_of (SNode a sts) = a"

primrec
  s_ss_of_Nil : "s_ss_of [] = []"
  s_ss_of_Cons : "s_ss_of (t # ts) = s_symbols_of t @ s_ss_of ts"

  s_symbols_of_SNode : "s_symbols_of (SNode s trs) = s # s_ss_of trs"
  s_symbols_of_SVar : "s_symbols_of (SVar n) = []"

primrec
  varss_of_Nil : "varss_of [] = []"
  varss_of_Cons : "varss_of (t # ts) = vars_of t @ varss_of ts"

  vars_of_SNode : "vars_of (SNode s trs) = varss_of trs"
  vars_of_SVar : "vars_of (SVar n) = [n]"

consts
  subt_S    :: "'a set => ('a stree * 'a stree) set"
  isubt_S    :: "'a set => ('a stree * 'a stree) set"
  psubt_S    :: "'a set => ('a stree * 'a stree) set"
  sub1t_S         :: "'a set => ('a stree * 'a stree list) set"
  oneup_S :: "'a set => ('a stree list * 'a stree list) set =>
    ('a stree * 'a stree) set"

inductive "oneup_S S r" 
  intros
    ouI : "(dtl1, dtl2) : r ==> a : S ==>
      (SNode a dtl1, SNode a dtl2) : oneup_S S r" 

inductive "isubt_S S"
  intros
    I : "sdt : set sts ==> a : S ==> (sdt, SNode a sts) : isubt_S S"

defs
  psubt_S_def : "psubt_S S == (isubt_S S)^+"
  subt_S_def : "subt_S S == (psubt_S S)^="

inductive "sub1t_S S"
  intros
    sub1t_SI : "[| dt : set dtl ; (dts, dt) : subt_S S |] ==>
      (dts, dtl) : sub1t_S S"

defs
  newvar_def : "newvar l == Suc (maxl l)"

primrec
  newvars_0 : "newvars l 0 = []"
  newvars_Suc : "newvars l (Suc n) = newvar l # newvars (newvar l # l) n"
end

