
(* stuff for proof of strong normalization in abstract setting *)
(* note - we tried to make it more general by specifying a type class
  representing trees abstractly, where there was an operation isubts
  giving subtrees, and where trees are of finite depth - specified by
  a rule "wf isubt".  But this didn't work, because there was nothing to
  say that if (dts, isubts a) : onered, then there exists a tree b
  such that isubts b = dts (whence (b, a) : nured).  
  Thus we could not show that if isubts a ~: wfp onered,
  then a ~: wfp nured (ie, snUpn need not hold) *)

theory base imports WfUn begin 
  
datatype 'a rtree = Node "'a" "'a rtree list"

types
  'a rule = "('a rtree * 'a rtree)"

consts 
  isubts :: "'a rtree => 'a rtree list"
  subt    :: "'a rule set"
  isubt    :: "'a rule set"
  psubt    :: "'a rule set"
  sub1t         :: "('a rtree * 'a rtree list) set"
  symb_of :: "'a rtree => 'a"
  symbs_in :: "'a set => 'a rule set"
  symbols_of :: "'a rtree => 'a list"
  ss_of :: "'a rtree list => 'a list"
  depth :: "'a rtree => nat"
  depths :: "'a rtree list => nat"
  maptree :: "('a => 'b) => 'a rtree => 'b rtree"
  maptrees :: "('a => 'b) => 'a rtree list => 'b rtree list"

  ndos :: "'a list => 'a list => 'a set => bool"
  nnv :: "'a list => 'a list => 'a set => bool"
  ndr :: "'a set => ('a rtree * 'a rtree) => bool"

primrec
  depth_def : "depth (Node s ts) = Suc (depths ts)"

  depths_Nil : "depths [] = 0"
  depths_Cons : "depths (t # ts) = 
    (if depth t <= depths ts then depths ts else depth t)" 

primrec 
  symb_of_def : "symb_of (Node a sts) = a"

inductive "symbs_in S"
  intros
    I : "a : S ==> b : S ==> (Node a ts, Node b ss) : symbs_in S"

primrec
  ss_of_Nil : "ss_of [] = []"
  ss_of_Cons : "ss_of (t # ts) = symbols_of t @ ss_of ts"

  symbols_of_Node : "symbols_of (Node s trees) = s # ss_of trees"

primrec 
  isubts_def : "isubts (Node a sts) = sts"

inductive "isubt"
  intros
    isubtI : "sdt : set sts ==> (sdt, Node a sts) : isubt"

defs
  psubt_def : "psubt == isubt^+"
  subt_def : "subt == psubt^="

inductive "sub1t"
  intros
    sub1tI : "[| dt : set dtl ; (dts, dt) : subt |] ==> (dts, dtl) : sub1t"

consts
  oneup :: "('a rtree list * 'a rtree list) set =>
    ('a rtree * 'a rtree) set"
  oneupS :: "'a set => ('a rtree list * 'a rtree list) set =>
    ('a rtree * 'a rtree) set"

inductive "oneup r" 
  intros
    ouI : "(dtl1, dtl2) : r ==> (Node a dtl1, Node a dtl2) : oneup r"

inductive "oneupS S r" 
  intros
    ouI : "(dtl1, dtl2) : r ==> a : S ==> 
      (Node a dtl1, Node a dtl2) : oneupS S r"

primrec
  maptree_def : "maptree f (Node a ts) = Node (f a) (maptrees f ts)"
  maptrees_Nil : "maptrees f [] = []"
  maptrees_Cons : "maptrees f (t # ts) = maptree f t # maptrees f ts"

(* converting a list into a tree where each node is unary (or nullary) *)
consts 
  tree :: "'a list => 'a rtree => 'a rtree"
  trees :: "'a list => 'a rtree list"

primrec
  tree_Nil : "tree [] t = t"
  tree_Cons : "tree (x # xs) t = Node x [tree xs t]"

primrec
  trees_Nil : "trees [] = []"
  trees_Cons : "trees (x # xs) = [Node x (trees xs)]"

(** conditions on rules, which we must express in terms of the
  instantiated rule, using S as set of "known" symbols,
  sl/sr as lists of symbols in instantiated lhs/rhs **)

defs
  (* no new variables on rhs - when instantiated, symbols on rhs
    must be either on lhs or among "known symbols *)
  nnv_def : "nnv sl sr S == set sr - set sl <= S"
  (* no duplicated variables on rhs - when instantiated, duplicated 
    symbols on rhs must be among "known symbols *)
  ndos_def : "ndos sl sr S == duplicates sr <= S"

(* a relation instance satisfying both the above *)
primrec
  ndr_def : "ndr S (t, s) = (nnv (symbols_of s) (symbols_of t) S & 
    ndos (symbols_of s) (symbols_of t) S)"

end
