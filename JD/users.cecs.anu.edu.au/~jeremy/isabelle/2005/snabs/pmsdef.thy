
(* proof of well-foundedness of multiset order *)

theory pmsdef imports orders_c begin 

datatype spms = Leaf "symb" | Inner
arities spms :: rewr

consts
  leaf :: "symb => spms rtree"
  collapse :: "spms rtree => spms rtree list"
  collapses :: "spms rtree list => spms rtree list"
  coll1s :: "(spms rtree list * spms rtree list) set"
  coll1 :: "(spms rtree list * spms rtree) set"
  pms_ruleredn :: "(spms rtree * spms rtree) set"
  pms_cutorder :: "(spms rtree * spms rtree) set"

defs
  leaf_def : "leaf x == Node (Leaf x) []"

inductive "coll1"
  intros
    I : "(ts, Node Inner ts) : coll1"

inductive "coll1s"
  intros
    hdI : "(ys, y) : coll1 ==> (ys @ xs, y # xs) : coll1s"
    tlI : "(ys, zs) : coll1s ==> (x # ys, x # zs) : coll1s"

primrec
  collapse_def : "collapse (Node s ts) = 
    (case s of Leaf a => [Node s ts] | Inner => ts)" 

primrec
  collapses_Nil : "collapses [] = []"
  collapses_Cons : "collapses (t # ts) = collapse t @ collapses ts"

consts
  pmr1 :: "(spms rtree * spms rtree) set"
  pmc1 :: "(spms rtree * spms rtree) set"
  pmc2 :: "(spms rtree * spms rtree) set"
  pmcc :: "(spms rtree * spms rtree) set"
  pmci :: "(spms rtree * spms rtree) set"

inductive "pmr1"
  intros
    I : "(ALL y: set ys. (y, x) : symborder) ==>
      (Node Inner (map leaf ys), Node (Leaf x) ls) : pmr1"
    
inductive "pmc1"
  intros
    I : "(Node Inner e, Node (Leaf s) ls) : pmc1"

inductive "pmc2"
  intros
    I : "(x, y) : symborder ==> (Node (Leaf x) ls, Node (Leaf y) ms) : pmc2"

inductive "pmcc"
  intros
    I : "xs = collapses ys ==> xs ~= ys ==> (Node a xs, Node a ys) : pmcc"

inductive "pmci"
  intros
    I : "(xs, ys) : coll1s ==> (Node a xs, Node a ys) : pmci"

defs
  pmsrdef : "pms_ruleredn == pmr1 Un pmci"
  pmscdef : "pms_cutorder == pmc1 Un pmc2 Un pmci"

end 


