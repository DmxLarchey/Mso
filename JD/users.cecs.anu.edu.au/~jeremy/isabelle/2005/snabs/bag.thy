
(* attempt to do a proof relating to a bag ordering on sets of subterms *)

theory bag imports orders begin 

consts
  glues :: "'a relation => 'a set => 'a set => bool"
  rp_exsf ::
    "['a relation, 'a relation, 'a relation, 'a relation] => 'a => bool" 
  rp_exscf ::
    "['a relation, 'a relation, 'a relation, 'a relation] => 'a => bool" 
  rp_gluesf ::
    "'a relation => 'a relation => 'a set relation => 'a => bool"
  rp_gluescf ::
    "'a relation => 'a relation => 'a set relation => 'a => bool"
  setord :: "'a set relation"
  colord :: "'a relation => 'a relation => 'a relation"
  colprop :: "'a relation => 'a relation => bool"

inductive "colord to col" 
  intros 
    I : "ALL r'. (r', r) : col --> (r', l) : col O to ==> 
      (r, l) : colord to col"

(* property of the colouring relation *)

defs
  glues_def : "glues isub sn G == ALL r. r : gbars isub G sn --> r : sn"


  (* so is ordering on sets, will be the bag ordering on sets of subterms
    from the ordering on types s, t < (s -> t) *)
  rp_gluesf_def : "rp_gluesf isub rho so == %l. ALL r. (r, l) : rho --> 
    (EX G. r : gbars isub G (wfp rho) & 
      (G, {l'. (l', l) : isub^*}) : so)" 
  rp_gluescf_def : "rp_gluescf isub rho so == %l. 
    (ALL x. (x, l) : isub --> x : wfp rho) --> rp_gluesf isub rho so l"

  (* col is the coloured subterm relation *)
  rp_exsf_def : "rp_exsf isub rho cuto col == %l. ALL r. (r, l) : rho --> 
    r : gbars isub {g. (g, r) : col} (wfp rho) & 
      (ALL g. (g, r) : col --> (g, l) : col O cuto)" 
  rp_exscf_def : "rp_exscf isub rho cuto col == %l. 
    (ALL x. (x, l) : isub --> x : wfp rho) --> rp_exsf isub rho cuto col l"

axioms
  wf_setord : "wf setord"

end 

