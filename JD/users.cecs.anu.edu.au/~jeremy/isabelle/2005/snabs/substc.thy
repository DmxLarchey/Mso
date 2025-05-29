
theory substc imports subst begin 

consts
  ctxt_S :: "'a set => 'a srule set => 'a srule set"
  cut0 :: "'a set => 'a srule set => 'a srule set"
  subs :: "'a srule set => 'a rule set"

inductive "ctxt_S S r" 
  intros
    nuI : "(dtr, dt) : oneup_S S (onerel (ctxt_S S r)) ==>
      (dtr, dt) : ctxt_S S r"
    cutI :  "(dtr, dt) : r ==> (dtr, dt) : ctxt_S S r"
  monos oo_S_mono

(* this is $\mathcal{R}_{\ll 0}$ of the paper *)
inductive "cut0 S r" 
  intros
    I : "[| (t, s) : ctxt_S S r ; (t, s) : rule0_prop S ; a : S ;
          (SNode a ts, t) : subt_S S |] ==> (SNode a ts, s) : cut0 S r" 

(* subs (cut0 S r) is $\ll_0'$ of the paper *)
inductive "subs r" 
  intros
    I : "(t, s) : r ==> (subst f t, subst f s) : subs r"
          
end

