(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

Require Import List Wellfounded Relations Permutation Utf8.
Import ListNotations.

Require Import utils acc perm_eq mso mpo.

Notation "'⟨' x '|' l '⟩ₜ'" := (node x l) (at level 0, l at level 200, format "⟨ x | l ⟩ₜ").

Section ctxt.

  Variables (X : Type).

  Implicit Type (R : term X → term X → Prop).

  Inductive ctxt R : term X → term X → Prop :=
    | ctxt_stop p q : R p q → ctxt R p q
    | ctxt_comp f l r p q : ctxt R p q → ctxt R ⟨f|l++[p]++r⟩ₜ ⟨f|l++[q]++r⟩ₜ
    .

  Fact ctxt_inv R p q : 
      ctxt R p q 
    → R p q \/ exists f l r u v , p = ⟨f|l++[u]++r⟩ₜ /\ q = ⟨f|l++[v]++r⟩ₜ /\ ctxt R u v.
  Proof.
    destruct 1; eauto.
    right; do 5 eexists; eauto.
  Qed. 
  
  Fact Acc_fall R f m : Acc R ⟨f|m⟩ₜ → Forall (Acc (ctxt R)) m → Acc (ctxt R) ⟨f|m⟩ₜ.
  Proof.
  Admitted.
  
  Fact wf_ctxt R : well_founded R → well_founded (ctxt R).
  Proof.
    intros HR t.
    induction t as [ f m IHm ].
    rewrite <- Forall_forall in IHm.
    apply Acc_fall; auto.
  Qed.
    constructor.
    intros ? [ | (g & l & r & p & q & -> & [=] & G)]%ctxt_inv; eauto.
    subst g m.
    apply IHm.
    
    

  Hint Constructors ctxt : core.
  
  Fact ctxt_idem R r s : ctxt (ctxt R) r s → ctxt R r s.
  Proof. induction 1; auto. Qed.
  
  Let SN := @Acc (term X).
  Let fwf R r t := R r t /\ SN R t.

  Variables (R : term X → term X → Prop).

  Inductive sn1 : term X → term X → Prop :=
    | sn1_intro f l p q r : SN R q → ctxt R p q → sn1 ⟨f|l++[p]++r⟩ₜ ⟨f|l++[q]++r⟩ₜ.

  Definition sn2 := ctxt sn1.
  
  Fact sn1__sn2 r t : sn1 r t → sn2 r t.
  Proof. now constructor 1. Qed.
  
  
  
  
  Inductive sn2 : term X → term X → Prop :=
    | sn1_intro f l p q r : SN q → ctxt p q → sn1 ⟨f|l++[p]++r⟩ₜ ⟨f|l++[q]++r⟩ₜ.
    
    (node f ()) (node f (l++[p]++r))
