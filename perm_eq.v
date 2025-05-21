(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

Require Import List Permutation Relations Utf8.
Import ListNotations.

Require Import utils.

Set Implicit Arguments.

Section perm_eq.

  Hint Resolve Permutation_app 
               Permutation_sym
               Permutation_trans
               Permutation_in
               Permutation_app_comm : core.

  Hint Resolve Forall2_app Forall2_diag : core.

  Variable (X : Type) (E : X → X → Prop).

  Inductive perm_eq (l k : list X) : Prop :=
    | perm_eq_intro m : Forall2 E l m → m ~ₚ k → perm_eq l k.

  Hint Constructors perm_eq : core.
  
  Notation "l ~ₑ m" := (perm_eq l m) (at level 70, format "l  ~ₑ  m" ).

  Fact perm_eq_in_inv l m x : l ~ₑ m → x ∈ l → ∃y, y ∈ m ∧ E x y.
  Proof.
    intros [ k H1 H2 ] Hx.
    destruct (Forall2_In_inv _ H1 Hx) as (? & []); eauto.
  Qed.

  Fact perm_eq_xchg l m : l ~ₑ m → ∃p, l ~ₚ p ∧ Forall2 E p m.
  Proof.
    destruct 1 as [ k H1 H2 ].
    apply (Forall2_perm_xchg H1 H2).
  Qed.

  (* We need relativized versions of refl-sym-trans to 
     reason recursivively in the case of nesting of perm_eq *)

  Fact perm_eq_refl_rel l : (∀x, x ∈ l → E x x) → l ~ₑ l.
  Proof.
    constructor 1 with l; auto.
    rewrite <- Forall_forall in H.
    induction H; eauto.
  Qed.

  Fact perm_eq_sym_rel l m :
      (∀ x y, x ∈ l → y ∈ m → E x y → E y x)
    → l ~ₑ m → m ~ₑ l.
  Proof.
    intros Hlm (p & H1 & H2%Forall2_xchg)%perm_eq_xchg.
    constructor 1 with p; auto.
    revert H2; apply Forall2_impl_dep; eauto.
  Qed.

  Fact perm_eq_trans_rel l m k : 
      (∀ x y z, x ∈ l → y ∈ m → z ∈ k → E x y → E y z → E x z)
    → l ~ₑ m → m ~ₑ k → l ~ₑ k.
  Proof.
    intros Hlmk.
    intros (u & H1 & H2)%perm_eq_xchg.
    destruct 1 as [ v H3 H4 ].
    assert (Forall2 E u v) as Huv.
    1: revert H2 H3; apply Forall2_trans_dep; eauto.
    destruct (perm_Forall2_xchg H1 Huv) as (? & []); eauto.
  Qed.

  Fact perm_eq_app l m k p : l ~ₑ m → k ~ₑ p → l++k ~ₑ m++p.
  Proof. do 2 destruct 1; eauto. Qed.

  Fact perm_eq_app_comm_rel l m :
      (∀x, x ∈ l → E x x)
    → (∀x, x ∈ m → E x x)
    → l++m ~ₑ m++l.
  Proof. rewrite <- !Forall_forall; eauto. Qed.

  Fact perm_eq_middle_inv l x r m : 
      l++[x]++r ~ₑ m 
    → ∃ l' y r', E x y 
               ∧ m = l'++[y]++r' 
               ∧ l++r ~ₑ l'++r'.
  Proof.
    destruct 1 as [ v (l1 & y & r1 & -> & H1 & H2 & H3)%Forall2_middle_inv_left 
                    (l' & r' & -> & H)%Permutation_middle_inv ].
    exists l', y, r'; eauto.
  Qed.
  
  Hypothesis E_refl : reflexive E.
  Hypothesis E_sym : symmetric E.
  Hypothesis E_trans : transitive E.

  Fact perm_eq_refl : reflexive perm_eq.
  Proof. intro; apply perm_eq_refl_rel; auto. Qed.

  Fact perm_eq_sym : symmetric perm_eq.
  Proof. intros ? ?; apply perm_eq_sym_rel; auto. Qed.

  Fact perm_eq_trans : transitive perm_eq.
  Proof. intros ? ? ?; apply perm_eq_trans_rel; eauto. Qed.
  
  Fact perm_eq_app_comm l m : l++m ~ₑ m++l.
  Proof. apply perm_eq_app_comm_rel; auto. Qed.

  Fact perm_eq_middle l m r l' r' :
      l++r ~ₑ l'++r'
    → l++m++r ~ₑ l'++m++r'.
  Proof.
    intro.
    do 2 apply (perm_eq_trans (perm_eq_app_comm _ _)), perm_eq_sym.
    rewrite <- ! app_assoc.
    apply perm_eq_app; auto using perm_eq_refl.
    now do 2 apply (perm_eq_trans (perm_eq_app_comm _ _)), perm_eq_sym.
  Qed.

End perm_eq.
