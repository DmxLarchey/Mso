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

Set Implicit Arguments.

#[global] Notation "x ∈ l" := (In x l) (at level 70, no associativity, format "x  ∈  l").
#[global] Notation "l ~ₚ m" := (@Permutation _ l m) (at level 70, no associativity, format "l  ~ₚ  m").
#[global] Notation "R ⁻¹" := (λ x y, R y x) (at level 1, left associativity, format "R ⁻¹").

Arguments clos_trans {_}.
Arguments clos_refl_trans {_}.
Arguments reflexive {_}.
Arguments symmetric {_}.
Arguments transitive {_}.

#[local] Hint Resolve in_cons in_eq in_elt in_or_app 
                      Permutation_app_inv Permutation_app_middle Permutation_app
                      Permutation_sym Permutation_trans : core.

#[local] Hint Constructors clos_trans clos_refl_trans : core.

Section utilities.

  Variable (X : Type).

  Implicit Types (x : X) (l : list X) (R : X → X → Prop) (P : X → Prop).

  Fact cons_inj x y l m : x::l = y::m → x = y ∧ l = m.
  Proof. now inversion 1. Qed.

  (* _++[_]++_ is a better shape than _++_::_ for rewrites below *)
  Fact in_split x m : x ∈ m → ∃ l r, m = l++[x]++r.
  Proof. apply in_split. Qed.

  Fact fold_right_conj P l : fold_right (λ x, and (P x)) True l ↔ ∀x, x ∈ l → P x.
  Proof.
    rewrite <- Forall_forall.
    induction l; simpl.
    + split; constructor.
    + now rewrite Forall_cons_iff, IHl.
  Qed.

  Fact Permutation_middle_inv l x r m :
    l++[x]++r ~ₚ m → ∃ l' r', m = l'++[x]++r' ∧ l++r ~ₚ l'++r'.
  Proof.
    intros H.
    assert (x ∈ m) as (l' & r' & ->)%in_split; simpl; eauto.
    apply Permutation_in with (1 := H); auto.
  Qed.
  
  Fact clos_trans__clos_refl_trans R x y : clos_trans R x y → clos_refl_trans R x y.
  Proof. induction 1; eauto. Qed. 
  
  Hint Resolve clos_trans__clos_refl_trans : core.

  Fact clos_refl_trans__clos_trans R x y : clos_refl_trans R x y ↔ x = y ∨ clos_trans R x y.
  Proof.
    split.
    + induction 1 as [ | | ? ? ? _ [] _ [] ]; subst; eauto.
    + intros [ <- | ]; eauto.
  Qed.

  Fact clos_trans_inv_right R x z : clos_trans R x z ↔ ∃y, clos_refl_trans R x y ∧ R y z.
  Proof. 
    split.
    + induction 1 as [ | ? ? ? ? _ _ (? & []) ]; eauto.
    + intros (? & [ <- | ]%clos_refl_trans__clos_trans & H2); eauto.
  Qed.

End utilities.

Fact Forall2_middle_inv_left X Y (R : X → Y → Prop) l x r m :
  Forall2 R (l++[x]++r) m → ∃ l' y r', m = l'++[y]++r' ∧ R x y ∧ Forall2 R l l' ∧ Forall2 R r r'.
Proof.
  intros (l' & [ | y r' ] & H1 & H2 & ->)%Forall2_app_inv_l.
  1: now inversion H2.
  apply Forall2_cons_iff in H2 as (? & ?).
  exists l', y, r'; auto.
Qed.

Fact Permutation_head_inv X (x : X) k m :
    x::k ~ₚ m → ∃ l r, m = l++x::r ∧ k ~ₚ l++r.
Proof.
  intros H.
  destruct (in_split x m) as (l & r & ->).
  + apply Permutation_in with (1 := H); simpl; auto.
  + exists l, r; split; auto.
    now apply Permutation_cons_inv with x,
          perm_trans with (1 := H), 
          Permutation_sym,
          Permutation_cons_app.
Qed.

Fact Forall2_xchg X Y (R : X → Y → Prop) l m : Forall2 R l m → Forall2 R⁻¹ m l.
Proof. induction 1; eauto. Qed.

Fact Forall2_impl_dep X Y (R T : X → Y → Prop) l m :
  (∀ x y, x ∈ l → y ∈ m → R x y → T x y) → Forall2 R l m → Forall2 T l m.
Proof.
  intros H1 H2; revert H2 H1.
  induction 1; simpl; intro; constructor; eauto.
Qed.

Fact Forall2_trans_dep X (R : X → X → Prop) l m k :
    (∀ x y z, x ∈ l → y ∈ m → z ∈ k → R x y → R y z → R x z)
  → Forall2 R l m
  → Forall2 R m k
  → Forall2 R l k.
Proof.
  intros H1 H2; revert H2 k H1.
  induction 1 as [ | x y l m H1 H2 IH2 ]; intros k H3; auto.
  + destruct k as [ | z k ]; [ now inversion 1 | ].
    intros (H4 & H5)%Forall2_cons_iff.
    constructor; eauto.
    revert H5; apply IH2; eauto.
Qed.

Fact Forall2_In_inv X Y (R : X → Y → Prop) x l m :
  Forall2 R l m → x ∈ l → ∃y, R x y ∧ y ∈ m.
Proof.
  induction 1 as [ | a b l m H1 H2 IH2 ].
  + now inversion 1.
  + intros [ <- | (? & [])%IH2 ]; eauto.
Qed.

Fact Forall2_perm_xchg [X Y] [E : X → Y → Prop] [l m k] :
  Forall2 E l m → m ~ₚ k → ∃p, l ~ₚ p ∧ Forall2 E p k.
Proof.
  induction 1 as [ | s t l m H1 H2 IH2 ] in k |- *.
  + intros ->%Permutation_nil; exists []; eauto.
  + intros (k1 & k2 & -> & (p & ? & (l1 & l2 & ? & ? & ->)%Forall2_app_inv_r)%IH2)%Permutation_head_inv.
    exists (l1++s::l2); split.
    * now apply Permutation_cons_app.
    * apply Forall2_app; auto.
Qed.

Fact Forall2_diag X (R : X → X → Prop) l : Forall (λ x, R x x) l → Forall2 R l l.
Proof. induction 1; eauto. Qed.

Fact perm_Forall2_xchg [X Y] [E : X → Y → Prop] [l m k] :
  l ~ₚ m → Forall2 E m k → ∃p, Forall2 E l p ∧ p ~ₚ k.
Proof.
  intros H1%Permutation_sym H2%Forall2_xchg.
  destruct (Forall2_perm_xchg H2 H1) as (? & ? & ?%Forall2_xchg); eauto.
Qed.