(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

Require Import List Permutation Wellfounded Relations Utf8.
Import ListNotations.

Set Implicit Arguments.

(* The proof displayed here is largely inspired from 
   the short outline of Tobias Nipkow:

  http://www4.in.tum.de/~nipkow/misc/multiset.ps

*)

#[local] Notation "x ∈ l" := (In x l) (at level 70, no associativity, format "x  ∈  l").
#[local] Notation "l '~ₚ' m" := (@Permutation _ l m) (at level 70, no associativity, format "l  ~ₚ  m").

Arguments clos_trans {_}.
Arguments clos_refl_trans {_}.

#[local] Reserved Notation "x '<ₗ' y" (at level 70, no associativity, format "x  <ₗ  y").
#[local] Reserved Notation "x '⊏' y" (at level 70, no associativity, format "x  ⊏  y").
#[local] Reserved Notation "x '⊏⁺' y" (at level 70, no associativity, format "x  ⊏⁺  y").

#[local] Hint Resolve in_cons in_eq in_elt in_or_app 
                      Permutation_app_inv Permutation_app_middle Permutation_app
                      Permutation_sym Permutation_trans : core.

#[local] Hint Constructors clos_trans clos_refl_trans : core.

Section utilities.

  Variable (X : Type).

  Implicit Types (x : X) (l : list X) (R : X → X → Prop).

  Fact cons_inj x y l m : x::l = y::m → x = y ∧ l = m.
  Proof. now inversion 1. Qed.

  Fact in_split x m : x ∈ m → ∃ l r, m = l++[x]++r.
  Proof. apply in_split. Qed.

  Fact Permutation_middle_inv l x r m :
    l++[x]++r ~ₚ m → ∃ l' r', m = l'++[x]++r' ∧ l++r ~ₚ l'++r'.
  Proof.
    intros H.
    assert (x ∈ m) as (l' & r' & ->)%in_split; simpl; eauto.
    apply Permutation_in with (1 := H); auto.
  Qed.

  Fact clos_trans_inv_right R x z :
    clos_trans R x z -> ∃y, clos_refl_trans R x y ∧ R y z.
  Proof.
    induction 1 as [ | ? ? ? _ (? & []) _ (? & []) ]; eauto.
    eexists; eauto.
  Qed.

End utilities.

Section multiset_order.

  Variables (X : Type) (R : X → X → Prop).

  (* Infix notation for the base relation *)
  Infix "<" := R.

  (* y is a <-upper bound for the list l *)
  Notation "l <ₗ y" := (∀x, x ∈ l → x < y).

  (* Inductive definition of the list/multiset relation ⊏
     of which the transitive closure ⊏⁺ is the mso. The
     least relation containing contextual reduction
     and closed under left permutation *)

  Inductive mso_step : list X → list X → Prop :=
    | mso_step_intro l m x r : m <ₗ x 
                             → l++m++r ⊏ l++[x]++r
    | mso_step_perm_l l m k  : l ~ₚ m 
                             → l ⊏ k 
                             → m ⊏ k
  where "l ⊏ m" := (mso_step l m).

  Hint Constructors mso_step : core.

  (* The inversion lemma gives an alternate FO characterization *)
  Fact mso_step_inv k p : 
     k ⊏ p ↔ ∃ l m x r, k ~ₚ l++m++r ∧ p = l++[x]++r ∧ m <ₗ x.
  Proof.
    split.
    + induction 1 as [ | ? ? ? ? ? (? & ? & ? & ? & ? & -> & ?) ]; do 4 eexists; eauto.
    + intros (? & ? & ? & ? & ?%Permutation_sym & -> & ?); eauto.
  Qed.

  Fact mso_step_sg x y : x < y → [x] ⊏ [y].
  Proof. 
    intros.
    change ([]++[x]++[] ⊏ []++[y]++[]).
    constructor 1; now intros ? [ <- | [] ].
  Qed.

  (* ⊏ is contextually closed *)
  Fact mso_step_ctx l r u v : u ⊏ v → l++u++r ⊏ l++v++r.
  Proof.
    induction 1 in l, r |- *; eauto.
    rewrite <- !app_assoc, ! (app_assoc l); eauto.
  Qed.

  (* ⊏ is closed under right permutation *)
  Fact mso_step_perm_r l m k : l ~ₚ m → k ⊏ l → k ⊏ m.
  Proof.
    intros H1 H2; revert H2 m H1.
    induction 1; intro; eauto.
    intros (? & ? & -> & ?)%Permutation_middle_inv; eauto.
  Qed.

  (** Case analysis for the shape _ ⊏ [] 
      The empty list is minimal for ⊏     *)
  Fact mso_step_nil_right_inv l : ¬ l ⊏ [].
  Proof. now intros ([|] & ? & ? & ? & ? & ? & ?)%mso_step_inv. Qed.

  Fact mso_step_cons x l : l ⊏ x::l.
  Proof. now apply @mso_step_intro with (l := []) (m := []); simpl. Qed.

  (** Case analysis (inversion) for the shape _ ⊏ _::_  
      This is the critical lemma for inverting after
      applying the Acc_intro constructor in the section
       Acc_mso_step below *)
  Lemma mso_step_cons_right_inv k y m : 
      k ⊏ y::m 
    → (∃ u, k ~ₚ u ++ m ∧ u <ₗ y)
    ∨ (∃ l u x r, m = l++[x]++r ∧ k ~ₚ y::l++u++r ∧ u <ₗ x).
  Proof.
    intros ([] & ? & ? & ? & ? & [-> ->]%cons_inj & ?)%mso_step_inv; simpl in *. 
    + left; eauto.
    + right; do 4 eexists; eauto.
  Qed.

  Section Acc_mso_step.

    Hint Resolve mso_step_perm_r Acc_intro : core.

    Notation W := (Acc mso_step).

    Local Fact Permutation_Acc_mso_step l m : l ~ₚ m → W m → W l.
    Proof. intros ? []; eauto. Qed.

    Local Fact Acc_mso_step_nil : W [].
    Proof. constructor; now intros ? ?%mso_step_nil_right_inv. Qed.

    (* This is the only complicated proof *)

    Local Fact W_app_bound y r :
        (∀x, x < y → ∀l, W l → W (x::l)) 
      → W r  
      → ∀l, l <ₗ y → W (l++r).
    Proof. 
      intros Hy ?; induction l; simpl; eauto.
      intros; apply Hy; eauto.
    Qed.

    Hint Resolve W_app_bound : core.

    Local Fact W_cons_rec y m :
        (∀x, x < y → ∀l, W l → W (x::l))
      → W m
      → (∀l, l ⊏ m → W (y::l))
      → W (y::m).
    Proof.
      intros Hy Hm IHm; constructor.
      (* Now we invert _ ⊏ _::_, the critical step *)
      intros ? [ (? & H & ?) | (? & ? & ? & ? & -> & H & ?) ]%mso_step_cons_right_inv;
        apply Permutation_Acc_mso_step with (1 := H); eauto.
    Qed.

    Hint Resolve W_cons_rec : core.

    Local Fact W_cons y : (∀x, x < y → ∀l, W l → W (x::l)) → ∀l, W l → W (y::l).
    Proof. induction 2; eauto. Qed.

    Hint Resolve W_cons : core.

    Definition Acc_mso_step_cons : ∀x, Acc R x → ∀l, W l → W (x::l).
    Proof. induction 1; eauto. Qed.

    Hint Resolve Acc_mso_step_nil 
                 Acc_mso_step_cons : core.

    Lemma Forall_Acc_mso_step l : Forall (Acc R) l → Acc mso_step l.
    Proof. induction 1; eauto. Qed.

  End Acc_mso_step.

  Definition mso := clos_trans mso_step.

  Infix "⊏⁺" := mso.

  (** Closure properties of mso/⊏⁺ *)

  (* The constructor for the basic reduction *)
  Fact mso_intro x l : l <ₗ x → l ⊏⁺ [x].
  Proof.
    constructor 1.
    rewrite <- (app_nil_r l).
    now constructor 1 with (l := []) (r := []).
  Qed.

  Fact mso_step__mso l m : l ⊏ m → l ⊏⁺ m.
  Proof. now constructor 1. Qed.

  Hint Resolve mso_step_sg mso_step__mso : core.

  Fact mso_sg x y : x < y → [x] ⊏⁺ [y].
  Proof. eauto. Qed.

  Hint Resolve mso_step_ctx : core.

  (* Contextual closure *)
  Fact mso_ctx l r u v : u ⊏⁺ v → l++u++r ⊏⁺ l++v++r.
  Proof. unfold mso; induction 1 in l, r |- *; eauto. Qed.

  (* Transitivity *)
  Fact mso_trans l m p : l ⊏⁺ m → m ⊏⁺ p → l ⊏⁺ p.
  Proof. unfold mso; eauto. Qed.

  Hint Resolve mso_step_perm_l mso_step_perm_r : core.

  (* Closure under left/right permutations *)

  Fact mso_perm_l l m k : l ~ₚ m → l ⊏⁺ k → m ⊏⁺ k.
  Proof. unfold mso; intros H1 H2; revert m H1; induction H2; eauto. Qed.

  Fact mso_perm_r l m k : l ~ₚ m → k ⊏⁺ l → k ⊏⁺ m.
  Proof. unfold mso; intros H1 H2; revert m H1; induction H2; eauto. Qed.

  Hint Resolve mso_step_cons mso_trans : core.

  (* Closure under right head/tail append *)
  Fact mso_app_head l m r : m ⊏⁺ r → m ⊏⁺ l++r.
  Proof.
    induction l as [ | x l IH ]; simpl; auto.
    intros H%IH; eauto.
  Qed.

  Fact mso_app_tail l m r : m ⊏⁺ l → m ⊏⁺ l++r.
  Proof.
    intros H.
    apply mso_perm_r with (r++l).
    + apply Permutation_app_comm.
    + now apply mso_app_head.
  Qed.

  (* [] is also minimal for ⊏⁺ *)
  Fact mso_nil_inv l : ¬ l ⊏⁺ [].
  Proof.
    now intros (? & _ & ?%mso_step_nil_right_inv)%clos_trans_inv_right.
  Qed.

  Hint Resolve mso_step_cons : core.

  Fact mso_cons x l : l ⊏⁺ x::l.
  Proof. auto. Qed.

  Hint Resolve mso_sg mso_app_head mso_app_tail : core.

  Lemma Acc_mso_Forall l : Acc mso l → Forall (Acc R) l.
  Proof.
    rewrite Forall_forall.
    induction 1 as [ l _ IHl ]; intros x Hx.
    constructor; intros y Hy.
    apply IHl with (y := [y]); auto.
    apply in_split in Hx as (? & ? & ->); auto.
  Qed.

  Hint Resolve Acc_mso_Forall Forall_Acc_mso_step Acc_clos_trans : core.

  (* This is the main theorem characterizing mso accessibility *)
  Theorem Acc_mso_iff l : Acc mso l ↔ Forall (Acc R) l.
  Proof. unfold mso; split; eauto. Qed.

  Hypothesis Rwf : well_founded R.

  Corollary mso_wf : well_founded mso.
  Proof. intro; apply Acc_mso_iff, Forall_forall; auto. Qed.
 
End multiset_order.

Arguments mso {_}.
