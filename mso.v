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

Require Import utils perm_eq acc.

(* The proof displayed here is largely inspired from 
   the short outline of Tobias Nipkow:

    https://www21.in.tum.de/~nipkow/Misc/multiset.ps

   see papers/multiset.[ps,pdf] for a local copy *)

#[local] Reserved Notation "x '<ₗ' y" (at level 70, no associativity, format "x  <ₗ  y").
#[local] Reserved Notation "x '⊏' y" (at level 70, no associativity, format "x  ⊏  y").
#[local] Reserved Notation "x '⊏⁺' y" (at level 70, no associativity, format "x  ⊏⁺  y").

#[local] Hint Resolve in_cons in_eq in_elt in_or_app 
                      Permutation_app_inv Permutation_app_middle Permutation_app
                      Permutation_sym Permutation_trans : core.

#[local] Hint Constructors clos_trans clos_refl_trans : core.

Section multiset_order.

  Variables (X : Type) (R E : X → X → Prop).

  (* Infix notation for the base relation *)
  Infix "<" := R.
  Notation "x ≃ y" := (E x y) (at level 70).
  Notation "x ~ₑ y" := (perm_eq E x y) (at level 70).

  Hypothesis E_refl : reflexive E.
  Hypothesis E_sym  : symmetric E.
  Hypothesis E_trans : transitive E.

  (* x is a <-upper bound for the list m *)
  Notation "m <ₗ x" := (∀y, y ∈ m → y < x).

  Local Fact perm_E_refl l : l ~ₑ l.
  Proof. apply perm_eq_refl; auto. Qed.

  Local Fact perm_E_sym l m : l ~ₑ m → m ~ₑ l.
  Proof. apply perm_eq_sym; auto. Qed.

  Local Fact perm_E_trans l m k : l ~ₑ m → m ~ₑ k → l ~ₑ k.
  Proof. apply perm_eq_trans; eauto. Qed.

  Local Fact perm_E_app l m p q : l ~ₑ m → p ~ₑ q → l++p ~ₑ m++q.
  Proof. apply perm_eq_app. Qed.

  Local Fact perm_E_app_comm l m : l++m ~ₑ m++l.
  Proof. now apply perm_eq_app_comm. Qed.

  Local Fact perm_E_middle l m r l' r' : l++r ~ₑ l'++r' → l++m++r ~ₑ l'++m++r'.
  Proof. now apply perm_eq_middle. Qed.

  Hint Resolve perm_E_refl perm_E_sym perm_E_trans perm_E_app 
               perm_E_app_comm perm_E_middle : core.

  (* Inductive definition of the list/multiset relation ⊏
     of which the transitive closure ⊏⁺ is the mso. The
     least relation containing contextual reduction
     and closed under left permutation *)

  Inductive mso_step : list X → list X → Prop :=
    | mso_step_intro l m x r : m <ₗ x 
                             → l++m++r ⊏ l++[x]++r
    | mso_step_perm_l l m k  : l ~ₑ m
                             → l ⊏ k
                             → m ⊏ k
  where "l ⊏ m" := (mso_step l m).

  Hint Constructors mso_step : core.

  (* The inversion lemma gives an alternate FO characterization *)
  Local Fact mso_step_inv k p : 
     k ⊏ p ↔ ∃ l m x r, k ~ₑ l++m++r ∧ p = l++[x]++r ∧ m <ₗ x.
  Proof.
    split.
    + induction 1 as [ | ? ? ? ? ? (? & ? & ? & ? & ? & -> & ?) ]; do 4 eexists; eauto.
    + intros (? & ? & ? & ? & ? & -> & ?); eauto.
  Qed.

  Local Fact mso_step_sg x y : x < y → [x] ⊏ [y].
  Proof.
    intro.
    change ([]++[x]++[] ⊏ []++[y]++[]).
    constructor 1; now intros ? [ <- | [] ].
  Qed.

  (* ⊏ is contextually closed *)
  Local Fact mso_step_ctx l r u v : u ⊏ v → l++u++r ⊏ l++v++r.
  Proof.
    induction 1 in l, r |- *; eauto.
    rewrite <- !app_assoc, ! (app_assoc l); eauto.
  Qed.

  (* l ⊏ _::l *) 
  Local Fact mso_step_cons x l : l ⊏ x::l.
  Proof. now apply @mso_step_intro with (l := []) (m := []); simpl. Qed.

  Section mso_step_perm_r_in.
 
    Local Fact E_bound_comp l m :
        (∀ a b, a ∈ l → b ∈ m → a ≃ b → ∀x, x < a → x < b)
      →  ∀ a b, a ∈ l → b ∈ m → a ≃ b → ∀k, k <ₗ a → k <ₗ b.
    Proof. eauto. Qed.

    Hint Resolve E_bound_comp : core.

    (* for reasons related to nesting, we need a relativized 
       version of mso_step_perm_r below *)
    Local Fact mso_step_perm_r_rel l m :
        (∀ a b, a ∈ l → b ∈ m → a ≃ b → ∀x, x < a → x < b)
      → l ~ₑ m → ∀k, k ⊏ l → k ⊏ m.
    Proof.
      intros Hlm H1 k H2; revert H2 m Hlm H1.
      induction 1 as [ l m x r Hm | ]; intros q Hlq; eauto.
      intros (l' & y & r' & ? & -> & ?)%perm_eq_middle_inv; auto.
      constructor 2 with (l'++m++r'); auto.
      constructor 1.
      revert Hm; eapply E_bound_comp; eauto.
    Qed.

  End mso_step_perm_r_in.

  Hypothesis E_bound : ∀ a b, a ≃ b → ∀x, x < a → x < b.

  (* ⊏ is closed under right permutation *)
  Local Fact mso_step_perm_r l m : l ~ₑ m → ∀k, k ⊏ l → k ⊏ m.
  Proof. apply mso_step_perm_r_rel; eauto. Qed.

  (** Inversion lemmas for Acc_mso_step_below *)

  (** Case analysis for the shape _ ⊏ [] 
      The empty list is minimal for ⊏     *)
  Local Fact mso_step_nil_right_inv l : ¬ l ⊏ [].
  Proof. now intros ([] & ? & ? & ? & ? & ? & ?)%mso_step_inv. Qed.

  (** Case analysis (inversion) for the shape _ ⊏ _::_  
      This is the critical lemma for inverting after
      applying the Acc_intro constructor in the section
       Acc_mso_step below *)
  Local Lemma mso_step_cons_right_inv k y m : 
      k ⊏ y::m 
    → (∃ u,       k ~ₑ u ++ m 
                ∧ u <ₗ y)
    ∨ (∃ l u x r, m = l++[x]++r
                ∧ k ~ₑ y::l++u++r
                ∧ u <ₗ x).
  Proof.
    intros ([] & ? & ? & ? & ? & [-> ->]%cons_inj & ?)%mso_step_inv; simpl in *. 
    + left; eauto.
    + right; do 4 eexists; eauto.
  Qed.

  Section Acc_mso_step.

    Hint Constructors Acc : core.

    Notation W := (Acc mso_step).

    Local Fact Permutation_Acc_mso_step l m : l ~ₑ m → W m → W l.
    Proof. intro; now apply Acc_lower_bounds, mso_step_perm_r. Qed.

    Local Fact Acc_mso_step_nil : W [].
    Proof. constructor; intros _ []%mso_step_nil_right_inv. Qed.

    (* This is the only complicated proof *)

    Local Fact W_app_bound y r :
        (∀x, x < y → ∀l, W l → W (x::l)) 
      → W r  
      → ∀l, l <ₗ y → W (l++r).
    Proof. 
      intros Hy ? l; induction l; simpl; eauto.
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

    Local Fact Acc_mso_step_cons : ∀x, Acc R x → ∀l, W l → W (x::l).
    Proof. induction 1; eauto. Qed.

    Hint Resolve Acc_mso_step_nil 
                 Acc_mso_step_cons : core.

    Local Lemma Forall_Acc_mso_step l : Forall (Acc R) l → Acc mso_step l.
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
    now constructor 1 with (l := []).
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

  Fact mso_perm_l l m k : l ~ₑ m → l ⊏⁺ k → m ⊏⁺ k.
  Proof. unfold mso; intros H1 H2; revert m H1; induction H2; eauto. Qed.

  (* A relativized version of mso_perm_r below *)
  Fact mso_perm_r_rel l m k :
      (∀ a b, a ∈ l → b ∈ m → a ≃ b → ∀x, x < a → x < b)
    → l ~ₑ m → k ⊏⁺ l → k ⊏⁺ m.
  Proof.
    intros Hlm H1 (p & H2 & H3)%clos_trans_inv_right.
    apply clos_rt_t with (1 := H2); constructor 1.
    revert H3; apply mso_step_perm_r_rel; auto.
  Qed.

  Fact mso_perm_r l m k : l ~ₑ m → k ⊏⁺ l → k ⊏⁺ m.
  Proof. apply mso_perm_r_rel; eauto. Qed.

  Hint Resolve mso_step_cons mso_trans : core.

  (* Closure under right head/tail append *)
  Fact mso_app_head l m r : m ⊏⁺ r → m ⊏⁺ l++r.
  Proof. induction l as [ | ? ? IH ]; simpl; auto; intros ?%IH; eauto. Qed.

  Fact mso_app_tail l m r : m ⊏⁺ l → m ⊏⁺ l++r.
  Proof.
    intros H.
    apply mso_perm_r with (r++l); auto.
    now apply mso_app_head.
  Qed.

  (* [] is also minimal for ⊏⁺ *)
  Fact mso_nil_inv l : ¬ l ⊏⁺ [].
  Proof. intros (? & _ & []%mso_step_nil_right_inv)%clos_trans_inv_right. Qed.

  Hint Resolve mso_step_cons : core.

  Fact mso_cons x l : l ⊏⁺ x::l.
  Proof. auto. Qed.

  Hint Resolve mso_sg mso_app_head mso_app_tail : core.

  Lemma Acc_mso_forall l : Acc mso l → ∀x, x ∈ l → Acc R x.
  Proof. induction 1; intros ? (? & ? & ->)%in_split; constructor; eauto. Qed.
  
  Hint Resolve Forall_Acc_mso_step Acc_clos_trans : core.
  
  Lemma forall_Acc_mso l : (∀x, x ∈ l → Acc R x) → Acc mso l.
  Proof. unfold mso; rewrite <- Forall_forall; auto. Qed.

  Hint Resolve Acc_mso_forall forall_Acc_mso : core.

  (* This is the main theorem characterizing mso accessibility *)
  Theorem Acc_mso_iff l : Acc mso l ↔ ∀x, x ∈ l → Acc R x.
  Proof. split; eauto. Qed.

  Hypothesis Rwf : well_founded R.

  Corollary mso_wf : well_founded mso.
  Proof. intro; apply Acc_mso_iff; auto. Qed.

End multiset_order.

Arguments mso {_}.
