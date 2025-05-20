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

    https://www21.in.tum.de/~nipkow/Misc/multiset.ps

   see papers/multiset.ps for a local copy *)

#[local] Notation "x ∈ l" := (In x l) (at level 70, no associativity, format "x  ∈  l").
#[local] Notation "l ~ₚ m" := (@Permutation _ l m) (at level 70, no associativity, format "l  ~ₚ  m").
#[local] Notation "R ⁻¹" := (λ x y, R y x) (at level 1, left associativity, format "R ⁻¹").

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

  (* _++[_]++_ is a better shape than _++_::_ for rewrites below *)
  Fact in_split x m : x ∈ m → ∃ l r, m = l++[x]++r.
  Proof. apply in_split. Qed.

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
  Forall2 R (l++[x]++r) m → ∃ l' y r', m = l'++[y]++r' ∧ Forall2 R l l' ∧ Forall2 R r r'.
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

#[local] Hint Resolve in_eq in_cons : core.

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

Fact perm_Forall2_xchg [X Y] [E : X → Y → Prop] [l m k] :
  l ~ₚ m → Forall2 E m k →  ∃p, Forall2 E l p ∧ p ~ₚ k.
Proof.
  intros H1%Permutation_sym H2%Forall2_xchg.
  destruct (Forall2_perm_xchg H2 H1) as (? & ? & ?%Forall2_xchg); eauto.
Qed.

Section perm_eq.

  Variable (X : Type).

  Implicit Type (E : X → X → Prop).

  Inductive perm_eq E : list X → list X → Prop :=
    | perm_eq_intro l m k : Forall2 E l m → m ~ₚ k → perm_eq E l k.

  Hint Constructors perm_eq : core.

  Fact perm_eq_refl E l :
      (∀x, x ∈ l → E x x)
    → perm_eq E l l.
  Proof.
    constructor 1 with l; auto.
    rewrite <- Forall_forall in H.
    induction H; eauto.
  Qed.

  Fact perm_eq_xchg E l m : perm_eq E l m → ∃p, l ~ₚ p ∧ Forall2 E p m.
  Proof.
    destruct 1 as [ l m k H1 H2 ].
    apply (Forall2_perm_xchg H1 H2).
  Qed.

  Hint Resolve Permutation_sym Permutation_in : core.

  Fact perm_eq_sym E l m :
      (∀ x y, x ∈ l → y ∈ m → E x y → E y x)
    → perm_eq E l m
    → perm_eq E m l.
  Proof.
    intros Hlm (p & H1 & H2%Forall2_xchg)%perm_eq_xchg.
    constructor 1 with p; auto.
    revert H2; apply Forall2_impl_dep; eauto.
  Qed.

  Fact perm_eq_trans E l m k : 
      (∀ x y z, x ∈ l → y ∈ m → z ∈ k → E x y → E y z → E x z)
    → perm_eq E l m
    → perm_eq E m k
    → perm_eq E l k.
  Proof.
    intros Hlmk.
    intros (u & H1 & H2)%perm_eq_xchg.
    destruct 1 as [ m v k H3 H4 ].
    assert (Forall2 E u v) as Huv.
    1: revert H2 H3; apply Forall2_trans_dep; eauto.
    destruct (perm_Forall2_xchg H1 Huv) as (? & []); eauto.
  Qed.

End perm_eq.

Section multiset_order.

  Variables (X : Type) (R : X → X → Prop).

  (* Infix notation for the base relation *)
  Infix "<" := R.

  (* x is a <-upper bound for the list m *)
  Notation "m <ₗ x" := (∀y, y ∈ m → y < x).

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
    + intros (? & ? & ? & ? & ? & -> & ?); eauto.
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

  Fact mso_step_cons x l : l ⊏ x::l.
  Proof. now apply @mso_step_intro with (l := []) (m := []); simpl. Qed.

  (** Inversion lemmas for Acc_mso_step_below *)

  (** Case analysis for the shape _ ⊏ [] 
      The empty list is minimal for ⊏     *)
  Fact mso_step_nil_right_inv l : ¬ l ⊏ [].
  Proof. now intros ([] & ? & ? & ? & ? & ? & ?)%mso_step_inv. Qed.

  (** Case analysis (inversion) for the shape _ ⊏ _::_  
      This is the critical lemma for inverting after
      applying the Acc_intro constructor in the section
       Acc_mso_step below *)
  Lemma mso_step_cons_right_inv k y m : 
      k ⊏ y::m 
    → (∃ u,       k ~ₚ u ++ m 
                ∧ u <ₗ y)
    ∨ (∃ l u x r, m = l++[x]++r
                ∧ k ~ₚ y::l++u++r
                ∧ u <ₗ x).
  Proof.
    intros ([] & ? & ? & ? & ? & [-> ->]%cons_inj & ?)%mso_step_inv; simpl in *. 
    + left; eauto.
    + right; do 4 eexists; eauto.
  Qed.

  Section Acc_mso_step.

    Hint Constructors Acc : core.
    Hint Resolve mso_step_perm_r : core.

    Notation W := (Acc mso_step).

    Local Fact Permutation_Acc_mso_step l m : l ~ₚ m → W m → W l.
    Proof. intros ? []; eauto. Qed.

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
  Proof. induction l as [ | x l IH ]; simpl; auto; intros ?%IH; eauto. Qed.

  Fact mso_app_tail l m r : m ⊏⁺ l → m ⊏⁺ l++r.
  Proof.
    intros H.
    apply mso_perm_r with (r++l).
    + apply Permutation_app_comm.
    + now apply mso_app_head.
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

  Fact mso_step_Forall2 (E : X → X → Prop) p l m :
     (∀ x y z, y ∈ l → z ∈ m → x < y → E y z → x < z)
   → p ⊏ l → Forall2 E l m → p ⊏⁺ m.
  Proof.
    intros H1 H2 H3.
    revert H3 p H2 H1.
    induction 1 as [ | x y l m H1 H2 IH2 ].
    + now intros ? ?%mso_step_nil_right_inv.
    + intros p [(u & H3 & H4)|]%mso_step_cons_right_inv G.
      * apply mso_perm_l with (1 := Permutation_sym H3).
        apply mso_trans with (y::l).
        - apply mso_ctx with (l := []) (v := [_]).
          apply mso_intro.
          intros z Hz.
          apply G with (3 := H4 _ Hz); auto.
        - rewrite <- (app_nil_r l), <- (app_nil_r m).
          apply mso_ctx with (l := [_]).

  Admitted.

  Fact mso_Forall2 (E : X → X → Prop) p l m :
     (∀ x y z, y ∈ l → z ∈ m → x < y → E y z → x < z)
   → p ⊏⁺ l → Forall2 E l m → p ⊏⁺ m.
  Proof.
    intros H1 (q & H2 & H3)%clos_trans_inv_right H4.
    apply clos_rt_t with (1 := H2).
    apply mso_step_Forall2 with (3 := H4); auto.
  Qed.

End multiset_order.

Arguments mso {_}.
