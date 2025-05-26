(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

Require Import List Wellfounded Relations Permutation Arith Lia Utf8.
Import ListNotations.

Require Import utils acc perm_eq mso mpo.

Notation "'⟨' x '|' l '⟩ₜ'" := (node x l) (at level 0, l at level 200, format "⟨ x | l ⟩ₜ").

(** Notations for the construction of the list order *)
#[local] Reserved Notation "x '≺' y" (at level 70, no associativity, format "x  ≺  y").
#[local] Reserved Notation "x '≺ₗ' y" (at level 70, no associativity, format "x  ≺ₗ  y").
#[local] Reserved Notation "x '⊏' y" (at level 70, no associativity, format "x  ⊏  y").
#[local] Reserved Notation "x '⊏⁺' y" (at level 70, no associativity, format "x  ⊏⁺  y").

#[local] Hint Constructors clos_trans : core.
#[local] Hint Resolve Acc_inv Acc_intro 
                      in_cons in_eq in_elt in_or_app : core.

Notation "R ⋆" := (clos_refl_trans R) (at level 1, left associativity, format "R ⋆").
Notation "R ⋄ T" := (λ x z, ∃y, R x y ∧ T y z) (at level 2, right associativity, format "R ⋄ T").

Section list_order.

  Variables (X : Type) (R : X → X → Prop).

  Infix "≺" := R.
  Notation "l ≺ₗ y" := (∀x, x ∈ l → x ≺ y).

  Local Fact lt_fall_sg x y : x ≺ y → [x] ≺ₗ y.
  Proof. now intros ? ? [ <- | [] ]. Qed.

  Hint Resolve lt_fall_sg : core.

  (* Inductive definition of the list relation ⊏ 
     of which the transitive closure ⊏⁺ is the list order. *)

  Inductive lo_step : list X → list X → Prop :=
    | lo_step_intro l x y r : x ≺ y → l++[x]++r ⊏ l++[y]++r
  where "l ⊏ m" := (lo_step l m).

  Hint Constructors lo_step : core.

  Fact lo_step_ctx l r u v : u ⊏ v → l++u++r ⊏ l++v++r.
  Proof.
    induction 1 in l, r |- *; eauto.
    rewrite <- !app_assoc, !(app_assoc l); eauto.
  Qed.

  (* The inversion lemma gives an alternate characterization,
     used below for more specific inversion lemmas below *)
  Local Fact lo_step_inv k p :
         k ⊏ p ↔ ∃ l x y r, k = l++[x]++r ∧ p = l++[y]++r ∧ x ≺ y.
  Proof.
    split.
    + intros [ l m x r ]; now exists l, m, x, r.
    + intros (? & ? & ? & ? & -> & -> & ?); eauto.
  Qed.

  (** These two are key lemmas in the proof of (Acc lo_step) below *)

  Local Fact lo_step_nil_inv l : ~ l ⊏ [].
  Proof. now intros ([] & ? & ? & ? & ? & ? & ?)%lo_step_inv. Qed.

  Local Lemma lo_step_cons_right_inv k y m : 
          k ⊏ y::m 
        → (∃ x, k = x::m ∧ x ≺ y)
        ∨ (∃ l u x r, m = l++[x]++r ∧ k = y::l++[u]++r ∧ u ≺ x).
  Proof.
    intros ([ | z l] & u & x & r & hk & e & hu)%lo_step_inv; simpl in *;
    apply cons_inj in e as [-> ->]; [ left | right ]; eauto.
    exists l, u, x, r; eauto.
  Qed.

  Section Acc_lo_step.

    Notation W := (Acc lo_step).

    Local Fact Acc_lo_step_nil : W [].
    Proof. constructor 1; intros _ []%lo_step_nil_inv. Qed.

    Local Fact W_app_bound y r :
        (∀x, x ≺ y → ∀l, W l → W (x::l))
       → W r 
       → ∀l, l ≺ₗ y → W (l++r).
    Proof.
      intros hy ? l. 
      induction l; simpl; eauto.
      intros; apply hy; eauto.
    Qed.

    Hint Resolve W_app_bound : core.

    Local Fact W_cons_rec y m :
           (∀x, x ≺ y → ∀l, W l → W (x::l))
         → W m
         → (∀l, l ⊏ m → W (y::l))
         → W (y::m).
    Proof. constructor; intros ? [ (? & -> & ?) | (? & ? & ? & ? & -> & -> & ?) ]%lo_step_cons_right_inv; eauto. Qed.

    Hint Resolve W_cons_rec : core.

    Local Fact W_cons y : (∀x, x ≺ y → ∀l, W l → W (x::l)) → ∀l, W l → W (y::l).
    Proof. induction 2; eauto. Qed.

    Hint Resolve W_cons : core.

    Local Lemma Acc_lo_step_cons x : Acc R x → ∀l, W l → W (x::l).
    Proof. induction 1; eauto. Qed.

  End Acc_lo_step.

  Hint Resolve Acc_lo_step_nil
               Acc_lo_step_cons : core.

  (* W is closed under [] and x::_ for any accessible x
     so it contains any list composed of accessibles *) 
  Lemma forall_Acc_lo_step l : (∀x, x ∈ l → Acc R x) → Acc lo_step l.
  Proof.
    rewrite <- Forall_forall.
    induction 1; eauto.
  Qed.

  Lemma Acc_lo_step_forall l : Acc lo_step l → ∀x, x ∈ l → Acc R x.
  Proof.
    induction 1 as [ m _ IH ]; intros y (l & r & ->)%in_split.
    constructor 1; intros x Hx.
    apply IH with (l++[x]++r); auto.
  Qed.

  Hint Resolve forall_Acc_lo_step Acc_lo_step_forall : core.

  Theorem Acc_lo_step_iff l : Acc lo_step l ↔ ∀x, x ∈ l → Acc R x.
  Proof. split; eauto. Qed.

End list_order.

Arguments lo_step {_}.

(*
Section mono.

  Variables (X : Type) (R T : X → X → Prop).

  Fact lo_step_mono : R ⊆₂ T → lo_step R ⊆₂ lo_step T.
  Proof. induction 2; constructor; eauto. Qed.

  Hint Resolve lo_step_mono : core.

  Fact lo_mono : R ⊆₂ T → lo R ⊆₂ lo T.
  Proof. intro; apply clos_trans_mono; eauto. Qed.

End mono.
*)

Definition restr₂ {X} (R : X → X → Prop) (P : X → Prop) (u v : sig P) :=
  R (proj1_sig u) (proj1_sig v).

Definition restr₁ {X} (Q : X → Prop) (P : X → Prop) (u : sig P) :=
  Q (proj1_sig u).

Inductive cover {X} (T : X → X → Prop) (P : X → Prop) x : Prop :=
  | cover_stop : P x → cover T P x
  | cover_next : (∀y, T y x → cover T P y) → cover T P x.

Hint Constructors cover : core.

Inductive covers {X} (T : X → X → Prop) (Q P : X → Prop) x : Prop :=
  | covers_stop : Q x → P x → covers T Q P x
  | covers_next : Q x → (∀y, Q y → T y x → covers T Q P y) → covers T Q P x.

Hint Constructors covers : core.

Fact covers__sub X T Q P x : @covers X T Q P x → Q x.
Proof. now intros []. Qed.

Fact covers__cover_restr X T Q P x : @covers X T Q P x → forall hx : Q x, cover (restr₂ T Q) (restr₁ P Q) (exist _ x hx).
Proof.
  induction 1 as [ x H1 H2 | x H1 H2 IH2 ]; intros hx.
  + constructor 1; red; auto.
  + constructor 2; intros (y & hy) H; apply IH2; auto.
Qed.

Fact cover_restr__covers X T Q P x : cover (restr₂ T Q) (restr₁ P Q) x → @covers X T Q P (proj1_sig x).
Proof.
  induction 1 as [ [x hx] H1 | [x hx] H1 IH1 ].
  + constructor; auto.
  + constructor 2; auto.
    intros y hy ?.
    now apply (IH1 (exist _ y hy)).
Qed.

Theorem cover_restr_iff_covers X T Q P x : cover (restr₂ T Q) (restr₁ P Q) x ↔ @covers X T Q P (proj1_sig x).
Proof.
  split.
  + apply cover_restr__covers.
  + destruct x; intro; now apply covers__cover_restr.
Qed.

Section cover_morphism.

  (* Transfert of the cover predicate using a morphism *)

  Variables (X Y : Type) (R : X → X → Prop) (T : Y → Y → Prop)
            (P : X → Prop) (Q : Y → Prop)
            (f : Y → X → Prop)
            (Hf : ∀y, exists x, f y x)
            (HPQ : ∀ y x, f y x → P x → Q y)
            (HRT : ∀ y₁ y₂ x₁ x₂, f y₁ x₁ → f y₂ x₂ → T y₁ y₂ → R x₁ x₂).

  Lemma cover_morphism x y : f y x → cover R P x → cover T Q y.
  Proof.
    intros Hy H; revert H y Hy.
    induction 1 as [ | x _ IHx ]; eauto.
    intros y Hyx; constructor 2.
    intros y' Hy'.
    destruct (Hf y') as (x' & Hx'); eauto.
  Qed.

End cover_morphism.

Notation wfp := Acc.

Fact wfp_clos_rt X T (x y : X) : T⋆ x y → wfp T y → wfp T x.
Proof. induction 1; eauto. Qed.

Section bars.

  Variables (X : Type).
  
  Implicit Types (T : X → X → Prop) (P Q : X → Prop).

  Definition gindy T P x := (∀y, T y x → P y) → P x.

  Inductive bars T P x : Prop :=
    | bars_stop : P x → bars T P x
    | bars_next : (∀y, T y x → bars T P y) → bars T P x.

  Inductive gbars T Q P x : Prop :=
    | gbars_stop : P x → gbars T Q P x
    | gbars_next : Q x → (∀y, T y x → gbars T Q P y) → gbars T Q P x.

  Hint Constructors gbars bars : core.

  Fact bars_iff_gbars T P x : bars T P x ↔ gbars T (λ _, True) P x.
  Proof. split; induction 1; eauto. Qed.

  Fact gindy_cover T P x : gindy T (bars T P) x.
  Proof. red; auto. Qed. 

  Fact covers__gbars T Q P x : covers T Q P x → gbars T Q P x.
  Proof.
    induction 1 as [ | x H1 H2 IH2 ]; eauto.
    constructor 2; auto.
  Admitted.

  Fact gbars_sequence T Q P x : gbars T Q P x → ∀f, f 0 = x → (∀n, T (f (S n)) (f n)) → ∃n, P (f n) ∧ ∀i, i < n → Q (f i).
  Proof.
    induction 1 as [ x Hx | x H1 H2 IH2 ]; intros f <- Hf2.
    + exists 0; split; auto; lia.
    + destruct (IH2 _ (Hf2 0) (fun n => f (S n))) as (n & G1 & G2); auto.
      exists (S n); split; auto.
      intros [|i] ?; auto; apply G2; lia.
  Qed.

  Fact bars_iff_wfp T x : bars T (λ _, False) x ↔ wfp T x.
  Proof. split; induction 1; now eauto. Qed.

  Fact bars_sequence T P x : bars T P x → ∀f, f 0 = x → (∀n, T (f (S n)) (f n)) → ∃n, P (f n).
  Proof.
    rewrite bars_iff_gbars.
    intros H f H1 H2.
    destruct (gbars_sequence _ _ _ _ H f H1 H2) as (n & []); eauto.
  Qed.
  
  Fact gbars_gindy T P x : gbars T (gindy T P) P x ↔ P x.
  Proof. split; auto; induction 1; eauto. Qed.
  
  Fact gindy_gbars T Q P x : Q x → gindy T (gbars T Q P) x.
  Proof. intros ? ?; eauto. Qed.
  
  Fact gindy_full T P : (∀x, gindy T P x) → ∀x, bars T P x ↔ P x.
  Proof.
    intros H; split; auto.
    induction 1; eauto; now apply H.
  Qed.
  
  Fact bars_wfp T x : bars T (wfp T) x ↔ wfp T x.
  Proof. apply gindy_full; constructor; auto. Qed.

  Fact gbars__bars_gbars R T Q P x: (∀y, T y x → gbars R Q P y) → bars T (gbars R Q P) x.
  Proof. constructor 2; constructor 1; eauto. Qed.

  Fact bars_inv T P x : bars T P x → (P x → ∀y, T y x → P y) → ∀y, T y x → bars T P y.
  Proof. intros []; auto. Qed.

  Fact gbars_inv T Q P x : gbars T Q P x → (P x → ∀y, T y x → P y) → ∀y, T y x → gbars T Q P y.
  Proof. intros []; auto. Qed.

  Fact wfp_inv T x : (wfp T x → ∀y, T y x → wfp T y).
  Proof. now intros []. Qed.

  Hint Constructors clos_refl_trans : core.

  Fact wfp__crt__gbars_disj R Q P y :
      wfp R y
    → (∀x, R⋆ x y → P x ∨ Q x)
    → gbars R Q P y.
  Proof.
    induction 1 as [ y _ IH ]; intros Hy.
    destruct (Hy y) as [ | ]; auto.
    constructor 2; eauto.
  Qed.

End bars.

Arguments gbars {_}.
Arguments bars {_}.
Arguments gindy {_}.

(* ⋄ ⋆ *)

Section bars_morphism.

  (* Transfert of the cover predicate using a morphism *)

  Variables (X Y : Type) (R : X → X → Prop) (T : Y → Y → Prop)
            (P : X → Prop) (Q : Y → Prop)
            (f : Y → X → Prop)
            (Hf : ∀y, ∃x, f y x)
            (HPQ : ∀ y x, f y x → P x → Q y)
            (HRT : ∀ y₁ y₂ x₁ x₂, f y₁ x₁ → f y₂ x₂ → T y₁ y₂ → R x₁ x₂).
            
  Hint Constructors bars : core.

  Lemma bars_morphism x y : f y x → bars R P x → bars T Q y.
  Proof.
    intros Hy H; revert H y Hy.
    induction 1 as [ | x _ IHx ]; eauto.
    intros y Hyx; constructor 2.
    intros y' Hy'.
    destruct (Hf y') as (x' & Hx'); eauto.
  Qed.

End bars_morphism.

Fact bars_mono X (R T : X → X → Prop) (P Q : X → Prop) :
    (∀x, P x → Q x)
  → (∀ x y, T x y → R x y)
  →  ∀x, bars R P x → bars T Q x.
Proof.
  intros H1 H2 x.
  apply bars_morphism with (f := eq); intros; subst; eauto.
Qed.

Hint Constructors gbars : core.

Fact gbars_mono X (R T : X → X → Prop) (Q Q' P P' : X → Prop) :
    (∀x, P x → P' x)
  → (∀x, Q x → Q' x)
  → (∀ x y, T x y → R x y)
  →  ∀x, gbars R Q P x → gbars T Q' P' x.
Proof. induction 4; eauto. Qed.

Local Fact gbars__bars X T Q P x : @gbars X T Q P x → ∀hx, bars (restr₂ T Q) (restr₁ P Q) (exist _ x hx).
Proof.
  induction 1; intro.
  + constructor 1; red; auto.
  + constructor 2; intros [] ?; auto.
Qed.

Local Fact bars__gbars X T Q P x : bars (restr₂ T Q) (restr₁ P Q) x → @gbars X T Q P (proj1_sig x).
Proof.
  induction 1 as [ [x hx] H1 | [x hx] H1 IH1 ].
  + constructor; auto.
  + constructor 2; auto.
Admitted.

Section termination.

  Variables (X : Type) (R T K : X → X → Prop).

  (* R := <| ; T := ρ ; K := << *)

  Section conditions.

    Variables (s : X).

    Definition condition1a := (∀r, R r s → wfp T r) → bars T (gbars R (λ r, K r s) (wfp T)) s.
    Definition condition1b := (∀r, R r s → wfp T r) → ∀t, T t s → gbars R (λ r, K r s) (wfp T) t.
    Definition condition1c := ∀t, T t s → gbars R (λ r, K r s) (λ v, T⋄R v s) t.
    Definition condition1c' := ∀t, T t s → gbars R (λ r, K r s) (λ v, T⋆⋄R v s) t.
    Definition condition1d := (∀r, wfp R r) ∧ ((∀r, R r s → wfp T r) → ∀t, T t s → ∀r, R⋆ r t → wfp T r ∨ K r s).
    Definition condition1e := (∀r, wfp R r) ∧ ∀ r t, T t s → R⋆ r t → (T⋆⋄R r s) ∨ K r s.
    
    (** Two chains (e) → (d) → (b) → (a)
                  (c) → (c') → (b) *)
    
    Fact condition1_b_a : condition1b → condition1a.
    Proof. intros H H1; now apply gbars__bars_gbars, H. Qed.

    Hint Constructors clos_refl_trans gbars : core.

    Fact condition1_d_b : condition1d → condition1b.
    Proof. intros [] ? ? ?; apply wfp__crt__gbars_disj; eauto. Qed.

    Hint Resolve wfp_clos_rt : core.
   
    Fact condition1_e_d : condition1e → condition1d.
    Proof.
      intros (H1 & H2); split; auto.
      intros Hs t Ht r Hr.
      destruct (H2 _ _ Ht Hr) as [ (? & []) | ]; eauto.
    Qed.

    Hint Resolve wfp_clos_rt : core.

    Fact condition1_c'_b : condition1c' → condition1b.
    Proof.
      intros H Hs t Ht; red in H.
      generalize (H _ Ht); clear Ht.
      apply gbars_mono; auto.
      intros ? (? & ? & ?%Hs); eauto.
    Qed.

    Fact condition1_c_b' : condition1c → condition1c'.
    Proof.
      intros H t Ht.
      generalize (H _ Ht); clear Ht.
      apply gbars_mono; auto.
      intros ? (? & []); eauto.
    Qed.

  End conditions.

  Lemma lemma6 s : condition1a s → gindy K (gindy R (wfp T)) s.
  Proof.
    intros H H1 H2; red in H.
    specialize (H H2).
    apply bars_wfp.
    revert H.
    apply bars_mono; auto.
    intros x Hx.
    apply gbars_gindy with (T := R).
    revert Hx; apply gbars_mono; auto.
  Qed.

  Theorem theorem7 :
      (∀s, condition1a s)
    → (∀s, (* (∀r, R r s → wfp T r) → *) bars K (gindy R (wfp T)) s)
    → (∀s, bars R (wfp T) s)
    → well_founded T.
  Proof.
    intros H1 H2 H3.
    generalize (gindy_full _ _ _ (λ s, lemma6 _ (H1 s))); intros H4.
    assert (∀s, gindy R (wfp T) s) as H5.
    1: intros s; apply H4, H2.
    generalize (gindy_full _ _ _ H5); intros H6.
    intro; apply H6, H3.
  Qed.

End termination.

Section goubault.

  Variables (X : Type) (R T K : X → X → Prop).

  Lemma lemma8 P s :
      (∀t, T t s → P t ∨ (K t s ∧ ∀u, R u t → T u s ∨ P u))
    → (∀r, wfp R r)
    → (∀t, T t s → gbars R (λ r, K r s) P t).
  Proof.
    intros H1 H2 t Ht.
    induction t as [ t IHt ] using (well_founded_induction H2).
    destruct (H1 _ Ht) as [ H3 | (H3 & H4) ]; auto.
    constructor 2; auto.
    intros u Hu.
    destruct (H4 _ Hu); eauto.
  Qed.

  Hint Resolve wfp_clos_rt : core.

  Lemma lemma9 s :
      (∀t, T t s → (T⋆⋄R t s) ∨ (K t s ∧ ∀u, R u t → T u s))
    → (∀r, wfp R r)
    → condition1b _ R T K s.
  Proof.
    intros H1 H2 H3.
    apply lemma8; auto.
    intros t Ht.
    destruct (H1 _ Ht) as [ (? & ? & ?%H3) | [] ]; eauto.
  Qed.

  Section thm1.

    Definition ovb (P : X → Prop) s := ∀u, R u s → P u.

(*    Notation SN := (wfp T).

    Let SNb s := ovb SN s → SN s.

    Goal forall s, SNb s = gindy R SN s.
    Proof. reflexivity. Qed. *)

    Hypothesis H1 : ∀ t s, T t s → T⋆⋄R t s ∨ K t s ∧ ∀u, R u t → T u s.
    Hypothesis H4 : ∀s, (∀r, R r s → wfp T r) → bars K (gindy R (wfp T)) s.

    Section goubault_orig.

      Hypothesis H3 : well_founded R.

      Theorem goubault s : wfp T s.
      Proof.
        induction s as [ s IHs ] using (well_founded_induction H3).
        cut (gindy R (wfp T) s).
        1: now intros H; apply H.
        apply H4 in IHs; clear H4.
        revert s IHs; apply gindy_full; intros s IH Hs.
        constructor; intros t.
        induction t as [ t IHt ] using (well_founded_induction H3).
        intros [ (u & G1 & G2) | (G1 & G2) ]%H1.
        + generalize (Hs _ G2); eauto.
        + apply IH; auto; red; auto.
      Qed.

    End goubault_orig.

    Section goubault_bar.

      Hypothesis H3 : ∀s, bars R (wfp T) s.

      Theorem goubault_bar s : wfp T s.
      Proof.
        generalize (H3 s).
        induction 1 as [ | s _ IHs ]; auto.
        cut (gindy R (wfp T) s).
        1: now intros H; apply H.
        apply H4 in IHs; clear H4.
        revert s IHs; apply gindy_full; intros s IH Hs.
        constructor; intros t.
        generalize (H3 t).
        induction 1 as [ | t _ IHt ]; auto.
        intros [ (u & G1 & G2) | (G1 & G2) ]%H1.
        + generalize (Hs _ G2); eauto.
        + apply IH; auto; red; auto.
      Qed.

    End goubault_bar.

    Section goubault_1a.

      Hypothesis H1' : ∀s, condition1a _ R T K s.
      Hypothesis H3 : ∀s, bars R (wfp T) s.

(*
      Theorem goubault_1a s : wfp T s.
      Proof.
        clear H1.
        generalize (H3 s).
        induction 1 as [ | s _ IHs ]; auto.
        cut (gindy R (wfp T) s).
        1: now intros H; apply H.
        apply H4 in IHs; clear H4.
        revert s IHs; apply gindy_full; intros s IH Hs.
        constructor; intros t.
        generalize (H3 t).
        induction 1 as [ | t _ IHt ]; auto.
        intros Ht.
        assert (Ht' : ∀y, R y t → wfp T y).
        1:{ intros r Hr.
 
        Check (H1' _ Hs).
        Search bars gbars.
        Check gbars_inv _ R (λ r : X, K r s) (wfp T) s.
 (gbars_inv _ _ _ _ _ (wfp_inv _ _)).
        intros ?%bars_inv.
        intros [ (u & G1 & G2) | (G1 & G2) ]%H1'.
        + generalize (Hs _ G2); eauto.
        + apply IH; auto; red; auto.
 *)

  End goubault_1a.


  Hypothesis H3 : well_founded R.

    Hypothesis xm : ∀P, P ∨ ¬ P.

    Local Fact H5 : ∀s, bars K (gindy R (wfp T)) s.
    Proof.
      intros s.
      destruct (xm (∀r, R r s → wfp T r)); auto.
      constructor 1; now red.
    Qed.

    (* Carefull than the prof require XM here *)

    Theorem goubault' s : wfp T s.
    Proof.
      revert s.
      apply theorem7 with (R := R) (K := K).
      + intro; apply condition1_b_a, lemma9; auto.
      + intro; apply H5.
      + intros s; generalize (H3 s).
        rewrite <- bars_iff_wfp.
        now apply bars_mono.
    Qed.

  End thm1.

End goubault.

Section ctxt.

  Variables (X : Type).

  Implicit Type (R : term X → term X → Prop).

  Inductive ctxt R : term X → term X → Prop :=
    | ctxt_stop p q : R p q → ctxt R p q
    | ctxt_comp f l r p q : ctxt R p q → ctxt R ⟨f|l++[p]++r⟩ₜ ⟨f|l++[q]++r⟩ₜ
    .

  Fact ctxt_inv R p q : 
      ctxt R p q 
    → R p q ∨ ∃ f l r u v, p = ⟨f|l++[u]++r⟩ₜ ∧ q = ⟨f|l++[v]++r⟩ₜ ∧ ctxt R u v.
  Proof.
    destruct 1; eauto.
    right; do 5 eexists; eauto.
  Qed.

  Hint Constructors ctxt : core.
  
  Fact ctxt_idem R r s : ctxt (ctxt R) r s → ctxt R r s.
  Proof. induction 1; auto. Qed.
  
  (** Fails: g[] > g[g[]] as single reduction
      gives  g[] > g²[] > g³[] > ... as in the contextual closure 
  
  Fact wf_ctxt R : well_founded R → well_founded (ctxt R). *)

  Let SN := @Acc (term X).
  Let fwf R r t := R r t /\ SN R t. 

  Variables (R : term X → term X → Prop).

  Inductive sn1 : term X → term X → Prop :=
    | sn1_intro f l p q r : SN R q → ctxt R p q → sn1 ⟨f|l++[p]++r⟩ₜ ⟨f|l++[q]++r⟩ₜ.

  Definition sn2 := ctxt sn1.
  
  Fact sn1__sn2 r t : sn1 r t → sn2 r t.
  Proof. now constructor 1. Qed.
