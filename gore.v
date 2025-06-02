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

Require Import utils term.

Notation "'⟨' x '|' l '⟩ₜ'" := (node x l) (at level 0, l at level 200, format "⟨ x | l ⟩ₜ").

(** Notations for the construction of the list order *)
#[local] Reserved Notation "x '≺' y" (at level 70, no associativity, format "x  ≺  y").
#[local] Reserved Notation "x '≺ₗ' y" (at level 70, no associativity, format "x  ≺ₗ  y").
#[local] Reserved Notation "x '⊏' y" (at level 70, no associativity, format "x  ⊏  y").
#[local] Reserved Notation "x '⊏⁺' y" (at level 70, no associativity, format "x  ⊏⁺  y").

#[local] Hint Constructors clos_trans : core.
#[local] Hint Resolve Acc_inv Acc_intro 
                      in_cons in_eq in_elt in_or_app : core.

Notation "R ⃰" := (clos_refl_trans R) (at level 1, left associativity, format "R ⃰").
Notation "R ⁺" := (clos_trans R) (at level 1, left associativity, format "R ⁺").
Notation "R ⋄ T" := (λ x z, ∃y, R x y ∧ T y z) (at level 2, right associativity, format "R ⋄ T").

#[global] Notation "P '⊆₁' Q" := (∀x, P x → Q x) (at level 70, no associativity, format "P  ⊆₁  Q").
#[global] Notation "P '⊆₂' Q" := (∀ x y, P x y → Q x y) (at level 70, no associativity, format "P  ⊆₂  Q").

#[global] Notation "P '≡₁' Q" := (∀x, P x ↔ Q x) (at level 70, no associativity, format "P  ≡₁  Q").
#[global] Notation "P '≡₂' Q" := (∀ x y, P x y ↔ Q x y) (at level 70, no associativity, format "P  ≡₂  Q").


#[global] Notation "P '∪₂' Q" := (λ x y, P x y ∨ Q x y) (at level 50, left associativity, format "P ∪₂ Q").
#[global] Notation "P '∩₂' Q" := (λ x y, P x y ∧ Q x y) (at level 48, left associativity, format "P ∩₂ Q").

Fact rel_comp_assoc U X Y Z (R : U → X → Prop) (T : X → Y → Prop) (K : Y → Z → Prop) u z : R⋄T⋄K u z ↔ (R⋄T)⋄K u z.
Proof. firstorder. Qed.

Definition restr₂ {X} (R : X → X → Prop) (P : X → Prop) (u v : sig P) :=
  R (proj1_sig u) (proj1_sig v).

Definition restr₁ {X} (Q : X → Prop) (P : X → Prop) (u : sig P) :=
  Q (proj1_sig u).

Fact forall_congr X (P Q : X → Prop) : P ≡₁ Q → (∀x, P x) ↔ (∀x, Q x).
Proof. firstorder. Qed.

#[local] Hint Constructors clos_trans clos_refl_trans : core.

Fact crt_mono X (R T : X → X → Prop) : R ⊆₂ T → R ⃰ ⊆₂ T ⃰.
Proof. induction 2; eauto. Qed.

Fact crt_xchg_l [X] [R T : X → X → Prop] : T⋄R ⊆₂ R⋄T → T ⃰⋄R ⊆₂ R⋄T ⃰.
Proof.
  intros HRT x z (y & H1%clos_rt_rt1n_iff & H2).
  revert H1 z H2.
  induction 1 as [ | x y z H1 H2 IH2 ]; eauto; intros u (v &[])%IH2.
  destruct (HRT x v) as (? & []); eauto.
Qed.

Fact crt_xchg_r [X] [R T : X → X → Prop] : T⋄R ⊆₂ R⋄T → T⋄R ⃰ ⊆₂ R ⃰⋄T.
Proof.
  intros HRT x z (y & H1 & H2%clos_rt_rtn1_iff).
  revert H2 x H1.
  induction 1 as [ | z x H1 H2 IH2 ]; eauto; intros u (v &[])%IH2.
  destruct (HRT v x) as (? & []); eauto.
Qed.

Fact crt_xchg [X] [R T : X → X → Prop] : T⋄R ⊆₂ R⋄T → T ⃰⋄R ⃰ ⊆₂ R ⃰⋄T ⃰.
Proof. intro; now apply crt_xchg_r, crt_xchg_l. Qed.

Fact crt_xchg_cup X (R T : X → X → Prop) : T⋄R ⊆₂ R⋄T → (T∪₂R) ⃰ ≡₂ R ⃰⋄T ⃰.
Proof.
  intros G; split.
  + induction 1 as [ u v [ H1 | H1 ] | | u v w _ (a & H1 & H2) _ (b & H3 & H4) ].
    * exists u; eauto.
    * exists v; eauto.
    * exists x; eauto.
    * destruct (crt_xchg G a b) as (? & []); eauto.
  + intros (w & H1 & H2); constructor 3 with w. 
    * revert H1; apply crt_mono; eauto.
    * revert H2; apply crt_mono; eauto.
Qed.

Notation wfp := Acc.

Section well_founded_part__well_founded.

  Variables (X : Type).

  Implicit Types (R T : X → X → Prop).

  Fact wfp_inv T x : wfp T x → ∀y, T y x → wfp T y.
  Proof. apply Acc_inv. Qed.

  Fact wfp_clos_rt T x y : T ⃰ x y → wfp T y → wfp T x.
  Proof. induction 1; eauto. Qed.

  Fact wfp_clos_t T : wfp T ⊆₁ wfp T⁺.
  Proof. induction 1; constructor 1; induction 1; eauto. Qed.

  Fact wfp_anti R T : R ⊆₂ T → wfp T ⊆₁ wfp R.
  Proof. induction 2; constructor; eauto. Qed.

  Fact wfp_congr R T : R ≡₂ T → wfp R ≡₁ wfp T.
  Proof. intros H ?; split; apply wfp_anti, H. Qed.

  Local Lemma lemma12a_one_dir R T : well_founded R⋄T → well_founded T⋄R.
  Proof.
    intros H x.
    constructor; intros y (z & H1 & H2).
    induction z in x, y, H1, H2 |- * using (well_founded_induction H).
    constructor; intros ? (? & []); eauto.
  Qed.

  Lemma lemma12a R T : well_founded R⋄T ↔ well_founded T⋄R.
  Proof. split; unfold well_founded; apply lemma12a_one_dir. Qed.

  Lemma lemma12b R T : well_founded T → wfp R⋄T ⃰ ≡₁ wfp (R∪₂T).
  Proof.
    intros HT x; split.
    + induction 1 as [ x _ IH ].
      induction x as [ x IHx ] using (well_founded_induction HT).
      constructor 1; intros y [ Hy | Hy ]; eauto.
      apply IHx; auto.
      intros z (? & []); apply IH; eauto.
    + intros Hx%wfp_clos_t.
      revert x Hx; apply wfp_anti.
      intros x z (y & H1 & H2).
      apply clos_t_rt with y; eauto.
      revert H2; apply crt_mono; eauto.
  Qed.

  Lemma lemma12c R T : well_founded T → R⋄T ⊆₂ T ⃰⋄R → wfp (R∪₂T) ≡₁ wfp R.
  Proof.
    intros HT HRT x; split.
    1: apply wfp_anti; eauto.
    induction 1 as [ x _ IH ].
    induction x as [ x IHx ] using (well_founded_induction HT).
    constructor 1.
    intros y [ Hy | Hy ]; eauto.
    apply IHx; auto.
    intros z Hz.
    destruct (HRT z x) as (u & H1 & H2); eauto.
    generalize (IH _ H2).
    apply wfp_clos_rt.
    revert H1; apply crt_mono; eauto.
  Qed.

  Variables (R T : _) (HRT : T⋄R ⊆₂ R⋄T).

  Fact wfp_commute s : wfp T s → ∀t, R t s → wfp T t.
  Proof.
    induction 1 as [ s _ IHs ]; intros t Ht.
    constructor.
    intros u Hu.
    destruct (HRT u s) as (? & []); eauto.
  Qed.

  Hint Resolve wfp_commute : core.

  Fact wfp_commute_crt s t : R ⃰ t s → wfp T s → wfp T t.
  Proof. induction 1; eauto. Qed.

End well_founded_part__well_founded.

Arguments wfp_inv {_ _ _} _ {_}.

Fact wf_cap_wfp X T : well_founded (λ x y : X, T x y ∧ wfp T y).
Proof.
  intros x; constructor 1.
  intros y (H1 & H2).
  generalize (wfp_inv H2 H1).
  apply wfp_anti; tauto.
Qed.

Section onerel.

  (** The oneup and onerel terminology comes from
         Jeremy Dawson https://users.cecs.anu.edu.au/~jeremy/isabelle/2005/snabs/ *)

  Variables (X : Type) (R : X → X → Prop).

  Inductive onerel : list X → list X → Prop :=
    | onerel_stop x y l : R x y → onerel (x::l) (y::l)
    | onerel_skip x l m : onerel l m → onerel (x::l) (x::m).

  Hint Constructors onerel : core.

  Fact onerel_iff p q :
      onerel p q 
    ↔ ∃ l x y r, p = l++[x]++r ∧ q = l++[y]++r ∧ R x y.
  Proof.
    split.
    + induction 1 as [ x y l | a p q _ (l & x & y & r & -> & -> & ?) ].
      * now exists [], x, y, l.
      * now exists (a::l), x, y, r.
    + intros (l & x & y & r & -> & -> & ?).
      induction l; simpl; eauto.
  Qed.
  
  Fact wfp_onerel l : Forall (wfp R) l → wfp onerel l.
  Proof.
    induction 1 as [ | x l H1 _ IH ].
    + constructor; now intros ? ([] & ? & ? & ? & _ & ? & _)%onerel_iff.
    + revert H1 l IH.
      induction 1 as [ x _ IHx ].
      induction 1 as [ l Hl IHl ].
      constructor.
      intros [ | y m ] ([|z l'] & u & v & r & H1 & H2& H3)%onerel_iff.
      1,2: easy.
      * inversion H1; inversion H2; subst; eauto.
      * inversion H1; inversion H2; subst m l z y.
        apply IHl, onerel_iff.
        now exists l', u, v, r.
  Qed.

End onerel.

Arguments onerel {_}.
Arguments node {_}.
Arguments wfp_onerel {_ _ _}.

Section oneup.

  (** The oneup and onerel terminology comes from
         Jeremy Dawson https://users.cecs.anu.edu.au/~jeremy/isabelle/2005/snabs/ *)

  Variables (X Y Z : Type) (f : X → Y → Z) (R : Y → Y → Prop).

  Inductive oneup : Z → Z → Prop :=
    | oneup_intro x a b : R a b → oneup (f x a) (f x b).

  Fact oneup_iff z1 z2 :
    oneup z1 z2 ↔ ∃ x a b, z1 = f x a ∧ z2 = f x b ∧ R a b.
  Proof.
    split.
    + induction 1 as [ x a b ]; exists x; eauto.
    + intros (? & ? & ? & -> & -> & ?); now constructor.
  Qed.

  Hypothesis f_inj : ∀ x₁ x₂ y₁ y₂, f x₁ y₁ = f x₂ y₂ → x₁ = x₂ ∧ y₁ = y₂.

  Fact wfp_oneup x y : wfp R y → wfp oneup (f x y).
  Proof.
    induction 1 as [ y _ IHy ]; constructor.
    intros z (x' & a & b & -> & []%f_inj & H3)%oneup_iff.
    subst; auto.
  Qed.

End oneup.

Arguments oneup {_ _ _}.

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

  Hint Constructors clos_refl_trans : core.

  Fact wfp__crt__gbars_disj R Q P y :
      wfp R y
    → (∀x, R ⃰ x y → P x ∨ Q x)
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

#[local] Hint Constructors gbars bars : core.

Section gbars_morphism.

  (* Transfert of the gbars predicate using a morphism *)

  Variables (X Y : Type) (R : X → X → Prop) (T : Y → Y → Prop)
            (P Q : X → Prop) (P' Q' : Y → Prop)
            (f : Y → X → Prop)
            (Hf : ∀y, ∃x, f y x)
            (HP : ∀ y x, f y x → P x → P' y)
            (HQ : ∀ y x, f y x → Q x → Q' y)
            (HRT : ∀ y₁ y₂ x₁ x₂, f y₁ x₁ → f y₂ x₂ → T y₁ y₂ → R x₁ x₂).

  Fact gbars_morphism x y : f y x → gbars R Q P x → gbars T Q' P' y.
  Proof.
    intros Hy H; revert H y Hy.
    induction 1 as [ | x H _ IHx ]; eauto.
    intros y Hyx; constructor 2; eauto.
    intros y' Hy'.
    destruct (Hf y') as (x' & Hx'); eauto.
  Qed.

End gbars_morphism.

Fact gbars_mono X (R T : X → X → Prop) (P Q P' Q' : X → Prop) : T ⊆₂ R → Q ⊆₁ Q' → P ⊆₁ P' → gbars R Q P ⊆₁ gbars T Q' P'.
Proof. intros ? ? ? ?; apply gbars_morphism with (f := eq); intros; subst; eauto. Qed.

Section bars_morphism.

  (* Transfert of the cover predicate using a morphism *)

  Variables (X Y : Type) (R : X → X → Prop) (T : Y → Y → Prop)
            (P : X → Prop) (Q : Y → Prop)
            (f : Y → X → Prop)
            (Hf : ∀y, ∃x, f y x)
            (HPQ : ∀ y x, f y x → P x → Q y)
            (HRT : ∀ y₁ y₂ x₁ x₂, f y₁ x₁ → f y₂ x₂ → T y₁ y₂ → R x₁ x₂).

  Fact bars_morphism x y : f y x → bars R P x → bars T Q y.
  Proof. rewrite !bars_iff_gbars; apply gbars_morphism; auto. Qed.

End bars_morphism.

Fact bars_mono X (R T : X → X → Prop) (P Q : X → Prop) : T ⊆₂ R → P ⊆₁ Q → bars R P ⊆₁ bars T Q.
Proof. intros ? ? ?; apply bars_morphism with (f := eq); intros; subst; eauto. Qed.

Section termination.

  Variables (X : Type) (R T K : X → X → Prop).

  (* R := <| ; T := ρ ; K := << *)
  
  Hint Constructors gbars : core.
  Hint Resolve wfp_clos_rt : core.

  Section conditions.

    Variable (s : X).

    Definition condition1z := gindy K (gindy R (wfp T)) s.
    Definition condition1a := (∀r, R r s → wfp T r) → bars T (gbars R (λ r, K r s) (wfp T)) s.
    Definition condition1b := (∀r, R r s → wfp T r) → ∀t, T t s → gbars R (λ r, K r s) (wfp T) t.
    Definition condition1c := ∀t, T t s → gbars R (λ r, K r s) (λ v, T⋄R v s) t.
    Definition condition1c' := ∀t, T t s → gbars R (λ r, K r s) (λ v, T ⃰⋄R v s) t.
    Definition condition1d := (∀r, wfp R r) ∧ ((∀r, R r s → wfp T r) → ∀r, R ⃰⋄T r s → wfp T r ∨ K r s).
    Definition condition1e := (∀r, wfp R r) ∧ ∀r, R ⃰⋄T r s → T ⃰⋄R r s ∨ K r s.

    (** Two chains (e) → (d) → (b) → (a) → (z) and (c) → (c') → (b) *)

    Fact condition1_a_z : condition1a → condition1z.
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

    Fact condition1_b_a : condition1b → condition1a.
    Proof. intros H H1; now apply gbars__bars_gbars, H. Qed.

    Fact condition1_d_b : condition1d → condition1b.
    Proof. intros [] ? ? ?; apply wfp__crt__gbars_disj; eauto. Qed.

    Hint Resolve wfp_clos_rt : core.

    Fact condition1_e_d : condition1e → condition1d.
    Proof.
      intros (H1 & H2); split; auto.
      intros Hs r Hr.
      destruct (H2 _ Hr) as [ (? & []) | ]; eauto.
    Qed.

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

  Theorem theorem7 :
      (∀s, condition1a s)
    → (∀s, bars K (gindy R (wfp T)) s)
    → (∀s, bars R (wfp T) s)
    → well_founded T.
  Proof.
    intros H1 H2 H3.
    generalize (gindy_full _ _ _ (λ s, condition1_a_z _ (H1 s))); intros H4.
    clear H1.
    assert (∀s, gindy R (wfp T) s) as H5.
    1: intros s; apply H4, H2.
    generalize (gindy_full _ _ _ H5); intros H6.
    intro; apply H6, H3.
  Qed.

  Theorem theorem7_strong :
      (∀s, condition1z s)
    → (∀s, (∀r, R r s → wfp T r) → bars K (gindy R (wfp T)) s)
    → (∀s, bars R (wfp T) s)
    → well_founded T.
  Proof.
    unfold condition1z.
    intros H1 H4 H3 s.
    unfold gindy in H1.
    generalize (H3 s).
    induction 1 as [ | s _ IHs ]; auto.
    cut (gindy R (wfp T) s).
    1: now intros H; apply H.
    apply H4 in IHs; clear H4.
    induction IHs as [ | s _ IHs ]; eauto; intros Hs.
    constructor; intros t.
    generalize (H3 t).
    induction 1 as [ | t _ IHt ]; auto; intros Ht.
    generalize (H1 _ IHs Hs); eauto.
  Qed.

End termination.

Section goubault.

  Variables (X : Type) (R T K : X → X → Prop).

  (* This is just a more generic version of lemma 9 below 
     where P := (wfp T) is abstracted away *)
  Lemma lemma8 P s :
      (∀t, T t s → P t ∨ (K t s ∧ ∀u, R u t → T u s ∨ P u))
    → (∀r, bars R P r)
    → (∀t, T t s → gbars R (λ r, K r s) P t).
  Proof.
    intros H1 H2 t.
    generalize (H2 t).
    induction 1 as [ | t _ IHt ]; intros Ht; auto.
    destruct (H1 _ Ht) as [ H3 | (H3 & H4) ]; auto.
    constructor 2; auto.
    intros u Hu.
    destruct (H4 _ Hu); eauto.
  Qed.

  Hint Resolve wfp_clos_rt : core.

  Lemma lemma9 s :
      (∀t, T t s → (T ⃰⋄R t s) ∨ (K t s ∧ ∀u, R u t → T u s))
    → (∀r, bars R (wfp T) r)
    → condition1b _ R T K s.
  Proof.
    intros H1 H2 H3.
    apply lemma8; auto.
    intros t Ht.
    destruct (H1 _ Ht) as [ (? & ? & ?%H3) | [] ]; eauto.
  Qed.

  Section thm1.

    Hypothesis H1 : ∀ t s, T t s → T ⃰⋄R t s ∨ K t s ∧ ∀u, R u t → T u s.
    Hypothesis H4 : ∀s, (∀r, R r s → wfp T r) → bars K (gindy R (wfp T)) s.

    Section goubault_thm1_strong.

      Hypothesis H3 : ∀s, bars R (wfp T) s.

      Theorem goubault_thm1_strong : well_founded T.
      Proof.
        apply theorem7_strong with (2 := H4); auto.
        intro; apply condition1_a_z, condition1_b_a, lemma9; auto.
      Qed.

    End goubault_thm1_strong.

    (* Be carefull, the original proof of Dawson&Gore (thm7) implies Goubault (thm1)
       uses XM whereas this proof relies on stronger version of thm7 and does not
       use XM *)

    Section goubault_thm1_orig.

      Hypothesis H3 : well_founded R.

      Theorem goubault_thm1_orig : well_founded T.
      Proof.
        apply goubault_thm1_strong.
        intros s; generalize (H3 s).
        rewrite <- bars_iff_wfp.
        now apply bars_mono.
      Qed.

    End goubault_thm1_orig.

  End thm1.

End goubault.

Section ctxt.

  Variables (X : Type).

  Implicit Type (T : term X → term X → Prop) (t : term X).

  Definition imsubt r t := r ∈ sons t.

  Notation "⊲" := imsubt.

  Fact wf_imsubt : well_founded ⊲.
  Proof. intros t; induction t; constructor; trivial. Qed.

  Inductive ctxt1 T : term X → term X → Prop :=
    | ctxt1_intro f l r p q : T p q → ctxt1 T ⟨f|l++[p]++r⟩ₜ ⟨f|l++[q]++r⟩ₜ.

  Fact ctxt1_iff T r t : ctxt1 T r t ↔ oneup node (onerel T) r t.
  Proof.
    split.
    + induction 1; constructor.
      apply onerel_iff; exists l, p, q, r; auto.
    + induction 1 as [ f ? ? (l & p & q & r & -> & -> & ?)%onerel_iff]; now constructor.
  Qed.

  Fact ctxt1_inv T p q : 
      ctxt1 T p q 
    → ∃ f l r u v, p = ⟨f|l++[u]++r⟩ₜ ∧ q = ⟨f|l++[v]++r⟩ₜ ∧ T u v.
  Proof. destruct 1; do 5 eexists; eauto. Qed.

  Fact wfp_ctxt1 T f l : Forall (wfp T) l → wfp (ctxt1 T) ⟨f|l⟩ₜ.
  Proof.
    intros Hl.
    cut (wfp (oneup node (onerel T)) ⟨f|l⟩ₜ).
    + apply wfp_anti; intros ? ?; apply ctxt1_iff.
    + apply wfp_oneup.
      * now inversion 1.
      * now apply wfp_onerel.
  Qed.

  Section ctxt1_closed.

    Variables (T : _) (HT : ctxt1 T ⊆₂ T).

    Fact ctxt1_closed_subterm_comm : T⋄⊲ ⊆₂ ⊲⋄T.
    Proof.
      intros u [f m] (v & H1 & (l & r & E)%in_split); simpl in E; subst.
      exists (node f (l++[u]++r)); split.
      + red; simpl; eauto.
      + apply HT; now constructor.
    Qed.

    Fact ctxt1_closed_wfp_subterm r t : ⊲ ⃰ r t → wfp T t → wfp T r.
    Proof. apply wfp_commute_crt, ctxt1_closed_subterm_comm. Qed.

  End ctxt1_closed.

  Inductive ctxt T : term X → term X → Prop :=
    | ctxt_stop p q : T p q → ctxt T p q
    | ctxt_comp f l r p q : ctxt T p q → ctxt T ⟨f|l++[p]++r⟩ₜ ⟨f|l++[q]++r⟩ₜ
    .

  Fact ctxt_inv T p q : 
      ctxt T p q 
    → T p q ∨ ∃ f l r u v, p = ⟨f|l++[u]++r⟩ₜ ∧ q = ⟨f|l++[v]++r⟩ₜ ∧ ctxt T u v.
  Proof.
    destruct 1; eauto.
    right; do 5 eexists; eauto.
  Qed.

  Hint Constructors ctxt1 ctxt : core.

  Fact ctxt1__ctxt T : ctxt1 T ⊆₂ ctxt T.
  Proof. induction 1; eauto. Qed.

  Fact ctxt_mono T K : T ⊆₂ K → ctxt T ⊆₂ ctxt K.
  Proof. induction 2; auto. Qed.

  Fact ctxt_idem T : ctxt (ctxt T) ⊆₂ ctxt T.
  Proof. induction 1; auto. Qed.

  Definition pctxt T := ctxt (ctxt1 T).
  
  Fact pctxt__ctxt T : pctxt T ⊆₂ ctxt T.
  Proof.
    intros ? ? H; apply ctxt_idem.
    revert H; apply ctxt_mono, ctxt1__ctxt.
  Qed.

  (** Fails: g[] > g[g[]] as single reduction
      gives  g[] > g²[] > g³[] > ... as in the contextual closure 
  
  Fact wf_ctxt R : well_founded R → well_founded (ctxt R). *)
  
  Variables (sigma K' : term X → term X → Prop).

  Notation σ := sigma.
  Notation ρ := (ctxt σ).

  Local Fact rho_ctxt1_closed : ctxt1 ρ ⊆₂ ρ.
  Proof. induction 1; now constructor 2. Qed.

  Hint Resolve rho_ctxt1_closed : core.

  Fact rho_comp_imsubt : ρ⋄⊲ ⊆₂ ⊲⋄ρ.
  Proof. apply ctxt1_closed_subterm_comm, rho_ctxt1_closed. Qed.
  
  Hint Resolve wf_imsubt rho_comp_imsubt : core.

  Fact subterm_wfp_rho r t : ⊲ ⃰ r t → wfp ρ t → wfp ρ r.
  Proof. apply ctxt1_closed_wfp_subterm, rho_ctxt1_closed. Qed.

  Hint Resolve subterm_wfp_rho : core.
  
  Fact wfp_T_R_Rplus s : (∀r, ⊲ r s → wfp ρ r) ↔ (∀r, ⊲⁺ r s → wfp ρ r).
  Proof.
    split.
    + intros H r; rewrite clos_trans_inv_right.
      intros (? & ? & ?%H); eauto.
    + intros H ? ?; apply H; auto.
  Qed.

  Let Condition2z K U := ∀s, (∀r, ⊲⁺ r s → wfp ρ r) → ∀u, ⊲ ⃰⋄U u s → wfp ρ u ∨ K u s.

  Fact In_R r g l : r ∈ l → ⊲ r ⟨g|l⟩ₜ.
  Proof. intro H; exact H. Qed.

  Hint Resolve In_R : core.

  Definition SN1 := ctxt1 (λ t s, ρ t s ∧ wfp ρ s).
  
  Fact wf_SN1 : well_founded SN1.
  Proof.
    intros []; apply wfp_ctxt1, Forall_forall.
    intros ? _; apply wf_cap_wfp.
  Qed.

  Local Fact Condition2z_ctxt {K} : SN1 ⊆₂ K → Condition2z K σ → Condition2z K ρ.
  Proof.
    intros H2 H1 s Hs u (t & H3 & H4).
    revert H4 Hs u H3.
    destruct 1 as [ t s | g l r p q H ]; intros G u Hu; eauto.
    rewrite clos_refl_trans__clos_trans, clos_trans_inv_right in Hu.
    destruct Hu as [ -> | (v & Hv1 & Hv2) ].
    + right; apply H2; red; constructor; split; eauto.
      apply G; constructor 1; apply In_R; auto.
    + left; apply in_app_iff in Hv2 as [ Hv2 | [ <- | Hv2 ] ].
      * apply G; apply clos_rt_t with v; auto.
      * cut (wfp ρ p); [ | cut (wfp ρ q) ]; eauto.
        apply G; constructor 1; apply In_R; auto.
      * apply G; apply clos_rt_t with v; auto.
        constructor 1; apply In_R; auto.
  Qed.

  (** Source code of Jeremy Dawson https://users.cecs.anu.edu.au/~jeremy/isabelle/2005/snabs/ *)

  Theorem theorem11 K : Condition2z K sigma → SN1 ⊆₂ K → well_founded K → well_founded ρ.
  Proof.
    intros H1 H2 H3.
    apply theorem7 with (R := ⊲) (K := K).
    + intros s; apply condition1_b_a, condition1_d_b; split; auto.
      intros Hs.
      apply (Condition2z_ctxt H2 H1).
      now apply wfp_T_R_Rplus.
    + intros s; generalize (H3 s).
      rewrite <- bars_iff_wfp; now apply bars_mono.
    + intros s; generalize (wf_imsubt s).
      rewrite <- bars_iff_wfp; now apply bars_mono.
  Qed.

  Let K := K' ∪₂ SN1. 

  Definition Condition2a := ∀s, (∀r, ⊲⁺ r s → wfp ρ r) → ∀u, ⊲ ⃰⋄σ u s → wfp ρ u ∨ K u s.
  Definition Condition2a' := ∀s, (∀r, ⊲ r s → wfp ρ r) → ∀u, ⊲ ⃰⋄σ u s → wfp ρ u ∨ K u s.
  Definition Condition2b := ⊲ ⃰⋄sigma ⊆₂ (ρ∪₂⊲) ⃰⋄⊲ ∪₂ K'.

  Hint Constructors clos_refl_trans : core.

  Fact crt_rho_cup_imsubt : (ρ∪₂⊲) ⃰ ⊆₂ ⊲ ⃰⋄ρ ⃰.
  Proof. apply crt_xchg_cup, rho_comp_imsubt. Qed.
  
  Hint Resolve subterm_wfp_rho wfp_clos_rt : core.

  Fact Condition_2b_2a' : Condition2b → Condition2a'.
  Proof.
    intros H2b s Hs u Hu; unfold K.
    destruct (H2b _ _ Hu) as [ (w & (z & H3 & H5)%crt_rho_cup_imsubt & H4%Hs) | ]; eauto.
  Qed.

  Fact Condition_2a'_2a : Condition2a' → Condition2a.
  Proof.
    intros H2a' s Hs; apply H2a'.
    intros r Hr; apply Hs; auto.
  Qed.

End ctxt.

Arguments imsubt {_}.
Arguments ctxt {_}.
Arguments SN1 {_}.

Section constricting.

  Variables (X : Type) (sigma : term X → term X → Prop).
  
  Implicit Types (t : term X).

  Notation σ := sigma.
  Notation ρ := (ctxt σ).
  Notation "⊲" := imsubt.

  Definition constrict t s := σ t s ∧ Forall (wfp ρ) (sons s). 
  
  Definition thm13_rel1 := (⊲ ⃰⋄constrict)∪₂(SN1 σ).
  Definition thm13_rel2 := (SN1 σ) ⃰⋄⊲ ⃰⋄constrict.
  Definition thm13_rel3 := constrict⋄(SN1 σ) ⃰⋄⊲ ⃰.
  Definition thm13_rel4 := ⊲ ⃰⋄constrict⋄(SN1 σ) ⃰.
  Definition thm13_rel5 := ⊲ ⃰⋄ρ.
  Definition thm13_rel6 := ρ∪₂⊲.
  Definition thm13_rel6' := (ρ∪₂⊲)⁺.
  Definition thm13_rel7 := ρ.
  Definition thm13_rel8 := ρ⁺.
  Definition thm13_rel9 := ρ⁺∪₂⊲.
  
  (* strategy : 
       1 -> 7 using theorem 11 then
       7 -> 6 -> 6' -> all others
       
       1 -> 7 -> 6 -> 6' -> 1 
       
       2 -> 3 -> 4 
       1 -> 4 -> 1
       
   *)

  Theorem thm13_1_7 : well_founded thm13_rel1 → well_founded thm13_rel7.
  Proof.
    unfold thm13_rel1, thm13_rel7.
    intros H; red.
    apply theorem11 with (K := ⊲ ⃰⋄constrict ∪₂ (SN1 σ)); eauto.
    apply Condition_2a'_2a.
    red.
    intros [ f l ] Hl u (v & H1 & H2); simpl in Hl.
    right; left.
    exists v; repeat split; auto.
    simpl; now apply Forall_forall.
  Qed.

  Theorem thm13_7_6 : well_founded thm13_rel7 → well_founded thm13_rel6.
  Proof.
    unfold thm13_rel6, thm13_rel7.
    intros H t.
    apply lemma12c; eauto.
    + apply wf_imsubt.
    + intros ? ? (? & [])%(@rho_comp_imsubt _ sigma); eauto.
  Qed.

  Theorem thm13_6_6' : well_founded thm13_rel6 → well_founded thm13_rel6'.
  Proof. intros H x; generalize (H x); apply wfp_clos_t. Qed.

  Theorem thm14_1_4 : well_founded thm13_rel1 ↔ well_founded thm13_rel4.
  Proof.
    unfold thm13_rel1, thm13_rel4.
    apply forall_congr; intro x; symmetry.
    rewrite <- (lemma12b _ (⊲ ⃰⋄constrict) (SN1 σ)).
    + revert x; apply wfp_congr.
      apply rel_comp_assoc.
    + apply wf_SN1.
  Qed.

  Theorem thm14_5_6 : well_founded thm13_rel5 ↔ well_founded thm13_rel6.
  Proof.
    unfold thm13_rel5, thm13_rel6.
    rewrite lemma12a.
    apply forall_congr; intro x.
    apply lemma12b, wf_imsubt.
  Qed.

End constricting.
