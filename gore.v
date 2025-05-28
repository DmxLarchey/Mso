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

Notation "R ⃰" := (clos_refl_trans R) (at level 1, left associativity, format "R ⃰").
Notation "R ⁺" := (clos_trans R) (at level 1, left associativity, format "R ⁺").
Notation "R ⋄ T" := (λ x z, ∃y, R x y ∧ T y z) (at level 2, right associativity, format "R ⋄ T").

#[global] Notation "P '⊆₁' Q" := (∀x, P x → Q x) (at level 70, no associativity, format "P  ⊆₁  Q").
#[global] Notation "P '⊆₂' Q" := (∀ x y, P x y → Q x y) (at level 70, no associativity, format "P  ⊆₂  Q").

#[global] Notation "P '∪₂' Q" := (λ x y, P x y ∨ Q x y) (at level 50, left associativity, format "P ∪₂ Q").
#[global] Notation "P '∩₂' Q" := (λ x y, P x y ∧ Q x y) (at level 48, left associativity, format "P ∩₂ Q").
	
 
(*

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

*)

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

Fact wfp_clos_rt X T (x y : X) : T ⃰ x y → wfp T y → wfp T x.
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
  
  Hint Constructors clos_refl_trans gbars : core.
  Hint Resolve wfp_clos_rt : core.

  Section conditions.

    Variables (s : X).

    Definition condition1z := gindy K (gindy R (wfp T)) s.
    Definition condition1a := (∀r, R r s → wfp T r) → bars T (gbars R (λ r, K r s) (wfp T)) s.
    Definition condition1b := (∀r, R r s → wfp T r) → ∀t, T t s → gbars R (λ r, K r s) (wfp T) t.
    Definition condition1c := ∀t, T t s → gbars R (λ r, K r s) (λ v, T⋄R v s) t.
    Definition condition1c' := ∀t, T t s → gbars R (λ r, K r s) (λ v, T ⃰⋄R v s) t.
    Definition condition1d := (∀r, wfp R r) ∧ ((∀r, R r s → wfp T r) → ∀t, T t s → ∀r, R ⃰ r t → wfp T r ∨ K r s).
    Definition condition1e := (∀r, wfp R r) ∧ ∀ r t, T t s → R ⃰ r t → (T ⃰⋄R r s) ∨ K r s.
    
    (** Two chains (e) → (d) → (b) → (a) → (z)
                  (c) → (c') → (b) *)
                  
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
      intros Hs t Ht r Hr.
      destruct (H2 _ _ Ht Hr) as [ (? & []) | ]; eauto.
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

Section iter.

  Variables (X : Type) (f : X → X).

  Fixpoint iter x n :=
    match n with
    | 0   => x
    | S n => iter (f x) n
    end.

  Fact iter_add x n m : iter x (n+m) = iter (iter x n) m.
  Proof. induction n in x |- *; simpl; auto. Qed.

  Fact iter_S x n : iter x (S n) = f (iter x n).
  Proof.
    replace (S n) with (n+1) by lia.
    now rewrite iter_add.
  Qed.

End iter.

Arguments iter {_}.

Section power.

  Variables (X : Type).

  Implicit Types (R T : X → X → Prop).

  Definition power R := iter (fun X => R⋄X) eq.

  Fact power_comp R T n u v : (power R n)⋄T u v ↔ iter (fun X => R⋄X) T n u v.
  Proof.
    unfold power.
    revert R T u v; induction n as [ | n IHn ]; intros R T u v.
    + simpl; split; eauto; now intros (? & [] & ?).
    + rewrite !iter_S; split.
      * intros (y & (z & H1 & H2) & H3).
        exists z; split; auto; apply IHn; eauto.
      * intros (y & H1 & (z & H2 & H3)%IHn); eauto.
  Qed.

  Fact power_add R n m u v : power R (n+m) u v ↔ (power R m)⋄(power R n) u v.
  Proof. rewrite power_comp; unfold power; now rewrite iter_add. Qed.

  Fact power_zero R : power R 0 = eq.
  Proof. reflexivity. Qed.

  Fact power_one R u v : power R 1 u v ↔ R u v.
  Proof.
    split.
    + cbn; now intros (? & ? & <-).
    + now exists v.
  Qed.

  Fact power_S_r R n u v : power R (S n) u v ↔ (power R n)⋄R u v.
  Proof.
    change (S n) with (1+n).
    rewrite power_add.
    split; intros (y & H1 & H2).
    + rewrite power_one in H2; eauto.
    + rewrite <- power_one in H2; eauto.
  Qed.

  Fact power_S_l R n u v : power R (S n) u v ↔ R⋄(power R n) u v.
  Proof.
    replace (S n) with (n+1) by lia.
    rewrite power_add.
    split; intros (y & H1 & H2).
    + rewrite power_one in H1; eauto.
    + rewrite <- power_one in H1; eauto.
  Qed.

  Fact power_xchg_l R T n : T⋄R ⊆₂ R⋄T → (power T n)⋄R ⊆₂ R⋄(power T n).
  Proof.
    intros H.
    induction n as [ | n IHn ].
    + rewrite power_zero.
      intros ? ? (? & []); subst; eauto.
    + intros x y (z & (u & H1 & H2)%power_S_r & H3).
      destruct (H u y) as (k & H4 & H5); eauto.
      destruct (IHn x k) as (b & []); eauto.
      exists b; split; auto.
      apply power_S_r; eauto.
  Qed.

  Fact power_xchg_r R T n : T⋄R ⊆₂ R⋄T → T⋄(power R n) ⊆₂ (power R n)⋄T.
  Proof.
    intros H.
    induction n as [ | n IHn ].
    + rewrite power_zero.
      intros ? ? (? & []); subst; eauto.
    + intros x y (z & H1 & (u & H2 & H3)%power_S_l).
      destruct (H x u) as (k & H4 & H5); eauto.
      destruct (IHn k y) as (b & []); eauto.
      exists b; split; auto.
      apply power_S_l; eauto.
  Qed.

  Fact power_xchg R T n m : T⋄R ⊆₂ R⋄T → (power T m)⋄(power R n) ⊆₂ (power R n)⋄(power T m).
  Proof. intro; now apply power_xchg_l, power_xchg_r. Qed.

End power.

Arguments power {_}.

Hint Constructors clos_refl_trans : core.

Fact power_iff_crt X (R : X → X → Prop) u v : R ⃰ u v ↔ ∃n, power R n u v.
Proof.
  split.
  + induction 1 as [ u v H | u | u v w _ (n & H1) _ (m & H2) ].
    * exists 1; now apply power_one.
    * exists 0; now rewrite power_zero.
    * exists (m+n); rewrite power_add; eauto.
  + intros (n & Hn).
    induction n as [ | n IHn ] in u, v, Hn |- *.
    * rewrite power_zero in Hn; subst; auto.
    * apply power_S_l in Hn as (w & H1 & H2%IHn); eauto.
Qed.

Fact crt_xchg_l [X] [R T : X → X → Prop] : T⋄R ⊆₂ R⋄T → T ⃰⋄R ⊆₂ R⋄T ⃰.
Proof.
  intros H u w (v & (n & Hn)%power_iff_crt & H1).
  destruct power_xchg_l with (T := T) (R := R) (n := n) (x := u) (y := w)
    as (z & []); eauto.
  exists z; rewrite !power_iff_crt; eauto.
Qed.

Fact crt_xchg [X] [R T : X → X → Prop] : T⋄R ⊆₂ R⋄T → T ⃰⋄R ⃰ ⊆₂ R ⃰⋄T ⃰.
Proof.
  intros H u w (v & (n & Hn)%power_iff_crt & (m & Hm)%power_iff_crt).
  destruct power_xchg with (T := T) (R := R) (n := m) (m := n) (x := u) (y := w)
    as (z & []); eauto.
  exists z; rewrite !power_iff_crt; eauto.
Qed.

Fact crt_mono X (R T : X → X → Prop) : R ⊆₂ T → R ⃰ ⊆₂ T ⃰.
Proof. induction 2; eauto. Qed.

Fact crt_xchg_cup X (R T : X → X → Prop) : T⋄R ⊆₂ R⋄T → ∀ u v, (T ∪₂ R) ⃰ u v ↔ R ⃰⋄T ⃰ u v.
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

Section wfp_commute.

  Variables (X : Type) (R T : X → X → Prop)
            (HRT : T⋄R ⊆₂ R⋄T).

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

End wfp_commute.

Section occ_eq.

  Variables (X : Type) (x : X).

  Definition lsum := fold_right plus 0.

  Inductive occ_eq : term X → nat → Prop :=
    | occ_eq_stop l : occ_eq ⟨x|l⟩ₜ 1
    | occ_eq_next f l m : x ≠ f → Forall2 occ_eq l m → occ_eq ⟨f|l⟩ₜ (lsum m).
    
  Hint Constructors occ_eq : core.
    
  Definition occ_eq_inv t n (o : occ_eq t n) :
    match t with
    | ⟨f|l⟩ₜ => x = f ∧ n = 1 ∨ x ≠ f ∧ ∃m, Forall2 occ_eq l m ∧ n = lsum m
    end.
  Proof. destruct o; simpl; eauto. Qed.

  Fact occ_eq_iff f l n :
     occ_eq ⟨f|l⟩ₜ n ↔ x = f ∧ n = 1 ∨ x ≠ f ∧ ∃m, Forall2 occ_eq l m ∧ n = lsum m.
  Proof.
    split.
    + apply occ_eq_inv.
    + intros [ (<- & ->) | (? & m & ? & ->) ]; eauto.
  Qed.

End occ_eq.

Arguments occ_eq {X}.

(*

Section context.

  Variables (X : Type).
  
  Definition is_ctx {I} (t : term (I+X)) := ∀i, occ_eq (inl i) t 1.
  
  Fixpoint context_subst {I J} (s : I → term (J+X)) t : term (J+X) :=
    match t with
    | ⟨inl i|l⟩ₜ => s i
    | ⟨inr i|l⟩ₜ => ⟨inr i|map (context_subst s) l⟩ₜ
    end.

  Fact is_ctx_subst I J (s : I → term (J+X)) (t : term (I+X)) :
      ∀ (f : I → nat), (∀i, occ_eq (inl i) t (f i))
    → ∀ (g : I → J → nat), (∀i j, occ_eq (inl j) (s i) (g i j))
    → ∀ j, occ_eq (inl j) (context_subst s t) (sum i (f i * g i j)).
    is_ctx t → (∀i, is_ctx (s i)) → is_ctx (context_subst s t).
  Proof.
    intros H1 Hs; revert H1. 
    induction t as [ [ i | x ] l IH ]; intros Ht; simpl; auto.
    intros j.
    apply occ_eq_iff; right; split; [ easy | ].
    red in H1.
End context.

Check context_subst.
Definition ctx I X := { t : term (I+X) | forall i, occ t i = 1 }.

*)

Section ctxt.

  Variables (X : Type).

  Implicit Type (T : term X → term X → Prop) (t : term X).
  
  Inductive ctx : Type :=
    | ctx_hole : ctx
    | ctx_cont : X → list (term X) → ctx → list (term X) → ctx.
    
  Fixpoint ctx_subst C t :=
    match C with
    | ctx_hole => t
    | ctx_cont f l D r => ⟨f|l++[ctx_subst D t]++r⟩ₜ
    end.
    
  Fixpoint ctx_comp C D :=
    match C with
    | ctx_hole => D
    | ctx_cont f l C r => ctx_cont f l (ctx_comp C D) r
    end.
    
  Fact ctx_comp_subst C D t : ctx_subst (ctx_comp C D) t = ctx_subst C (ctx_subst D t).
  Proof. induction C; simpl; do 3 f_equal; auto. Qed.

  Inductive ctxt1 T : term X → term X → Prop :=
    | ctxt1_intro f l r p q : T p q → ctxt1 T ⟨f|l++[p]++r⟩ₜ ⟨f|l++[q]++r⟩ₜ.

  Fact ctxt1_inv T p q : 
      ctxt1 T p q 
    → ∃ f l r u v, p = ⟨f|l++[u]++r⟩ₜ ∧ q = ⟨f|l++[v]++r⟩ₜ ∧ T u v.
  Proof. destruct 1; do 5 eexists; eauto. Qed.

  Inductive ctx_pair (a b : term X) : term X → term X → Prop :=
    | ctx_pair_stop : ctx_pair a b a b
    | ctx_pair_comp f l r p q : ctx_pair a b p q → ctx_pair a b ⟨f|l++[p]++r⟩ₜ ⟨f|l++[q]++r⟩ₜ
    .

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
  
  Hint Constructors ctxt1 ctxt ctx_pair : core.
  
  Fact ctxt_iff T p q : ctxt T p q ↔ ∃c r s, p = ctx_subst c r ∧ q = ctx_subst c s ∧ T r s.
  Proof.
    split.
    + induction 1 as [ p q H | f l r p q H (c & a & b & -> & -> & ?) ].
      * exists ctx_hole, p, q; now simpl.
      * exists (ctx_cont f l c r), a, b; simpl; auto.
    + intros (c & a & b & -> & -> & H).
      induction c as [ | f l c IH r ]; simpl; auto; now constructor 2.
  Qed.

  Fact ctxt_iff_ctx_pair T p q : ctxt T p q ↔ ∃ a b, T a b ∧ ctx_pair a b p q.
  Proof.
    split.
    + induction 1 as [ p q H | f l r p q H (a & b & ? & ?) ].
      * exists p, q; auto.
      * exists a, b; eauto.
    + intros (a & b & H1 & H); revert H.
      induction 1; eauto.
  Qed.

  Definition pctxt T := ctxt (ctxt1 T).

  Fact ctxt1__ctxt T : ctxt1 T ⊆₂ ctxt T.
  Proof. induction 1; eauto. Qed.
  
  Fact ctxt_mono R T : R ⊆₂ T → ctxt R ⊆₂ ctxt T.
  Proof. induction 2; auto. Qed.
  
  Fact ctxt_idem T : ctxt (ctxt T) ⊆₂ ctxt T.
  Proof. induction 1; auto. Qed.
  
  Fact pctxt__ctxt T : pctxt T ⊆₂ ctxt T.
  Proof.
    intros ? ? H; apply ctxt_idem.
    revert H; apply ctxt_mono, ctxt1__ctxt.
  Qed.
  
  (** Fails: g[] > g[g[]] as single reduction
      gives  g[] > g²[] > g³[] > ... as in the contextual closure 
  
  Fact wf_ctxt R : well_founded R → well_founded (ctxt R). *)

  Definition root t := match t with node f _ => f end.
  Definition sons t := match t with node _ l => l end.
  
  Let R r t := r ∈ sons t.
  
  Local Fact Rwf : well_founded R.
  Proof. intros t; induction t; constructor; trivial. Qed.
  
  Variables (sigma K' : term X → term X → Prop).
  
  Let T := ctxt sigma.
  Let SN1 := ctxt1 (λ t s, T t s ∧ wfp T s).
  
  Fact T_comp_R : T⋄R ⊆₂ R⋄T.
  Proof.
    intros u [f m] (v & H1 & (l & r & E)%in_split); simpl in E; subst.
    exists (node f (l++[u]++r)); split.
    + red; simpl; eauto.
    + now constructor 2.
  Qed.
  
  Hint Resolve Rwf T_comp_R : core.
  
  Fact wfp_T_R_Rplus s : (∀r, R r s → wfp T r) ↔ (∀r, R⁺ r s → wfp T r).
  Proof.
    split.
    + intros H r; rewrite clos_trans_inv_right.
      intros (u & H1 & H2%H).
      revert H1 H2; apply wfp_commute_crt; auto.
    + intros H r Hr; apply H; auto.
  Qed.

  Definition Condition2a K := ∀s, (∀r, R⁺ r s → wfp T r) → ∀u, R ⃰⋄sigma u s → wfp T u ∨ K u s.
  
  Fact ctx_in_inv C u a :
      R u (ctx_subst C a)
    →  C = ctx_hole ∧ R u a
    ∨ (∃ f l D r, C = ctx_cont f l D r ∧ u = ctx_subst D a)
    ∨ (∃ f l m D r, C = ctx_cont f (l++[u]++m) D r)
    ∨ (∃ f l D m r, C = ctx_cont f l D (m++[u]++r)).
  Proof.
    destruct C as [ | f l D r ]; simpl; auto.
    unfold R; simpl.
    intros [ (l' & m & ->)%in_split | [ | (m & r' & ->)%in_split ] ]%in_app_iff; right.
    + right; left; exists f, l', m; eauto. 
    + left; exists f, l, D, r; auto.
    + right; right; exists f, l, D, m, r'; auto.
  Qed.

  Fact Rstar_ctx u a : R ⃰ u a → ∃C, a = ctx_subst C u.
  Proof.
    induction 1 as [ u [f m] H | u | u v a _ (D & ?) _ (C & ?) ].
    + apply in_split in H; simpl in H.
      destruct H as (l & r & ->).
      exists (ctx_cont f l ctx_hole r); auto.
    + exists ctx_hole; auto.
    + exists (ctx_comp C D); rewrite ctx_comp_subst; now subst.
  Qed.

  Fact ctx_Rstar_inv C u a :
      R ⃰ u (ctx_subst C a)
    → u = ctx_subst C a
    \/ (C = ctx_hole /\ ∃D, a = ctx_subst D u)
    \/ (∃ f l D r, C = ctx_cont f l D r ∧ u = ctx_subst D a)
    \/ (∃ f l E m D r, C = ctx_cont f (l++[ctx_subst E u]++m) D r)
    \/ (∃ f l D m E r, C = ctx_cont f l D (m++[ctx_subst E u]++r)).
  Proof.
    rewrite clos_refl_trans__clos_trans, clos_trans_inv_right.
    intros [ H | (v & Hv & Ha) ]; eauto; right.
    apply ctx_in_inv in Ha
      as [ (-> & Ha) 
       | [ (f & l & D & r & H1 & H2)
       | [ (f & l & m & D & r & H1)
       |   (f & l & D & m & r & H1) 
       ] ] ].
    + left; split; auto.
      apply Rstar_ctx; eauto.
    + right; left.
      exists f, l, D, r; split; auto.
      apply  Rstar_ctx in Hv as (E & HE).
      admit.
    + do 2 right; left.
      apply Rstar_ctx in Hv as (E & ->).
      exists f, l, E, m, D, r; auto.
    + do 3 right.
      apply Rstar_ctx in Hv as (E & ->).
      exists f, l, D, m, E, r; auto.
  Admitted.

  Fact Rstar_ctx_pair_inv s a b p q :
      R ⃰ s p
    → ctx_pair a b p q 
    → R ⃰ s a ∨ R⁺ s q
    ∨ ∃t, ctx_pair a b s t ∧ ctx_pair s t p q.
  Proof.
    intros H1 H2; revert H2 H1.
    induction 1 as [ | f l r p q H IH ]; auto.
    + rewrite clos_refl_trans__clos_trans,
              clos_trans_inv_right.
      intros [ -> | (k & H1 & H2) ].
      * do 2 right; exists ⟨f|l ++ [q] ++ r⟩ₜ; auto.
      * red in H2; simpl in H2.
        apply in_app_iff in H2 as [ H2 | [ <- | H2 ] ].
        - right; left; apply clos_rt_t with k; auto.
          constructor 1; red; simpl; auto.
        - apply IH in H1 as [ H1 | [ H1 | (t & H1 & H2) ] ]; auto.
          ++ right; left; constructor 2 with q; auto.
             constructor 1; red; simpl; auto.
          ++ do 2 right; eauto.
        - right; left; apply clos_rt_t with k; auto.
          constructor 1; red; simpl; auto.
  Qed.

  Fact ctx_pair_Rstart a b p q :
       ctx_pair a b p q
     → p = a /\ q = b
    \/ R⁺ a p /\ R⁺ b q.
  Proof.
    induction 1 as [ | f l r p q H [ (-> & ->) | [] ] ]; auto; right.
    + split; constructor 1; red; simpl; auto.
    + split; [ constructor 2 with p | constructor 2 with q ]; auto; constructor 1; red; simpl; auto.
  Qed.

  Theorem theorem11 K : Condition2a K → SN1 ⊆₂ K → well_founded K → ∀s, wfp T s.
  Proof.
    intros H1 H2 H3.
    apply theorem7 with (R := R) (K := K).
    + intros s; apply condition1_b_a, condition1_d_b; split; auto.
      rewrite wfp_T_R_Rplus; intros Hs.
      generalize (H1 _ Hs); intros H0.
      intros t (a & b & Hab & H)%ctxt_iff_ctx_pair u Hu.
      destruct Rstar_ctx_pair_inv with (1 := Hu) (2 := H)
        as [ G | [ G | (v & G1 & G2) ] ]; auto.
      * destruct ctx_pair_Rstart with (1 := H) as [ (<- & <-) | (G1 & G2) ]; eauto. 
        generalize (Hs _ G2).
        admit.
      * admit. 
      
      induction 1 as [ t s Ht | f l r t s Hts IH ]; eauto; intros u Hu.
      rewrite clos_refl_trans__clos_trans in Hu.
      destruct Hu as [ -> | Hu ].
      * right; apply H2; constructor; split; auto.
        apply Hs; constructor 1; red; simpl; auto.
      * apply clos_trans_inv_right in Hu as (v & Hv & Hu).
        apply in_app_iff in Hu as [ Hu | [ <- | Hu ] ].
        - left; apply (Hs u), clos_rt_t with v; auto.
          constructor; red; simpl; auto.
        - apply IH in Hv; eauto.
          ++ admit.
          ++ admit.
          ++ intros w Hw; apply Hs.
             constructor 2 with s; auto.
             constructor 1; red; simpl; eauto.
        - simpl in Hu. 
          left; apply (Hs u), clos_rt_t with v; auto.
          constructor; red; simpl; auto.
    + intros s; generalize (H3 s).
      rewrite <- bars_iff_wfp; now apply bars_mono.
    + intros s; generalize (Rwf s).
      rewrite <- bars_iff_wfp; now apply bars_mono.
  Admitted.
  
  Let K := K' ∪₂ SN1. 



  Definition Condition2a := ∀s, (∀r, R⁺ r s → wfp T r) → ∀u, R ⃰⋄sigma u s → wfp T u ∨ K u s.
  Definition Condition2a' := ∀s, (∀r, R r s → wfp T r) → ∀u, R ⃰⋄sigma u s → wfp T u ∨ K u s.
  Definition Condition2b := R ⃰⋄sigma ⊆₂ (T∪₂R) ⃰⋄R ∪₂ K'.

  Hint Constructors clos_refl_trans : core.

  Fact T_cup_R_star : (T ∪₂ R) ⃰ ⊆₂ R ⃰ ⋄T ⃰.
  Proof. apply crt_xchg_cup, T_comp_R. Qed.
  
  Fact Condition_2b_2a : Condition2b → Condition2a'.
  Proof.
    intros H2b s Hs u Hu; unfold K.
    destruct (H2b _ _ Hu) as [ (w & H3 & H4) | ]; auto.
    left.
    apply T_cup_R_star in H3 as (z & H3 & H5).
    assert (Hw : wfp T w).
    1: apply Hs; eauto.
    assert (Hz : wfp T z).
    1: revert H5 Hw; apply wfp_clos_rt.
    revert H3 Hz; apply wfp_commute_crt; auto.
  Qed.
  
  Fact Condition_2a'_2a : Condition2a' → Condition2a.
  Proof.
    intros H2a' s Hs; apply H2a'.
    intros r Hr; apply Hs; auto.
  Qed.
    
  
  Let SN := @Acc (term X).
  Let fwf R r t := R r t /\ SN R t. 

  Variables (R : term X → term X → Prop).

  Inductive sn1 : term X → term X → Prop :=
    | sn1_intro f l p q r : SN R q → ctxt R p q → sn1 ⟨f|l++[p]++r⟩ₜ ⟨f|l++[q]++r⟩ₜ.

  Definition sn2 := ctxt sn1.
  
  Fact sn1__sn2 r t : sn1 r t → sn2 r t.
  Proof. now constructor 1. Qed.
