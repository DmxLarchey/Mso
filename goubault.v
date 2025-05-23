(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

Require Import List Wellfounded Relations Utf8.

Import ListNotations.

Require Import utils mpo.


(*Arguments clos_refl_trans {_}.

#[global] Notation "R ⁻¹" := (λ x y, R y x) (at level 1, left associativity, format "R ⁻¹").
*)

Inductive cover {X} (T : X → X → Prop) (P : X → Prop) x : Prop :=
  | cover_stop : P x → cover T P x
  | cover_next : (∀y, T x y → cover T P y) → cover T P x.

Hint Constructors cover : core.

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

Hint Constructors Acc : core.

Fact cover_Acc_iff X T x : @Acc X T⁻¹ x ↔ cover T (λ _, False) x.
Proof. split; induction 1; now eauto. Qed.

Section Acc_morphism.

  Variables (X Y : Type) (R : X → X → Prop) (T : Y → Y → Prop)
            (f : Y → X → Prop)
            (Hf : ∀y, exists x, f y x)
            (HRT : ∀ y₁ y₂ x₁ x₂, f y₁ x₁ → f y₂ x₂ → T y₁ y₂ → R x₁ x₂).

  Lemma Acc_morphism x y : f y x → Acc R x → Acc T y.
  Proof.
    rewrite !cover_Acc_iff.
    apply cover_morphism; eauto.
  Qed.

End Acc_morphism.

Definition restr {X} (R : X → X → Prop) (P : X → Prop) (u v : sig P) :=
  R (proj1_sig u) (proj1_sig v).

Fact wf_restr X (R : X → X → Prop) (P : X → Prop) : 
  well_founded (restr R P) ↔ well_founded (λ x y, R x y ∧ P x).
Proof.
  split.
  + intros H x.
    constructor; intros y (_ & Hy).
    clear x.
    generalize (H (exist _ y Hy)).
    change y with (proj1_sig (exist P y Hy)) at 2.
    induction 1 as [ [ x Hx ] _ IH ].
    constructor; simpl.
    intros z (? & Hz).
    apply (IH (exist P z Hz)); auto.
  + intros H (x & Hx).
    generalize (H x).
    apply Acc_morphism with (f := fun u v => proj1_sig u = v); auto.
    * intros []; simpl; eauto.
    * intros [] [] ? ? ? ?; subst; simpl; auto.
Qed.

Fact wf_cap_Acc X (R : X → X → Prop) : well_founded (λ x y, R x y ∧ Acc R x).
Proof.
  constructor.
  intros y (H1 & H2).
  revert H2; apply Acc_incl; now intros ? ? [].
Qed.

Fact wf_restr_Acc X (R : X → X → Prop) : well_founded (restr R (Acc R)).
Proof. apply wf_restr, wf_cap_Acc. Qed.

(*
Definition cmpl {X} (P : X → Prop) t := ¬ P t.

Fact Acc_cover X T P :
    (∀ x, P x ∨ ¬ P x)
  → ∀x, Acc (λ x y : X, T y x ∧ P y) x → cover T (cmpl P) x.
Proof.
  intros HP.
  induction 1 as [ x _ IHx ].
  destruct (HP x) as [ Hx | Hx ].
  + constructor 2; eauto.
  + constructor 1; auto.
Qed.

Fact Acc_cover_cmpl X T P :
    (∀ x, P x ∨ ¬ P x)
  → ∀x, Acc (λ x y : X, T y x ∧ ¬ P y) x → cover T P x.
Proof.
  intros HP.
  induction 1 as [ x _ IHx ].
  destruct (HP x) as [ Hx | Hx ].
  + constructor 1; auto.
  + constructor 2; eauto.
Qed.

Fact cover_Acc_cmpl X T P x : cover T P x → Acc (λ x y : X, T y x ∧ ¬ P y) x. 
Proof. induction 1; constructor 1; [ easy | ]; intros ? []; eauto. Qed.

Fact cover_cmpl_Acc X T P x : cover T (cmpl P) x → Acc (λ x y : X, T y x ∧ P y) x. 
Proof. induction 1; constructor 1; [ easy | ]; intros ? []; eauto. Qed.
*)

Section goubault.

  Variables (X : Type) (R T K : X → X → Prop).
    (* R is |>, T is >, K is >> *)

  Notation SN := (Acc T⁻¹).

  Definition ovb (P : X → Prop) s := ∀u, R s u → P u.

  Let SNb s := ovb SN s → SN s.

  Fact SN_crt s t : clos_refl_trans T s t → SN s → SN t. 
  Proof. induction 1; eauto; intros []; eauto. Qed.

  Remark prop2 s : (∀t, T s t → SN t) → SN s.
  Proof. intros H; constructor 1; apply H. Qed.

  Section thm1.

    Hypothesis H1 : ∀ s t, T s t → (∃u, R s u ∧ clos_refl_trans T u t) ∨ K s t ∧ ∀u, R⁻¹ u t → T s u.
    Hypothesis H3 : well_founded R⁻¹.
    Hypothesis H4 : ∀s, ovb SN s → cover K SNb s.

    Theorem theorem1 s : SN s.
    Proof.
      induction s as [ s IHs ] using (well_founded_induction H3).
      cut (SNb s).
      1: intros H; apply H; now red. 
      apply H4 in IHs.
      revert IHs; clear H4.
      induction 1 as [ s H | s _ IH ]; eauto.
      intros Hs.
      constructor; intros t.
      induction t as [ t IHt ] using (well_founded_induction H3).
      intros [ (u & G1 & G2) | (G1 & G2) ]%H1.
      + generalize (Hs _ G1); apply SN_crt; auto.
      + apply IH; auto; red; auto.
    Qed.

  End thm1.

  Hypothesis xm : ∀P, P ∨ ¬ P.

  Fact remark6 :
      well_founded (λ x y, K y x ∧ ovb SN x)
    → ∀s, cover K SNb s.
  Proof.
    intros H s.
    induction s as [ s IHs ] using (well_founded_induction H).
    constructor 2.
    intros y Hy.
    destruct (xm (ovb SN y)); eauto.
    constructor 1; red; tauto.
  Qed.

End goubault.

Arguments ovb {_}.

Section ferreira_zantema.

  Hypothesis xm : ∀P, P ∨ ¬ P.

  Variables (X : Type) (T K : term X → term X → Prop) (Ttrans : transitive T).

  Implicit Types (s t : term X) (T : term X → term X → Prop) (P : term X → Prop).

  Let R t s := s ∈ sons t.

  Fact HR : well_founded R⁻¹.
  Proof.
    intros s.
    induction s as [ f l IH ].
    constructor; unfold R; simpl; auto.
  Qed. 

  Hypothesis lifting : ∀P, well_founded (λ x y, T y x ∧ P x) → well_founded (λ x y, K y x ∧ ovb R P x).
  Hypothesis HT : ∀ s t, R s t → T s t.
  Hypothesis H1 : ∀ s t, T s t → (∃r, r ∈ sons s ∧ clos_refl_trans T r t) ∨ K s t.

  Hint Resolve HR : core.

  Theorem ferreira_zantema : well_founded T⁻¹.
  Proof.
    red; apply theorem1 with (R := R) (K := K); auto.
    + intros s t Hst. 
      destruct (H1 _ _ Hst) as [ | G ]; auto; right; split; auto.
      intros u Hu%HT.
      revert Hst Hu; apply Ttrans.
    + specialize (lifting (Acc T⁻¹) (wf_cap_Acc _ _)).
      intros s _; revert lifting s.
      apply remark6, xm.
  Qed.

End ferreira_zantema.





  





