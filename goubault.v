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

Hint Constructors cover Acc : core.

Fact cover_Acc_iff X T x : @Acc X T⁻¹ x ↔ cover T (λ _, False) x.
Proof. split; induction 1; now eauto. Qed.

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

Section goubault.

  Variables (X : Type) (R T K : X → X → Prop).
    (* R is |>, T is >, K is >> *)

  Notation SN := (Acc T⁻¹).

  Fact Acc_SN x : Acc (λ x y, T y x ∧ SN x ∧ SN y) x.
  Proof.
    constructor.
    intros y (H1 & _ & [H]).
    generalize (H _ H1).
    apply Acc_incl.
    now intros ? ? [].
  Qed.

(*
  Fact cover_SN x : cover T (cmpl SN) x.
  Proof.
    constructor 2.
 *)

  Definition ovb (P : X → Prop) s := ∀u, R s u → P u.

  Let SNb s := ovb SN s → SN s.

  Section thm1.

  Hypothesis H1 : ∀ s t, T s t → (∃u, R s u ∧ clos_refl_trans T u t) ∨ K s t ∧ ∀u, R⁻¹ u t → T s u.
  Hypothesis H3 : well_founded R⁻¹.
  Hypothesis H4 : ∀s, ovb SN s → cover K SNb s.

  Fact SN_crt s t : clos_refl_trans T s t → SN s → SN t. 
  Proof.
    induction 1; eauto.
    intros []; eauto.
  Qed.

  Remark prop2 s : (∀t, T s t → SN t) → SN s.
  Proof. intros H; constructor 1; apply H. Qed.

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

  (** Ca n'a pas l'air de marcher !! *)

  Hypothesis xm : forall P, P \/ ~ P.

  Fact remark6 : 
      (∀s, ovb SN s → Acc (λ x y, K y x ∧ ¬ ovb SN y) s)
    → (∀s, ovb SN s → cover K SNb s).
  Proof.
    intros H s Hs.
    generalize (H _ Hs).
    clear Hs.
    induction 1 as [ s Hs IHs ].
    constructor 2.
    intros t Ht.
    destruct (xm (ovb SN t)); eauto.
    + apply IHs; split; auto.
      intros C.
  Admitted.

End goubault.

Arguments ovb {_}.

Section ferreira_zantema.

  Variables (X : Type) (T K : term X → term X → Prop) (Ttrans : transitive T).

  Implicit Types (s t : term X) (T : term X → term X → Prop) (P : term X → Prop).

  Let R t s := s ∈ sons t.

  Fact HR : well_founded R⁻¹.
  Proof.
    intros s.
    induction s as [ f l IH ].
    constructor; unfold R; simpl; auto.
  Qed. 

  Hypothesis lifting : ∀P, (∀t, Acc (λ x y, T y x ∧ P x ∧ P y) t) → (∀t, Acc (λ x y, K y x ∧ ovb R P x ∧ ovb R P y) t).
  Hypothesis HT : ∀ s t, R s t → T s t.
  Hypothesis H1 : ∀ s t, T s t → (exists r, r ∈ sons s /\ clos_refl_trans T r t) \/ K s t.

  Hint Resolve HR : core.

  Theorem ferreira_zantema : well_founded T⁻¹.
  Proof.
    red; apply theorem1 with (R := R) (K := K); auto.
    + intros s t Hst. 
      destruct (H1 _ _ Hst) as [ | G ]; auto; right; split; auto.
      intros u Hu%HT.
      revert Hst Hu; apply Ttrans.
    + intros s Hs.
      change (ovb R (Acc T⁻¹) s) in Hs.
      change (cover K (λ x, ovb R (Acc T⁻¹) x → Acc T⁻¹ x) s).
      apply Acc_cover_cmpl.
      1: admit.
      revert Hs.
      generalize (lifting (Acc T⁻¹) (Acc_SN _ _) s).
      induction 1 as [ s _ IHs ]; intros Hs.
      constructor.
      intros t Ht; apply IHs; auto.
 
      destruct t as [ f l ]; unfold R; simpl.
  Admitted.

End ferreira_zantema.





  





