(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

Require Import List Wellfounded Utf8.

Import ListNotations.

Set Implicit Arguments.

Fact Acc_lower_bounds X (R : X → X → Prop) x y : (∀u, R u x → R u y) → Acc R y → Acc R x.
Proof. intros ? []; constructor; eauto. Qed. 

Section lex2.

  (* A double Acc induction principle for the lexicographic product 
     This one is somewhat new compared to the above reference
     and allows for a clearer (even straightforward) proof 
     of Acc_mpo_node below *)

  Variables (X Y : Type) (R : X → X → Prop) (T : Y → Y → Prop).

  Unset Elimination Schemes.

  Inductive lex2 : X*Y → X*Y → Prop :=
    | lex2_left  x₁ x₂ y₁ y₂ : R x₁ x₂ → lex2 (x₁,y₁) (x₂,y₂)
    | lex2_right x y₁ y₂ :     T y₁ y₂ → lex2 (x,y₁) (x,y₂).

  Set Elimination Schemes.

  Hint Constructors lex2 : core.

  Fact lex2_inv p q :
      lex2 p q
    ↔ match p, q with
      | (x₁,y₁), (x₂,y₂) => R x₁ x₂ ∨ x₁ = x₂ ∧ T y₁ y₂
      end.
  Proof.
    split.
    + intros []; auto.
    + revert p q; intros [] [] [ | (<- & ?) ]; auto.
  Qed.

  Section Acc_lex2.

    (* When proving a property for pairs
       (x,y) s.t. Acc R x and Acc T y, we can
       assume that it already holds for (x',y')
       which are lex2-less as well as Acc(essible) *)

    Variables (P : X → Y → Prop)
              (HP : ∀ x₂ y₂, Acc R x₂
                           → Acc T y₂
                           → (∀ x₁ y₁, Acc R x₁
                                     → Acc T y₁
                                     → lex2 (x₁,y₁) (x₂,y₂)
                                     → P x₁ y₁) 
                           → P x₂ y₂).

    Hint Resolve Acc_inv Acc_intro : core.

    Theorem Acc_lex2 x y : Acc R x → Acc T y → P x y.
    Proof.
      intros Hx Hy; revert Hx y Hy.
      do 2 induction 1.
      apply HP; auto.
      intros ? ? ? ? [ | (<- & ?) ]%lex2_inv; auto.
    Qed.

  End Acc_lex2.

  Hypothesis (Rwf : well_founded R)
             (Twf : well_founded T).

  Theorem wf_lex2 : well_founded lex2.
  Proof.
    intros (x,y).
    generalize (Rwf x) (Twf y).
    revert x y; apply Acc_lex2.
    constructor; intros [] ?; auto. 
  Qed.

End lex2.

Section lex_list.

  Variables (X : Type) (R : X → X → Prop).

  Inductive lex_list : list X → list X → Prop :=
    | lex_list_lt x y l m : R x y → length l = length m → lex_list (x::l) (y::m)
    | lex_list_eq x l m : lex_list l m → lex_list (x::l) (x::m).

  Fact lex_list_length l m : lex_list l m → length l = length m.
  Proof. induction 1; simpl; f_equal; auto. Qed.

  Hint Resolve lex_list_length : core.
  Hint Constructors lex2 : core.
 
  Fact lex_list_inv l m :
      lex_list l m
    → match m with
      | []    => False
      | y::m' => ∃ x l', l = x::l' ∧ length l' = length m' ∧ lex2 R lex_list (x,l') (y,m')
      end.
  Proof. destruct 1 as [ x ? l | x l ]; exists x, l; auto. Qed.
  
  (* {0,1,2} with R :={(0,1),(2,2)}
     then Acc R = {0,1}
     hence [1;1] is composed of accessible elements only
     but [0;2] < [1;1] is not compose of accessible elements
     and indeed [0;2] < [0;2] is a loop
     so [1;1] is not Accessible *)

  (** Fail Acc_lex_list n : forall l, length l = n -> Forall (Acc R) l -> Acc lex_list l. *)
  
  Hypothesis (Rwf : well_founded R).

  Local Lemma Acc_lex_list_length n : ∀l, length l = n → Acc lex_list l.
  Proof.
    induction n as [ | n IHn ]; intros m Hm.
    + destruct m; [ | easy ]; constructor.
      now intros ? ?%lex_list_inv.
    + destruct m as [ | y m ]; [ easy | ].
      apply f_equal with (f := pred) in Hm; simpl in Hm.
      generalize (Rwf y) (IHn _ Hm); intros H1 H2.
      revert Hm; pattern y, m.
      revert y m H1 H2.
      apply Acc_lex2.
      constructor.
      intros ? (? & ? & ? & [])%lex_list_inv; subst; auto.
  Qed.

  Theorem wf_lex_list : well_founded lex_list.
  Proof. intros l; apply Acc_lex_list_length with (1 := eq_refl). Qed.

End lex_list.
     
    
    