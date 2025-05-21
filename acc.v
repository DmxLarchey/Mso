(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

Require Import Wellfounded Utf8.

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

End lex2.