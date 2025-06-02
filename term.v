(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

Require Import List Wellfounded Relations Permutation Utf8.
Import ListNotations.

Require Import utils.

Set Implicit Arguments.

#[global] Reserved Notation "'⟨' x '|' l '⟩ₜ'" (at level 0, l at level 200, format "⟨ x | l ⟩ₜ").

Section terms.

  Variables (X : Type).

  (** terms indexed with X are rose trees *)

  Unset Elimination Schemes.

  Inductive term := node : X → list term → term.

  Set Elimination Schemes.
  
  Notation "⟨ f | l ⟩ₜ" := (node f l).

  Definition root t := match t with ⟨f|_⟩ₜ => f end.
  Definition sons t := match t with ⟨_|l⟩ₜ => l end.

  Section term_ind.

    (* Induction principle for rose trees *)

    Variables (P : term → Prop)
              (HP : ∀ f l, (∀t, t ∈ l → P t) → P ⟨f|l⟩ₜ).
    
    Fixpoint term_ind t : P t.
    Proof.
      destruct t as [ f l ].
      apply HP.
      clear f HP.
      induction l as [ | s l IH ].
      + intros ? [].
      + intros t [ <- | ].
        * apply term_ind.
        * now apply IH.
    Qed.

  End term_ind.

  Section term_fall.

    (* Finitary conjunction of a property over the
       nodes of a rose tree *)

    Variables (P : X → Prop).

    Fixpoint term_fall t :=
      match t with
      | ⟨f|l⟩ₜ => P f ∧ fold_right (λ p, and (term_fall p)) True l
      end.

    Fact term_fall_fix f l : term_fall ⟨f|l⟩ₜ ↔ P f ∧ ∀t, t ∈ l → term_fall t.
    Proof. rewrite <- fold_right_conj; easy. Qed.

    (* And its associated induction principle *)

    Section term_fall_ind.

      Variables (Q : term → Prop)
                (HQ : ∀ f l, P f
                           → (∀t, t ∈ l → term_fall t)
                           → (∀t, t ∈ l → Q t)
                           → Q ⟨f|l⟩ₜ).

      Fact term_fall_ind t : term_fall t → Q t.
      Proof. induction t; intros []%term_fall_fix; apply HQ; eauto. Qed.

    End term_fall_ind.

  End term_fall.

End terms.

Arguments node {_}.
Arguments root {_}.
Arguments sons {_}.

#[global] Notation "⟨ f | l ⟩ₜ" := (node f l).

