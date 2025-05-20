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

Require Import mso.

Set Implicit Arguments.

(* The proof displayed here is somewhat inspired from 
   the paper of JGL

   http://www.lsv.ens-cachan.fr/Publis/PAPERS/PDF/JGL-mfcs13.pdf *)

#[local] Notation "x ∈ l" := (In x l) (at level 70, no associativity, format "x  ∈  l").
#[local] Notation "l ~ₚ m" := (@Permutation _ l m) (at level 70, no associativity, format "l  ~ₚ  m").
#[local] Reserved Notation "l ~ₜ m" (at level 70, no associativity, format "l  ~ₜ  m").
#[local] Notation "R ⁻¹" := (λ x y, R y x) (at level 1, left associativity, format "R ⁻¹").

Section lex2.

  (* An accessibility principle for the lexicographic product 
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

    Hint Resolve Acc_inv : core.

    Theorem Acc_lex2 x y : Acc R x → Acc T y → P x y.
    Proof.
      intros Hx Hy; revert Hx y Hy.
      do 2 induction 1.
      apply HP.
      1,2: constructor; auto.
      intros ? ? ? ? [ | (<- & ?) ]%lex2_inv; auto.
    Qed.

  End Acc_lex2.

End lex2.

Fact fold_right_conj X (P : X → Prop) l :
  fold_right (λ x, and (P x)) True l ↔ ∀x, x ∈ l → P x.
Proof.
  rewrite <- Forall_forall.
  induction l; simpl.
  + split; constructor.
  + now rewrite Forall_cons_iff, IHl.
Qed.

Section multiset_path_ordering.

  Variables (X : Type).

  (** terms indexed with X are rose trees *)

  Unset Elimination Schemes.

  Inductive term := node : X → list term → term.

  Set Elimination Schemes.

  Section term_ind.

    (* Induction principle for rose trees *)

    Variables (P : term → Prop)
              (HP : ∀ f l, (∀t, t ∈ l → P t) → P (node f l)).
    
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
      | node f l => P f ∧ fold_right (λ p, and (term_fall p)) True l
      end.

    Fact term_fall_fix f l : term_fall (node f l) ↔ P f ∧ ∀t, t ∈ l → term_fall t.
    Proof. rewrite <- fold_right_conj; easy. Qed.

    (* And its associated induction principle *)

    Section term_fall_ind.

      Variables (Q : term → Prop)
                (HQ : ∀ f l, P f
                           → (∀t, t ∈ l → term_fall t)
                           → (∀t, t ∈ l → Q t)
                           → Q (node f l)).

      Fact term_fall_ind t : term_fall t → Q t.
      Proof. induction t; intros []%term_fall_fix; apply HQ; eauto. Qed.

    End term_fall_ind.

  End term_fall.

  (* t(erm)perm is nested permutations on the term, ie we can permute
     sons, but sons themselves can be internally permuted etc ... 
     so f[x[a,b],y] ~ₜ f[y,x[b,a]] for instance  *)
  Inductive tperm : term → term → Prop :=
    | tperm_intro f l m : perm_eq tperm l m
                        → tperm (node f l) (node f m).

  Hint Constructors tperm : core.

  Infix "~ₜ" := tperm.

  Fact tperm_inv s t :
       s ~ₜ t
     → match s, t with
       | node f l, node g m =>
          f = g ∧ perm_eq tperm l m
      end.
  Proof. destruct 1; eauto. Qed.

  Hint Resolve perm_eq_refl perm_eq_sym perm_eq_trans : core.

  Fact tperm_xchg {l m k} :
      Forall2 tperm l m
    → m ~ₚ k 
    → ∃p, l ~ₚ p 
        ∧ Forall2 tperm p k.
  Proof. apply Forall2_perm_xchg. Qed.

  (* tperm is an equivalence relation *)

  Fact tperm_refl t : t ~ₜ t.
  Proof. induction t; eauto. Qed. 

  Fact tperm_sym s t : s ~ₜ t → t ~ₜ s.
  Proof. revert t; induction s; intros [] []%tperm_inv; subst; eauto. Qed.

  Fact tperm_trans r s t : r ~ₜ s → s ~ₜ t → r ~ₜ t.
  Proof. revert r t; induction s; intros [] [] []%tperm_inv []%tperm_inv; subst; eauto. Qed.

  Hint Resolve tperm_refl tperm_sym tperm_trans : core.

  (** The multiset path ordering *)

  Variables (R : X → X → Prop).

  (* mpo is is a nested form of mso *)
  Inductive mpo : term → term → Prop :=
    | mpo_in_lt s t g m :   t ∈ m
                          → mpo s t
                          → mpo s (node g m)
    | mpo_in_eq s t g m :   t ∈ m
                          → s ~ₜ t
                          → mpo s (node g m)
    | mpo_lt f l g m :      (∀r, r ∈ l → mpo r (node g m))
                          → R f g
                          → mpo (node f l) (node g m)
    | mpo_eq l g m :        (∀r, r ∈ l → mpo r (node g m))
                          → mso mpo l m
                          → mpo (node g l) (node g m).

  Fact mpo_inv s t :
      mpo s t 
    → match s, t with
      | node f l, node g m =>
          (∃r, r ∈ m ∧ mpo s r)
        ∨ (∃r, r ∈ m ∧ s ~ₜ r)
        ∨ (R f g ∧ ∀r, r ∈ l → mpo r (node g m))
        ∨ (f = g ∧ mso mpo l m ∧ ∀r, r ∈ l → mpo r (node g m))
      end.
  Proof.
    destruct 1; eauto.
    + destruct s; eauto.
    + destruct s; eauto.
    + do 3 right; auto.
  Qed.

  Hint Constructors tperm : core.

  Fact tperm_mpo_right r s t : s ~ₜ t → mpo r s → mpo r t.
  Proof.
    revert r t.
    induction s as [ g l IHs ];
    induction r as [ f p IHr ].
    intros [ h m ].
    intros (<- & k & H1 & H2)%tperm_inv.
    intros [ (r & H3 & H4) 
         | [ (r & H3 & H4)
         | [ (H3 & H4)
           | (<- & H3 & H4) ]
            ] ]%mpo_inv.
    + destruct (tperm_xchg H1 H2) as (u & H5 & H6).
      destruct Forall2_In_inv
        with (1 := H6) (x := r)
        as (v & H7 & H8); eauto.
      constructor 1 with v; eauto.
    + destruct (tperm_xchg H1 H2) as (u & H5 & H6).
      destruct Forall2_In_inv
        with (1 := H6) (x := r)
        as (v & H7 & H8); eauto.
      constructor 2 with v; eauto.
    + constructor 3; eauto.
    + constructor 4; eauto.
      apply mso_perm_r with (1 := H2).
      revert H3.
      assert (forall x y z, x ∈ p → y ∈ l → z ∈ k → y ~ₜ z → mpo x y → mpo x z).
      1: eauto. intros ? ? ? ? ? ?; apply IHs.
  Admitted.

  Fact tperm_Acc_mpo s t : s ~ₜ t → Acc mpo s → Acc mpo t.
  Proof.
    intros H1 H2; revert H2 t H1.
    induction 1 as [ s _ IHs ]; intros t Hst.
    constructor.
    intros r Hr.
    generalize (tperm_mpo_right (tperm_sym Hst) Hr); eauto.
  Qed.

  Hint Constructors lex2 : core.
  Hint Resolve Acc_inv forall_Acc_mso : core.

  (* node f l inherits Acc(essibility) from that of f and of l *)
  Local Lemma Acc_mpo_node : ∀ f l, Acc R f → Acc (mso mpo) l → Acc mpo (node f l).
  Proof.
    (* We use Acc_lex2 induction for a straightforward proof 
       The other essential property of of course 
          Acc (mso T) l ↔ ∀x, x ∈ l → Acc T x applied to T := mpo *)
    apply Acc_lex2; intros g m Hg Hm IH.
    rewrite Acc_mso_iff in Hm.
    constructor; intros s.
    induction s as [ f l IHl ].
    intros [ (? & [])
         | [ (? & [])
         | [ []
           | (<- & []) ] ] ]%mpo_inv; eauto.
    + admit.
    + apply IH; eauto.
  Qed.

  Hint Resolve Acc_mpo_node : core.

  (* Hence if all nodes are Acc(essible) then so is the tree *)
  Lemma Acc_mpo_term_fall : ∀t, term_fall (Acc R) t → Acc mpo t.
  Proof. apply term_fall_ind; auto. Qed.

  Hypothesis R_wf : well_founded R.

  (* If R is well founded then all nodes are Acc(essible) *) 
  Local Fact term_fall_Acc_R t : term_fall (Acc R) t.
  Proof. induction t; apply term_fall_fix; auto. Qed.

  Hint Resolve term_fall_Acc_R Acc_mpo_term_fall : core.

  (* Hence MPO is well-founded *)
  Theorem mpo_wf : well_founded mpo.
  Proof. red; auto. Qed.

End multiset_path_ordering.

