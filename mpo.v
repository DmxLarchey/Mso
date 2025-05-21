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

Require Import utils acc perm_eq mso.

Set Implicit Arguments.

(* The proof displayed here is somewhat inspired from 
   the paper of JGL

   http://www.lsv.ens-cachan.fr/Publis/PAPERS/PDF/JGL-mfcs13.pdf *)

#[local] Reserved Notation "l ~ₜ m" (at level 70, no associativity, format "l  ~ₜ  m").
#[local] Reserved Notation "x ⊏ₜ y" (at level 70, no associativity, format "x  ⊏ₜ  y").
#[local] Reserved Notation "'⟨' x '|' l '⟩ₜ'" (at level 0, l at level 200, format "⟨ x | l ⟩ₜ").

Section multiset_path_ordering.

  Variables (X : Type).

  (** terms indexed with X are rose trees *)

  Unset Elimination Schemes.

  Inductive term := node : X → list term → term.

  Set Elimination Schemes.
  
  Notation "⟨ f | l ⟩ₜ" := (node f l).

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

  (* t(erm)perm are nested permutations on terms, ie one can permute
     sons, but sons themselves can be internaly permuted etc ... 
     so f[g[a,b],h] ~ₜ f[h,g[b,a]] for instance  *)
  Inductive tperm : term → term → Prop :=
    | tperm_intro f l m : perm_eq tperm l m
                        → ⟨f|l⟩ₜ ~ₜ ⟨f|m⟩ₜ
  where "s ~ₜ t" := (tperm s t).

  Hint Constructors tperm : core.

  Fact tperm_inv s t :
       s ~ₜ t
     → match s, t with
       | ⟨f|l⟩ₜ, ⟨g|m⟩ₜ => f = g ∧ perm_eq tperm l m
      end.
  Proof. destruct 1; eauto. Qed.

  Fact tperm_xchg {l k} : perm_eq tperm l k → ∃p, l ~ₚ p ∧ Forall2 tperm p k.
  Proof. apply perm_eq_xchg. Qed.

  (** tperm is an equivalence relation *)

  (* because of the nesting, we need relativized versions *)
  Hint Resolve perm_eq_refl_rel perm_eq_sym_rel perm_eq_trans_rel : core.

  Fact tperm_refl : reflexive tperm.
  Proof. intro t; induction t; eauto. Qed. 

  Fact tperm_sym : symmetric tperm.
  Proof. intro s; induction s; intros [] []%tperm_inv; subst; eauto. Qed.

  Fact tperm_trans : transitive tperm.
  Proof. intros r s; revert r; induction s; intros [] [] []%tperm_inv []%tperm_inv; subst; eauto. Qed.

  Hint Resolve tperm_refl tperm_sym tperm_trans : core.

  Section example.
  
    Variables (f g c d e : X).
    
    Let a := ⟨c|[]⟩ₜ.
    Let b := ⟨d|[]⟩ₜ.
    Let h := ⟨e|[]⟩ₜ.
    Let t1 := ⟨f|[⟨g|[a;b]⟩ₜ;h]⟩ₜ.
    Let t2 := ⟨f|[h;⟨g|[b;a]⟩ₜ]⟩ₜ.
    
    Local Fact tperm_example : t1 ~ₜ t2.
    Proof.
      constructor.
      constructor 1 with [⟨g|[b; a]⟩ₜ;h].
      2: apply Permutation_app_comm with (l := [_]) (l' := [_]).
      repeat constructor; auto.
      constructor 1 with [a;b].
      2: apply Permutation_app_comm with (l := [_]) (l' := [_]).
      repeat constructor; auto.
    Qed.

  End example.

  (** The multiset path ordering *)

  Variables (R : X → X → Prop).

  (* mpo containing mso mpo tperm is a nested form of mso *)
  Inductive mpo : term → term → Prop :=
    | mpo_in_lt s t g m :   t ∈ m
                          → s ⊏ₜ t
                          → s ⊏ₜ ⟨g|m⟩ₜ
    | mpo_in_eq s t g m :   t ∈ m
                          → s ~ₜ t
                          → s ⊏ₜ ⟨g|m⟩ₜ
    | mpo_lt f l g m :      (∀t, t ∈ l → t ⊏ₜ ⟨g|m⟩ₜ)
                          → R f g
                          → ⟨f|l⟩ₜ ⊏ₜ ⟨g|m⟩ₜ
    | mpo_eq l g m :        (∀t, t ∈ l → t ⊏ₜ ⟨g|m⟩ₜ)
                          → mso mpo tperm l m
                          → ⟨g|l⟩ₜ ⊏ₜ ⟨g|m⟩ₜ
  where "s ⊏ₜ t" := (mpo s t). 

  Hint Constructors mpo : core.

  Fact mpo_inv s t :
      mpo s t 
    → match s, t with
      | ⟨f|l⟩ₜ, ⟨g|m⟩ₜ =>
          (∃r, r ∈ m ∧ s ⊏ₜ r)
        ∨ (∃r, r ∈ m ∧ s ~ₜ r)
        ∨ (R f g ∧ ∀r, r ∈ l → r ⊏ₜ t)
        ∨ (f = g ∧ mso mpo tperm l m ∧ ∀r, r ∈ l → r ⊏ₜ t)
      end.
  Proof.
    destruct 1; eauto.
    1,2: destruct s; eauto.
    do 3 right; auto.
  Qed.

  Hint Resolve Permutation_in Permutation_sym : core.

  (** We first show that ~ₜ is a congruence for mpo.
      This involves nested inductions, hence the 
      relativized form of mso_perm_r *)

  (* This one was the hardest lemma to get right !!
      We need the relativized form of mso_perm_r *)
  Lemma mpo_tperm_right s t : s ~ₜ t → ∀r, r ⊏ₜ s → r ⊏ₜ t.
  Proof.
    (* By induction on s then r *)
    intros H r; revert s r t H.
    intro s; induction s as [ g l IHl ].
    intro r; induction r as [ f p IHp ].
    intros [ ? m ] (<- & Hlm)%tperm_inv.
    intros [ (r & H3 & H4) 
         | [ (r & H3 & H4)
         | [ (H3 & H4)
           | (<- & H3 & H4) ]
            ] ]%mpo_inv.
    + apply tperm_xchg in Hlm as (u & H5 & H6).
      destruct Forall2_In_inv with (1 := H6) (x := r) as (? & []); eauto.
    + apply tperm_xchg in Hlm as (u & H5 & H6).
      destruct Forall2_In_inv with (1 := H6) (x := r) as (? & []); eauto.
    + constructor 3; eauto.
    + constructor 4; eauto.
      (* We need a relativized form mso_perm_r_rel 
         than can be applied recursively *)
      revert H3; apply mso_perm_r_rel; eauto.
  Qed.

  (* This one follows as a consequence *)
  Lemma mpo_tperm_left r s t : r ~ₜ s → r ⊏ₜ t → s ⊏ₜ t.
  Proof.
    revert t r s.
    intro t; induction t as [ g m IHm ].
    intro r; induction r as [ f l IHl ].
    intros [ ? p ] (<- & Hlm)%tperm_inv.
    intros [ (r & H3 & H4) 
         | [ (r & H3 & H4)
         | [ (H3 & H4)
           | (<- & H3 & H4) ]
            ] ]%mpo_inv; eauto.
    + constructor 3; auto.
      apply perm_eq_sym in Hlm; auto.
      intros r Hr.
      destruct perm_eq_in_inv with (1 := Hlm) (2 := Hr) as (? & []); eauto.
    + constructor 4; eauto.
      * apply perm_eq_sym in Hlm; auto. 
        intros r Hr.
        destruct perm_eq_in_inv with (1 := Hlm) (2 := Hr) as (? & []); eauto.
      * revert H3; apply mso_perm_l; auto.
        apply mpo_tperm_right.
  Qed.

  (** Now we establish Accessibility by structural induction *)

  Local Corollary tperm_Acc_mpo s t : s ~ₜ t → Acc mpo t → Acc mpo s.
  Proof. intro; now apply Acc_lower_bounds, mpo_tperm_right. Qed.

  Hint Constructors lex2 : core.
  Hint Resolve Acc_inv tperm_Acc_mpo forall_Acc_mso mpo_tperm_right : core.

  (* node f l inherits Acc(essibility) from that of f and of l *)
  Local Lemma Acc_mpo_node : ∀ f l, Acc R f → Acc (mso mpo tperm) l → Acc mpo ⟨f|l⟩ₜ.
  Proof.
    (* We use Acc_lex2 induction for a straightforward proof
       The other essential property is of course 
          Acc (mso T) l ↔ ∀x, x ∈ l → Acc T x applied to T := mpo *)
    apply Acc_lex2; intros g m Hg Hm IH.
    rewrite Acc_mso_iff in Hm; eauto.
    constructor.
    intro s; induction s as [ f l IHl ].
    intros [ (? & [])
         | [ (? & [])
         | [ []
           | (<- & []) ] ] ]%mpo_inv; eauto.
    all: apply IH; eauto.
  Qed.

  Hint Resolve Acc_mpo_node : core.

  (* Hence if all nodes are Acc(essible) then so is the tree *)
  Lemma Acc_mpo_term_fall t : term_fall (Acc R) t → Acc mpo t.
  Proof. induction 1 using term_fall_ind; eauto. Qed.

  (** We conclude with the well-foundedness result *)

  Hypothesis R_wf : well_founded R.

  (* If R is well founded then all nodes are Acc(essible) *) 
  Local Fact term_fall_Acc_R t : term_fall (Acc R) t.
  Proof. induction t; apply term_fall_fix; auto. Qed.

  Hint Resolve term_fall_Acc_R Acc_mpo_term_fall : core.

  (* Hence MPO is well-founded *)
  Theorem mpo_wf : well_founded mpo.
  Proof. red; auto. Qed.

End multiset_path_ordering.

Check mpo_wf.

