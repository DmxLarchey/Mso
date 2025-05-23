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
  | cover_next : (∀y, T x y → cover T P y) → cover T P x.

Hint Constructors cover : core.

Inductive covers {X} (T : X → X → Prop) (Q P : X → Prop) x : Prop :=
  | covers_stop : Q x → P x → covers T Q P x
  | covers_next : Q x → (∀y, Q y → T x y → covers T Q P y) → covers T Q P x.

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

Definition gindy {X} (T : X → X → Prop) (P : X → Prop) x :=
  (∀y, T x y → P y) → P x.

Fact gindy_cover X T P x : gindy T (@cover X T P) x.
Proof. red; now constructor 2. Qed. 

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
