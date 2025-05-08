# The well-foundedness of the multiset ordering in Coq/Rocq

This is a [standalone Coq constructive proof](mso.v) of the [Dershowitz-Manna ordering](https://en.wikipedia.org/wiki/Dershowitz%E2%80%93Manna_ordering) theorem,
i.e. the well-foundedness of the multiset ordering. The proof follows the
[outline of Tobias Nipkow](http://www4.in.tum.de/~nipkow/misc/multiset.ps).

Stated in Coq, the main results looks like:
```coq
Notation "l ~ₚ m" := (Permutation l m).

Variables (X : Type) (< : X → X → Prop).

Inductive mso_step : list X → list X → Prop :=
    | mso_step_intro l m x r : (∀x, x ∈ l → x < y)
                             → l++m++r ⊏ l++[x]++r
    | mso_step_perm_l l m k  : l ~ₚ m 
                             → l ⊏ k 
                             → m ⊏ k
  where "l ⊏ m" := (mso_step l m).

Definition mso := (clos_trans mso_step).

Theorem Acc_mso_iff l : Acc mso l ↔ Forall (Acc R) l.

Corollary mso_wf : well_founded < → well_founded mso.
```

This code was developed and refactored several times (for better automation) by [Dominique Larchey-Wendling](https://www.loria.fr/~larchey). It it distributed under the [`MPL-2.0`](LICENSE) public  license. 
