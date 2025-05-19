# The well-foundedness of the multiset ordering in Coq/Rocq

This is a [standalone Coq constructive proof](mso.v) of the [Dershowitz-Manna ordering](https://en.wikipedia.org/wiki/Dershowitz%E2%80%93Manna_ordering) theorem,
i.e. the well-foundedness of the multiset ordering. The proof follows the
[outline of Tobias Nipkow](papers/multiset.pdf).

Multisets are viewed as list identified under permutations (ie a setoid). Stated in Coq, the main results looks like:
```coq
Notation "x ∈ l" := (In x l).
Notation "l ~ₚ m" := (Permutation l m).

Variables (X : Type) (< : X → X → Prop).

Inductive mso_step : list X → list X → Prop :=
  | mso_step_intro l m x r : (∀y, y ∈ m → y < x)
                           → l++m++r ⊏ l++[x]++r
  | mso_step_perm_l l m k  : l ~ₚ m 
                           → l ⊏ k 
                           → m ⊏ k
where "l ⊏ m" := (mso_step l m).

Definition mso := (clos_trans mso_step).

Infix "⊏⁺" := mso.

Theorem Acc_mso_iff l : Acc ⊏⁺ l ↔ ∀x, x ∈ l → Acc R x.

Corollary mso_wf : well_founded < → well_founded ⊏⁺.
```

Others result are proved for `mso`/`⊏⁺`, such as:
```coq
∀ x l, (∀y, y ∈ l → y < x) → l ⊏⁺ [x]    (* basic replacement by finitely many lesser values *)
∀ x y, y < x → [y] ⊏⁺ [x]                (* particular case where l = [y] *)
∀ l r u v, u ⊏⁺ v → l++u++r ⊏⁺ l++v++r   (* contextual closure *)
∀ l m p, l ⊏⁺ m → m ⊏⁺ p → l ⊏⁺ p        (* transitivity *)
∀ l m k, l ~ₚ m → l ⊏⁺ k → m ⊏⁺ k        (* closure under left permutations *)
∀ l m k, l ~ₚ m → k ⊏⁺ l → k ⊏⁺ m        (* closure under right permutations *)
∀ l m r, m ⊏⁺ r → m ⊏⁺ l++r              (* closure under right l-expansion *)
∀ l m r, m ⊏⁺ l → m ⊏⁺ l++r              (* closure under right r-expansion *)
∀ l, ¬ l ⊏⁺ []                           (* the empty list is the smallest *)
∀ x l, l ⊏⁺ x::l                         (* discarding the head *)                      
```

# The multiset path ordering in Coq/Rocq

We use the theorem `Acc_mso_iff` to establish the well-foundedness of the multiset path ordering `mpo`, a nested form of `mso` above.
The proof we implement is somewhat inspired, but arguably also simplified, from the proof given by Jean Goubault-Larecq in 
[_A Constructive Proof of the Topological Kruskal Theorem_](http://www.lsv.ens-cachan.fr/Publis/PAPERS/PDF/JGL-mfcs13.pdf).

The `mpo` is inductively defined on rose trees as:
```coq
Variables (X : Type) (R : X → X → Prop).

Inductive term := node : X → list term → term.

Inductive mpo : term → term → Prop :=
  | mpo_in_lt s f t l : t ∈ l
                      → mpo s t
                      → mpo s (node f l)
  | mpo_in_eq t g m :   t ∈ m
                      → mpo t (node g m)
  | mpo_lt f l g m :    (∀r, r ∈ l → mpo r (node g m))
                      → R f g
                      → mpo (node f l) (node g m)
  | mpo_eq l g m :      (∀r, r ∈ l → mpo r (node g m))
                      → mso mpo l m
                      → mpo (node g l) (node g m)
  .

Theorem mpo_wf : well_founded R → well_founded mpo.
```

# Who wrote the code

This code was developed and refactored several times (for better automation) by [Dominique Larchey-Wendling](https://www.loria.fr/~larchey). It it distributed under the [`MPL-2.0`](LICENSE) public  license. 
