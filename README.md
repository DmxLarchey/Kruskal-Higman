```
(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)
```

# What is this library?

This library is an extension of [`Kruskal-AlmostFull`](https://github.com/DmxLarchey/Kruskal-AlmostFull).
It contains an detailed and expanded constructive/inductive proofs of:
- Higman's theorem for unary trees (according to the terminology of \[1\]);
- and as a consequence, [Higman's lemma](#Higman's lemma for lists).

The terminology and proof structure are largely inspired from Wim Veldman's \[1\] 
which is (IMHO) the reference pen-and-paper work of the matter.

\[1\]. [_An intuitionistic proof of Kruskal's theorem_](https://link.springer.com/article/10.1007/s00153-003-0207-x), Win Veldman, 2004

# Idea about the proof of Higman theorem for unary trees

We define _(decorated) unary trees_ and the (product) embedding between
those:
```coq
Variables (X Y : Type).

Inductive utree := ⟨ _ : X ⟩₀ | ⟨ _ : Y | _ : utree X Y ⟩₁.
  
Inductive utree_embed R T : utree X Y → utree X Y → Prop :=
  | utree_embed_leaf x₁ x₂ : R x₁ x₂ → ⟨x₁⟩₀ ≤ₑ ⟨x₂⟩₀
  | utree_embed_subt s y t : s ≤ₑ t → s ≤ₑ ⟨y|t⟩₁
  | utree_embed_root y₁ t₁ y₂ t₂ : T y₁ y₂ → t₁ ≤ₑ t₂ → ⟨y₁|t₁⟩₁ ≤ₑ ⟨y₂|t₂⟩₁
where "s ≤ₑ t" := (@utree_embed _ _ s t).
```

Higman's theorem for `utree X Y` is stated and proved as following:
```coq
Theorem af_utree_embed X Y (R : rel₂ X) (R : rel₂ Y) : af R → af T → af (utree_embed R T). 
```

The proof proceeds as following:
- first a lexicographic induction on the AF-complexity of `(af T,af R)`. How this is implemented
  here is a bit complicated because it is a downgrade for the case of a list `[af Rₙ;...;af R₁]`
  of almost ful predicates (see [``](theories/af/af_lex.v);
- this lexicographic can just be implemented as a nested induction when `n=2` for `utree X Y`;
- then apply the second constructor of `af` and one needs to prove `af (utree_embed R T)↑t` for
  any `t : utree X Y`;
- then proceed by structural induction on `t`. We consider only the more complicated case
  where `t = ⟨α|τ⟩₁` where `α : Y` and `τ : utree X Y`;
- then the following steps holds (see [`af/af_utree_embed_fun.v`](theories/af/af_utree_embed_fun.v):
  - `af (utree_embed R T)↑τ` (by induction on `t`)
  - hence `af R'` where `R' := R + T ⨉ (utree_embed R T)↑τ` (by Ramsey)
  - `af T↑α` (because `af T` holds)
  - hence `af (utree_embed R' T↑α)` (because `T↑α` is smaller than `T`)
- finally we transfer `af` through `af (utree_embed R' T↑α) → af (utree_embed R T)↑⟨α|τ⟩₁`
  using a [quasi-morphism](theories/af/af_quasi_morphism.v).

# Higman's lemma for lists

Using the isomorphism between `list X` and `utree unit X` (ie lists are just unary trees where
there is no information on the leaves).

```coq
Inductive list_embed {X Y} (R : X → Y → Prop) : list X → list Y → Prop :=
  | list_embed_nil :           [] ≤ₗ []
  | list_embed_head x l y m :  R x y  → l ≤ₗ m → x::l ≤ₗ y::m
  | list_embed_skip l y m :    l ≤ₗ m → l ≤ₗ y::m
where "l ≤ₗ m" := (list_embed R l m).

Theorem af_list_embed X (R : rel₂ X) : af R → af (list_embed R).
```

We derive Higman's lemma as [eg stated on Wikipedia](https://en.wikipedia.org/w/index.php?title=Higman%27s_lemma&oldid=841018000)
where the sub-list relation `≼` is abstracted by assuming its inductive rules. This allows the statement to be independent of
an external inductive definition:
```coq
Variables (X : Type) (≼ : rel₂ (list X))
          (_ : ∃ l, ∀x : X, x ∈ l) 
          (_ :                    [] ≼ [])
          (_ : ∀ x l m, l ≼ m → x::l ≼ x::m)
          (_ : ∀ x l m, l ≼ m →    l ≼ x::m).

Theorem Higman_lemma : ∀ f : nat → list X, ∃ i j, i < j ∧ fᵢ ≼ fⱼ.
```
