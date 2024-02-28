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

# The proof of Higman theorem for unary trees (sketch)

We define _(decorated) unary trees_ and the _(product) embedding_ between those:
```coq
Inductive utree X Y := ⟨ _ : X ⟩₀ | ⟨ _ : Y | _ : utree X Y ⟩₁.
  
Inductive utree_embed {X Y} R T : utree X Y → utree X Y → Prop :=
  | utree_embed_leaf x₁ x₂ : R x₁ x₂ → ⟨x₁⟩₀ ≤ₑ ⟨x₂⟩₀
  | utree_embed_subt s y t : s ≤ₑ t → s ≤ₑ ⟨y|t⟩₁
  | utree_embed_root y₁ t₁ y₂ t₂ : T y₁ y₂ → t₁ ≤ₑ t₂ → ⟨y₁|t₁⟩₁ ≤ₑ ⟨y₂|t₂⟩₁
where "s ≤ₑ t" := (utree_embed _ _ s t).
```

Higman's theorem for `utree X Y` is [stated and proved](heories/af/af_utree_embed.v) as following:
```coq
Theorem af_utree_embed X Y (R : rel₂ X) (T : rel₂ Y) : af R → af T → af (utree_embed R T). 
```

The proof proceeds as following (sketch):
1. first a lexicographic induction on a kind of _measure of the AF-complexity_ of `(af T,af R)`. 
   How this is implemented here is a bit complicated because it is a downgrade for 
   the case of a list `[af Rₙ;...;af R₁]` of almost full predicates ordered using the
   _easier ordering of \[1\]_ (see [`af/af_lex.v`](theories/af/af_lex.v));
    - alternatively for `utree X Y` where `n=2`, this lexicographic ordering could
      just be implemented by nested induction, first on `af T`, then on `af R`;
3. apply the second constructor of `af`. One needs to prove `af (utree_embed R T)↑t` for
   any `t : utree X Y`. We proceed by structural induction on `t`. 
    - here we consider only the more complicated case where `t = ⟨α|τ⟩₁` where `α : Y` and `τ : utree X Y`;
5. the following propositions hold (see [`af/af_utree_embed_fun.v`](theories/af/af_utree_embed_fun.v)):
    - `af (utree_embed R T)↑τ` (by induction on `t`)
    - hence `af R'` where `R' := R + T ⨉ (utree_embed R T)↑τ` (by Coquand's [`af_product,af_sum`](https://github.com/DmxLarchey/Kruskal-AlmostFull/blob/main/theories/af/af_tools.v))
    - `af T'` where `T' := T↑α` (because `T ⊆ T'`  holds)
    - hence `af (utree_embed R' T')` (because `T' = T↑α` is smaller than `T` and the lexicographic product)
6. finally we transfer `af` through `af (utree_embed R' T') → af (utree_embed R T)↑⟨α|τ⟩₁`
   using a [quasi-morphism](theories/af/af_quasi_morphism.v) of which the construction
   composes most of contents of the file [`af/af_utree_embed_fun.v`](theories/af/af_utree_embed_fun.v);
7. there is also version if that proof with [_a relational quasi morphism_](theories/af/af_utree_embed_rel.v)
   to illustrate the differences with the functional version above.
    - indeed Higman's theorem and Kruskal's tree theorem are only reasonably implementable with a 
      relational version and this project is an introduction to those more involved proofs, 
      but with a similar sketch.

# Higman's lemma for lists

Using the isomorphism between `list X` and `utree unit X`. Indeed, lists are just unary trees where
there is no information (eg of type `unit`) on the leaves.

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
