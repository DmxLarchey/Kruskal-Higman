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
It contains a detailed and expanded constructive/inductive proofs of:
- Higman's theorem for unary trees (according to the terminology of \[1\]);
- and as a consequence, [Higman's lemma](#Higmans-lemma-for-lists).

This `README` itself contains the outline of the proof with the critical steps.
The terminology and proof structure are largely inspired from Wim Veldman's \[1\] 
which is (IMHO) the reference pen-and-paper work on this proof technique.

\[1\]. [_An intuitionistic proof of Kruskal's theorem_](https://link.springer.com/article/10.1007/s00153-003-0207-x), Wim Veldman, 2004

# How to install `Kruskal-Higman`

It can be installed via `opam` since release `v1.0` is now include into [`coq-opam`](https://github.com/coq/opam).
```console
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq-kruskal-higman
```

Notice that to import it in a development, as with `Kruskal-AlmostFull`, one should
consistently choose between:
- the `Prop`-bounded version accessed via eg `Require Import KruskalHigmanProp`;
- or the `Type`-bounded version via eg `Require Import KruskalHigmanType`.

Mixing both versions is possible is possible but hard and not recommended due 
to the total overlap of the namespaces except for the prefixes `KruskalHigman{Prop,Type}`.

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
1. first a [lexicographic induction](#Lexicographic-induction-on-AF-predicates) on a kind of _measure of the AF-complexity_ of `(af T,af R)`. 
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
      
# The quasi-morphism 

We describe the quasi-morphism that implements the following transfer `af (utree_embed R' T') → af (utree_embed R T)↑⟨α|τ⟩₁`.
Recall that we are in the case where the induction on `t` above is a unary tree `⟨α|τ⟩₁` and
also when `∀y, af T↑y` holds. In particular we have `af T↑α`. Recall the following definitions:
```coq
X' := X + Y ⨉ utree X Y
Y' := Y
R' := R + T ⨉ (utree_embed R T)↑τ
T' := T↑α
```
As argued above, `af (utree_embed R' T')` can be establish using (the consequences of) Ramsey's theorem
and the induction hypotheses available.

We build an _evaluation/analysis_ pair as a _single binary relation_ between the types
`utree X' Y'` (the analyses) and `utree X Y` (the evaluations). In the simple case 
of `utree`(s), that can be implemented directly as evaluation _function_. 
In the more complicated case of Kruskal's theorem (for roses trees),
we will really need to view the evaluation/analysis as a relation between analyses and
evaluations. So here we write `==>` for this evaluation relation.

Terms in the type `X'` are either of the form 
- `⦗x⦘₁` with `x : X`;
- or `⦗y,t⦘₂` with `(y : Y)` and `t : utree X Y`.

Evaluation consists in (recursively) replacing a leaf by a sub-tree, if it is
of shape `⦗y,t⦘₂`. Hence, we get the following rules for the evaluation relation:
```coq
                                                      t' ==> t
 ------------------   -----------------------   --------------------
  ⟨⦗x⦘₁⟩₀ ==> ⟨x⟩₀     ⟨⦗y,t⦘₂⟩₀  ==> ⟨y|t⟩₁     ⟨y|t'⟩₁ ==> ⟨y|t⟩₁
```
but in the simple case of `utree`, these can also be implemented as the following fixpoint equations:
```coq
ev ⟨⦗x⦘₁⟩₀ = ⟨x⟩₀
ev ⟨⦗y,t⦘₂⟩₀ = ⟨y|t⟩₁
ev ⟨y|t'⟩₁ = ⟨y|ev t⟩₁
```
One can understand the analyses as ways to displace information in an evaluation.
Nothing can be done at leaves but at a node of arity 1, it is possible to cut
the `utree` there, and hide the sub-tree into a new leaf. For instance,
the  `⟨1|⟨2|⟨0⟩₀⟩₁⟩₁ : utree nat nat` can be analyzed as:
- `⟨⦗1,⟨2|⟨0⟩₀⟩₁⦘₂⟩₀`
- `⟨1|⟨⦗2,⟨0⟩₀⦘₂⟩₀⟩₁`
- `⟨1|⟨2|⟨⦗0⦘₁⟩₀⟩₁⟩₁`

in the type `utree (nat+nat*utree nat nat) nat`.

This can look simple here because unary trees are _linear_ but imagine what is
going on when the arity (number of sons) is allowed to be larger than 2. Then
there is an exponential number of ways to analyses (displace information).
However one can show that there are only finitely many ways to do it.

Then we say that an analysis in `utree X' Y'` is _disappointing_ if either:
- it is of shape `⟨y|_⟩₁` with `T α y`
- or of shape `⟨⦗_,t⦘₂⟩₀` with `utree_embed R T τ t`

and an analysis is _exceptional_ (denoted `E t'`) if it contains a disappointing sub-tree.
We say that an evaluation is _exceptional_ (and write `E t`) if all its analyses are exceptional,
ie. `E t := ∀t', t' ==> t  →  E' t'`.

We show the three following properties for `ev` and `E'/E`:
1. `fin(λ t', t' ==> t)` (`ev` has finite inverse image);
2. `utree_embed R' T' s' t' → utree_embed R T (ev s') (ev t') ∨ E' s'` (quasi morphism)
3. `E t → utree_embed R T ⟨α|τ⟩₁ t` (exceptional evaluations embed `⟨α|τ⟩₁`)

Actually, Item 3 holds in both directions but this is not needed.
These 3 items are the conditions that constitute a _quasi morphism_
(see [`af/af_quasi_morhism.v`](theories/af/af_quasi_morhism.v)) 
and thus enable the transfer of the `af` property.

All this construction is performed:
- in a functional form in [`af/af_utree_embed_fun.v`](theories/af/af_utree_embed_fun.v) and heavily commented;
- and in relational form in [`af/af_utree_embed_rel.v`](theories/af/af_utree_embed_rel.v) (not really commented);

They describe in the simple case of unary trees `utree` the very same steps that will
also be performed for Kruskal's tree theorem, but the general setting is more complicated
because the analysis/evaluation relation is much harder to implement.

# Higman's lemma for lists

Lists are just unary trees where there is no information (eg of type `unit`) on the leaves.
Hence there is an isomorphism between `list X` and `utree unit X` that we use as
 relational morphism to transfer `af_utree_embed` to lists.
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

# Lexicographic induction on AF predicates

__To be completed__, the reference files being:
- [`wf/wf_upto.v`](theories/wf/wf_upto.v) which defines the notion of _well foundedness up to a projection_ and shows that it is closed
  under lexicographic products;
- [`af/af_lex.v`](theories/af/af_lex.v)) which show how to transform almost fullness in well foundedness up to a projection
  and then derives the _easier \[1\]_ lexicographic induction principle for pairs of AF relations.
 
