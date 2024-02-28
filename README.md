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

This library is an extension of [`Kruskal-AlmostFull`](https://github.com/DmxLarchey/Kruskal-AlmostFull) contained an detailed and expanded constructive/inductive proofs of:
- Higman's theorem for unary trees (according to the terminology of [1]);
- and as a consequence, [Higman's lemma](https://en.wikipedia.org/wiki/Higman%27s_lemma) for lists.

The terminology and proof structure are largely inspired from Wim Veldman's [1] 
which is (IMHO) the reference pen-and-paper work of the matter.

`[1]`. [_An intuitionistic proof of Kruskal's theorem_](https://link.springer.com/article/10.1007/s00153-003-0207-x), Win Veldman, 2004

# What is established in here

```coq
Inductive list_embed {X Y} (R : X → Y → Prop) : list X → list Y → Prop :=
  | list_embed_nil :           [] ≤ₗ []
  | list_embed_head x l y m :  R x y  → l ≤ₗ m → x::l ≤ₗ y::m
  | list_embed_skip l y m :    l ≤ₗ m → l ≤ₗ y::m
where "l ≤ₗ m" := (list_embed R l m).

Theorem af_list_embed X (R : rel₂ X) : af R → af (list_embed R).
```

We derive Higman's lemma [as stated on Wikipedia](https://en.wikipedia.org/w/index.php?title=Higman%27s_lemma&oldid=841018000)
where the sub-list relation is abstracted by assuming its inductive rules:
```coq
Variables (X : Type) (≤sl : rel₂ (list X))
          (_ : ∃ l, ∀x : X, x ∈ l) 
          (_ : [] ≤sl [])
          (_ : ∀ x l m, l ≤sl m → x::l ≤sl x::m)
          (_ : ∀ x l m, l ≤sl m → l ≤sl x::m).

Theorem Higman_lemma : ∀ f : nat → list X, ∃ i j, i < j ∧ fᵢ ≤sl fⱼ.
```

