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
- Higman's theorem for unary trees;
- and as a consequence, [Higman's lemma](https://en.wikipedia.org/wiki/Higman%27s_lemma) for lists.

The terminology and proof structure are largely inspired from Wim Veldman's [intuitionistic proof of Kruskal's theorem](https://link.springer.com/article/10.1007/s00153-003-0207-x) which is (IMHO) the reference pen-and-paper work of the matter.

# What is established in here

```coq
Inductive list_embed {X Y} (R : X → Y → Prop) : list X → list Y → Prop :=
  | list_embed_nil :           [] ≤ₗ []
  | list_embed_head x l y m :  R x y → l ≤ₗ m → x::l ≤ₗ y::m
  | list_embed_skip l y m :    l ≤ₗ m → l ≤ₗ y::m
where "l ≤ₗ m" := (list_embed R l m).

Theorem af_list X (R : rel₂ X) : af R → af (list_embed R).
```
