(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import List Utf8.

From KruskalTrees
  Require Import list_utils utree.

Require Import base list_embed utree_embed af_utree_embed.

Import ListNotations utree_notations af_notations.

Set Implicit Arguments.

Section af_list_embed.

  (** We deduce Higman's lemma as an instance of
      af_utree_embed with X := unit *)

  Variable (X : Type) (R : rel₂ X).

  Let Fixpoint u2l (t : utree unit X) : list X :=
    match t with
    | ⟨_⟩₀   => []
    | ⟨x|t⟩₁ => x::u2l t
    end.

  Local Fact u2l_surj l : ∃ₜ t, u2l t = l.
  Proof.
    induction l as [ | x l (t & Ht) ].
    + exists ⟨tt⟩₀; auto.
    + exists ⟨x|t⟩₁; simpl; subst; auto.
  Qed.

  Corollary af_list_embed : af R → af (list_embed R).
  Proof.
    intros H; generalize (af_utree_embed af_unit H); clear H.
    af rel morph (λ x y, u2l x = y).
    + apply u2l_surj.
    + intros s t ? ? <- <-.
      induction 1 as [ ? ? -> | | ]; simpl; auto with list_db.
  Qed.

End af_list_embed.
