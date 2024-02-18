(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import Utf8.

From KruskalTrees
  Require Import notations utree.

Require Import base.

Import utree_notations.

Set Implicit Arguments.

#[local] Reserved Notation "s '≤ut' t" (at level 70, no associativity, format "s  ≤ut  t").
#[local] Reserved Notation "l '≤ₑ' m" (at level 70, no associativity, format "l  ≤ₑ  m").

Create HintDb utree_db.

Section utree_embed.

  (* Embedding for unary trees with leaves in X, nodes in Y *)

  Variable (X Y : Type).

  Implicit Types (R : rel₂ X) (T : rel₂ Y).

  Inductive sub_utree : rel₂ (utree X Y) :=
    | sub_utree_refl t : t ≤ut t
    | sub_utree_subt s y t : s ≤ut t → s ≤ut ⟨y|t⟩₁
  where "s ≤ut t" := (sub_utree s t).

  Hint Constructors sub_utree : core.

  Fact sub_utree_trans r s t : r ≤ut s → s ≤ut t → r ≤ut t.
  Proof. induction 2; eauto. Qed.

  Fact sub_utree_inv_right s t :
          s ≤ut t
        → s = t
        ∨ match t with
          | ⟨x⟩₀    => False
          | ⟨_|t'⟩₁ => s ≤ut t'
          end.
  Proof. induction 1; auto. Qed.

  Inductive utree_embed R T : utree X Y → utree X Y → Prop :=
    | utree_embed_leaf x₁ x₂ : R x₁ x₂ → ⟨x₁⟩₀ ≤ₑ ⟨x₂⟩₀
    | utree_embed_subt s y t : s ≤ₑ t → s ≤ₑ ⟨y|t⟩₁
    | utree_embed_root y₁ t₁ y₂ t₂ : T y₁ y₂ → t₁ ≤ₑ t₂ → ⟨y₁|t₁⟩₁ ≤ₑ ⟨y₂|t₂⟩₁
  where "s ≤ₑ t" := (@utree_embed _ _ s t).

  Fact utree_embed_inv_right R T s t :
          utree_embed R T s t
        → match t with
          | ⟨x₂⟩₀    => ∃ x₁, s = ⟨x₁⟩₀ ∧ R x₁ x₂
          | ⟨y₂|t₂⟩₁ => utree_embed R T s t₂
                      ∨ ∃ y₁ t₁, s = ⟨y₁|t₁⟩₁ ∧ T y₁ y₂ ∧ utree_embed R T t₁ t₂
          end.
  Proof.
    intros []; eauto.
    right; eauto.
  Qed.

  Fact utree_sub_embed R T r s t : r ≤ut s → utree_embed R T s t → utree_embed R T r t.
  Proof.
    induction 1 as [ | r y s H IH ] in t |- *; auto.
    induction t as  [ x | y' t IHt ].
    + now intros (? & ? & _)%utree_embed_inv_right.
    + intros [ ? | (? & ? & [=] & ? & ?) ]%utree_embed_inv_right.
      * constructor 2; eauto.
      * subst; constructor 2; eauto.
  Qed.

  Fact utree_embed_trans R T x s t : utree_embed R T ⟨x|s⟩₁ t → utree_embed R T s t.
  Proof. apply utree_sub_embed; eauto. Qed.

End utree_embed.

#[global] Hint Constructors sub_utree utree_embed : utree_db.
#[global] Hint Resolve sub_utree_trans : utree_db.

Module utree_embeddings_notations.

  Infix "≤ut" := sub_utree.

End utree_embeddings_notations.


