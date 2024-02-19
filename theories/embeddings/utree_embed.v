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

  Inductive sub_utree s : rel₁ (utree X Y) :=
    | sub_utree_refl : s ≤ut s
    | sub_utree_subt y t : s ≤ut t → s ≤ut ⟨y|t⟩₁
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

  Hint Constructors utree_embed : core.

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

  Fact utree_embed_inv_0_ R T x₁ t :
         utree_embed R T ⟨x₁⟩₀ t
       → match t with
         | ⟨x₂⟩₀    => R x₁ x₂
         | ⟨y₂|t₂⟩₁ => utree_embed R T ⟨x₁⟩₀ t₂
         end.
  Proof.
    intros H%utree_embed_inv_right; destruct t as [ x1 | y2 t2 ].
    + destruct H as (? & [=] & ?); now subst.
    + destruct H as [ | (? & ? & ? & _) ]; now auto.
  Qed.

  Fact utree_embed_inv_1_ R T y₁ t₁ t :
         utree_embed R T ⟨y₁|t₁⟩₁ t
       → match t with
         | ⟨x₂⟩₀    => False
         | ⟨y₂|t₂⟩₁ => utree_embed R T ⟨y₁|t₁⟩₁ t₂ ∨ T y₁ y₂ ∧ utree_embed R T t₁ t₂
         end.
  Proof.
    intros H%utree_embed_inv_right; destruct t as [ x1 | y2 t2 ].
    + now destruct H as (? & ? & _).
    + destruct H as [ | (? & ? & [=] & []) ]; subst; eauto.
  Qed.

  Fact utree_embed_inv_1_ex R T y₁ t₁ t :
         utree_embed R T ⟨y₁|t₁⟩₁ t
       → ∃ y₂ t₂, utree_embed R T ⟨y₁|t₁⟩₁ t₂ ∨ T y₁ y₂ ∧ utree_embed R T t₁ t₂.
  Proof.
    destruct t as [ | y2 t2 ]; intros H%utree_embed_inv_right.
    + now destruct H as (? & ? & _).
    + exists y2, t2.
      destruct H as [ | (? & ? & [=] & []) ]; subst; eauto.
  Qed.

  Fact utree_embed_inv_10 R T y₁ t₁ x₂ :
         utree_embed R T ⟨y₁|t₁⟩₁ ⟨x₂⟩₀ → False.
  Proof. now intros (? & ? & _)%utree_embed_inv_right. Qed.

  Fact utree_embed_inv_11 R T y₁ t₁ y₂ t₂ :
         utree_embed R T ⟨y₁|t₁⟩₁ ⟨y₂|t₂⟩₁
       → utree_embed R T ⟨y₁|t₁⟩₁ t₂
       ∨ T y₁ y₂ ∧ utree_embed R T t₁ t₂.
  Proof. intros [ | (? & ? & [=] & []) ]%utree_embed_inv_right; subst; eauto. Qed.

  Fact utree_sub_embed R T r s t : r ≤ut s → utree_embed R T s t → utree_embed R T r t.
  Proof.
    induction 1 as [ | y s H IH ] in t |- *; auto.
    induction t as  [ x | y' t IHt ].
    + now intros ?%utree_embed_inv_10.
    + intros [ ? | [] ]%utree_embed_inv_11.
      * constructor 2; eauto.
      * subst; constructor 2; eauto.
  Qed.

  Fact utree_embed_sub R T r s t : utree_embed R T r s → s ≤ut t → utree_embed R T r t.
  Proof. induction 2; eauto. Qed.

  (** Notice that utree_embed is transtive if R and T are transitive *)

  Fact utree_embed_leaf_iff R T x₁ x₂ : utree_embed R T ⟨x₁⟩₀ ⟨x₂⟩₀ ↔ R x₁ x₂.
  Proof. split; auto; intros (? & [=] & ?)%utree_embed_inv_right; now subst. Qed.
  
  Fact utree_embed_node_iff R T x (_ : R x x) y₁ y₂ : utree_embed R T ⟨y₁|⟨x⟩₀⟩₁ ⟨y₂|⟨x⟩₀⟩₁ ↔ T y₁ y₂.
  Proof.
    split; eauto.
    now intros [ []%utree_embed_inv_10 | [] ]%utree_embed_inv_11.
  Qed.

  Section utree_embed_trans.

    Variables (R : rel₂ X) (Rtrans : ∀ x₁ x₂ x₃, R x₁ x₂ → R x₂ x₃ → R x₁ x₃)
              (T : rel₂ Y) (Ttrans : ∀ y₁ y₂ y₃, T y₁ y₂ → T y₂ y₃ → T y₁ y₃).

    Lemma utree_embed_trans r s t : utree_embed R T r s → utree_embed R T s t → utree_embed R T r t.
    Proof.
      intros H; revert H t.
      induction 1 as [ x1 x2 H1 | r y1 s H1 IH1 | y1 r y2 s H1 H2 IH2 ]; intros t.
      + induction t; intros H%utree_embed_inv_0_; eauto.
      + induction t; intros H%utree_embed_inv_1_; [ easy | destruct H as [ | [] ] ]; eauto.
      + induction t; intros H%utree_embed_inv_1_; [ easy | destruct H as [ | [] ] ]; eauto.
    Qed.

  End utree_embed_trans.

  Section utree_embed_trans_inv.

     Variables (R : rel₂ X) (T : rel₂ Y) (Hute : ∀ r s t, utree_embed R T r s → utree_embed R T s t → utree_embed R T r t).

     Fact utree_embed_trans_0 x₁ x₂ x₃ : R x₁ x₂ → R x₂ x₃ → R x₁ x₃.
     Proof.
       intros H1%(utree_embed_leaf_iff R T) H2%(utree_embed_leaf_iff R T).
       apply (utree_embed_leaf_iff R T); eauto.
     Qed.

     (** The hypothesis below could be relaxed with (t : utree X Y) (utree_embed R T t t) but that
         would require more work, in particular to generalize utree_embed_node_iff by replacing 
         ⟨x⟩₀ with t *)
     Variables (x : X) (Hx : R x x).

     Fact utree_embed_trans_1 y₁ y₂ y₃ : T y₁ y₂ → T y₂ y₃ → T y₁ y₃.
     Proof.
       intros ?%(utree_embed_node_iff R T _ Hx) ?%(utree_embed_node_iff R T _ Hx).
       apply (utree_embed_node_iff R T _ Hx); eauto.
     Qed.

     (* Notice that if X is not inhabited then utree X _ is neither (because trees
        must have leaves) and hence utree_embed R T is transitive (by lack of trees), 
        regardedless of T *) 

  End utree_embed_trans_inv.

End utree_embed.

#[global] Hint Constructors sub_utree utree_embed : utree_db.
#[global] Hint Resolve sub_utree_trans utree_sub_embed utree_embed_sub: utree_db.

Module utree_embeddings_notations.

  Infix "≤ut" := sub_utree.

End utree_embeddings_notations.


