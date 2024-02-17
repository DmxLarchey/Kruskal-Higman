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
  Require Import utree.

Require Import base tactics
               utree_embed
               af_lex
               af_utree_embed_fun.

Import utree_notations
    af_notations af_choice_notations af_lex_notations.

Set Implicit Arguments.

Section higman_utree_leaves_full.

  Variables (X : Type) (R : rel₂ X) (x : X)
            (Y : Type) (T : rel₂ Y).

  Local Lemma af_utree_leaves_full :
        (∀ x y, R x y)
      → af (utree_embed R T)↑⟨x⟩₀.
  Proof.
    intros HR; constructor 1.
    intros t s; right; clear s.
    induction t; auto with utree_db.
  Qed.

End higman_utree_leaves_full.

Section higman_utree_leaves_lift.

  Variables (X : Type) (R : rel₂ X) (x : X)
            (Y : Type) (T : rel₂ Y).

  Local Lemma af_utree_leaves_lift :
        af (utree_embed R↑x T)
      → af (utree_embed R T)↑⟨x⟩₀.
  Proof.
    apply af_mono.
    induction 1 as [ ? ? [] | ? ? ? ? [] | ? ? ? ? ? ? [] ];
      simpl; eauto with utree_db.
  Qed.

End higman_utree_leaves_lift.

#[local] Hint Constructors af_easier lt_wrel₂ : core.

Theorem af_utree_embed X Y (R : rel₂ X) (T : rel₂ Y) :
        af R → af T → af (utree_embed R T).
Proof.
  (* First the "easier" induction on the af pair (af R , af T) *)
  revert X R Y T;
    apply af_easier_ind;
    intros sR X R sT Y T HR HT IH.

  (* Then lifting by t and induction on t *)
  constructor 2; intros t.
  induction t as [ x | α τ IHτ ].

  + (* The case of leaves ⟨x⟩₀, depending on sR = ◩, ▣  or ▢ *)
    destruct sR as [ [] | ].
    * (* R is af/◩ *)
      apply af_utree_leaves_lift.
      apply IH with ◩ sT; auto.
      apply af_inv, HR.
    * (* R is full/▣ *)
      apply af_utree_leaves_full; auto.
    * (* X cannot be empty/▢ because it is inhabited by x *)
      simpl in HR; tauto.

  + (* The case of nodes ⟨α|τ⟩₁, depending on sT ∈ {◩,▣} or sT = ▢ *)
    destruct sT as [ c | ].
    * (* either T is af/◩ or T is full/▣ *)
      now apply af_utree_nodes with sR (Some c); auto.
    * (* Y cannot be empty/▢ because it is inhabited by α *)
      exfalso; revert α; apply HT.
Qed.
