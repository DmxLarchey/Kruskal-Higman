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
  Require Import list_utils vec.

Require Import base vec_embed list_embed af_list_embed.

Import af_notations.

Set Implicit Arguments.

Section list_embed_vec_embed.

  Variables (X Y : Type) (R : X → Y → Prop).

  Fact list_embed_vec_embed l m :
       list_embed R l m → vec_embed R (list_vec l) (list_vec m).
  Proof. induction 1; simpl; eauto with vec_db. Qed.

  Fact list_embed_vec_embed_rev n (v : vec _ n) m (w : vec _ m) :
       list_embed R (vec_list v) (vec_list w) → vec_embed R v w.
  Proof.
    intros H.
    apply list_embed_vec_embed in H.
    destruct (list_vec_list v) as (e & He).
    destruct (list_vec_list w) as (f & Hf).
    rewrite <- He, <- Hf in H; clear He Hf.
    revert e f H.
    generalize (vec_list v) (vec_list w).
    intros ? ? -> ->; auto.
  Qed.

  Fact vec_embed_iff_list_embed n (v : vec _ n) m (w : vec _ m) :
       vec_embed R v w ↔ list_embed R (vec_list v) (vec_list w).
  Proof.
    split.
    + induction 1; simpl; auto with list_db.
    + apply list_embed_vec_embed_rev.
  Qed.

  Fact list_embed_iff_vec_embed l m :
       list_embed R l m ↔ vec_embed R (list_vec l) (list_vec m).
  Proof.
    split.
    + apply list_embed_vec_embed.
    + rewrite vec_embed_iff_list_embed.
      rewrite !vec_list_vec; auto.
  Qed.

End list_embed_vec_embed.

Section af_lvec_embed.

  Variable (X : Type) (R : rel₂ X) (HR : af R).

  (* Beware that vec_embed is not a relation of type
         vec X n → vec X n → Prop
     but instead of type
         vec X n → vec X m → Prop
     so it does not fit the af framework *)
  Theorem af_lvec_embed : af (lvec_embed R).
  Proof.
    generalize (af_list_embed HR).
    af rel morph (λ l v, l = vec_list (lvec_vec v)).
    + intros []; simpl; eauto.
    + intros ? ? [] []; simpl; intros -> ->; apply vec_embed_iff_list_embed.
  Qed.

End af_lvec_embed.
