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

Require Import base list_embed af_list_embed.

Import ListNotations af_notations.

Set Implicit Arguments.

Section Higman_lemma.

  (** This is a proof of Higman's lemma as stated on

        https://en.wikipedia.org/w/index.php?title=Higman%27s_lemma&oldid=841018000

   *)

  Variables (X : Type) (HX : ∃ₜ l, ∀x : X, x ∈ l) (R : rel₂ (list X)).

  Notation "l '≤sl' m" := (R l m) (at level 70, no associativity, format "l  ≤sl  m").

  Hypotheses (HR_nil : [] ≤sl [])
             (HR_head : ∀ x l m, l ≤sl m → x::l ≤sl x::m)
             (HR_skip : ∀ x l m, l ≤sl m → l ≤sl x::m).

  Local Fact list_embed_eq_sublist : list_embed eq ⊆₂ R.
  Proof. induction 1; subst; eauto. Qed.

  Variables (f : nat → list X).

  (* The bound n below can be computed provided Base is Type, ie
     af predicate are informative, but i and j cannot unless R is
     furthermore decidable *)

  Theorem Higman_lemma_strong : ∃ₜ n, ∃ i j, i < j < n ∧ f i ≤sl f j.
  Proof.
    apply af_good_pair,
          af_mono with (1 := list_embed_eq_sublist),
          af_list_embed,
          af_eq_fin.
    destruct HX as (l & ?); eauto.
  Qed.

  Theorem Higman_lemma : ∃ i j, i < j ∧ f i ≤sl f j.
  Proof. destruct Higman_lemma_strong as (? & i & j & (? & _) & ?); eauto. Qed.

End Higman_lemma.

About Higman_lemma.
Print Assumptions Higman_lemma.
