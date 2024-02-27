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
  Require Import notations idx vec.

From KruskalFinite
  Require Import finite.

Require Import base vec_embed indexed_choice.

Import ListNotations idx_notations vec_notations.

Set Implicit Arguments.

Theorem fin_vec_fall2_find X Y (R : X → Y → Prop) P n (v : vec X n) :
      (∀i, fin (R v⦃i⦄))
    → (∀w, vec_fall2 R v w → ∃i, P w⦃i⦄)
    → (∃i, R v⦃i⦄ ⊆₁ P).
Proof. 
  intros H1 H2. 
  apply fin_indexed_choice with (X := fun i => R v⦃i⦄); auto.
  intros w Hw.
  destruct (H2 (vec_set w)) as (i & Hi).
  + intro; vec rew; auto.
  + exists i; revert Hi; now vec rew.
Qed.

Theorem vec_combi_principle X n (P : rel₁ (vec X n)) (B : rel₁ X) (R : vec (list X) n) :
         (∀v, vec_fall2 In v R → P v ∨ ∃p, B v⦃p⦄)
       → (∃v, vec_fall2 In v R ∧ P v)
       ∨ (∃i, ∀x, x ∈ R⦃i⦄ → B x).
Proof.
  intros H.
  destruct fin_matrix_choice
    with (P := fun c => P (vec_set c))
         (Q := fun _ : idx n => B)
         (X := fun i x => x ∈ R⦃i⦄)
    as [ (c & H1 & H2) | (p & Hp) ]; eauto.
  + intro i; exists R⦃i⦄; tauto.
  + intros c Hc.
    destruct (H (vec_set c)) as [ | (p & Hp) ]; auto.
    * now intro; vec rew.
    * right; exists p; rewrite vec_prj_set in Hp; auto.
  + left; exists (vec_set c); split; auto.
    now intro; vec rew.
Qed.

Theorem list_combi_principle X (P : rel₁ (list X)) (B : rel₁ X) ll :
         (∀c, Forall2 In c ll → P c ∨ (λ x, x ∈ c) ⧫ B)
       → (∃c, Forall2 In c ll ∧ P c)
       ∨ (∃A, A ∈ ll ∧ ∀x, x ∈ A → B x).
Proof.
  intros H.
  generalize ⌊ll⌋ (list_vec ll) (vec_list_vec ll); intros n R <-.
  destruct (@vec_combi_principle X n (fun v => P (vec_list v)) B R)
    as [ (v & H1 & H2) | (p & Hp) ].
  + intros v Hv.
    destruct (H (vec_list v)) as [ | (x & H1 & H2) ]; auto.
    * apply Forall2_iff_vec_fall2; auto.
    * apply in_vec_list in H1 as (p & <-); eauto.
  + left; exists (vec_list v); split; auto.
    apply Forall2_iff_vec_fall2; auto.
  + right; exists (R⦃p⦄); split; auto.
    apply in_vec_list; eauto.
Qed.
