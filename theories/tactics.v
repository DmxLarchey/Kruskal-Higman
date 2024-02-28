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

Set Implicit Arguments.

(* structurally dealing with equivalences *)

#[local] Notation "P '⇄' Q" := ((P → Q) * (Q → P))%type (at level 95, no associativity, format "P  ⇄  Q").

Section logic.

  Fact False_or_equiv A : False ∨ A ↔ A.
  Proof. tauto. Qed.

  Fact or_False_equiv A : A ∨ False ↔ A.
  Proof. tauto. Qed.

  Fact and_equiv A A' B B' : A ↔ A' → B ↔ B' → A ∧ B ↔ A' ∧ B'.
  Proof. tauto. Qed.

  Fact or_equiv A A' B B' : A ↔ A' → B ↔ B' → A ∨ B ↔ A' ∨ B'.
  Proof. tauto. Qed.

  Fact sum_equiv (A A' B B' : Type) : A ⇄ A' → B ⇄ B' → A + B ⇄ A' + B'.
  Proof. intros [] []; split; tauto. Qed.

  Fact prod_equiv (A A' B B' : Type) : A ⇄ A' → B ⇄ B' → A * B ⇄ A' * B'.
  Proof. intros [] []; split; tauto. Qed.

  Fact imp_equiv A A' B B' : A ↔ A' → B ↔ B' → (A → B) ↔ (A' → B').
  Proof. tauto. Qed.

  Fact exists_equiv X (P Q : X → Prop) : (∀x, P x ↔ Q x) → ex P ↔ ex Q.
  Proof. firstorder. Qed.

  Fact forall_equiv X (P Q : X → Prop) : (∀x, P x ↔ Q x) → (∀x, P x) ↔ (∀x, Q x).
  Proof. firstorder. Qed.

End logic.

Tactic Notation "equiv" "sum" :=
  ( apply or_equiv || apply sum_equiv ).

Tactic Notation "equiv" "auto" :=
  repeat (
    match goal with
    | |-  _ ∨ _  ↔  _ ∨ _  => apply or_equiv
    | |-  _ ∧ _  ↔  _ ∧ _  => apply and_equiv
    | |- (_ → _) ↔ (_ → _) => apply imp_equiv
    | |-  _ + _  ⇄  _ + _  => apply sum_equiv
    | |-  _ * _  ⇄  _ * _  => apply prod_equiv
    | |- ex _ ↔ ex _ => let x := fresh in apply exists_equiv; intro x
    | |- (∀_, _) ↔ (∀_, _) => let x := fresh in apply forall_equiv; intro x
    end; auto; try tauto).
