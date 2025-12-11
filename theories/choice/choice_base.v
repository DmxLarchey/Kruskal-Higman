(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib
  Require Import List Utf8.

From KruskalFinite
   Require Import finite.

Require Import base.

Import ListNotations.

Set Implicit Arguments.

(* 𝕆𝕊 λ ∀∃ → ↔ ∧ ∨ *)

(* Same as list_choice[_t] from KruskalTrees.list_utils but parametric in Base := {Prop,Type} *)

Fact list_choice_base X (P Q : rel₁ X) (l : list X) :
        (∀x, x ∈ l → P x ∨ₜ Q x)
      → (∀x, x ∈ l → P x) ∨ₜ ∃ₜ x, x ∈ l ∧ₜ Q x.
Proof.
  induction l as [ | x l IHl ]; intros Hl.
  + left; simpl; tauto.
  + destruct IHl as [ H | (y & ? & ?) ].
    * intros; apply Hl; simpl; auto.
    * destruct (Hl x); simpl; auto.
      - left; intros ? [ <- | ]; auto.
      - right; exists x; simpl; auto.
    * right; exists y; simpl; auto.
Qed.

Fact fin_choice_base X (F P Q : rel₁ X) :
         fin F
       → (∀x, F x → P x ∨ₜ Q x)
       → F ⊆₁ P ∨ₜ ∃ₜ x, F x ∧ₜ Q x.
Proof.
  intros (l & Hl) HF.
  destruct (@list_choice_base _ P Q l); firstorder.
Qed.
