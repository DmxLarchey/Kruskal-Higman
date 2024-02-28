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

From KruskalFinite
  Require Import finite choice.

Require Import base.

Import ListNotations.

Set Implicit Arguments.

#[local] Hint Resolve in_eq in_cons : core.

(** Below the FAN of a list of lists is characterized as a
    predicate derived for the list product Forall2 in list
    membership. Its finiteness is not explicited but rather
    derived from KruskalFinite tools. *)

#[local] Notation FAN lw := (λ c, Forall2 (λ x l, x ∈ l) c lw).

Fact fin_FAN X (lw : list (list X)) : fin (FAN lw).
Proof. apply fin_Forall2_rev; fin auto. Qed.

Theorem list_combi_principle X (P : rel₁ (list X)) (B : rel₁ X) ll :
         (∀c, FAN ll c → P c ∨ (λ x, x ∈ c) ⧫ B)
       → (∃c, FAN ll c ∧ P c)
       ∨ (∃l, l ∈ ll ∧ ∀x, x ∈ l → B x).
Proof.
  induction ll as [ | w lw IHlw ] in P |- *; intros HPB.
  + destruct (HPB []) as [ | (_ & [] & _) ]; eauto.
  + assert (H: ∀x, x ∈ w → B x ∨ (∀c, FAN lw c → P (x :: c) ∨ (∃y, y ∈ c ∧ B y))).
    1:{ intros x Hx.
        apply fin_choice_cst_left.
        + apply fin_FAN.
        + intros c Hc.
          destruct (HPB (x::c)) as [ | (? & [<- | ] & ?) ]; eauto. }
    apply fin_choice in H as [ | (x & ? & [ (c & []) | (m & []) ]%IHlw) ]; fin auto.
    * right; exists w; eauto.
    * left; exists (x::c); eauto.
    * right; exists m; eauto.
Qed.
