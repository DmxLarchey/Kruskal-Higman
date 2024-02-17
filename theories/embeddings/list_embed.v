(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import List Arith Lia Utf8.

From KruskalTrees
  Require Import notations.

From KruskalFinite
  Require Import decide.

Import ListNotations.

Set Implicit Arguments.

Create HintDb list_db.

#[local] Reserved Notation "l '≤ₑ' m" (at level 70, no associativity, format "l  ≤ₑ  m").

Section list_embed.

  Variables (X Y : Type) (R : X → Y → Prop).

  (** The homeomorhic embedding of lists *)

  Inductive list_embed : list X → list Y → Prop :=

    | list_embed_nil :             [] ≤ₑ[]

    | list_embed_head {x l y m} :  R x y
                              →    l ≤ₑ m
                              → x::l ≤ₑ y::m

    | list_embed_skip {l y m} :    l ≤ₑ m
                              →    l ≤ₑ y::m

  where "l ≤ₑ m" := (list_embed l m).

  Hint Constructors list_embed : core.

  Fact list_embed_left l m k : l ≤ₑ m → l ≤ₑ k++m.
  Proof. intro; induction k; simpl; eauto. Qed.

  Fact list_embed_nil_any l : [] ≤ₑ l.
  Proof. induction l; eauto. Qed.

  Hint Resolve list_embed_nil_any : core.

  Fact Forall2_embed l m : Forall2 R l m → l ≤ₑ m.
  Proof. induction 1; auto. Qed.

  Fact list_embed_length l m : l ≤ₑ m → ⌊l⌋ ≤ ⌊m⌋.
  Proof. induction 1; simpl; lia. Qed.

  (** Left/right inversion lemmas *)

  Fact list_embed_inv_left l m :
          l ≤ₑ m
        → match l with
          | []   => True
          | x::l => ∃ m₁ y m₂, m = m₁++y::m₂ ∧ R x y ∧ l ≤ₑ m₂
          end.
  Proof.
    induction 1 as [ | x l y m H1 H2 IH2 | l y m H1 IH2 ]; auto.
    + eexists [], _, _; simpl; eauto.
    + destruct l as [ | x l ]; auto.
      destruct IH2 as (m1 & z & m2 & -> & ? & ?).
      exists (y::m1), z, m2; simpl; auto.
  Qed.

  Fact list_embed_inv_right l m :
          l ≤ₑ m
        ↔ match m with
          | []   => l = []
          | y::m => l = []
                  ∨ l ≤ₑ m
                  ∨ match l with
                    | []   => False
                    | x::l => R x y ∧ l ≤ₑ m
                    end
          end.
  Proof.
    split.
    + induction 1; eauto; do 2 right; eauto.
    + destruct m as [ | y m ].
      * intros ->; auto.
      * intros [ -> | [ H | H ] ]; auto.
        destruct l; auto; destruct H; auto.
  Qed.

  (** Specialized inversions *)

  Fact list_embed_cons_inv x l m :
          x::l ≤ₑ m → ∃ m₁ y m₂, m = m₁++y::m₂ ∧ R x y ∧ l ≤ₑ m₂.
  Proof. apply list_embed_inv_left. Qed.

  Fact list_embed_in_left_inv l m : l ≤ₑ m → ∀x, x ∈ l → ∃y, y ∈ m ∧ R x y.
  Proof.
    induction 1 as [ | x l y m H1 H2 IH2 | l y m H1 IH1 ]; simpl; try easy.
    + intros ? [ <- | (? & [])%IH2 ]; eauto.
    + intros ? (? & [])%IH1; eauto.
  Qed.

  Hint Resolve in_cons in_eq : core.

  Theorem list_embed_decide l m :
         (∀ x y, x ∈ l → y ∈ m → decider (R x y)) → decider (l ≤ₑ m).
  Proof.
    revert l; induction m as [ | y m IHm ]; intros l Hm.
    + destruct l as [ | ]; [ left | right ]; auto.
      now intros H; apply list_embed_cons_inv in H as ([] & ? & ? & ? & _).
    + decide eq (list_embed_inv_right l (y::m)).
      decide auto.
      * destruct l; auto; right; easy.
      * destruct l; decide auto.
  Qed.

End list_embed.

Arguments list_embed_nil {X Y R}.

#[global] Hint Constructors list_embed : list_db.
#[global] Hint Resolve list_embed_nil_any : list_db.

Fact list_embed_map X X' Y Y' (f : X → X') (g : Y → Y') (R : X' → Y' → Prop) l m :
   list_embed (λ x y, R (f x) (g y)) l m → list_embed R (map f l) (map g m).
Proof. induction 1; simpl; eauto with list_db. Qed.

Definition list_embed_mono {X Y} {P Q : X → Y → Prop} (HPQ : P ⊆₂ Q) : list_embed P ⊆₂ list_embed Q :=
  fix loop l m Hlm :=
    match Hlm return list_embed Q _ _ with
    | list_embed_nil        => list_embed_nil
    | list_embed_head H1 H2 => list_embed_head (HPQ _ _ H1) (loop _ _ H2)
    | list_embed_skip H1    => list_embed_skip (loop _ _ H1)
    end.


