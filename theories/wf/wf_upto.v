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

Require Import base.

Set Implicit Arguments.

Section wf_upto.

  (** Well founded upto is similar to well_founded except that we
      can only prove by induction predicates of the form P∘f, ie
      P can only express properties of the projections of the
      inhabitants of X.

      This will help at decorating member of Y with information
      helpfull for the inductive proof but not recoverable from
      the value of y : Y. *)

  (** Notice the reading of the statement:

        to prove P (f a), you may assume P (f b) already
        holds for values b which are R-lower than a

      Notice that the relation is between the non-projected
      values, ie it may use the information which is hidden
      by the projection f *)

  Variable (X Y : Type) (f : X → Y).

  Implicit Types (R : X → X → Base) (P : Y → Base).

  Definition wf_upto R :=
      ∀P, (∀a, (∀b, R b a → P (f b)) → P (f a))
        → (∀a,                         P (f a)).

End wf_upto.

Section wf_upto_lex_prod.

  (** This is the critical observation for the notion wf_upto,
      it is closed under lexicographic products *)

  Variables (Xₑ X : Type) (f : Xₑ → X) (R : Xₑ → Xₑ → Base)
            (Yₑ Y : Type) (g : Yₑ → Y) (T : Yₑ → Yₑ → Base).

  Let Zₑ := prod Xₑ Yₑ.
  Let Z  := prod X Y.

  Let lex_prj : Zₑ → Z :=
    λ '(x,y), (f x,g y).

  Let lex_prod : Zₑ → Zₑ → Base :=
    λ '(x₁,y₁) '(x₂,y₂), R x₁ x₂ ∨ₜ f x₁ = f x₂ ∧ₜ T y₁ y₂.

  Lemma wf_upto_lex_prod :
           wf_upto f R
         → wf_upto g T
         → wf_upto lex_prj lex_prod.
  Proof.
    intros HR HT P IHP (x,y); simpl; revert x y.
    apply (HR (λ x, ∀ y, P (x, _))); intros x IHx.
    apply (HT (λ y, P (_, y))); intros y IHy.
    apply (IHP (_,_)).
    intros [] [ | (E & ?) ]; simpl.
    + apply IHx; auto.
    + rewrite E; apply IHy; auto.
  Qed.

End wf_upto_lex_prod.
