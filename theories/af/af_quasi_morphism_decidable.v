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
  Require Import notations.

From KruskalFinite
  Require Import finite.

Require Import base choice_base.

Import lift_notations.

Set Implicit Arguments.

Section af_quasi_morphism_decidable.

  Variables (X Y : Type) (ev : X → Y).

  Notation ana_rel := (λ y x, ev x = y).

  Variables (ana_fin : ∀y, fin (ana_rel y)) (* ev has finite inverse images *)

            (R : rel₂ X) (* abstracts the src embedding, eg higman' *)
            (E : rel₁ X) (* abstracts "exceptional" analyses, eg "has disappointing subtree" *)

            (T : rel₂ Y) (* abstracts the dst embedding, eg higman *)
            (y₀ : Y)     (* abstracts the tree by which T is lifted *)

            (* ev is a "quasi" morphism from R to T, ie. "up to" E *)
            (ev_qmorph : ∀ x₁ x₂, R x₁ x₂ → T (ev x₁) (ev x₂) ∨ E x₁)

            (* if no analysis of y avoids E then y must T-embed y0 *)
            (HET : ∀y, ana_rel y ⊆₁ E → T y₀ y).

            (** We want to conclude: af R → af T↑y₀ *)

    (** Let us present a justification of the result in the decidable case
       (see below for what "the decidable case" precisely means)

        E represents E(xceptional) analyses. We say that an evaluation y
        is "exceptional" if every ana(lysis) of y is E(xceptional), or no
        analysis of y avoids E.

        (ev_qmorph) says that ev is a R/T-morphism on non-exceptional analyses
        (HET) says that y is exceptional only when y T-embeds y₀

        Now let us explain why af R implies af T↑y0 reasonning in the
        decidable case:

     a) af T↑y0 is the same as af T⇓(¬ T y₀) when (T y₀) is decidable
     b) for y not to T-embed y₀, it must have a non exceptional analysis
        hence there is a reverse map,

                     { y | ¬ T y₀ y } → { x | ana_rel y x ∧ ¬ E x }

     c) hence, restricted to that type

               f : { x | ¬ E x } → { ev x | ¬ T y0 y }

        is a surjective morphism from R⇓(¬E) to T⇓(¬T y₀)

     d) since R is AF, so is R⇓(¬E) and thus T⇓(¬T y0) and finally T↑y0

        The decidable case is when

     a) λ y, T y0 y is decidable (hence for decidable embeddings)
     b) E is decidable (but E is instanciated as "x contains
        a disappointing subtree" which can be decided provided
        disapointing is, and this is also decidable if embeddings
        are decidable).

     This explains:
       1) why the result generalizes the "af_rel_morph" result transferring
          af using surjective morphism
       2) gives a intuitive understanding of the result on quasi-morphisms
       3) how to circumvent the non-decidable case with the use of the FAN theorem
       4) this might give some insights into the limitations of M. Seisenberger's
          proof (which is restricted to the decidable case)
     *)

  (** In the decidable case we have af T↑y₀ <-> af T⇓(~ T y₀)
       - the -> implication always holds 
       - while the <- implications use decidablity of T y0 *)

  Goal af T↑y₀ → af T⇓(λ y, ¬ T y₀ y).
  Proof. apply af_lift_af_sub_rel. Qed.

  Hypothesis (Ty₀_dec : ∀y, T y₀ y ∨ₜ ¬ T y₀ y).

  Local Lemma af_not_af_lift : af T⇓(λ y, ¬ T y₀ y) → af T↑y₀.
  Proof.
    intros H.
    generalize (af_sum (af_True (sig (T y₀))) H).
    af rel morph (fun x y =>
        match x with
          | inl x => proj1_sig x = y
          | inr x => proj1_sig x = y
        end).
    + intros y; destruct (Ty₀_dec y) as [ Hy | Hy ].
      * exists (inl (exist _ y Hy)); auto.
      * exists (inr (exist _ y Hy)); auto.
    + intros [[]|[]] [[]|[]] ? ?; simpl; intros <- <-; tauto.
  Qed.

  Hypothesis (E_dec : ∀x, E x ∨ₜ ¬ E x).

  (** ev becomes a surjective relational morphism

          { x | ¬ E x } → { y | ¬ T y0 y }

      that transports AF from R⇓(¬ E)
      to T⇓(¬T y0).  *)

  Theorem af_quasi_morphism_decidable : af R → af T↑y₀.
  Proof.
    intros HR.
    apply af_not_af_lift.
    cut (af R⇓(λ x, ¬ E x)); [ | revert HR; apply af_af_sub_rel ].
    af rel morph (fun x y => ev (proj1_sig x) = proj1_sig y).
    + intros (y & Hy).
      assert (∃ₜ x, ana_rel y x ∧ₜ ¬ E x) as (x & H1 & H2).
      2: exists (exist _ x H2); auto.
      destruct (fin_choice_base E (λ x, ¬ E x) (ana_fin y)) as [ | (? & ? & ?) ]; eauto.
      destruct Hy; eauto.
    + intros [] [] [] []; simpl.
      intros <- <- ?.
      destruct ev_qmorph with (1 := H); tauto.
  Qed.

End af_quasi_morphism_decidable.


