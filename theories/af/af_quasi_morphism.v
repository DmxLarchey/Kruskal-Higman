(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import Arith List Lia Utf8.

From KruskalTrees
  Require Import notations list_utils.

From KruskalFinite
  Require Import finite choice.

Require Import base tactics fan combi_principle.

Import ListNotations lift_notations.

Set Implicit Arguments.

Section af_quasi_morphism.

  Variables (X Y : Type) (ev : X → Y).

  Notation ana_rel := (λ y x, ev x = y).

  Variables (* ev has finite inverse images *)
            (ana_fin : ∀y, fin (ana_rel y))

            (R : rel₂ X) (* abstracts the src embedding, eg higman' *)
            (E : rel₁ X) (* abstracts "exceptional" analyses, eg "has disappointing subtree" *)

            (T : rel₂ Y) (* abstracts the dst embedding, eg higman *)
            (y₀ : Y)     (* abstracts the tree by which T is lifted *)

            (* ev is a "quasi" morphism from R to T, ie. "up to" E *)
            (ev_qmorph : ∀ x₁ x₂, R x₁ x₂ → T (ev x₁) (ev x₂) ∨ E x₁)

            (* if every analysis of y is exceptional then y must T-embed y0 *)
            (excep_embed : ∀y, ana_rel y ⊆₁ E → T y₀ y).

            (** We want to conclude: af R → af T↑y₀ *)

  (* We construct the ana(lysis) function *)
  Local Definition ana y := proj1_sig (ana_fin y).

  Local Fact ana_spec x y : ev x = y ↔ x ∈ ana y.
  Proof. apply (proj2_sig (ana_fin _)). Qed.

  Local Fact FAN_analysis_eq lx ly :
        FAN (map ana ly) lx ↔ map ev lx = ly.
  Proof.
    rewrite Forall2_map_right, <- Forall2_eq, Forall2_map_left.
    apply Forall2_equiv; intros ? ?; rewrite ana_spec; tauto.
  Qed.

  Hint Resolve in_map in_or_app in_cons in_eq : core.

  (* If a list is R-good then its evaluation is T-good unless it meets E 
     This extends the ev_qmorph property to good sequences *)
  Local Fact ev_good_or_exceptional lx :
         good R lx → good T (map ev lx) ∨ (λ x, x ∈ lx) ⧫ E.
  Proof.
    induction 1 as [ t2' t1' l H1 H2 | t1' l H IH ]; simpl.
    + destruct ev_qmorph with (1 := H2); eauto.
    + destruct IH as [ | (? & ? & ?) ]; simpl; eauto.
  Qed.

  (* A(nalyses) W(ell): all possible choice sequences of analyses are good *)
  Local Definition AW ly := FAN (map ana ly) ⊆₁ good R.

  (* The critical proof step: if ly Analyses Well then ly++[y₀] is good for T *)
  Local Lemma AW_good_lifted ly : AW ly → good T (ly++[y₀]).
  Proof.
    intros Hly; red in Hly.
    destruct list_combi_principle
      with (P := λ l, good T (map ev l))
           (B := E) (ll := map ana ly)
      as [ (lx & H1 & H2) | (a & H1 & H2) ].
    + (* Hypothesis for combi principle *)
      now intros lx Hlx%Hly%ev_good_or_exceptional.
    + (* there is (choice) sequence of analyses lx of ly which maps
         to a good sequence, but lx maps to ly hence ly is good *)
      apply FAN_analysis_eq in H1 as <-.
      now apply good_app_right.
    + (* there is an evaluation in ly of which all analyses are exceptional *)
      apply in_map_iff in H1 as (y & <- & H1).
      apply good_snoc with y, excep_embed; auto.
      now intros ? ?%ana_spec%H2.
  Qed.

  (* The previous results lifted to bar *)
  Local Corollary bar_AW_good_lifted ly : bar AW ly → bar (good T) (ly++[y₀]).
  Proof.
    intros Hly; apply bar_app.
    revert Hly; apply bar_mono, AW_good_lifted.
  Qed.

  Hypothesis (HR : af R).

  (* The bar formulation for the FAN theorem below *)
  Local Fact bar_goodR_nil : bar (good R) [].
  Proof. now apply af_iff_bar_good_nil. Qed.

  Hint Resolve good_skip bar_goodR_nil : core.

  (* By the FAN theorem, since R is af, all sequences
     will uniformly analyse well *)
  Local Lemma bar_AW_nil : bar AW [].
  Proof.
    apply bar_map_inv
      with (f := ana)
           (Q := λ ll, FAN ll ⊆₁ good R); auto.
    apply FAN_theorem; auto.
  Qed.

  Theorem af_quasi_morph_fun : af T↑y₀.
  Proof.
    apply af_iff_bar_good_nil, bar_rel_lift,
          bar_AW_good_lifted, bar_AW_nil.
  Qed.

End af_quasi_morphism.

Tactic Notation "af" "quasi" "morph" "fun" uconstr(f) uconstr(e) :=
  match goal with
  | |- af _ → af _ => apply af_quasi_morph_fun with (ev := f) (E := e)
  end.

Section af_quasi_morph.

  Variables (X Y : Type) (ea_rel : X → Y → Prop).

  Notation "x '⇝' y" := (ea_rel x y) (at level 70, no associativity, format "x ⇝ y").
  Notation ana_rel := (λ y x, x⇝y).

  Variables (ea_fun : ∀ x y₁ y₂, x⇝y₁ → x⇝y₂ → y₁ = y₂)
            (ea_total : ∀ x, { y | x⇝y })
            (ea_fin : ∀ y, fin (ana_rel y))
            (R : rel₂ X) (E : rel₁ X)
            (T : rel₂ Y) (y₀ : Y)
            (HRT : ∀ x₁ x₂ y₁ y₂, R x₁ x₂ → x₁⇝y₁ → x₂⇝y₂ → T y₁ y₂ ∨ E x₁)
            (HT : ∀ y, ana_rel y ⊆₁ E → T y₀ y).

  Let ev' x := proj1_sig (ea_total x).

  Local Fact ev'_spec x : x⇝ev' x.
  Proof. apply (proj2_sig _). Qed.

  Hint Resolve ev'_spec : core.

 Theorem af_quasi_morph_rel : af R → af T↑y₀.
  Proof.
    af quasi morph fun ev' E.
    + intros y.
      destruct (ea_fin y) as (l & Hl).
      exists l; intros x.
      rewrite <- Hl; split.
      * intros <-; auto.
      * apply ea_fun; auto.
    + intros x1 x2 []%(@HRT _ _ (ev' x1) (ev' x2)); auto.
    + intros y Hy; apply HT.
      intros x Hx; apply Hy.
      revert Hx; apply ea_fun; auto.
  Qed.

End af_quasi_morph.

Tactic Notation "af" "quasi" "morph" "rel" uconstr(f) uconstr(e) :=
  match goal with
  | |- af _ → af _ => apply af_quasi_morph_rel with (ea_rel := f) (E := e)
  end.


