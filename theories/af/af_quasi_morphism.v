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

Require Import base tactics list_fan fan combi_principle.

Import ListNotations lift_notations.

Set Implicit Arguments.

Section af_quasi_morphism.

  Variables (X Y : Type) (ev : X → Y).

  Notation ana_rel := (λ y x, ev x = y).

  Variables
            (* ev has finite inverse images *)
            (ana_fin : ∀y, fin (ana_rel y))

            (R : rel₂ X) (* abstracts the src embedding, eg higman' *)
            (E : rel₁ X) (* abstracts "exceptional" analyses, eg "has disappointing subtree" *)

            (T : rel₂ Y) (* abstracts the dst embedding, eg higman *)
            (y₀ : Y)     (* abstracts the tree by which T is lifted *)

            (* ev is a "quasi" morphism from R to T, ie. "up to" E *)
            (ev_qmorph : ∀ x₁ x₂, R x₁ x₂ → T (ev x₁) (ev x₂) ∨ E x₁)

            (* if no analysis of y avoids E then y must T-embed y0 *)
            (HET : ∀y, ana_rel y ⊆₁ E → T y₀ y).

            (** We want to conclude: af R → af T↑y₀ *)

  (* We construct the ana(lysis) function *)
  Local Definition ana y := proj1_sig (ana_fin y).

  Local Fact ana_spec x y : ev x = y ↔ x ∈ ana y.
  Proof. apply (proj2_sig (ana_fin _)). Qed.

  Local Fact Forall2_analysis_eq lx ly :
        Forall2 In lx (map ana ly) ↔ map ev lx = ly.
  Proof.
    rewrite Forall2_map_right, <- Forall2_eq, Forall2_map_left.
    apply Forall2_equiv; intros ? ?; rewrite ana_spec; tauto.
  Qed.

  Hint Resolve in_map in_or_app in_cons in_eq : core.

  (* If a list is R-good then its evaluation is T-good unless it meets E *)
  Local Fact ev_good_or_E lx :
         good R lx → good T (map ev lx) ∨ (λ x, x ∈ lx) ⧫ E.
  Proof.
    induction 1 as [ t2' t1' l H1 H2 | t1' l H IH ]; simpl.
    + destruct (ev_qmorph H2); eauto.
    + destruct IH as [ | (? & ? & ?) ]; simpl; eauto.
  Qed.

  (* A(nalyses) W(ell): all possible choice sequences of analyses are good *)
  Local Definition AW ly := Forall (good R) (list_fan (map ana ly)).

  (*  Alternative defn. could be Forall2 ana ly ⊆₁ good R *)
  Goal ∀ly, AW ly ↔ Forall2 ana_rel ly ⊆₁ good R.
  Proof.
    intros ly; unfold AW.
    rewrite Forall_forall.
    apply forall_equiv; intros lx.
    rewrite list_fan_spec; equiv auto.
    rewrite Forall2_map_right, Forall2_xchg.
    apply Forall2_equiv; intros ? ?.
    rewrite ana_spec; tauto.
  Qed.

  (* The critical proof: if ly AW for R then ly++[y₀] is good for T *)
  Local Lemma AW_good_snoc ly : AW ly → good T (ly++[y₀]).
  Proof.
    intros Hm; red in Hm.
    destruct list_combi_principle
      with (P := fun l => good T (map ev l))
           (B := E)
           (ll := map ana ly)
      as [ (lc & H1 & H2) | (a & H1 & H2) ].

    + (* Hypothesis for combi principle *)
      intros lx Hlx.
      rewrite Forall_forall in Hm.
      apply list_fan_spec, Hm in Hlx.
      now apply ev_good_or_E.

    + (* there is (choice) sequence of analyses lx of ly which maps
         to a good sequence, but lx maps to ly hence ly is good *)
      apply Forall2_analysis_eq in H1 as <-.
      apply good_app_right; auto.

    + (* there is an evaluation in ly of which all analyses are exceptional *)
      apply in_map_iff in H1 as (y & <- & H3).
      apply good_snoc with y; auto.
      apply HET.
      intro; rewrite ana_spec; auto.
  Qed.

  Hint Resolve AW_good_snoc : core.

  Local Corollary bar_AW_good_snoc ly : bar AW ly → bar (good T) (ly++[y₀]).
  Proof. induction 1; auto. Qed.

  Hypothesis (HR : af R).

  (* The bar formulation for the FAN theorem below *)
  Local Fact bar_goodR_nil : bar (good R) [].
  Proof. apply af_iff_bar_good_nil; auto. Qed.

  Hint Resolve bar_goodR_nil : core.

  (* By the FAN theorem, since R is af,
     all sequences will uniformly AW *)
  Local Fact bar_AW_nil : bar AW [].
  Proof.
    apply bar_map_inv
      with (f := ana)
           (Q := fun ll => Forall (good R) (list_fan ll)); auto.
    simpl; apply fan_on_list; auto.
  Qed.

  Theorem af_quasi_morphism : af T↑y₀.
  Proof.
    apply af_iff_bar_good_nil,
          bar_rel_lift,
          bar_AW_good_snoc,
          bar_AW_nil.
  Qed.

End af_quasi_morphism.

Check af_quasi_morphism.

Tactic Notation "af" "quasi" "morph" uconstr(f) uconstr(e) :=
  match goal with
    | |- af _ → af _ => apply af_quasi_morphism with (ev := f) (E := e)
  end.

