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
  Require Import notations.

Require Import base wf_upto.

Inductive af_choice := af_choice_af | af_choice_full.
Definition af_status := option af_choice.

Module af_choice_notations.

  Notation "▢" := (@None _) (at level 0).
  Notation "▣" := (Some af_choice_full) (at level 0).
  Notation "◩" := (Some af_choice_af) (at level 0).

End af_choice_notations.

Import ListNotations lift_notations af_choice_notations.

Set Implicit Arguments.

#[local] Reserved Notation "⟪ a , b , c ⟫"
    (at level 0, no associativity, c at level 200, format "⟪ a , b , c ⟫").

#[local] Reserved Notation "⟪ a , b , c ⟫ₐ"
    (at level 0, no associativity, c at level 200, format "⟪ a , b , c ⟫ₐ").

Section afw.

  (** This stand for witnessed relation, ie a relation together with status information *)

  Definition srel₂ := sigT (λ X, rel₂ X).
  Definition wrel₂ := (af_status * srel₂)%type.

  Implicit Type wr : wrel₂.

  Notation "⟪ a , b , c ⟫" := (a,existT _ b c).

  (** Accepted witnessed relations, explaining the meaning of the witness *)

  Definition wrel₂_accepted wr : Base :=
    match wr with
    | ⟪▢,X,_⟫ => X → False      (* ▢ witnesses that X is not inhabited *)
    | ⟪▣,_,R⟫ => ∀ x y, R x y   (* ▣ witnesses that R is full *)
    | ⟪◩,_,R⟫ => af R           (* ◩ witnesses that R is almost full *)
    end.

  Notation "⟪ a , b , c ⟫ₐ" := (wrel₂_accepted ⟪a,b,c⟫).

  (** Accepted witnessed relations are af *)

  Fact wrel₂_accepted_af s X R : ⟪s,X,R⟫ₐ → af R.
  Proof.
    destruct s as [ [] | ]; simpl; auto.
    constructor 1; intros x; tauto.
  Qed.

  (** The "simpler" relation between wrel₂ is described by two rules
        a)   ⟪▢,_,_⟫ ≺ ⟪▣,_,_⟫    (empty simpler than full)
        b) ⟪◩,X,R↑x⟫ ≺ ⟪◩,X,R⟫    (lifting simplifies) *)

  Reserved Notation "x ≺ y" (at level 70).

  Inductive lt_wrel₂ : wrel₂ → wrel₂ → Base :=
    | lt_af_status_1 X R Y T :    ⟪▢,X,R⟫ ≺ ⟪▣,Y,T⟫
    | lt_af_status_2 X R x :    ⟪◩,X,R↑x⟫ ≺ ⟪◩,X,R⟫
  where "x ≺ y" := (lt_wrel₂ x y).

  Section inversions.

    Local Fact lt_wrel₂_inv1 wr1 wr2 :
           wr1 ≺ wr2
        → match wr1, wr2 with
          | ⟪s1,X1,R1⟫, ⟪s2,X2,R2⟫ =>
            match s1 with
            | ▢ => s2 = ▣
            | ▣ => False
            | ◩ => s2 = ◩ ∧ₜ ∃ₜ x (e : X1 = X2), eq_rect _ (λ X, rel₂ X) R1 _ e = R2↑x
            end
          end.
    Proof. intros [|? ? x]; auto; split; auto; exists x, eq_refl; auto. Qed.

    Local Fact lt_wrel₂_inv2 wr1 wr2 :
           wr1 ≺ wr2
         → match wr1, wr2 with
           | ⟪s1,X1,R1⟫, ⟪s2,X2,R2⟫ =>
             match s2 with
             | ▢ => False
             | ▣ => s1 = ▢
             | ◩ => True
             end
           end.
    Proof. intros []; auto. Qed.

    Local Fact lt_wrel₂_inv_empty s1 X1 R1 X2 R2 : ⟪s1,X1,R1⟫ ≺ ⟪▢,X2,R2⟫ → False.
    Proof. apply lt_wrel₂_inv2. Qed.

    Local Fact lt_wrel₂_inv_full s1 X1 R1 X2 R2 : ⟪s1,X1,R1⟫ ≺ ⟪▣,X2,R2⟫ → s1 = ▢.
    Proof. apply lt_wrel₂_inv2. Qed.

    Local Fact lt_wrel₂_inv_af X1 R1 s2 X2 R2 :
           ⟪◩,X1,R1⟫ ≺ ⟪s2,X2,R2⟫ → s2 = ◩ ∧ₜ ∃ₜ x (e : X1 = X2), eq_rect _ (λ X, rel₂ X) R1 _ e = R2↑x.
    Proof. apply lt_wrel₂_inv1. Qed.

  End inversions.

  (** The Σ-type of accepted witnessed af relations *)

  Local Definition afw := sigT wrel₂_accepted.

  (* Notation better than Definition because unification does not work well
     below otherwise, and we would need to unfold many times *)

  Notation afw_forget := (λ w, snd (projT1 w)).

  Local Definition lt_afw (x y : afw) := projT1 x ≺ projT1 y.

  Infix "<w" := lt_afw (at level 70).

  (** We show that lt_afw is wf_upto forgetting the witness & correctness proof *)

  Section lt_afw_wf_upto.

    (* Here we show that <w is well-founded up to forgetting the witness *)

    Local Fact lt_afw_empty : ∀ w r C, w <w existT _ (▢,r) C → False.
    Proof. intros ((?,(?,?)) & ?) (?,?) ?; simpl; apply lt_wrel₂_inv_empty. Qed.

    Local Fact lt_afw_full : ∀ s r C r' C', existT _ (s,r) C <w existT _ (▣,r') C' → s = ▢.
    Proof. intros ? (?,?) ? (?,?) ?; simpl; apply lt_wrel₂_inv_full. Qed.

    Local Fact lt_afw_lift X1 R1 C1 X2 R2 C2 :
          existT _ (◩,existT _ X1 R1) C1 <w existT _ (◩,existT _ X2 R2) C2
        ⇄ₜ ∃ₜ x (e : X1 = X2), eq_rect _ (λ X, rel₂ X) R1 _ e = R2↑x.
    Proof.
      split.
      + simpl; intros H.
        apply lt_wrel₂_inv_af in H as [ _ H ]; auto.
      + intros (x & -> & ?); simpl in *; subst; constructor.
    Qed.

    Variables (P : sigT (λ X, rel₂ X) → Base)
              (IHP : ∀w, (∀w', w' <w w → P (afw_forget w')) → P (afw_forget w)).

    (* We prove the property for empty X *)
    Local Fact HP_empty XR : wrel₂_accepted (▢,XR) → P XR.
    Proof.
      intros C.
      apply IHP with (w := existT _ (▢,_) C); auto.
      intros ? []%lt_afw_empty.
    Qed.

    Hint Resolve HP_empty : core.

    (* We prove the property for full R over X *)
    Local Fact HP_full XR : wrel₂_accepted (▣,XR) → P XR.
    Proof.
      simpl; intros C.
      apply IHP with (w := existT _ (▣,_) C); auto.
      intros ([] & ?) ->%lt_afw_full; simpl; auto.
    Qed.

    (* We prove the property for @af X R,
       and stop the induction by switching to
       witness ▣, via a call to HP_full.

       This is how the termination information of
       af X R is embedded into the witnessed pair.

       If we could not forget the witness, then
       one could not apply HP_full below hence
       once could not stop the recursive process. *)

    Hint Resolve HP_full : core.

    Local Fact HP_lift XR : wrel₂_accepted (◩,XR) → P XR.
    Proof.
      destruct XR as (X,R); simpl.
      induction 1 as [ R HR | R HR IHR ].
      + apply HP_full; simpl; auto.
      + apply IHP with (w := existT _ (◩,existT _ X R) (af_lift HR)); simpl; auto.
        intros (([[]|],(X',R')) & H1) H2; simpl.
        * apply lt_afw_lift in H2 as (x & -> & ?); simpl in *; subst; auto.
        * now apply HP_full.
        * now apply HP_empty.
    Qed.

    Hint Resolve HP_lift : core.

    Local Lemma lt_afw_wf_upto_rec : ∀w : afw, P (afw_forget w).
    Proof. intros (([[]|],(X,R)) & C); simpl; auto. Qed.

  End lt_afw_wf_upto.

  Local Theorem wf_upto_lt_afw : wf_upto afw_forget lt_afw.
  Proof. intros ? ? []; apply lt_afw_wf_upto_rec; auto. Qed.

End afw.

#[local] Notation "⟪ a , b , c ⟫" := (a,existT _ b c).
#[local] Notation "⟪ a , b , c ⟫ₐ" := (wrel₂_accepted ⟪a,b,c⟫).
#[local] Notation "x ≺ y" := (lt_wrel₂ x y) (at level 70).
#[local] Notation afw_witness := (λ w, fst (projT1 w)).
#[local] Notation afw_forget  := (λ w, snd (projT1 w)).

#[local] Reserved Notation "x '≺₂' y" (at level 70, no associativity, format "x  ≺₂  y").

Section af_easier_ind.

  Unset Elimination Schemes.

  Inductive af_easier : wrel₂ * wrel₂ → wrel₂ * wrel₂ → Base :=
    | af_easier_left wr₁ wr₁' wr₂ wr₂' :   wr₂ ≺ wr₂' → (wr₁,wr₂) ≺₂ (wr₁',wr₂')
    | af_easier_right wr₁ wr₁' wr₂ :       wr₁ ≺ wr₁' → (wr₁,wr₂) ≺₂ (wr₁',wr₂)
  where "p ≺₂ q" := (af_easier p q).

  Set Elimination Schemes.

  Local Fact af_easier_inv p q :
          p ≺₂ q
        → match p, q with
          | (wr₁,wr₂), (wr₁',wr₂') => wr₂ ≺ wr₂' ∨ₜ wr₁ ≺ wr₁' ∧ₜ wr₂ = wr₂'
          end.
  Proof. intros []; auto. Qed.

  Variables (Q : ∀{X}, rel₂ X → ∀{Y}, rel₂ Y → Base)
            (IHQ : ∀ s₃ X₃ R₃ s₄ X₄ R₄,
                       ⟪s₃,X₃,R₃⟫ₐ
                     → ⟪s₄,X₄,R₄⟫ₐ
                     → (∀ s₁ X₁ R₁ s₂ X₂ R₂,
                          ⟪s₁,X₁,R₁⟫ₐ
                        → ⟪s₂,X₂,R₂⟫ₐ
                        → (⟪s₁,X₁,R₁⟫,⟪s₂,X₂,R₂⟫) ≺₂ (⟪s₃,X₃,R₃⟫,⟪s₄,X₄,R₄⟫)
                        → Q R₁ R₂)
                     → Q R₃ R₄)
            (X : Type) (R : rel₂ X)
            (Y : Type) (T : rel₂ Y)
            .

  (* This is the easier (lexicographic) induction principle for two
     af relations, Base-bounded *)
  Theorem af_easier_induction : af R → af T → Q R T.
  Proof.
    intros HR HT.
    generalize (wf_upto_lex_prod wf_upto_lt_afw wf_upto_lt_afw); intros E.
    set (Q' (σ : srel₂ * srel₂) := Q (projT2 (snd σ)) (projT2 (fst σ))).
    set (s' := (existT _ ⟪◩,_,_⟫ HT, existT _ ⟪◩,_,_⟫ HR) : afw * afw).
    change (Q' (afw_forget (fst s'), afw_forget (snd s'))).
    apply (E Q') with (a := s'); unfold s'; clear E X R Y T HR HT s'.
    intros (((s3,(X3,R3)) & H3),((s4,(X4,R4)) & H4)) IH; unfold Q'; simpl in *.
    apply IHQ with s4 s3; auto.
    intros s1 X1 R1 s2 X2 R2 H1 H2 H.
    apply af_easier_inv in H.
    apply (IH (existT _ (s2,existT _ _ R2) H2,existT _ (s1,existT _ _ _) H1)).
    unfold lt_afw; simpl.
    destruct H as [ H | (H&E) ]; simpl; auto.
    right; split; auto.
    apply f_equal with (f := snd) in E; auto.
  Qed.

End af_easier_ind.

Module af_lex_notations.

  Notation "⟪ a , b , c ⟫ₐ" := (wrel₂_accepted ⟪a,b,c⟫).
  Notation "⟪ a , b , c ⟫ ≺ ⟪ x , y , z ⟫" := (lt_wrel₂ ⟪a,b,c⟫ ⟪x,y,z⟫).
  Notation "⟪ a , b , c | a' , b' , c' ⟫ ≺₂ ⟪ x , y , z | x' , y' , z' ⟫" :=
     (af_easier (⟪a,b,c⟫,⟪a',b',c'⟫) (⟪x,y,z⟫,⟪x',y',z'⟫)).

End af_lex_notations.


