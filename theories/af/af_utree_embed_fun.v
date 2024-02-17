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
  Require Import notations tactics utree.

From KruskalFinite
  Require Import finite choice.

Require Import base
               utree_embed
               af_lex af_quasi_morphism.

Import
    utree_notations utree_embeddings_notations
    af_notations af_lex_notations.

Set Implicit Arguments.

Section af_utree_nodes_fun.

  (** The proof here mimics (ie downgrades) the proof of Higman's theorem
      and does it using functions as morphism, not relations, which leads
      to shorter code but less versatile when dealing with Sigma types,
      when the quasi morphism is difficult or impossible to implement
      as a function *)

  Variables (sR : option af_choice) (X : Type) (R : rel₂ X) (HR : ⟪sR,X,R⟫ₐ)
            (sT : option af_choice) (Y : Type) (T : rel₂ Y) (HT : ⟪sT,Y,T⟫ₐ)
            (α : Y) (τ : utree X Y).

  Notation "▣" := af_choice_full.
  Notation "◩" := af_choice_af.

  Notation "⦗ x ⦘₁" := (inl x) (at level 1, format "⦗ x ⦘₁").
  Notation "⦗ y , t ⦘₂" := (inr (y,t)) (at level 1, format "⦗ y , t ⦘₂").

  Notation X' := (X+Y*utree X Y)%type.

  Inductive hl_rel_leaves : rel₂ X' :=
    | hl_rel_leaves_refl u v :
              R u v
            → hl_rel_leaves ⦗u⦘₁ ⦗v⦘₁
    | hl_rel_leaves_nest u s v t :
              T u v
            → (utree_embed R T)↑τ s t
            → hl_rel_leaves ⦗u,s⦘₂ ⦗v,t⦘₂.

  Notation R' := hl_rel_leaves.

  Hint Constructors R' : core.

  Local Fact hl_rel_leaves_inv x1' x2' :
           R' x1' x2'
         ↔ match x1', x2' with
           |⦗u⦘₁  , ⦗v⦘₁   => R u v
           |⦗u,s⦘₂, ⦗v,t⦘₂ => T u v ∧ (utree_embed R T)↑τ s t
           | _    , _      => False
           end.
  Proof.
    split.
    + destruct 1; auto.
    + revert x1' x2'; intros [ | [] ] [ | [] ]; auto; intros []; eauto.
  Qed.

  Let Y' c := match c with ◩ => Y | ▣ => Empty_set end.

  Let T' c : rel₂ (Y' c) :=
    match c return rel₂ (Y' c) with
    | ◩ => T↑α
    | ▣ => ⊥₂  (* anything works here because Y' ▣ is void *)
    end.

  (* The evaluation function, hev c : utree X' (Y' c) -> utree X Y
     A bit of dependent pattern matching to define hev ◩/▣ simultaneously *)
  Fixpoint hev c (t' : utree X' (Y' c)) : utree X Y :=
    match t' with
    | ⟨⦗x⦘₁⟩₀   => ⟨x⟩₀
    | ⟨⦗y,t⦘₂⟩₀ => ⟨y|t⟩₁
    | ⟨y'|t'⟩₁  =>
      match c return Y' c → utree X' (Y' c) → utree X Y with
      | ◩ => fun y' t' => ⟨y'|hev ◩ t'⟩₁
      | ▣ => fun y' _  => match y' with end
      end y' t'
   end.

  Goal forall c x, hev c ⟨⦗x⦘₁⟩₀ = ⟨x⟩₀.               Proof. reflexivity. Qed.
  Goal forall c y t, hev c ⟨⦗y,t⦘₂⟩₀ = ⟨y|t⟩₁.         Proof. reflexivity. Qed.
  Goal forall y' t', hev ◩ ⟨y'|t'⟩₁ = ⟨y'|hev ◩ t'⟩₁.  Proof. reflexivity. Qed.

  (* ana(lysis) is the reverse of evalutation *)
  Notation ana := (fun c t t' => hev c t' = t).

  Section analysis.

    Local Fact analysis_leaf c x t' : ana c ⟨x⟩₀ t' ↔ ⟨⦗x⦘₁⟩₀ = t'.
    Proof.
      split.
      + destruct t' as [ [ x' | [y t] ] | ]; simpl; intros H; try easy.
        * inversion H; auto.
        * now destruct c.
      + now intros <-.
    Qed.

    Local Fact analysis_node_f y t t' : ana ▣ ⟨y|t⟩₁ t' ↔ ⟨⦗y,t⦘₂⟩₀ = t'.
    Proof.
      split.
      + destruct t' as [ [|[]] | ]; simpl; inversion 1; auto; easy.
      + now intros <-.
    Qed.

    Local Fact analysis_node_l y t t' :
            ana ◩ ⟨y|t⟩₁ t' ↔ ⟨⦗y,t⦘₂⟩₀ = t'
                            ∨ ∃t'', ⟨y|t''⟩₁ = t' ∧ ana ◩ t t''.
    Proof.
      split.
      + now destruct t' as [ [|[]] | ]; simpl; inversion 1; eauto.
      + now intros [ <- | (? & <- & <-) ].
    Qed.

  End analysis.

  Local Lemma analysis_fin c t : fin (ana c t).
  Proof.
    induction t as [ x | y t IHt ].
    + finite eq (analysis_leaf _ _).
    + destruct c.
      * finite eq (analysis_node_l _ _).
      * finite eq (analysis_node_f _ _).
  Qed.

  Hint Resolve analysis_fin : core.

  (** Remember than ⟨α|τ⟩₁ is the tree by which (utree_embed R T) is lifted

      A tree of utree X' (Y' c) is disappointing
         1) if its root node is T-above α (when c = ◩, otherwise Y' ▣ is void)
      or 2) if it embeds τ

    *)

  Infix "≼" := (utree_embed R T) (at level 70).

  Notation "r '≼[' c ']' t" := (utree_embed R' (T' c) r t) (at level 70, format "r  ≼[ c ]  t").

  Inductive disapointing : ∀c, utree X' (Y' c) → Prop :=
    | disapointing_cons y t :   T α y → disapointing ◩ ⟨y|t⟩₁
    | disapointing_nest c y t : τ ≼ t → disapointing c ⟨⦗y,t⦘₂⟩₀.

  Hint Constructors disapointing : core.

  Notation D := disapointing.

  Local Fact disapointing_inv c t' :
           D c t'
         ↔ match t' with
           | ⟨x'⟩₀  => ∃ y t, x' = ⦗y,t⦘₂ ∧ τ ≼ t
           | ⟨y|_⟩₁ =>
             match c return Y' c → Prop with
             | ◩ => T α
             | ▣ => ⊥₁
             end y
           end.
  Proof.
    split.
    + induction 1 as [ | [] ]; eauto.
    + destruct t' as [ [] | ].
      * now intros (? & ? & ? & _).
      * intros (? & ? & -> & ?); auto.
      * now destruct c; auto.
  Qed.

  Local Definition has_disapointing c t := ∃s, s ≤ut t ∧ D c s.

  (* Exceptional *)

  Notation E := has_disapointing.

  Local Fact disap_has_disap : D ⊆₂ E.
  Proof. intros ? t; exists t; auto with utree_db. Qed.

  Local Fact sub_utree_has_disap c s t : s ≤ut t → E c s → E c t.
  Proof. intros ? (w & ? & ?); exists w; eauto with utree_db. Qed.

  Hint Resolve disap_has_disap
               sub_utree_has_disap : core.

  Local Lemma hev_quasi_morphism c r t :
         r ≼[c] t → hev c r ≼ hev c t ∨ E c r.
  Proof.
    induction 1 as [ x1 x2 H1
                   |    t1' y2 t2' H1 IH1
                   | y1 t1' y2 t2' H1 H2 IH2 ].
    + destruct H1 as [ | ? ? ? ? ? [] ]; simpl; eauto with utree_db.
    + destruct IH1; eauto.
      now destruct c; simpl in *; eauto with utree_db.
    + destruct IH2; eauto with utree_db.
      destruct c; simpl in *; destruct H1; eauto with utree_db.
  Qed.

  (* We assume sT is not empty/▢ and
     we freeze c such that Some c = sT *)

  Hypothesis HsT : sT ≠ None.

  Section af_choice.

    Local Fact af_choice_sT_pwc : { c | sT = Some c }.
    Proof. destruct sT; try easy; eauto. Qed.

    Local Definition af_choice_sT := proj1_sig af_choice_sT_pwc.

    Local Fact af_choice_sT_spec : sT = Some af_choice_sT.
    Proof. apply (proj2_sig af_choice_sT_pwc). Qed.

  End af_choice.

  Notation c := af_choice_sT.

  Section only_improper_analyses.

    (* A proper analysis of t an analysis t' (ie hev c t' = t)
       which does not contain a disapointing subtree

       A tree has only improper analyses if each of its analysis
       contains a disapointing sub-tree, ie it has no proper analysis *)

    (* Every analysis of t is exceptional *)
    Let E' t := (ana c t ⊆₁ E c).

    (* when a tree with only improper analyses is analysed by a leaf
       then this leaf is disapointing *)

    Local Fact E_leaf_D_leaf x' : E c ⟨x'⟩₀ → D c ⟨x'⟩₀.
    Proof.
      intros (s & H1 & H2).
      apply sub_utree_inv_right in H1 as [ -> | [] ]; auto.
    Qed.

    Hint Resolve E_leaf_D_leaf : core.

    Local Fact E'_ana_leaf x' t : E' t → ana c t ⟨x'⟩₀ → D c ⟨x'⟩₀.
    Proof. now intros H1 H2%H1%E_leaf_D_leaf. Qed.

    (* leaves ⟨_⟩₀ cannot have only exceptional analyses *)

    Local Fact E'_leaf_False x : E' ⟨x⟩₀ → False.
    Proof.
      intros H.
      apply E'_ana_leaf with (x' := ⦗x⦘₁) in H; auto.
      now apply disapointing_inv in H as (? & ? & ? & _).
    Qed.

    (* A disapointing leaf ⟨⦗y,_⦘₂⟩₀ with T α y embeds ⟨α|τ⟩₁ *)

    Local Fact disap_leaf_embed y t : D c ⟨⦗y,t⦘₂⟩₀ → T α y → ⟨α|τ⟩₁ ≼ ⟨y|t⟩₁.
    Proof.
      intros Ht Hy.
      apply disapointing_inv in Ht as (? & ? & E & Ht).
      inversion E; subst; auto with utree_db.
    Qed.

    Hint Resolve disap_leaf_embed : core.

    Local Fact E'_node_embed y t : E' ⟨y|t⟩₁ → T α y → ⟨α|τ⟩₁ ≼ ⟨y|t⟩₁.
    Proof.
      intros Ht H.
      apply (@E'_ana_leaf ⦗y,t⦘₂) in Ht; eauto.
    Qed.

    (* E' hereditary property *)

    Local Fact E'_hereditary y' s t :
            E' t
          → (∀s', ana c s s' → ana c t ⟨y'|s'⟩₁)
          → E' s ∨ ∃s', ana c s s' ∧ D c ⟨y'|s'⟩₁.
    Proof.
      intros H1 H2.
      apply fin_choice; auto.
      intros s' Hs'.
      destruct (H1 _ (H2 _ Hs')) as (u & H3 & H4).
      apply sub_utree_inv_right in H3 as [ -> | H3 ]; auto.
      left; exists u; auto.
    Qed.

    (** This property is similar to
             1) intercalate_any_vec_fall2
         and 2) intercalate_any_vec_embed

        By induction on t using HPQ0/HPQ1 above
        which are finitary choice principles
     *)

    (* If every analysis of t is exceptional that t embeds ⟨α|τ⟩₁ *)
    Local Lemma E'_embed t : E' t → ⟨α|τ⟩₁ ≼ t.
    Proof.
      generalize af_choice_sT_spec; intros Hc.
      induction t as [ x | y t IHt ]; intros Ht.
      + (* leaves have proper (non-exceptional) analyses *)
        apply E'_leaf_False in Ht as [].
      + generalize E'_hereditary E'_node_embed; destruct c; intros L1 L2.
        * (* if c = ◩, nodes *)
          destruct (L1 y t _ Ht) as [ | (t' & H1 & H2) ]; eauto with utree_db.
          - now intros ? <-.
          - apply disapointing_inv in H2; eauto.
        * (* if c = ▣, T is full *)
          rewrite Hc in HT; simpl in HT; auto.
    Qed.

  End only_improper_analyses.

  Hypotheses (IHτ : af (utree_embed R T)↑τ)

             (IHRT : ∀ sR' X' R' sT' Y' T',
                        ⟪sR',X',R'⟫ₐ
                      → ⟪sT',Y',T'⟫ₐ
                      → ⟪sR',X',R'|sT',Y',T'⟫ ≺₂ ⟪sR,X,R|sT,Y,T⟫
                      → af (utree_embed R' T')).

  Section higman'_af.

    Local Fact R_af : af R. Proof. now apply wrel₂_accepted_af in HR. Qed.
    Local Fact T_af : af T. Proof. now apply wrel₂_accepted_af in HT. Qed.

    (* Sum and product below by Ramsey's theorem *)

    Local Fact R'_af : af R'.
    Proof.
      generalize (af_sum R_af (af_product T_af IHτ)).
      apply af_mono.
      intros [|[]] [|[]]; simpl; auto; try easy.
      intros []; auto.
    Qed.

    Let sR' := (Some ◩).
    Let sT' := match c with ◩ => Some ◩ | ▣ => None end.

    Local Fact correct_R' : ⟪sR',X',R'⟫ₐ.
    Proof. exact R'_af. Qed.

    Local Fact correct_T' : ⟪sT',Y' c,T' c⟫ₐ.
    Proof.
      unfold sT'; destruct c; simpl; try easy.
      apply af_inv, T_af.
    Qed.

    Local Fact lesser : ⟪Some ◩,X',R'|sT',Y' c,T' c⟫ ≺₂ ⟪sR,X,R|sT,Y,T⟫.
    Proof.
      generalize af_choice_sT_spec; intros Hc.
      unfold sT'; constructor 1; rewrite Hc.
      destruct c; simpl; constructor.
    Qed.

    Hint Resolve correct_R' correct_T' lesser : core.

    Local Fact higman'_af : af (utree_embed R' (T' c)).
    Proof. apply IHRT with (sR' := sR') (sT' := sT'); auto. Qed.

  End higman'_af.

  Hint Resolve hev_quasi_morphism E'_embed : core.

  Theorem af_utree_nodes : af (utree_embed R T)↑⟨α|τ⟩₁.
  Proof.
    generalize higman'_af.
    af quasi morph (hev c) (E c); eauto.
  Qed.

End af_utree_nodes_fun.

