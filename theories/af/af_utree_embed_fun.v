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

Section af_utree_nodes.

  (** The proof here mimics (ie downgrades) the proof of Higman's theorem
      and does it using functions as morphism, not relations, which leads
      to shorter code but less versatile when dealing with Σ-types,
      when the quasi morphism is difficult or impossible to implement
      as a function. *)

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

  (* c := ◩ represents the situation where T on nodes of arity 1 is af
     c := ▣ represents the situation where T on nodes of arity 1 if full *) 

  Let Y' c := match c with ◩ => Y | ▣ => Empty_set end.

  Let T' c : rel₂ (Y' c) :=
    match c return rel₂ (Y' c) with
    | ◩ => T↑α
    | ▣ => ⊥₂  (* anything works here because Y' ▣ is void *)
    end.

  Infix "≼" := (utree_embed R T) (at level 70).
  Notation "r '≼[' c ']' t" := (utree_embed R' (T' c) r t) (at level 70, format "r  ≼[ c ]  t").

  (* The type utree X' (Y' ▣) := utree (X+Y*utree X Y) Empty_set
              utree X' (Y' ◩) := utree (X+Y*utree X Y) Y

     The relation R' on X+Y*utree X Y is R + T*(utree_embed R T)↑τ
     is AF by Ramsey and the induction hypotheses

     The relation T' ▣ := _ (anything) is AF because on the empty type
     The relation T' ◩ := T↑α is AF (it is smaller by IH because lifted from T) 

     The interesting case here is when ◩. In that case, the type for
     the leaf X' (arity 0) is augmented by a node of arity 1 and
     one subtree from that node. *)

  (** We build a quasi morphism hev c : utree X' (Y' c) → utree X Y 
     from the embedding ≼[c] to the lifted embedding ≼↑⟨α|τ⟩₁

      It describes the process of evaluation of tree in utree X' (Y' c)
      which consists in rebuilding the original tree from displaced
      information.

      A bit of dependent pattern matching to define hev ◩/▣ simultaneously *)

  Fixpoint hev c (t' : utree X' (Y' c)) : utree X Y :=
    match t' with
    | ⟨⦗x⦘₁⟩₀   => ⟨x⟩₀
    | ⟨⦗y,t⦘₂⟩₀ => ⟨y|t⟩₁
    | ⟨y'|t'⟩₁  =>
      match c return Y' c → utree X' (Y' c) → utree X Y with
      | ◩ => λ y' t', ⟨y'|hev ◩ t'⟩₁
      | ▣ => λ y' _ , match y' with end
      end y' t'
   end.

  (** These are the recursives equations that we want for the evaluation *)

  Goal ∀ c x,   hev c ⟨⦗x⦘₁⟩₀   = ⟨x⟩₀.            Proof. reflexivity. Qed.
  Goal ∀ c y t, hev c ⟨⦗y,t⦘₂⟩₀ = ⟨y|t⟩₁.          Proof. reflexivity. Qed.
  Goal ∀ y' t', hev ◩ ⟨y'|t'⟩₁  = ⟨y'|hev ◩ t'⟩₁.  Proof. reflexivity. Qed.

  (* ana(lysis) is the reverse of evaluation 

     an analysis of t : utree X Y is a t' : utree X' (Y' c)
     which evaluates to t. There are finitely many analyses
     of a given tree. *)
  Notation ana := (λ c t t', hev c t' = t).

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

  (* The evaluation function has finite inverse image *)
  Local Lemma analysis_fin c t : fin (ana c t).
  Proof.
    induction t as [ x | y t IHt ].
    + finite eq (analysis_leaf _ _).
    + destruct c.
      * finite eq (analysis_node_l _ _).
      * finite eq (analysis_node_f _ _).
  Qed.

  Hint Resolve analysis_fin : core.

  (** Remember that ⟨α|τ⟩₁ is the tree by which (utree_embed R T) is lifted

      A tree of utree X' (Y' c) is disappointing
         1) if it is a node which T-embeds α (when c = ◩, otherwise Y' ▣ is void)
      or 2) if it is a leaf which ≼-embeds τ (in its added information) _+ _*(utree X Y) *)

  Inductive disapointing : ∀c, utree X' (Y' c) → Prop :=
    | disapointing_cons y t :   T α y → disapointing ◩ ⟨y|t⟩₁
    | disapointing_nest c y t : τ ≼ t → disapointing c ⟨⦗y,t⦘₂⟩₀.

  Hint Constructors disapointing : core.

  Notation D' := disapointing.

  Local Fact disapointing_inv c t' :
           D' c t'
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

  Local Definition has_disapointing c t := ∃s, s ≤ut t ∧ D' c s.

  (* Exceptional is "has a dispointing sub-tree" *)
  Notation E' := has_disapointing.

  Local Fact disap_has_disap : D' ⊆₂ E'.
  Proof. intros ? t; exists t; auto with utree_db. Qed.

  Local Fact sub_utree_has_disap c s' t' : s' ≤ut t' → E' c s' → E' c t'.
  Proof. intros ? (w & ? & ?); exists w; eauto with utree_db. Qed.

  Hint Resolve disap_has_disap sub_utree_has_disap : core.

  (* hev c is a quasi morphism *)
  Local Lemma hev_quasi_morphism c s' t' :
         s' ≼[c] t' → hev c s' ≼ hev c t' ∨ E' c s'.
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

  Section af_choice.

    (* sT cannot be empty/▢ because α inhabits Y. *)

    (* We freeze c st sT = Some c *)
    Local Fact af_choice_sT_pwc : { c | sT = Some c }.
    Proof. destruct sT; [ eauto | now simpl in HT ]. Qed.

    Local Definition af_choice_sT := proj1_sig af_choice_sT_pwc.

    Local Fact af_choice_sT_spec : sT = Some af_choice_sT.
    Proof. apply (proj2_sig af_choice_sT_pwc). Qed.

  End af_choice.

  Notation c := af_choice_sT.

  Section only_improper_analyses.

    (* A proper analysis of t is an analysis t' (ie hev c t' = t)
       which does not contain a disapointing subtree.

       A tree has only improper analyses if all of its analyses
       contains a disapointing sub-tree, ie it has no proper analysis *)

    (* Every analysis of t is exceptional *)
    Let E t := (ana c t ⊆₁ E' c).

    (* When a tree with only improper analyses is analysed by a leaf
       then this leaf is disapointing *)
    Local Fact E'_leaf_D'_leaf x' : E' c ⟨x'⟩₀ → D' c ⟨x'⟩₀.
    Proof. now intros (? & [ -> | [] ]%sub_utree_inv_right & ?). Qed.
 
    Local Fact E_ana_leaf x' t : E t → ana c t ⟨x'⟩₀ → D' c ⟨x'⟩₀.
    Proof. now intros H1 H2%H1%E'_leaf_D'_leaf. Qed.

    (* Leaves ⟨_⟩₀ cannot have only exceptional analyses *)
    Local Fact E_leaf_False x : E ⟨x⟩₀ → False.
    Proof. now intros (? & ? & ? & _)%(@E_ana_leaf ⦗x⦘₁)%disapointing_inv; auto. Qed.

    (* A disapointing leaf ⟨⦗y,_⦘₂⟩₀ with T α y embeds ⟨α|τ⟩₁ *)
    Local Fact D'_leaf_embed y t : D' c ⟨⦗y,t⦘₂⟩₀ → T α y → ⟨α|τ⟩₁ ≼ ⟨y|t⟩₁.
    Proof. intros (? & ? & [=] & Ht)%disapointing_inv Hy; subst; auto with utree_db. Qed.

    Hint Resolve D'_leaf_embed : core.

    Local Fact E_node_embed y t : E ⟨y|t⟩₁ → T α y → ⟨α|τ⟩₁ ≼ ⟨y|t⟩₁.
    Proof. intros Ht%(@E_ana_leaf ⦗y,t⦘₂) H; eauto. Qed.

    (* E hereditary property *)
    Local Fact E_hereditary y' s t :
            E t
          → (∀s', ana c s s' → ana c t ⟨y'|s'⟩₁)
          → E s ∨ ∃s', ana c s s' ∧ D' c ⟨y'|s'⟩₁.
    Proof.
      intros H1 H2.
      apply fin_choice; auto.
      intros s' Hs'.
      destruct (H1 _ (H2 _ Hs')) as (u & H3 & H4).
      apply sub_utree_inv_right in H3 as [ -> | ]; eauto.
    Qed.

    (** This property is similar to
             1) intercalate_any_vec_fall2
         and 2) intercalate_any_vec_embed

        By induction on t using HPQ0/HPQ1 above
        which are finitary choice principles
     *)

    (* If every analysis of t is exceptional that t embeds ⟨α|τ⟩₁ *)
    Local Lemma E_embed t : E t → ⟨α|τ⟩₁ ≼ t.
    Proof.
      generalize af_choice_sT_spec; intros Hc.
      induction t as [ x | y t IHt ]; intros Ht.
      + (* leaves have proper (non-exceptional) analyses *)
        apply E_leaf_False in Ht as [].
      + generalize E_hereditary E_node_embed.
        destruct c; intros EH Ene.
        * (* if c = ◩, nodes *)
          destruct (EH y t _ Ht) as [ | (t' & H1 & H2) ]; eauto with utree_db.
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

  Section RT'_af.

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

    Local Fact RT'_lesser_RT : ⟪sR',X',R'|sT',Y' c,T' c⟫ ≺₂ ⟪sR,X,R|sT,Y,T⟫.
    Proof.
      generalize af_choice_sT_spec; intros Hc.
      unfold sT'; constructor 1; rewrite Hc.
      destruct c; simpl; constructor.
    Qed.

    Hint Resolve correct_R' correct_T' RT'_lesser_RT : core.

    Local Lemma RT'_af : af (utree_embed R' (T' c)).
    Proof. apply IHRT with (sR' := sR') (sT' := sT'); auto. Qed.

  End RT'_af.

  Hint Resolve hev_quasi_morphism E_embed : core.

  Theorem af_utree_nodes : af (utree_embed R T)↑⟨α|τ⟩₁.
  Proof.
    generalize RT'_af.
    af quasi morph (hev c) (E' c); eauto.
  Qed.

End af_utree_nodes.


