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
  Require Import utree.

From KruskalFinite
  Require Import finite choice.

Require Import base
               utree_embed
               af_lex af_quasi_morphism.

Import utree_notations utree_embeddings_notations
       af_notations af_lex_notations.

Set Implicit Arguments.

Section af_utree_nodes_rel.

  Notation "▣" := af_choice_full.
  Notation "◩" := af_choice_af.

  (** This proof take the one in "af_utree_embed_fun.v"
      as a reference but modifies it by using
      an evaluation relation instead of an
      evaluation map/function.

      It is only commented wrt the difference with
      the reference one over graph vs function.

      For detailed comments about how the proof works,
      refer to the reference one *)

  Variables (sR : _) (X : _) (R : rel₂ _) (HR : ⟪sR,X,R⟫ₐ)
            (sT : _) (Y : _) (T : rel₂ _) (HT : ⟪sT,Y,T⟫ₐ)
            (α : Y) (τ : utree X Y).

  Let X' := (X+Y*utree X Y)%type.

  Notation "⦗ x ⦘₁" := (inl x) (at level 1, format "⦗ x ⦘₁").
  Notation "⦗ y , t ⦘₂" := (inr (y,t)) (at level 1, format "⦗ y , t ⦘₂").

  Inductive hig_rel_leaves : rel₂ X' :=
    | hig_rel_leaves_refl u v :
              R u v
            → hig_rel_leaves ⦗u⦘₁ ⦗v⦘₁
    | hig_rel_leaves_nest u s v t :
              T u v
            → (utree_embed R T)↑τ s t
            → hig_rel_leaves ⦗u,s⦘₂ ⦗v,t⦘₂.

  Hint Constructors hig_rel_leaves : core.

  Notation R' := hig_rel_leaves.

  Local Fact hig_rel_leaves_inv x1' x2' :
           R' x1' x2'
         ↔ match x1', x2' with
           | ⦗u⦘₁, ⦗v⦘₁ => R u v
           | ⦗u,s⦘₂, ⦗v,t⦘₂ => T u v ∧ (utree_embed R T)↑τ s t
           | _, _ => False
           end.
  Proof.
    split.
    + destruct 1; auto.
    + revert x1' x2'; intros [ | [] ] [ | [] ]; auto; intros []; eauto.
  Qed.

  Let Y' c :=
    match c with
    | ◩ => Y
    | ▣ => Empty_set
    end.

  Let T' c : rel₂ (Y' c) :=
    match c return rel₂ (Y' c) with
    | ◩ => T↑α
    | ▣ => ⊥₂
    end.

  Infix "≼" := (utree_embed R T) (at level 70).
  Notation "r '≼[' c ']' t" := (utree_embed R' (T' c) r t) (at level 70, format "r  ≼[ c ]  t").

  Reserved Notation "a '-[' c ']->' b" (at level 70, format "a  -[ c ]->  b").

  (* The evaluation map that unpacks compound nodes, described as a relation
     (ie a graph), not as a (Coq) function *)
  Inductive ev_graph : ∀c, utree X' (Y' c) → utree X Y → Prop :=
    | in_ev_graph_0 c x :        ⟨⦗x⦘₁⟩₀   -[c]-> ⟨x⟩₀
    | in_ev_graph_1 c y t :      ⟨⦗y,t⦘₂⟩₀ -[c]-> ⟨y|t⟩₁
    | in_ev_graph_2 y s t :              s -[◩]-> t
                                  → ⟨y|s⟩₁ -[◩]-> ⟨y|t⟩₁
  where "t' -[ c ]-> t" := (ev_graph c t' t).

  Hint Constructors ev_graph : core.

  Section inversion_lemmas.

    (** We prove iff inversion lemmas to be sure not to forget information
        Notice that inversion lemmas are usually easy/trivial to prove but
        can be somewhat tricky to write down so that they properly type,
        eg see dependent pattern matching below *)

    Local Fact ev_graph_left_inv c t' t :
         t' -[c]-> t
       ↔ match t' with
         | ⟨⦗x⦘₁⟩₀   => t = ⟨x⟩₀
         | ⟨⦗y,s⦘₂⟩₀ => t = ⟨y|s⟩₁
         | ⟨y|s'⟩₁  =>
           match c return Y' c → utree X' (Y' c) → Prop with
           | ◩ => λ y s', ∃s, t = ⟨y|s⟩₁ ∧ s' -[◩]-> s
           | ▣ => λ _ _ , False
           end y s'
         end.
    Proof.
      split.
      + induction 1 as [ [] | [] | ]; eauto.
      + revert t'; intros [ [ | [] ] | ].
        1,2: intros ->; auto.
        destruct c; try tauto.
        intros (? & -> & ?); auto.
    Qed.

    Local Fact ev_graph_right_inv c t' t :
          t' -[c]-> t
        ↔ match c, t return utree X' (Y' c) → Prop with
          | ▣, ⟨x⟩₀   => λ t', t' = ⟨⦗x⦘₁⟩₀
          | ▣, ⟨y|s⟩₁ => λ t', t' = ⟨⦗y,s⦘₂⟩₀
          | ◩, ⟨x⟩₀   => λ t', t' = ⟨⦗x⦘₁⟩₀
          | ◩, ⟨y|s⟩₁ => λ t', t' = ⟨⦗y,s⦘₂⟩₀ ∨ ∃s', t' = ⟨y|s'⟩₁ ∧ s' -[◩]-> s
          end t'.
    Proof.
      split.
      + induction 1 as [ [] | [] | ]; eauto.
      + revert t; destruct c; intros [].
        1,3,4: intros ->; constructor.
        intros [ -> | (? & -> & ?) ]; auto.
    Qed.

  End inversion_lemmas.

  Tactic Notation "ev" "left" "inv" hyp(H) :=
    match type of H with
      | ⟨⦗_⦘₁⟩₀ -[_]-> _   => apply ev_graph_left_inv in H as ->
      | ⟨⦗_,_⦘₂⟩₀ -[_]-> _ => apply ev_graph_left_inv in H as ->
      | ⟨_|_⟩₁ -[◩]-> ?x   => let t := fresh in
                              apply ev_graph_left_inv in H as (t & -> & H);
                                rename t into x
      | ⟨_|_⟩₁ -[▣]-> ?x   => apply ev_graph_left_inv in H as []
      | ⟨_|_⟩₁ -[?c]-> ?x  => let t := fresh in
                              apply ev_graph_left_inv in H; revert H;
                                destruct c; [ intros (t & -> & H) | intros [] ];
                                rename t into x
    end.

  (* The graph describes a functional and strongly total relation *)
  Local Lemma ev_graph_fun c t' t₁ t₂ : t' -[c]-> t₁ → t' -[c]-> t₂ → t₁ = t₂.
  Proof.
    intros H; revert H t₂.
    induction 1; intros ? G; ev left inv G; auto.
    f_equal; auto.
  Qed.

  Local Lemma ev_graph_total c t' : { t | t' -[c]-> t }.
  Proof.
    induction t' as [ [ x | (y,t) ] | y t' (t & Ht) ].
    + exists ⟨x⟩₀; auto.
    + exists ⟨y|t⟩₁; auto.
    + destruct c; simpl in *.
      * exists ⟨y|t⟩₁; auto.
      * destruct y.
  Qed.

  Notation ana c := (λ t t', t' -[c]-> t).

  Section analysis_cases.

    Local Fact analysis_leaf c x t' :
        ana c ⟨x⟩₀ t' ↔ ⟨⦗x⦘₁⟩₀ = t'.
    Proof.
      split.
      + intros ?%ev_graph_right_inv; now destruct c.
      + intros <-; auto.
    Qed.

    Local Fact analysis_node_full y t t' :
        ana ▣ ⟨y|t⟩₁ t' ↔ ⟨⦗y,t⦘₂⟩₀ = t'.
    Proof.
      split.
      + now intros ?%ev_graph_right_inv.
      + intros <-; auto.
    Qed.

    Local Fact analysis_node_lift y t t' :
        ana ◩ ⟨y|t⟩₁ t' ↔ ⟨⦗y,t⦘₂⟩₀ = t'
                         ∨ ∃t'', ⟨y|t''⟩₁ = t' ∧ ana ◩ t t''.
    Proof.
      split.
      + intros ?%ev_graph_right_inv; firstorder.
      + intros [ <- | (? & <- & ?) ]; auto.
    Qed.

  End analysis_cases.

  (* The reverse of the evaluation graph (ie the analysis) is finitary *)
  Local Lemma ev_graph_inv_fin c t : fin (ana c t).
  Proof.
    induction t as [ x | y t IHt ].
    + finite eq (analysis_leaf _ _).
    + destruct c.
      * finite eq (analysis_node_lift _ _).
      * finite eq (analysis_node_full _ _).
  Qed.

  Inductive disapointing : ∀c, utree X' (Y' c) → Prop :=
    | disapointing_cons y t :   T α y → disapointing ◩ ⟨y|t⟩₁
    | disapointing_nest c y t : τ ≼ t → disapointing c ⟨⦗y,t⦘₂⟩₀.

  Notation D' := disapointing.

  Hint Constructors disapointing : core.

  Fact disapointing_inv c t' :
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
    + induction 1; auto; destruct c; eauto.
    + destruct t' as [ [ x | p ] | y t' ].
      * now intros (? & ? & ? & _).
      * intros (y & t & -> & H); auto.
      * destruct c; auto; tauto.
  Qed.

  Local Definition has_disapointing c t := (λ s, s ≤ut t) ⧫ D' c.

  Notation E' := has_disapointing.

  Local Fact disap_has_disap c : D' c ⊆₁ E' c.
  Proof. intros t; exists t; auto with utree_db. Qed.

  Local Fact sub_utree_has_disap c s t : s ≤ut t → E' c s → E' c t.
  Proof. intros ? (w & ? & ?); exists w; eauto with utree_db. Qed.

  Hint Resolve ev_graph_inv_fin
               disap_has_disap
               sub_utree_has_disap : core.

  (* By induction on the utree_embed predicate and
     then left inversion on -[c]->, and also on R' *)
  Local Lemma ev_quasi_morphism c t1' t2' t1 t2 :
         t1' ≼[c] t2'
       → t1' -[c]-> t1
       → t2' -[c]-> t2
       → t1 ≼ t2 ∨ E' c t1'.
  Proof.
    intros H1 H2 H3; revert H1 t1 t2 H2 H3.
    induction 1 as [ x1 x2 H1
                   |    t1' y2 t2' H1 IH1
                   | y1 t1' y2 t2' H1 H2 IH2 ]; intros t1 t2 G1 G2.
    + destruct H1 as [ | ? ? ? ? ? [] ];
        ev left inv G1; ev left inv G2; auto with utree_db.
    + ev left inv G2.
      destruct (IH1 _ _ G1 G2); auto with utree_db.
    + ev left inv G1; ev left inv G2.
      specialize (IH2 _ _ G1 G2).
      revert H1 IH2; intros [] []; eauto with utree_db.
  Qed.

  Notation E c t := (ana c t ⊆₁ E' c).

  Section exceptional_vs_embedding.

    Local Remark embed_exceptional c t : ⟨α|τ⟩₁ ≼ t → E c t.
    Proof.
      intros H t' Ht'; revert Ht' H; simpl.
      induction 1 as [ c x | c y t | y s t H IH ].
      + now intros ?%utree_embed_inv_10.
      + intros [ | [] ]%utree_embed_inv_11;
          exists ⟨⦗y,t⦘₂⟩₀; eauto with utree_db.
      + intros [ (v & [])%IH | [] ]%utree_embed_inv_11.
        * exists v; eauto with utree_db.
        * exists ⟨y|s⟩₁; eauto with utree_db.
    Qed.

    Local Fact E'_D'_leaf c x' : E' c ⟨x'⟩₀ → D' c ⟨x'⟩₀.
    Proof. now intros (? & [ -> | [] ]%sub_utree_inv_right & ?). Qed.

    Local Fact E_D'_leaf c x' t : E c t → ana c t ⟨x'⟩₀ → D' c ⟨x'⟩₀.
    Proof. now intros Ht (? & [ -> | [] ]%sub_utree_inv_right & Hs)%Ht. Qed.

    Local Lemma E_leaf_False c x : E c ⟨x⟩₀ → False.
    Proof. now intros (? & ? & ? & _)%(@E_D'_leaf _ ⦗x⦘₁)%disapointing_inv; auto. Qed.

    Local Fact D'_leaf_embed c y t : D' c ⟨⦗y,t⦘₂⟩₀ → T α y → ⟨α|τ⟩₁ ≼ ⟨y|t⟩₁.
    Proof. intros (? & ? & [=] & Ht)%disapointing_inv Hy; subst; auto with utree_db. Qed.

    Hint Resolve D'_leaf_embed : core.

    Local Fact E_node_embed c y t : E c ⟨y|t⟩₁ → T α y → ⟨α|τ⟩₁ ≼ ⟨y|t⟩₁.
    Proof. intros Ht%(@E_D'_leaf _ ⦗y,t⦘₂) H; eauto. Qed.

    Local Fact E_hereditary c y s t :
          E c t
        → (∀ s', ana c s s' → ana c t ⟨y|s'⟩₁)
        → E c s
        ∨ ana c s ⧫ λ s', D' c ⟨y|s'⟩₁.
    Proof.
      intros Ht Hs.
      apply fin_choice; auto; intros s' Hs'.
      destruct (Ht _ (Hs _ Hs')) as (u & Hu & ?).
      apply sub_utree_inv_right in Hu as [ -> | ]; eauto.
    Qed.

    Local Lemma E_embed c t : 
          (c = ▣ → ∀ y₁ y₂, T y₁ y₂)
        → E c t
        → ⟨α|τ⟩₁ ≼ t.
    Proof.
      intros Hc.
      induction t as [ x | y t IHt ]; intros Ht.
      + apply E_leaf_False in Ht as [].
      + destruct c.
        * destruct (@E_hereditary ◩ y t _ Ht) as [ | (t' & H1 & H2) ]; eauto with utree_db.
          apply disapointing_inv in H2.
          apply (@E_node_embed ◩); auto.
        * apply (@E_node_embed ▣); auto.
    Qed.

  End exceptional_vs_embedding.

  Section af_choice.

    Local Definition af_choice_sT_pwc : { c | sT = Some c }.
    Proof. destruct sT; try easy; eauto. Qed.

    Local Definition af_choice_sT := proj1_sig af_choice_sT_pwc.

    Local Fact af_choice_sT_spec : sT = Some af_choice_sT.
    Proof. apply (proj2_sig af_choice_sT_pwc). Qed.

  End af_choice.

  Notation c₀ := af_choice_sT.
  Notation Hc₀ := af_choice_sT_spec. (* sT = Some c₀ *)

  Local Lemma exceptional_embed t : E c₀ t → ⟨α|τ⟩₁ ≼ t.
  Proof.
    apply E_embed; intros E.
    generalize HT.
    rewrite Hc₀, E; trivial.
  Qed.

  Local Remark exceptional_iff_embed t : E c₀ t ↔ ⟨α|τ⟩₁ ≼ t.
  Proof. split; [ apply exceptional_embed | apply embed_exceptional ]. Qed.

  Hypotheses (IHτ : af (utree_embed R T)↑τ)

             (IHRT : ∀ sR' X' R' sT' Y' T',
                        ⟪sR',X',R'⟫ₐ
                      → ⟪sT',Y',T'⟫ₐ
                      → ⟪sR',X',R'|sT',Y',T'⟫ ≺₂ ⟪sR,X,R|sT,Y,T⟫
                      → af (utree_embed R' T')).

  Section RT'_af.

    Local Fact R_af : af R.  Proof. now apply wrel₂_accepted_af in HR. Qed.
    Local Fact T_af : af T.  Proof. now apply wrel₂_accepted_af in HT. Qed.

    Local Fact R'_af : af R'.
    Proof.
      generalize (af_sum R_af (af_product T_af IHτ)).
      apply af_mono.
      intros [|[]] [|[]]; simpl; auto; try easy.
      intros []; auto.
    Qed.

    Let sR' := (Some ◩).
    Let sT' := match c₀ with ◩ => Some ◩ | ▣ => None end.

    Local Fact correct_R' : ⟪sR',X',R'⟫ₐ.
    Proof. exact R'_af. Qed.

    Local Fact correct_T' : ⟪sT',Y' c₀,T' c₀⟫ₐ.
    Proof.
      unfold sT'; destruct c₀; simpl; try easy.
      apply af_inv, T_af.
    Qed.

    Local Fact RT'_lesser_RT : ⟪Some ◩,X',R'|sT',Y' c₀,T' c₀⟫ ≺₂ ⟪sR,X,R|sT,Y,T⟫.
    Proof.
      unfold sT'; constructor 1; rewrite Hc₀.
      destruct c₀; simpl; constructor.
    Qed.

    Hint Resolve correct_R' correct_T' RT'_lesser_RT : core.

    Local Lemma RT'_af : af (utree_embed R' (T' c₀)).
    Proof. eapply IHRT; eauto. Qed.

  End RT'_af.

  Hint Resolve ev_graph_total
               ev_graph_fun
               ev_quasi_morphism
               exceptional_embed : core.

  Theorem af_utree_nodes : af (utree_embed R T)↑⟨α|τ⟩₁.
  Proof.
    generalize RT'_af.
    af quasi morph rel (ev_graph c₀) (E' c₀); eauto.
  Qed.

End af_utree_nodes_rel.

