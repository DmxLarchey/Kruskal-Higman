(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
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

Import
    utree_notations utree_embeddings_notations
    af_notations af_lex_notations.

Set Implicit Arguments.

Section af_utree_nodes_rel.

  (** The proof here mimics (ie downgrades) the proof of Higman's theorem
      using an evaluation relation, not a function *)

  Variables (sR : _) (X : Type) (R : rel₂ X) (sT : _) (Y : Type) (T : rel₂ Y)
            (HR : ⟪sR,X,R⟫ₐ) (HT : ⟪sT,Y,T⟫ₐ)
            (IHRT : ∀ sR' X' R' sT' Y' T',
                        ⟪sR',X',R'⟫ₐ
                      → ⟪sT',Y',T'⟫ₐ
                      → ⟪sR',X',R'|sT',Y',T'⟫ ≺₂ ⟪sR,X,R|sT,Y,T⟫
                      → af (utree_embed R' T'))

            (HsT : sT <> None)

            (α : Y) (τ : utree X Y)
            (IHτ : af (utree_embed R T)↑τ).

  Notation "▣" := af_choice_full.
  Notation "◩" := af_choice_af.

  Infix "≤ₑ" := (utree_embed R T) (at level 70).

  Notation "⦉ x ⦊₁" := (inl x) (at level 1, format "⦉ x ⦊₁").
  Notation "⦉ y , t ⦊₂" := (inr (y,t)) (at level 1, format "⦉ y , t ⦊₂").

  Notation sR' := (Some ◩) (only parsing).
  Notation X' := (X+Y*utree X Y)%type.

  Inductive hig_rel_leaves : rel₂ X' :=
    | hig_rel_leaves_refl u v :
              R u v
            → hig_rel_leaves ⦉u⦊₁ ⦉v⦊₁
    | hig_rel_leaves_nest u s v t :
              T u v
            → (utree_embed R T)↑τ s t
            → hig_rel_leaves ⦉u,s⦊₂ ⦉v,t⦊₂.

  Notation R' := hig_rel_leaves.

  Hint Constructors R' : core.

  Local Fact hig_rel_leaves_inv x1' x2' :
           R' x1' x2'
         ↔ match x1', x2' with
             | ⦉u⦊₁, ⦉v⦊₁ => R u v
             | ⦉u,s⦊₂, ⦉v,t⦊₂ => T u v ∧ (utree_embed R T)↑τ s t
             | _, _ => False
           end.
  Proof.
    split.
    + destruct 1; auto.
    + revert x1' x2'; intros [ | [] ] [ | [] ]; auto; intros []; eauto.
  Qed.

  Local Definition Y' c :=
    match c with
      | ◩ => Y
      | ▣ => Empty_set
    end.

  Local Definition T' c : rel₂ (Y' c) :=
    match c return rel₂ (Y' c) with
      | ◩ => T↑α
      | ▣ => ⊥₂
    end.

  Infix "≤ₐ" := (utree_embed R' (T' _)) (at level 70).

  Section higman'_af.

    Let R_af : af R.
    Proof. now apply wrel₂_accepted_af in HR. Qed.

    Let T_af : af T.
    Proof. now apply wrel₂_accepted_af in HT. Qed.

    Let R'_af : af R'.
    Proof.
      generalize (af_sum R_af (af_product T_af IHτ)).
      apply af_mono.
      intros [|[]] [|[]]; simpl; auto; try easy.
      intros []; auto.
    Qed.

    Variable (c : af_choice).

    Let sT' :=
      match c with
        | ◩ => Some ◩
        | ▣ => None
      end.

    Let correct : ⟪sT',Y' c,T' c⟫ₐ.
    Proof.
      unfold sT'; destruct c; simpl; try easy.
      apply af_inv; auto.
    Qed.

    Hypothesis Hc : sT = Some c.

    Let lesser : ⟪Some ◩,X',R'|sT',Y' c,T' c⟫ ≺₂ ⟪sR,X,R|sT,Y,T⟫.
    Proof.
      unfold sT'; constructor 1; rewrite Hc.
      destruct c; simpl; constructor.
    Qed.

    Local Fact higman'_af : af (utree_embed R' (T' c)).
    Proof. apply IHRT with (sR' := sR') (sT' := sT'); simpl; auto. Qed.

  End higman'_af.

  Hint Resolve higman'_af : core.

  (* The evaluation map that unpacks compound nodes, described as a relation
     (ie a graph), not as a (Coq) function *)

  Reserved Notation "a '-[' c ']->' b" (at level 70, format "a  -[ c ]->  b").

  Inductive hev_graph : ∀c, utree X' (Y' c) → utree X Y → Prop :=
    | in_hev_graph_0 c x :       ⟨⦉x⦊₁⟩₀   -[c]-> ⟨x⟩₀
    | in_hev_graph_1 c y t :     ⟨⦉y,t⦊₂⟩₀ -[c]-> ⟨y|t⟩₁
    | in_hev_graph_2 y s t :            s -[◩]-> t
                                 → ⟨y|s⟩₁ -[◩]-> ⟨y|t⟩₁
  where "t' -[ c ]-> t" := (hev_graph c t' t).

  Hint Constructors hev_graph : core.

  Section inversion_lemmas.

    (** We prove iff inversion lemmas to be sure not to forget information
        Notice that inversion lemmas are usually easy/trivial to prove but
        can be somewhat tricky to write down so that they properly type,
        eg see dependent pattern matching below *)

    Local Lemma hev_graph_left_inv c t' t :
         t' -[c]-> t
       ↔ match t' with
           | ⟨⦉x⦊₁⟩₀   => t = ⟨x⟩₀
           | ⟨⦉y,s⦊₂⟩₀ => t = ⟨y|s⟩₁
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

    Local Lemma hev_graph_right_inv c t' t :
          t' -[c]-> t
        ↔ match c, t return utree X' (Y' c) → Prop with
            | ▣, ⟨x⟩₀   => λ t', t' = ⟨⦉x⦊₁⟩₀
            | ▣, ⟨y|s⟩₁ => λ t', t' = ⟨⦉y,s⦊₂⟩₀
            | ◩, ⟨x⟩₀   => λ t', t' = ⟨⦉x⦊₁⟩₀
            | ◩, ⟨y|s⟩₁ => λ t', t' = ⟨⦉y,s⦊₂⟩₀ ∨ ∃s', t' = ⟨y|s'⟩₁ ∧ s' -[◩]-> s
          end t'.
    Proof.
      split.
      + induction 1 as [ [] | [] | ]; eauto.
      + revert t; destruct c; intros [].
        1,3,4: intros ->; constructor.
        intros [ -> | (? & -> & ?) ]; auto.
    Qed.

  End inversion_lemmas.

  Tactic Notation "hev" "left" "inv" hyp(H) :=
    match type of H with
      | ⟨⦉_⦊₁⟩₀ -[_]-> _   => apply hev_graph_left_inv in H as ->
      | ⟨⦉_,_⦊₂⟩₀ -[_]-> _ => apply hev_graph_left_inv in H as ->
      | ⟨_|_⟩₁ -[◩]-> ?x  => let t := fresh in
                             apply hev_graph_left_inv in H as (t & -> & H);
                               rename t into x
      | ⟨_|_⟩₁ -[▣]-> ?x  => apply hev_graph_left_inv in H as []
      | ⟨_|_⟩₁ -[?c]-> ?x => let t := fresh in
                             apply hev_graph_left_inv in H; revert H;
                               destruct c; [ intros (t & -> & H) | intros [] ];
                               rename t into x
    end.

  (* The graph describes a functional and strongly total relation *)

  Local Lemma hev_graph_fun c t' t₁ t₂ : t' -[c]-> t₁ → t' -[c]-> t₂ → t₁ = t₂.
  Proof.
    intros H; revert H t₂.
    induction 1; intros ? G; hev left inv G; auto.
    f_equal; auto.
  Qed.

  Local Lemma hev_graph_total c t' : { t | t' -[c]-> t }.
  Proof.
    induction t' as [ [ x | (y,t) ] | y t' (t & Ht) ].
    + exists ⟨x⟩₀; auto.
    + exists ⟨y|t⟩₁; auto.
    + destruct c; simpl in *.
      * exists ⟨y|t⟩₁; auto.
      * destruct y.
  Qed.

  (* Ana(lysis) is the converse of evaluation *)
  Notation ana c := (λ t t', t' -[c]-> t).

  Section analysis_cases.

    Local Fact analysis_leaf c x t' :
        ana c ⟨x⟩₀ t' ↔ ⟨⦉x⦊₁⟩₀ = t'.
    Proof.
      split.
      + intros H; apply hev_graph_right_inv in H; destruct c; easy.
      + intros <-; auto.
    Qed.

    Local Fact analysis_node_full y t t' :
        ana ▣ ⟨y|t⟩₁ t' ↔ ⟨⦉y,t⦊₂⟩₀ = t'.
    Proof.
      split.
      + intros H; apply hev_graph_right_inv in H; easy.
      + intros <-; auto.
    Qed.

    Local Fact analysis_node_lift y t t' :
        ana ◩ ⟨y|t⟩₁ t' ↔ ⟨⦉y,t⦊₂⟩₀ = t'
                         ∨ ∃t'', ⟨y|t''⟩₁ = t' ∧ ana ◩ t t''.
    Proof.
      split.
      + intros H; apply hev_graph_right_inv in H; firstorder.
      + intros [ <- | (t'' & <- & ?) ]; auto.
    Qed.

  End analysis_cases.

  (* The reverse of the evaluation graph (ie the analysis) is finitary *)

  Local Lemma hev_graph_inv_fin c t : fin (ana c t).
  Proof.
    induction t as [ x | y t IHt ].
    + finite eq (analysis_leaf _ _).
    + destruct c.
      * finite eq (analysis_node_lift _ _).
      * finite eq (analysis_node_full _ _).
  Qed.

  (** Remember than ⟨α|τ⟩₁ is the tree by which (utree_embed R T) is lifted
      An analysis in utree X' (Y' c) is disappointing
         1) if its root node is >= α (only when c = ◩, otherwise Y' ▣ is empty)
      or 2) if it is a leaf and the label embeds τ
    *)
  Inductive disapointing_ana : forall c, utree X' (Y' c) -> Prop :=
    | disapointing_ana_cons y t : T α y → disapointing_ana ◩ ⟨y|t⟩₁
    | disapointing_ana_nest c y t : τ ≤ₑ t → disapointing_ana c ⟨⦉y,t⦊₂⟩₀.
  Notation D := disapointing_ana.

  Hint Constructors disapointing_ana : core.

  Fact disapointing_ana_inv c t' :
           D c t'
         ↔ match t' with
             | ⟨x'⟩₀  => ∃ y t, x' = ⦉y,t⦊₂ ∧ τ ≤ₑ t
             | ⟨y|_⟩₁ =>
             match c return Y' c → Prop with
               | ◩ => λ y, T α y
               | ▣ => λ _, False
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

  (* An analysis is exceptional is one of its sub-trees in disapointing *)
  Local Definition exceptional_ana c t := (λ s, s ≤ut t) ⧫ D c.
  Notation E := exceptional_ana.

  Local Fact disap_ana_excep_ana c : D c ⊆₁ E c.
  Proof. intros t; exists t; auto with utree_db. Qed.

  Local Fact sub_utree_excep_ana c s t : s ≤ut t → E c s → E c t.
  Proof. intros ? (w & ? & ?); exists w; eauto with utree_db. Qed.

  Hint Resolve hev_graph_inv_fin
               disap_ana_excep_ana
               sub_utree_excep_ana : core.

  (* By induction on the utree_embed predicate and
     then left inversion on -[c]->, and also on R' *)
  Local Lemma hev_quasi_morphism c t1' t2' t1 t2 :
         t1' ≤ₐ t2'
       → t1' -[c]-> t1
       → t2' -[c]-> t2
       → t1 ≤ₑ t2 ∨ E c t1'.
  Proof.
    intros H1 H2 H3; revert H1 t1 t2 H2 H3.
    induction 1 as [ x1 x2 H1
                   |    t1' y2 t2' H1 IH1
                   | y1 t1' y2 t2' H1 H2 IH2 ]; intros t1 t2 G1 G2.
    + induction H1 as [ | ? ? ? ? ? [] ];
        hev left inv G1; hev left inv G2; auto with utree_db.
    + hev left inv G2.
      specialize (IH1 _ _ G1 G2).
      revert IH1; intros []; auto with utree_db.
    + hev left inv G1; hev left inv G2.
      specialize (IH2 _ _ G1 G2).
      revert H1 IH2; intros [] []; eauto with utree_db.
  Qed.

  Section af_choice.
   (* Since sT <> None, we freeze some c₀ such that Some c₀ = sT *)

    Let af_choice_sT_pwc : { c | sT = Some c }.
    Proof. destruct sT; try easy; eauto. Qed.

    Local Definition af_choice_sT := proj1_sig af_choice_sT_pwc.

    Local Fact af_choice_sT_spec : sT = Some af_choice_sT.
    Proof. apply (proj2_sig af_choice_sT_pwc). Qed.

  End af_choice.

  Notation c₀ := af_choice_sT.
  Notation Hc₀ := af_choice_sT_spec.

  Section excep_ev_embed.

    (** An evaluation is exceptional if each of its analysis is exceptional *)
    Let excep_ev t := ana c₀ t ⊆₁ E c₀.

    (* If T α y then a disapointing leaf ⟨⦉y,t⦊₂⟩₀ must embed ⟨α|τ⟩₁ *)
    Let D_leaf_embed y t : T α y → D c₀ ⟨⦉y,t⦊₂⟩₀ → ⟨α|τ⟩₁ ≤ₑ ⟨y|t⟩₁.
    Proof.
      intros Hy Ht.
      apply disapointing_ana_inv in Ht as (? & ? & E & ?).
      inversion E; subst; auto with utree_db.
    Qed.

    (* If an exceptional evaluation is analysed by
       a leaf then this leaf must be disapointing *)
    Let excep_ev_leaf x' t : excep_ev t → ana c₀ t ⟨x'⟩₀ → D c₀ ⟨x'⟩₀.
    Proof.
      intros Ht Hx'.
      apply Ht in Hx' as (s & Hx' & Hs).
      apply sub_utree_inv_right in Hx' as [ -> | [] ]; auto.
    Qed.

    (* hence leaves ⟨_⟩₀ cannot be exceptional *)
    Let not_excep_ev_leaf x : ¬ excep_ev ⟨x⟩₀.
    Proof.
      intros H.
      apply excep_ev_leaf with (x' := ⦉x⦊₁) in H; auto.
      now apply disapointing_ana_inv in H as (? & ? & ? & _).
    Qed.

    (* If a node ⟨y|t⟩₁ is exceptional and y embed α
       then ⟨y|t⟩₁ embeds ⟨α|τ⟩₁ *)
    Let excep_ev_node_embed y t : excep_ev ⟨y|t⟩₁ → T α y → ⟨α|τ⟩₁ ≤ₑ ⟨y|t⟩₁.
    Proof.
      intros Ht Hy.
      apply (@excep_ev_leaf ⦉y,t⦊₂) in Ht.
      + apply D_leaf_embed; assumption.
      + constructor.
    Qed.

    (* How to call this: hereditary property ?? *)
    Let excep_ev_hereditary y s t :
                      excep_ev t
                    → (∀ s', ana c₀ s s' → ana c₀ t ⟨y|s'⟩₁)
                    → excep_ev s
                    ∨ ana c₀ s ⧫ λ s', D c₀ ⟨y|s'⟩₁.
    Proof.
      intros Ht Hs.
      apply fin_choice; auto; intros s' Hs'.
      destruct (Ht _ (Hs _ Hs')) as (u & Hu & ?).
      apply sub_utree_inv_right in Hu as [ -> | ].
      + right; auto.
      + left; now exists u.
    Qed.

    (** This property is similar to
             1) intercalate_any_vec_fall2
         and 2) intercalate_any_vec_embed
     *)
    Local Lemma excep_ev_embed t : excep_ev t → ⟨α|τ⟩₁ ≤ₑ t.
    Proof.
      generalize Hc₀; intros Hc₀.
      induction t as [ x | y t IHt ]; intros Ht.
      + now apply not_excep_ev_leaf in Ht.
      + destruct c₀.
        * (* if c = ◩, nodes *)
          destruct (@excep_ev_hereditary y t)
            with (1 := Ht)
            as [ | (t' & ? & Dt') ];
            auto with utree_db.
          apply disapointing_ana_inv in Dt'.
          now apply excep_ev_node_embed.
        * (* if c = ▣, T is full *)
          rewrite Hc₀ in HT; simpl in HT.
          now apply excep_ev_node_embed.
    Qed.

  End excep_ev_embed.

  Hint Resolve hev_graph_total
               hev_graph_fun
               hev_quasi_morphism
               excep_ev_embed : core.

  Theorem af_utree_nodes : af (utree_embed R T)↑⟨α|τ⟩₁.
  Proof.
    generalize (higman'_af Hc₀).
    af quasi morph rel (hev_graph c₀) (E c₀); eauto.
  Qed.

End af_utree_nodes_rel.

