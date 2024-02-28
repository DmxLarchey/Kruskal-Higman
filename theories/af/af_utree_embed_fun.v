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

  Notation "▣" := af_choice_full.
  Notation "◩" := af_choice_af.

  (** The proof here mimics (ie downgrades) the proof of Higman's theorem
      and does it using functions as morphism, not relations, which leads
      to shorter code but less versatile when dealing with Σ-types,
      when the quasi morphism is difficult or impossible to implement
      as a function. *)

  Variables (sR : option af_choice) (X : Type) (R : rel₂ X) (HR : ⟪sR,X,R⟫ₐ)
            (sT : option af_choice) (Y : Type) (T : rel₂ Y) (HT : ⟪sT,Y,T⟫ₐ)
            (α : Y) (τ : utree X Y).

  (** sR/sT is are witnesses that R/T are AF, ie they measure the 
      AF complexity of the pair (R,T).

      We want to show that (utree_embed R T)↑⟨α|τ⟩₁ is AF and
      for this, we use a quasi morphism defined below. See
      "af_quasi_morphism.v" for a description of that tool.

      We build a new type utree X' Y' equipped with an
      embedding utree_embed R' T' where the pair (R',T')
      has lesser AF complexity than (R,T). This is witnessed
      by a pair sR'/sT' which is lesser that sR/sT.

      As a consequence of the induction hypothesis, utree_embed R' T'
      can then be proved AF.

      Finally, the quasi morphism transports this AF property to
      (utree_embed R T)↑⟨α|τ⟩₁. *)

  Notation "⦗ x ⦘₁" := (inl x) (at level 1, format "⦗ x ⦘₁").
  Notation "⦗ y , t ⦘₂" := (inr (y,t)) (at level 1, format "⦗ y , t ⦘₂").

  (** The new types of leaves X' and nodes Y':
       - X' := X + Y x utree X Y
       - Y' depends the value of the witness sT = Some c
       - c is a parameter that is related to sT quite late in the proof.
      Remark that sT = None is not possible because α inhabits Y. *)

  Notation X' := (X+Y*utree X Y)%type.

  (* c := ◩ represents the situation where T on nodes of arity 1 is af
     c := ▣ represents the situation where T on nodes of arity 1 if full 

     These two properties are only needed late in the proof. *) 

  Let Y' c := match c with ◩ => Y | ▣ => Empty_set end.

  Goal utree X' (Y' ▣) = utree (X+Y*utree X Y) Empty_set.  Proof. reflexivity. Qed.
  Goal utree X' (Y' ◩) = utree (X+Y*utree X Y) Y.          Proof. reflexivity. Qed.

  (* The new relations on X' and Y' respectivelly *)

  Inductive hl_rel_leaves : rel₂ X' :=
    | hl_rel_leaves_refl u v :
              R u v
            → hl_rel_leaves ⦗u⦘₁ ⦗v⦘₁
    | hl_rel_leaves_nest u s v t :
              T u v
            → (utree_embed R T)↑τ s t
            → hl_rel_leaves ⦗u,s⦘₂ ⦗v,t⦘₂.

  Notation R' := hl_rel_leaves.

  (* The relation R' on X+Y*utree X Y is equivalent to R + T*(utree_embed R T)↑τ
     and well be proved AF by Ramsey and the induction hypotheses. *)

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

  (* Again, the relation T' on Y' depends on c.
     Notice that anything works here because Y' ▣ is
     an empty type. *)
  Let T' c := match c return rel₂ (Y' c) with ◩ => T↑α | ▣ => ⊥₂ end.

  (* The relation T' ▣ := _ (anything) is AF because on the empty type
     The relation T' ◩ := T↑α is AF (it is smaller by IH because lifted from T)

     The most interesting case here is when ◩. In that case, the type for
     the leaf X' (arity 0) is augmented by a node of arity 1 and
     one subtree from that node. *)

  Infix "≼" := (utree_embed R T) (at level 70).
  Notation "r '≼[' c ']' t" := (utree_embed R' (T' c) r t) (at level 70, format "r  ≼[ c ]  t").

  (** We build a quasi morphism hev c : utree X' (Y' c) → utree X Y 
     from the embedding ≼[c] to the lifted embedding ≼↑⟨α|τ⟩₁

      It describes the process of evaluation of tree in utree X' (Y' c)
      which consists in rebuilding the original tree from displaced
      information.

      A bit of dependent pattern matching to define hev ◩/▣ simultaneously *)

  Fixpoint ev c (t' : utree X' (Y' c)) : utree X Y :=
    match t' with
    | ⟨⦗x⦘₁⟩₀   => ⟨x⟩₀
    | ⟨⦗y,t⦘₂⟩₀ => ⟨y|t⟩₁
    | ⟨y'|t'⟩₁  =>
      match c return Y' c → utree X' (Y' c) → utree X Y with
      | ◩ => λ y' t', ⟨y'|ev ◩ t'⟩₁
      | ▣ => λ y' _ , match y' with end
      end y' t'
   end.

  (** These are the recursives equations that we want for the evaluation *)

  Goal ∀ c x,   ev c ⟨⦗x⦘₁⟩₀   = ⟨x⟩₀.           Proof. reflexivity. Qed.
  Goal ∀ c y t, ev c ⟨⦗y,t⦘₂⟩₀ = ⟨y|t⟩₁.         Proof. reflexivity. Qed.
  Goal ∀ y' t', ev ◩ ⟨y'|t'⟩₁  = ⟨y'|ev ◩ t'⟩₁.  Proof. reflexivity. Qed.

  (** There is no equation for ev ▣ ⟨y'|t'⟩₁ because Y' ▣ is empty *)

  (** Here we view the "evaluation" (ev) as a total function but in more
      complicated cases, it is very relevant to view it as a "bidirectional
      process" instead, ie a binary relation. Indeed, the evaluation is
      not necessarily total or computable. Moreover, its converse relation
      is pf critical importance. Wim Veldman calls it "analysis":

              Analyses in utree X' Y'   /      Evalutations in utree X y

                t' : utree X' Y'    --[ev]->    t = ev t' : utree X Y
                  ana t t'          <-[ana]-    t : utree X Y

      The ana(lysis) process is not a function because it is
      non-deterministic. However (and critically) it is finitary hence
      an evaluation only has finitely many corresponding analyses. Hence
      one could possibly view analysis as a map 

                 ana : utree X Y → list (utree X' Y')

      but it is really not convenient to view it as a function because
      it overloads proofs with lots of edge-cases and cannot work when 
      we moreover have to deal with the case where evaluation is partial 
      function on a non computable domain.

      The analysis process consists in possibly displacing information 
      in the utree by hidding a sub-tree of unary node into a leaf. Same
      process happens also for higher arities (binary trees etc) in the case
      of Higman's theorem for k-ary trees. Evaluation simply puts the
      tree in its original form: it is deterministic and much simpler to
      describe. 

      In the case of unary trees (or lists), it is possible to give
      a reasonably readable analysis function explicitly. It consists
      of cutting the utree in half and storing one half in a leaf. Of
      course there are many ways to cut a utree in half. It it is a
      binary (or k-ary tree), of can even consider multiple cuts in
      different parts of the tree.

      Manipulating the explicit form of analysis is possible but 
      "it is not necessary to do so" and hence, we strongly advise
      not to try this bloated path.

      This is what is done in eg Monika Seisenberger proofs of Higman's
      lemma (CHECK reference), and we extended this to Higman's theorem
      and Kruskal's tree theorem in our very first mechanization back
      in 2014. This renders the proof mostly undeciphereable. *)

  (* ana(lysis) is the converse relation of evaluation *)
  Notation ana := (λ c t t', ev c t' = t).

  (** We put the ana(lysis) predicate in a shape compatible with
      the KruskalFinite library tools *)

  Local Fact analysis_leaf c x t' : ana c ⟨x⟩₀ t' ↔ ⟨⦗x⦘₁⟩₀ = t'.
  Proof.
    split.
    + destruct t' as [ [ x' | [y t] ] | ]; simpl; intros H; try easy.
      * now inversion H.
      * now destruct c.
    + now intros <-.
  Qed.

  Local Fact analysis_node_full y t t' : ana ▣ ⟨y|t⟩₁ t' ↔ ⟨⦗y,t⦘₂⟩₀ = t'.
  Proof.
    split.
    + destruct t' as [ [|[]] | ]; simpl; now inversion 1; auto.
    + now intros <-.
  Qed.

  Local Fact analysis_node_lift y t t' :
            ana ◩ ⟨y|t⟩₁ t' ↔ ⟨⦗y,t⦘₂⟩₀ = t'
                            ∨ ∃t'', ⟨y|t''⟩₁ = t' ∧ ana ◩ t t''.
  Proof.
    split.
    + now destruct t' as [ [|[]] | ]; simpl; inversion 1; eauto.
    + now intros [ <- | (? & <- & <-) ].
  Qed.

  (** The following property is all we need to know about the
      analysing process except that its converse is evalutation.
      In particular, we do not need to know the explicit form
      of the "function". Actually the fin predicate is informative
      and contains that function but it is hidden in how the
      KruskalFinite tools compute finiteness, and it is much
      better to keep it that way. *)

  (* ana(lysis) is finitary, ie the evaluation function has finite inverse image *)
  Local Lemma analysis_fin c t : fin (ana c t).
  Proof.
    induction t as [ x | y t IHt ].
    + finite eq (analysis_leaf _ _).
    + destruct c.
      * finite eq (analysis_node_lift _ _).
      * finite eq (analysis_node_full _ _).
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
  Proof. intros ? (w & []); exists w; eauto with utree_db. Qed.

  Hint Resolve disap_has_disap sub_utree_has_disap : core.

  (* ev c is a quasi morphism *)
  Local Lemma ev_quasi_morphism c s' t' :
         s' ≼[c] t' → ev c s' ≼ ev c t' ∨ E' c s'.
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

  (** An analysis is exceptional (E') if it contains a disapointing sub-tree (D')
      An evalutation is exceptional (E) if all its analyses are exceptional 

      Below we show that exceptional evaluations are exactly those embedding ⟨α|τ⟩₁ *)

  Notation E c t := (ana c t ⊆₁ E' c).

  Section exceptional_vs_embedding.

    (** First, if "t" embeds ⟨α|τ⟩₁ then it is exceptional, ie all its analyses
        contain a disapointing sub-tree *)

    Local Remark embed_exceptional c t : ⟨α|τ⟩₁ ≼ t → E c t.
    Proof.
      intros H t' <-.
      induction t' as [ [ | (x2,t2) ] | y t' IH ]; simpl in H.
      + now apply utree_embed_inv_10 in H.
      + exists ⟨⦗x2,t2⦘₂⟩₀; split; eauto with utree_db.
        apply utree_embed_inv_11 in H as [ | [] ]; eauto with utree_db.
      + destruct c; [ | destruct y ].
        apply utree_embed_inv_11 in H as [ (v & [])%IH | [] ].
        * exists v; eauto with utree_db.
        * exists ⟨y|t'⟩₁; eauto with utree_db.
    Qed.

    (** Then we show the converse, which is the important property here:
        if an evaluation is exceptional then it embeds ⟨α|τ⟩₁ ≼ t *) 

    (** Let us first study exceptional leaves (of arity 0) *)

    (* A leaf (analysis) is exceptional only if it is disapointing *)
    Local Fact E'_D'_leaf c x' : E' c ⟨x'⟩₀ → D' c ⟨x'⟩₀.
    Proof. now intros (? & [ -> | [] ]%sub_utree_inv_right & ?). Qed.
 
    (* An evaluation of a leaf is exceptional only if this leaf is disapointing *)
    Local Fact E_D'_leaf c x' t : E c t → ana c t ⟨x'⟩₀ → D' c ⟨x'⟩₀.
    Proof. now intros H1 H2%H1%E'_D'_leaf. Qed.

    (* Hence leaves ⟨_⟩₀ are not exceptional *)
    Local Lemma E_leaf_False c x : E c ⟨x⟩₀ → False.
    Proof. now intros (? & ? & ? & _)%(@E_D'_leaf _ ⦗x⦘₁)%disapointing_inv; auto. Qed.
 
    (* If ⟨⦗y,_⦘₂⟩₀ is a disapointing leaf with T α y then its evaluation embeds ⟨α|τ⟩₁ *)
    Local Fact D'_leaf_embed c y t : D' c ⟨⦗y,t⦘₂⟩₀ → T α y → ⟨α|τ⟩₁ ≼ ⟨y|t⟩₁.
    Proof. intros (? & ? & [=] & Ht)%disapointing_inv Hy; subst; auto with utree_db. Qed.

    Hint Resolve D'_leaf_embed : core.

    (** Let us now study exceptional trees of arity 1 *)

    (* An exceptional evaluation ⟨y|_⟩₁ with T α y embeds ⟨α|τ⟩₁ *)
    Local Fact E_node_embed c y t : E c ⟨y|t⟩₁ → T α y → ⟨α|τ⟩₁ ≼ ⟨y|t⟩₁.
    Proof. intros Ht%(@E_D'_leaf _ ⦗y,t⦘₂) H; eauto. Qed.

    (* E hereditary property *)
    Local Fact E_hereditary c y' s t :
            E c t
          → (∀s', ana c s s' → ana c t ⟨y'|s'⟩₁)
          → E c s ∨ ∃s', ana c s s' ∧ D' c ⟨y'|s'⟩₁.
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

        Here we NEED that c is related to sT
     *)

    (* If every analysis of t is exceptional that t embeds ⟨α|τ⟩₁ *)
    Local Lemma E_embed c t :
          (c = ▣ → ∀ y₁ y₂, T y₁ y₂)
        → E c t
        → ⟨α|τ⟩₁ ≼ t.
    Proof.
      intros Hc.
      induction t as [ x | y t IHt ]; intros Ht.
      + (* leaves are not exceptional *)
        apply E_leaf_False in Ht as [].
      + destruct c.
        * (* case c = ◩ *)
          destruct (@E_hereditary ◩ y t _ Ht) as [ | (t' & H1 & H2) ]; eauto with utree_db.
          - now intros ? <-.
          - apply disapointing_inv in H2.
            apply (@E_node_embed ◩); auto.
        * (* case c = ▣, T is full *)
          apply (@E_node_embed ▣); auto.
    Qed.

  End exceptional_vs_embedding.

  Section af_choice.

    (* sT cannot be empty/▢ because α inhabits Y. *)

    (* We freeze c st sT = Some c *)
    Local Fact af_choice_sT_pwc : { c | sT = Some c }.
    Proof. destruct sT; [ eauto | now simpl in HT ]. Qed.

    Local Definition af_choice_sT := proj1_sig af_choice_sT_pwc.

    Local Fact af_choice_sT_spec : sT = Some af_choice_sT.
    Proof. apply (proj2_sig af_choice_sT_pwc). Qed.

  End af_choice.

  Notation c₀ := af_choice_sT.
  Notation Hc₀ := af_choice_sT_spec.  (* sT = Some c₀ *)

  (* T is full when c₀ = ▣ *)
  Local Theorem exceptional_embed t : E c₀ t → ⟨α|τ⟩₁ ≼ t.
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

    (* sum and product below by consequences of Ramsey's theorem,
       ie the theorems "af_sum" and "af_product" *)

    Local Fact R'_af : af R'.
    Proof.
      apply af_mono
        with (2 := af_sum
                     R_af 
                     (af_product T_af IHτ)).
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

    Local Fact RT'_lesser_RT : ⟪sR',X',R'|sT',Y' c₀,T' c₀⟫ ≺₂ ⟪sR,X,R|sT,Y,T⟫.
    Proof.
      generalize af_choice_sT_spec; intros Hc.
      unfold sT'; constructor 1; rewrite Hc.
      destruct c₀; simpl; constructor.
    Qed.

    Hint Resolve correct_R' correct_T' RT'_lesser_RT : core.

    Local Theorem RT'_af : af (utree_embed R' (T' c₀)).
    Proof. eapply IHRT; eauto. Qed.

  End RT'_af.

  Hint Resolve ev_quasi_morphism exceptional_embed : core.

  Theorem af_utree_nodes : af (utree_embed R T)↑⟨α|τ⟩₁.
  Proof.
    generalize RT'_af.
    af quasi morph fun (ev c₀) (E' c₀); eauto.
  Qed.

End af_utree_nodes.


