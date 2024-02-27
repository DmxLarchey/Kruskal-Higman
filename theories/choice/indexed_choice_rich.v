(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import List Utf8.

From KruskalTrees
  Require Import notations idx.

From KruskalFinite
  Require Import finite choice.

Require Import base.

Import ListNotations idx_notations.

Set Implicit Arguments.

Section list_prod.

  Variable (X Y Z : Type) (f : X → Y → Z).

  Implicit Types (l : list X) (m : list Y).

  Definition list_prod l m := flat_map (λ x, map (f x) m) l.

  Hint Resolve in_map : core.

  Fact list_prod_spec l m z : z ∈ list_prod l m ↔ ∃ x y, z = f x y ∧ x ∈ l ∧ y ∈ m.
  Proof.
    unfold list_prod; rewrite in_flat_map; split.
    + intros (? & ? & (? & <- & ?)%in_map_iff); eauto.
    + intros (? & ? & -> & []); eauto.
  Qed.

End list_prod.

Section matrix_choice_list.

  (** Given an heterogenous vector of lists

      hv  =  [x(1,1)  ....  x(1,k₁) ] : list X₁
                       ..
             [x(n,1)  ....  x(n,kₙ) ] : list Xₙ

      A "choice sequence for hv" is a map
            c : Πᵢ Xᵢ  st  ∀i, cᵢ ∈ hvᵢ

      For P a predicate over the product Πᵢ Xᵢ
      and Q a predicate over the sum     Σᵢ Xᵢ

      If any choice sequence for hv satisfies P
      or intersects Q then either:
        - P is satisfied by some choice sequence for hv
        - or Qᵢ is satisfied over a hvᵢ for some i

      Classical proof (no finiteness assumption needed):
        assume no hvᵢ is included in Qᵢ
        then for each ᵢ, define cᵢ ∈ hvᵢ\Qᵢ
        c is a choice sequence for hv that
        does no intersect Q, hence it must
        satisfy P.

      Intuitionistic proof below in the finitary case
      based on a specialization using a fan, ie a list
      enumerating choice sequences (up to extensionality)
    *)

  (* 𝕆𝕊 λ ∀∃ → ↔ ∧ ∨ *)

  Notation lift c := (λ i, c (𝕊 i)).

  Local Definition dnil {X : idx 0 → Type} i : X i := idx_O_rect (X i) i.

  Local Definition dcons {n} {X : idx (S n) → Type} (x : X 𝕆) (c : ∀i, X (𝕊 i)) i : X i :=
     idx_S_rect x c i.

  Arguments dcons {n X} x c i /.

  (** We build the heterogenous fan for
       X : idx n → Type   lX : Πᵢ (list Xᵢ)

     We have to proceed over fan X lX because
     the type { c : Πᵢ Xᵢ | ∀i, cᵢ ∈ lXᵢ } is not "finite"
     whereas the extensionally equivalent fan X lX, being a
     list, is of course finite *)

  Local Fixpoint fan {n} : ∀ {X : idx n → Type} (lX : ∀i, list (X i)), list (∀i, X i) :=
    match n with
    | 0   => λ _ _ , [dnil]
    | S n => λ _ lX, list_prod dcons (lX 𝕆) (fan (lift lX))
    end.

  (* fan lX contains choices sequences over lX₁,...,lXₙ *)
  Local Fact fan_prop n (X : idx n → Type) (lX : ∀i, list (X i)) c : c ∈ fan lX → ∀i, c i ∈ lX i.
  Proof.
    induction n as [ | n IHn ] in X, lX, c |- *; simpl.
    + intros _ ?; idx invert all.
    + rewrite list_prod_spec; intros (x & c' & -> & H2 & H3) p.
      idx invert p; auto.
      apply (IHn (lift X) (lift lX) c' H3 p).
  Qed.

  (* And, extensionnally, all of them!! But we do not need to that inclusion below *) 
  Local Remark fan_prop_rev n (X : idx n → Type) (lX : ∀i, list (X i)) c : (∀i, c i ∈ lX i) → ∃c', c' ∈ fan lX ∧ ∀i, c' i = c i.
  Proof.
    induction n as [ | n IHn ] in X, lX, c |- *; simpl; intros Hc.
    + exists dnil; split; auto; intro; idx invert all.
    + destruct IHn with (lX := lift lX) (c := lift c)
        as (c' & H1 & H2); auto.
      exists (dcons (c 𝕆) c'); split.
      * apply list_prod_spec; eauto.
      * intro i; idx invert i; auto.
  Qed.

  Hint Resolve in_cons in_eq : core.

  (* Theproof is by induction on n *)
  Local Lemma matrix_choice_fan
      {n : nat}
      {X : idx n → Type}
      (P : (∀i, X i) → Prop)       (* predicate over choice seq. *)
      (Q : ∀i, X i → Prop)         (* seq. of sub-types *)
      (lX : ∀i, list (X i))        (* finite fan *)
      (HPQ : ∀c, c ∈ fan lX → P c ∨ ∃i, Q i (c i)) :
         (∃c, c ∈ fan lX ∧ P c) ∨ (∃i, ∀x, x ∈ lX i → Q i x).
  Proof.
    induction n as [ | n IHn ] in X, P, Q, lX, HPQ |- *.
    + destruct HPQ with (c := @dnil X) as [ | (? & _) ]; simpl; auto.
      * left; exists dnil; auto.
      * idx invert all.
    + assert (H: ∀x, x ∈ lX 𝕆
                   → Q 𝕆 x
                   ∨ ∀c, c ∈ fan (lift lX)
                       → P (dcons x c)
                       ∨ ∃i, Q (𝕊 i) (c i)).
      1:{ intros x Hx.
          (* fin_choice_cst_left permutes "Q 𝕆 x ∨ _" with the universal quantifier
             "∀c, _" and this is allowed constructivelly because the 
             quantification is finitary.

             In fact "∀c" is bounded by "c ∈ fan (lift lX)". The predicate 
             "∀i, c i ∈ lift lX i" is (ext.) equivalent (see fan_prop_rev above)
             and we would have favored the later but it is not finitary unfortunately.

             On the other hand, _ ∈ fan (lift lX) is finitary by definition and this
             is the very reason why we introduce the fan in this proof. *)
          apply fin_choice_cst_left.
          + fin auto.
          + intros c Hc.
            destruct (HPQ (dcons x c)) as [ | (i & ?) ]; auto.
            * simpl; apply list_prod_spec; eauto.
            * idx invert i; simpl in *; eauto. }
      apply fin_choice in H as [ | (x & H1 & H2) ].
      * right; eauto.
      * apply (IHn _ (λ c, P (dcons x c)) (lift Q)) in H2
          as [ (c & []) | (p & ?) ].
        - left; exists (dcons x c); split; auto.
          apply list_prod_spec; eauto.
        - eauto.
      * fin auto.
  Qed.

  Hint Resolve fan_prop : core.

  (** Now we can replace c ∈ fan lX with ∀i, c i ∈ lX i 
      and get rid of the fan in the statement *)

  (** Choice Hypothesis (see below):

      Every choice sequence (among a finite fan) either:
       - belongs to P
       - over intersects Q at some index

      Then either:
       - there is a choice sequence satisfying P
       - there is an index i such that every choice
         sequence intersects Q i. *)

  Local Corollary matrix_choice_list
         {n : nat}
         {X : idx n → Type}
         (P : rel₁ (∀i, X i))
         (Q : ∀i, rel₁ (X i))
         (lX : ∀i, list (X i)) :
         (∀c, (∀i, c i ∈ lX i) → P c ∨ ∃i, Q i (c i))
       → (∃c, (∀i, c i ∈ lX i) ∧ P c)
       ∨ (∃i, ∀x, x ∈ lX i → Q i x).
  Proof.
    intros Hhv.
    destruct (matrix_choice_fan P Q lX)
      as [ (? & []) | [] ]; eauto.
  Qed.

End matrix_choice_list.

(** We get a more abstract statement where the notion
    of heteregeneous vector (over lX as above) has been removed. 
    In here, X₁,...,Xₙ are finite sub-types/predicates
    over T₁,...,Tₙ respectivelly. *)
Theorem fin_matrix_choice
         (n : nat) 
         (T : idx n → Type) (X : ∀i, rel₁ (T i)) (Xfin : ∀i, fin (X i))
         (P : rel₁ (∀i, T i))
         (Q : ∀i, rel₁ (T i)) :
         (∀c, (∀i, X i (c i)) → P c ∨ ∃i, Q i (c i))
       → (∃c, (∀i, X i (c i)) ∧ P c)
       ∨ (∃i, X i ⊆₁ Q i).
Proof.
  intros H.
  apply reif_t_dep in Xfin as (lX & HlX).
  destruct (matrix_choice_list P Q lX)
    as [ (c & ? & ?) | (i & ?) ].
  + intros c Hc; apply H; intro; apply HlX; auto.
  + left; exists c; split; auto; intro; apply HlX; auto.
  + right; exists i; intro; rewrite HlX; auto.
Qed.

(** Just another version where X₁,...,Xₙ are not sub-types
    but finite types. *)
Theorem finite_matrix_choice
         (n : nat)
         (X : idx n → Type)
         (Xfin : ∀i, finite (X i))
         (P : rel₁ (∀i, X i))
         (Q : ∀i, rel₁ (X i)) :
         (∀c, P c ∨ ∃i, Q i (c i))
       → (∃c, P c) ∨ (∃i, ∀x, Q i x).
Proof.
  intros HQ.
  destruct (@fin_matrix_choice _ _ _ (λ i, fin_True (Xfin i)) P Q)
    as [ (? & []) | [] ]; fin eauto.
Qed.

(** Given a finite sequence X₁,...,Xₙ of finite predicates over T 
    and a single predicate P over T (not necessarilly finite),
    if all choice sequences c over X (ie Xᵢ cᵢ for any i) 
       intersect P (ie P cᵢ for some i) 
    then for some index i, P covers Xᵢ. *) 

Corollary fin_indexed_choice T n (X : idx n → rel₁ T) (P : rel₁ T) :
      (∀i, fin (X i))
    → (∀c, (∀i, X i (c i)) → ∃i, P (c i))
    → ∃i, X i ⊆₁ P.
Proof.
  intros H ?.
  destruct (@fin_matrix_choice _ _ _ H ⊥₁ (λ _, P))
      as [ (? & _ & []) | ]; auto.
Qed.

(** given a finite sequence of predicates 
        P₁ over X₁,
        ...
        Pₙ over Xₙ, 
    where X₁,...,Xₙ are all finite types,
    if all choice sequence c over X₁,...,Xₙ intersect P (ie Pᵢ cᵢ for some i) 
    then for some index i, Pᵢ covers the type Xᵢ.
*) 

Corollary finite_indexed_choice n (X : idx n → Type) (P : ∀i, rel₁ (X i)) :
      (∀i, finite (X i)) → (∀c, ∃i, P i (c i)) → (∃i, ∀x, P i x).
Proof.
  intros H ?.
  destruct (@finite_matrix_choice _ _ H ⊥₁ P) as [ (_ & []) | ]; auto.
Qed.
