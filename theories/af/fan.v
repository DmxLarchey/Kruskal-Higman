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
  Require Import tactics list_utils.

From KruskalFinite
  Require Import finite.

Require Import base  (* list_fan *).

Import ListNotations.

Set Implicit Arguments.

#[local] Hint Resolve Forall2_app in_eq in_cons : core.

Section Forall2.

  Variables (X Y : Type) (R : X → Y → Prop).

  Fact Forall2_nil_inv_l m : Forall2 R [] m ↔ m = [].
  Proof.
    split.
    + now inversion 1.
    + intros ->; auto.
  Qed.

  Fact Forall2_nil_inv_r l : Forall2 R l [] ↔ l = [].
  Proof.
    split.
    + now inversion 1.
    + intros ->; auto.
  Qed.

  Fact Forall2_cons_inv_l x l m : Forall2 R (x::l) m ↔ ∃ y m', m = y::m' ∧ R x y ∧ Forall2 R l m'.
  Proof.
    split.
    + destruct l; inversion 1; eauto.
    + intros (? & ? & -> & []); eauto.
  Qed.

  Fact Forall2_cons_inv_r l y m : Forall2 R l (y::m) ↔ ∃ x l', l = x::l' ∧ R x y ∧ Forall2 R l' m.
  Proof.
    split.
    + destruct l; inversion 1; eauto.
    + intros (? & ? & -> & []); eauto.
  Qed.

  (* Forall2_app_inv_r is already in the stdlib since Coq 8.13 *)

  Fact Forall2_snoc_inv_r l y m : Forall2 R l (m++[y]) ↔ ∃ l' x, l = l'++[x] ∧ R x y ∧ Forall2 R l' m.
  Proof.
    split.
    + intros (l' & r & ? & (x & ? & -> & ? & ->%Forall2_nil_inv_r)%Forall2_cons_inv_r & ->)%Forall2_app_inv_r; eauto.
    + intros (? & ? & -> & []); eauto.
  Qed.

  Fact fin_Forall2 l : (∀x, x ∈ l → fin (R x)) → fin (Forall2 R l).
  Proof.
    induction l as [ | x l IHl ]; intros Hl.
    + finite as (eq []).
      intro; rewrite Forall2_nil_inv_l; split; auto.
    + finite as (λ v, ∃y, (∃m, y::m = v ∧ Forall2 R l m) ∧ R x y).
      * intros m; rewrite Forall2_cons_inv_l; firstorder.
      * finite compose; eauto.
  Qed.

End Forall2.

Fact fin_Forall2_rev X Y (R : X → Y → Prop) m : (∀y, y ∈ m → fin (λ x, R x y)) → fin (λ l, Forall2 R l m).
Proof.
  intros H.
  finite as (Forall2 (λ y x, R x y) m).
  + intro; apply Forall2_xchg.
  + now apply fin_Forall2.
Qed.

Notation monotone P := (∀ x l, P l → P (x::l)).

#[global] Notation FAN lw := (λ c, Forall2 (λ x l, x ∈ l) c lw).

Theorem fin_FAN X (lw : list (list X)) : fin (FAN lw).
Proof. apply fin_Forall2_rev; fin auto. Qed.

Section FAN_theorem.

  (** That proof of the FAN theorem on inductive bars is derived
      by significantly reworked from Daniel Fridlender's paper

      https://www.brics.dk/RS/98/39/BRICS-RS-98-39.pdf

      which was designed with ACL2.

      In particular, we completely avoid using an explicit
      computation of the FAN like "list_fan" above
      and instead work directly with the FAN predicate. *)

  Variables (X : Type) (P : rel₁ (list X)) (HP : monotone P).

  Local Fact P_monotone_app l m : P m → P (l++m).
  Proof. induction l; simpl; auto. Qed.

  (* P right-lifted by u holds over all choices seqs of lw 
     Notice that when u is [], we simply get FAN lw ⊆₁ P *)
  Let Plift_on_FAN u lw := FAN lw ⊆₁ λ v, P (v++u).

  About Forall2_app_inv_r.

  Local Fact Plift_on_FAN_monotone u : monotone (Plift_on_FAN u).
  Proof.
    intros ? ? Hv ? (? & ? & -> & ? & ?%Hv)%Forall2_cons_inv_r.
    now apply HP.
  Qed.

  Hint Resolve P_monotone_app Plift_on_FAN_monotone : core.

  Local Lemma bar_P_bar_Plift_on_FAN {u} : bar P u → bar (Plift_on_FAN u) [].
  Proof.
    induction 1 as [ | u _ IHu ].
    + constructor 1; unfold Plift_on_FAN; simpl; auto.
    + constructor 2; intros w.
      induction w as [ | a w IHw ].
      * constructor 1.
        (* FAN [[]] is empty *)
        intros ? (_ & _ & _ & [] & _)%Forall2_cons_inv_r.
      * (* We combine IHu and IHv using bar_intersection *)
        specialize (IHu a).
        apply bar_app_nil in IHw.
        apply bar_app_nil.
        generalize (@Plift_on_FAN_monotone (a::u)); intros Hu.
        assert (monotone (λ v, Plift_on_FAN u (v++[w]))) as Hw by (simpl; auto).
        generalize (bar_intersection Hu Hw IHu IHw).
        clear Hu Hw IHu IHw; unfold Plift_on_FAN.
        (* The result follows by mono(tonicity) *)
        apply bar_mono.
        intros ? [] ? (? & ? & -> & [ <- | ] & ?)%Forall2_snoc_inv_r; eauto.
        rewrite <- app_assoc; auto.
  Qed.

  (* The FAN theorem for list based FANs
     If a (monotone) P is unavoidable starting from []
     then P is also uniformly unavoidable on FANs starting from [] *)
  Theorem FAN_theorem : bar P [] → bar (λ lw, FAN lw ⊆₁ P) [].
  Proof.
    (* Plift_on_FAN [] is equivalent to λ lw, FAN lw ⊆₁ P *)
    intros H.
    apply bar_mono with (2 := bar_P_bar_Plift_on_FAN H).
    intros ? H1 ? ?%H1; now rewrite <- app_nil_r.
  Qed.

End FAN_theorem.

(*
Section fan_on_list.

  (** That proof of the FAN theorem is derived 
     from Daniel Fridlender's paper 

      https://www.brics.dk/RS/98/39/BRICS-RS-98-39.pdf  *)

  Notation mono P := (∀ x l, P l → P (x::l)).

  Variables (X : Type) (P : list X → Prop) (HP : mono P).

  Local Fact P_mono_gen l m : P m → P (l++m).
  Proof. induction l; simpl; auto. Qed.

  (** FAN_from u for lw = [l1;..;ln] means
      for every choice sequence [x1;...;xn]
      (st for any i, xi ∈ li) we have P ([x1;...;xn]++u) 
      ie however u is prefixed with a choice seq
      from lw, P holds *)

  Let FAN_from u lw := Forall (λ v, P (v++u)) (list_fan lw).

  Local Fact FAN_from_mono u : mono (FAN_from u).
  Proof.
    unfold FAN_from; intros w lw H.
    apply list_fan_Forall.
    rewrite Forall_forall; intros x _.
    revert H; apply Forall_impl.
    intro; apply HP.
  Qed.

  Hint Resolve P_mono_gen FAN_from_mono : core.

  Local Lemma bar_P_bar_FAN_from u : bar P u → bar (FAN_from u) [].
  Proof.
    induction 1 as [ u Hu | u Hu IHu ].
    + constructor 1; unfold FAN_from; simpl; auto.
    + constructor 2; intros w.
      induction w as [ | a w IHw ].
      * constructor 1; unfold FAN_from; simpl; auto.
      * specialize (IHu a).
        apply bar_app_nil in IHw.
        unfold FAN_from in IHw.
        generalize (@FAN_from_mono (a::u)); intros HV1.
        assert (mono (fun lw => FAN_from u (lw++w::nil))) as HV2.
        1: intros x ll; simpl; auto.
        generalize (bar_intersection HV1 HV2 IHu IHw); intros HV3; clear HV1 HV2.
        apply bar_app_nil.
        revert HV3; apply bar_mono.
        intros x [ H1 H2 ]; unfold FAN_from in *.
        rewrite Forall_forall; intros z; rewrite list_fan_middle_cons;
          revert z; apply Forall_forall.
        apply Forall_app; split; auto.
        rewrite Forall_forall; intros z; rewrite list_fan_sg_right;
          revert z; apply Forall_forall.
        rewrite Forall_map.
        revert H1; apply Forall_impl.
        intro; rewrite app_ass; auto.
  Qed.

  (* list_fan [[0;1];[3;4]] = [[0;3];[0;4];[1;3];[1;4]] *)

  Theorem fan_on_list : bar P [] → bar (λ l, Forall P (list_fan l)) [].
  Proof.
    intros H.
    generalize (bar_P_bar_FAN_from H).
    apply bar_mono.
    intros lw; unfold FAN_from.
    apply Forall_impl.
    intro; rewrite <- app_nil_end; auto.
  Qed.

End fan_on_list.
*)
