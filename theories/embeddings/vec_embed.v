(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib
  Require Import Arith List Lia Utf8.

From KruskalTrees
  Require Import notations tactics idx vec.

Require Import base.

Set Implicit Arguments.

Import idx_notations vec_notations.

#[local] Reserved Notation "l '≤ₑ' m" (at level 70, no associativity, format "l  ≤ₑ  m").

(* 𝕆𝕊 λ ∀∃ → ↔ ∧ ∨ *)

Section vec_forall2.

  (** An inductive version of vec_fall2 *)

  Variables (X Y : Type).

  Variable (R : X → Y → Prop).

  Inductive vec_forall2 : ∀n, vec X n → ∀m, vec Y m → Prop :=
    | vec_forall2_nil : vec_forall2 ∅ ∅
    | vec_forall2_cons n x v m y w : R x y → @vec_forall2 n v m w → vec_forall2 (x##v) (y##w).

  Hint Constructors vec_forall2 : core.

  (* Induction is ok because { _ : T | ... } types in sort Prop when T : Prop *)

  Fact vec_forall2_fall2 n v m w : @vec_forall2 n v m w → { e | vec_fall2 R v↺e w }.
  Proof.
    induction 1 as [ | n x v m y w H1 H2 (-> & He) ].
    + exists eq_refl; auto with vec_db.
    + exists eq_refl; simpl in *; auto with vec_db.
  Qed.

  Fact vec_fall2_forall2 n v w : @vec_fall2 _ _ R n v w → vec_forall2 v w.
  Proof. induction 1 using vec_fall2_rect; auto. Qed.

  (* Beware the below equivalence restriction vec_forall2 to vec X n → vec Y n → Prop *)

  Fact vec_forall2_iff_fall2 n v w : @vec_forall2 n v n w ↔ vec_fall2 R v w.
  Proof.
    split.
    + intros H; destruct (vec_forall2_fall2 H); eq refl; auto.
    + apply vec_fall2_forall2.
  Qed.

  Fact Forall2_vec_forall2 l m :
     Forall2 R l m → vec_forall2 (list_vec l) (list_vec m).
  Proof. induction 1; simpl; auto. Qed.

  Fact vec_forall2_Forall2 n (u : vec _ n) m (v : vec _ m) :
     vec_forall2 u v → Forall2 R (vec_list u) (vec_list v).
  Proof. induction 1; simpl; auto. Qed.

  Fact Forall2_iff_vec_fall2 n (u v : vec _ n) :
     Forall2 R (vec_list u) (vec_list v) ↔ vec_fall2 R u v.
  Proof.
    split.
    + intros H.
      apply Forall2_vec_forall2 in H.
      destruct (list_vec_list u) as (e1 & H1).
      destruct (list_vec_list v) as (e2 & H2).
      revert H1 H2 H; intros <- <-.
      revert e1 e2; rewrite !vec_list_length.
      intros ? ?; eq refl.
      apply vec_forall2_iff_fall2.
    + rewrite <- vec_forall2_iff_fall2.
      apply vec_forall2_Forall2.
  Qed.

End vec_forall2.

#[global] Hint Constructors vec_forall2 : vec_db.
#[global] Hint Resolve vec_fall2_forall2 : vec_db.

Fact vec_forall2_swap X Y R n u m v :
     @vec_forall2 X Y R n u m v → vec_forall2 (λ x y, R y x) v u.
Proof. induction 1; auto with vec_db. Qed.

(* 𝕆𝕊 λ ∀∃ → ↔ ∧ ∨ *)

Section vec_embed.

  Variables (X Y : Type) (R : X → Y → Prop).

  (** The homeomorhic embedding of vectors *)

  Inductive vec_embed : ∀n, vec X n → ∀m, vec Y m → Prop :=

    | vec_embed_nil :              ∅ ≤ₑ∅

    | vec_embed_head n x (v : vec _ n) m y (w : vec _ m) :
                                   R x y
                             →     v ≤ₑ w
                             →  x##v ≤ₑ y##w

    | vec_embed_skip n (v : vec _ n) m y (w : vec _ m) :
                                   v ≤ₑ w
                             →     v ≤ₑ y##w

  where "v ≤ₑ w" := (@vec_embed _ v _ w).

  Hint Constructors vec_embed : core.

  Definition lvec_embed u v := vec_embed (lvec_vec u) (lvec_vec v).

  Fact vec_embed_left n (u : vec _ n) m (v : vec _ m) k (w : vec _ k) : u ≤ₑ v → u ≤ₑ vec_app w v.
  Proof. intro; induction w; simpl; eauto. Qed.

  Fact vec_embed_nil_any n (v : vec _ n) : ∅ ≤ₑ v.
  Proof. induction v; eauto. Qed.

  Hint Resolve vec_embed_nil_any : core.

  Fact vec_embed_length n (v : vec _ n) m (w : vec _ m) : v ≤ₑ w → n ≤ m.
  Proof. induction 1; simpl; lia. Qed.

  Fact vec_embed_inv_left n (v : vec _ n) m (w : vec _ m) :
           v ≤ₑ w
         → match v with
           | ∅     => True
           | x##v' =>
             match w with
             | ∅     => False
             | y##w' => R x y ∧ v' ≤ₑ w' ∨ v ≤ₑ w'
             end
           end.
  Proof.
    induction 1 as [ | | ? v ]; simpl; auto.
    destruct v; auto.
  Qed.

  Fact vec_embed_inv_right n (v : vec _ n) m (w : vec _ m) :
           v ≤ₑ w
         → match w with
           | ∅ => match v with
                  | ∅    => True
                  | _##_ => False
                  end
           | y##w' => v ≤ₑ w'
                    ∨ match v with
                      | ∅     => True
                      | x##v' => R x y ∧ v' ≤ₑ w'
                      end
           end.
  Proof. induction 1; simpl; auto. Qed.

  Fact vec_fall2_embed n v w : @vec_fall2 _ _ R n v w → v ≤ₑ w.
  Proof. induction 1 using vec_fall2_rect; auto. Qed.

  Fact vec_embed_fall2 n (v : vec _ n) m (w : vec _ m) :
          v ≤ₑ w → ∀e : n = m, vec_fall2 R (v↺e) w.
  Proof.
    induction 1 as [ | n x v m y w H1 H2 IH2
                     | n v m y w H1 IH2 ]; intros e.
    + eq refl; auto with vec_db.
    + assert (n = m) as <- by lia.
      eq refl; specialize (IH2 eq_refl); auto with vec_db.
    + apply vec_embed_length in H1; lia.
  Qed.

  Fact vec_embed_fall2_eq n (v w : vec _ n) : v ≤ₑ w → vec_fall2 R v w.
  Proof. intros H; apply (vec_embed_fall2 H eq_refl). Qed.

  Fact vec_embed_in_left_inv n (v : vec _ n) m (w : vec _ m) :
          v ≤ₑ w → ∀x, x ∈ᵥ v → ∃y, y ∈ᵥ w ∧ R x y.
  Proof.
    induction 1 as [ | x n v y m w H1 H2 IH2 | n v y m w H1 IH1 ]; simpl; try easy.
    + intros z; rewrite vec_in_cons_inv; intros [ <- | H ]; eauto with vec_db.
      apply IH2 in H as (? & ? & ?); eauto with vec_db.
    + intros z Hz.
      apply IH1 in Hz as (? & ? & ?); eauto with vec_db.
  Qed.

  Fact vec_embed_prj n (u : vec _ n) m (v : vec _ m) :
        u ≤ₑ v → ∀i, ∃j, R u⦃i⦄ v⦃j⦄.
  Proof.
    induction 1 as [ | n x v m y w H1 H2 IH2
                     | n v m y w H1 IH2 ]; intros p.
    + idx invert all.
    + idx invert p.
      * exists idx_fst; auto.
      * destruct (IH2 p) as (q & Hq).
        exists (idx_nxt q); auto.
    + destruct (IH2 p) as (q & Hq).
      exists (idx_nxt q); auto.
  Qed.

  Fact vec_embed_map n (u : vec _ n) m (v : vec _ m) :
        u ≤ₑ v → ∃f, ∀i, R u⦃i⦄ v⦃f i⦄.
  Proof.
    intros H.
    generalize (vec_embed_prj H); clear H; intros H.
    idx reif H as (f & Hf); eauto.
  Qed.

  Fact vec_sg_embed_prj x n (w : vec _ n) : x##∅ ≤ₑ w ↔ ∃i, R x w⦃i⦄.
  Proof.
    split.
    + intros H.
      apply vec_embed_prj with (i := idx_fst) in H as (p & Hp).
      exists p; auto.
    + intros (p & Hp).
      revert p Hp.
      induction w; intro p; idx invert p; eauto.
  Qed.

End vec_embed.

#[global] Hint Constructors vec_embed : vec_db.
#[global] Hint Resolve vec_embed_nil_any : vec_db.

(* 𝕆𝕊 λ ∀∃ → ↔ ∧ ∨ *)

Fact vec_embed_mono X Y (R T : X → Y → Prop) :
        R ⊆₂ T
      → ∀n (v : vec X n) m (w : vec Y m),
            vec_embed R v w
          → vec_embed T v w.
Proof. induction 2; auto with vec_db. Qed.

Fact vec_embed_compose X Y Z (R : X → Y → Prop) (T : Y → Z → Prop) n (u : vec _ n) m (v : vec _ m) p (w : vec _ p) :
      vec_embed R u v → vec_embed T v w → vec_embed (T∘R) u w.
Proof.
  intros H1 H2; revert H2 n u H1.
  induction 1 as [ | m y v p z w H1 H2 IH2
                   | m v p z w H1 IH2 ]; intros n u.
  + intros ?%vec_embed_inv_right; now destruct u; eauto with vec_db.
  + intros [|Hu]%vec_embed_inv_right.
    * constructor 3; eauto.
    * destruct u.
      - apply vec_embed_nil_any.
      - destruct Hu; constructor 2; eauto.
  + constructor 3; auto.
Qed.

Section vec_embed_vec_map.

  Variables (X X' Y Y' : Type)
            (f : X → X')
            (g : Y → Y')
            (R : X' → Y' → Prop).

  Fact vec_embed_vec_map n (u : vec _ n) m (v : vec _ m) :
       vec_embed (λ x y, R (f x) (g y)) u v
     → vec_embed R (vec_map f u) (vec_map g v).
  Proof. induction 1; simpl; eauto with vec_db. Qed.

  Fact lvec_embed_lvec_map u v :
       lvec_embed (λ x y, R (f x) (g y)) u v
     → lvec_embed R (lvec_map f u) (lvec_map g v).
  Proof. revert u v; intros [] []; apply vec_embed_vec_map. Qed.

End vec_embed_vec_map.

Fact vec_embed_fall2_inv X Y Z R T n u m v w :
        @vec_embed X Y R n u m v
      → @vec_fall2 Y Z T _ v w
      → ∃u', vec_fall2 R u u' ∧ vec_embed T u' w.
Proof.
  intros H; revert H w.
  induction 1 as [ | n x u m y v H1 H2 IH2 | n u m y v H1 IH1 ]; intros w.
  + vec invert w; exists ∅; split; auto with vec_db.
  + vec invert w as z w; rewrite vec_fall2_cons_inv; intros (H3 & H4).
    destruct IH2 with (1 := H4) as (u' & H5 & H6).
    exists (y##u'); auto with vec_db.
  + vec invert w as z w; rewrite vec_fall2_cons_inv; intros (H3 & H4).
    destruct IH1 with (1 := H4) as (u' & H5 & H6).
    eauto with vec_db.
Qed.

#[local] Infix "≤sv" := (vec_embed (@eq _)) (at level 70).

Section vec_embed_sub_vec.

  Variables (X Y : Type) (R : X → Y → Prop).

  Infix "≤ₑ" := (vec_embed R).

  Fact vec_embed_sub_vec_fall2 n (u : vec _ n) m (v : vec _ m) :
           u ≤ₑ v ↔ ∃w, vec_fall2 R u w ∧ w ≤sv v.
  Proof.
    split.
    + induction 1 as [
                     | ? ? ? ? ? ? ? ? (? & [])
                     |   ? ? ? ? ?   ? (? & [])
                     ].
      * exists ∅; eauto with vec_db.
      * eexists (_##_); eauto with vec_db.
      * eexists; eauto with vec_db.
    + intros (? & H1 & H2).
      apply vec_embed_mono with (2 := vec_embed_compose (vec_fall2_embed H1) H2).
      now intros ? ? (? & ? & []).
  Qed.

  Fact vec_sub_embed_trans nu (u : vec X nu) nv (v : vec _ nv) nw (w : vec _ nw) :
        u ≤sv v → v ≤ₑ w → u ≤ₑ w.
  Proof.
    intros H1 H2.
    generalize (vec_embed_compose H1 H2).
    apply vec_embed_mono.
    intros ? ? (? & [] & ?); auto.
  Qed.

  Fact vec_embed_sub_trans nu (u : vec X nu) nv (v : vec _ nv) nw (w : vec _ nw) :
         u ≤ₑ v → v ≤sv w → u ≤ₑ w.
  Proof.
    intros H1 H2.
    generalize (vec_embed_compose H1 H2).
    apply vec_embed_mono.
    intros ? ? (? & ? & []); auto.
  Qed.

End vec_embed_sub_vec.

Fact vec_sub_refl X n (u : vec X n) : u ≤sv u.
Proof. induction u; eauto with vec_db. Qed.

Fact vec_sub_trans X nu (u : vec X nu) nv (v : vec _ nv) nw (w : vec _ nw) :
         u ≤sv v → v ≤sv w → u ≤sv w.
Proof. apply vec_sub_embed_trans. Qed.

#[global] Hint Resolve vec_sub_refl vec_sub_trans : vec_db.

(* 𝕆𝕊 λ ∀∃ → ↔ ∧ ∨ *)

Section vec_embed_disj_inv_gen.

  Variable (X₁ X₂ Y₁ Y₂ : Type)
           (f : X₁ → Y₁ → Prop)
           (g : X₂ → Y₂ → Prop)
           (R : Y₁ → Y₂ → Prop)
           (T : X₁ → X₂ → Y₁ → Y₂ → Prop).

  Fact vec_fall2_disj_inv_gen n (u u' : vec _ n) v v' :
        vec_fall2 (λ x x', ∀ y y', f x y → g x' y' → R y y' ∨ T x x' y y') u v
      → vec_fall2 f u u'
      → vec_fall2 g v v'
      → vec_fall2 R u' v' ∨ ∃ i j, T u⦃i⦄ v⦃j⦄ u'⦃i⦄ v'⦃j⦄.
  Proof.
    induction 1 as [ | n x u y v H1 H2 IH2 ] using vec_fall2_rect; intros G1 G2; auto with vec_db.
    vec invert u' as x' u'; vec invert v' as y' v'.
    apply vec_fall2_cons_inv in G2 as (G3 & G4).
    apply vec_fall2_cons_inv in G1 as (G1 & G2).
    destruct (H1 _ _ G1 G3) as [ F0 | F0 ].
    + destruct (IH2 _ _ G2 G4) as [ F | (p & q & F) ]; auto with vec_db.
      right; exists (idx_nxt p), (idx_nxt q); eauto.
    + right; exists idx_fst, idx_fst; auto.
  Qed.

  Fact vec_embed_disj_inv_gen n (u u' : vec _ n) m (v v' : vec _ m) :
        vec_embed (λ x x', ∀y y', f x y → g x' y' → R y y' ∨ T x x' y y') u v
      → vec_fall2 f u u'
      → vec_fall2 g v v'
      → vec_embed R u' v' ∨ ∃ i j, T u⦃i⦄ v⦃j⦄ u'⦃i⦄ v'⦃j⦄.
  Proof.
    induction 1 as [ | n x u m y v H1 H2 IH2
                     | n   u m y v H1 IH2 ]; intros G1 G2; auto.
    + vec invert u'; vec invert v'; auto with vec_db.
    + vec invert u' as x' u'; vec invert v' as y' v'.
      apply vec_fall2_cons_inv in G2 as (G3 & G4).
      apply vec_fall2_cons_inv in G1 as (G1 & G2).
      destruct (H1 _ _ G1 G3) as [ F0 | F0 ].
      * destruct (IH2 _ _ G2 G4) as [ F | (p & q & F) ]; auto with vec_db.
        right; exists (idx_nxt p), (idx_nxt q); auto.
      * right; exists idx_fst, idx_fst; auto.
    + vec invert v' as y' v'.
      apply vec_fall2_cons_inv in G2 as (G3 & G4).
      destruct (IH2 _ _ G1 G4) as [ F | (p & q & F) ]; auto with vec_db.
      right; exists p, (idx_nxt q); auto.
  Qed.

End vec_embed_disj_inv_gen.

Section vec_embed_disj_inv.

  Variable (X₁ X₂ Y₁ Y₂ : Type)
           (P : X₁ → Y₁ → Prop)
           (Q : X₂ → Y₂ → Prop)
           (R T : Y₁ → Y₂ → Prop).

  Fact vec_embed_disj_inv n (u u' : vec _ n) m (v v' : vec _ m) :
        vec_embed (λ x x', ∀y y', P x y → Q x' y' → R y y' ∨ T y y') u v
      → vec_fall2 P u u'
      → vec_fall2 Q v v'
      → vec_embed R u' v' ∨ ∃ i j, T u'⦃i⦄ v'⦃j⦄.
  Proof. apply vec_embed_disj_inv_gen. Qed.

End vec_embed_disj_inv.

Fact vec_embed_disj_inv' X Y (R T : X → Y → Prop) n (u : vec _ n) m (v : vec _ m) :
        vec_embed (R ∪₂ T) u v → vec_embed R u v ∨ ∃ i j, T u⦃i⦄ v⦃j⦄.
Proof.
  intros H.
  apply vec_embed_disj_inv with (P := eq) (Q := eq) (u := u) (v := v).
  2,3: red; auto.
  revert H; apply vec_embed_mono; intros; subst; auto.
Qed.

Fact vec_embed_rel_lift_inv X (R : rel₂ X) a n (u : vec _ n) m (v : vec _ m) :
       vec_embed (λ x y, R x y ∨ R a x) u v → vec_embed R u v ∨ ∃i, R a u⦃i⦄.
Proof. intros H; apply vec_embed_disj_inv' in H as [ | (? & _ & ?) ]; eauto. Qed.

Section vec_fall2_embed_disj_special.

  Variables (X₁ X₂ Y₁ Y₂ : Type)
            (f : X₁ → Y₁ → Prop)
            (g : X₂ → Y₂ → Prop)
            (R : Y₁ → Y₂ → Prop)
            (T : X₁ → Prop).

  Fact vec_fall2_disj_special n (u u' : vec _ n) v v' :
        vec_fall2 (λ x x', ∀ y y', f x y → g x' y' → R y y' ∨ T x) u v
      → vec_fall2 f u u'
      → vec_fall2 g v v'
      → vec_fall2 R u' v' ∨ ∃i, T u⦃i⦄.
  Proof.
    intros HR HP HQ.
    apply vec_fall2_disj_inv_gen
      with (T := λ x _ _ _, T x) (u' := u') (v' := v')
      in HR
      as [ | (? & ? & ?) ]; eauto.
  Qed.

  Fact vec_embed_disj_special n (u u' : vec _ n) m (v v' : vec _ m) :
        vec_embed (λ x x', ∀ y y', f x y → g x' y' → R y y' ∨ T x) u v
      → vec_fall2 f u u'
      → vec_fall2 g v v'
      → vec_embed R u' v' ∨ ∃i, T u⦃i⦄.
  Proof.
    intros HR HP HQ.
    apply vec_embed_disj_inv_gen
      with (T := λ x _ _ _, T x) (u' := u') (v' := v')
      in HR
      as [ | (? & ? & ?) ]; eauto.
  Qed.

End vec_fall2_embed_disj_special.
