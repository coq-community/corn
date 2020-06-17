(*
Copyright © 2006-2008 Russell O’Connor

Permission is hereby granted, free of charge, to any person obtaining a copy of
this proof and associated documentation files (the "Proof"), to deal in
the Proof without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Proof, and to permit persons to whom the Proof is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Proof.

THE PROOF IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE PROOF OR THE USE OR OTHER DEALINGS IN THE PROOF.
*)

Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.QArith.QArith Coq.QArith.Qabs.
Require Import Coq.QArith.Qpower Coq.QArith.Qround.
Require Import CoRN.model.totalorder.QMinMax.
Require Import CoRN.order.TotalOrder.

(** Positive rational numbers *)

Definition Qpos: Set := sig (Qlt 0).
Definition QposEq (a b:Qpos) := Qeq (proj1_sig a) (proj1_sig b).
Lemma QposEq_refl : forall a : Qpos, QposEq a a.
Proof.
  reflexivity.
Qed.
Lemma Qpos_ispos : forall a:Qpos, 0 < proj1_sig a.
Proof.
  intros. destruct a; exact q.
Qed.
Lemma Qpos_nonneg : forall a:Qpos, 0 <= proj1_sig a.
Proof.
  intros. apply Qlt_le_weak. destruct a; exact q.
Qed.
Lemma Qpos_nonzero : forall a:Qpos, ~(proj1_sig a == 0).
Proof.
  intros. intro abs. destruct a. simpl in abs.
  rewrite abs in q. exact (Qlt_irrefl 0 q).
Qed.
Definition Qpos_plus (x y:Qpos) : Qpos.
Proof.
  exists (proj1_sig x + proj1_sig y).
  apply (Qle_lt_trans _ (0+0) _ (Qle_refl _)).
  apply Qplus_lt_le_compat. destruct x; assumption.
  apply Qlt_le_weak; destruct y; assumption.
Defined.
Definition Qpos_mult (x y:Qpos) : Qpos.
Proof.
  exists (proj1_sig x * proj1_sig y).
  apply (Qle_lt_trans _ (proj1_sig x * 0)).
  rewrite Qmult_0_r. apply Qle_refl.
  apply Qmult_lt_l. destruct x; assumption.
  destruct y; assumption.
Defined.
Bind Scope Qpos_scope with Qpos.
Delimit Scope Qpos_scope with Qpos.

Notation "a # b" := (exist (Qlt 0) (Qmake (Z.pos a) b) eq_refl) (at level 55, no associativity) : Qpos_scope.
Infix "+" := Qpos_plus : Qpos_scope.
Infix "*" := Qpos_mult : Qpos_scope.

Definition comparison_eq_dec (a b: comparison): { a = b } + { a <> b}.
 destruct a, b; try (left; reflexivity); try (right; discriminate).
Defined.
Lemma Zlt_hprop (a b: Z) (p q: (a < b)%Z): p = q.
Proof.
 unfold Z.lt in *. destruct p. intros.
 apply (Eqdep_dec.K_dec_set comparison_eq_dec).
 reflexivity.
Qed.
Lemma Qpos_hprop (a b: Qpos)
  : proj1_sig a = proj1_sig b -> a = b.
Proof.
 destruct a, b. intros H. simpl in H. subst x0.
 f_equal. exact (Zlt_hprop _ _ q q0).
Qed.

Lemma Qpos_red_ispos : forall a:Qpos, 0 < Qred (proj1_sig a).
Proof.
  destruct a. simpl.
  rewrite -> Qred_correct. exact q.
Qed. 
Definition Qpos_red (a:Qpos) : Qpos
  := exist _ (Qred (proj1_sig a)) (Qpos_red_ispos a).
(* By reducing, we get true equality *)
Lemma Qpos_red_eq : forall (a b : Qpos), QposEq a b -> Qpos_red a = Qpos_red b.
Proof.
 intros p q H.
 apply Qpos_hprop. simpl.
 apply Qred_complete. exact H.
Qed.

Definition Qpos_sum (l:list Qpos) : Q := List.fold_right
(fun (x:Qpos) (y:Q) => proj1_sig x + y) 0%Q l.
Lemma Qpos_sum_nonneg : forall l, 0 <= Qpos_sum l.
Proof.
 induction l. apply Qle_refl.
 simpl. apply (Qle_trans _ (0+0) _ (Qle_refl _)).
 apply Qplus_le_compat.
 destruct a. apply Qlt_le_weak, q. exact IHl.
Qed.
Definition Qpos_sub (a b : Q)
  : a < b
    -> {c : Qpos | b == a + proj1_sig c}.
Proof.
  intro H. assert (0 < b - a).
  { apply (Qplus_lt_l _ _ a).
    destruct a,b. simpl. ring_simplify. exact H. }
  exists (exist _ _ H0).
  destruct a,b; unfold QposEq; simpl. ring_simplify. reflexivity.
Defined. 
Definition QabsQpos (x : Q) : Qpos :=
  match x with
  | 0 # _ => exist (Qlt 0) (1#1) eq_refl
  | (Zpos an) # ad => exist (Qlt 0) (Z.pos an # ad) eq_refl
  | (Zneg an) # ad => exist (Qlt 0) (Z.pos an # ad) eq_refl
  end.
Definition Qpos_inv (x : Qpos) : Qpos.
Proof.
  exists (/ proj1_sig x). destruct x. 
  apply Qinv_lt_0_compat, q.
Defined.
Lemma Qpos_power_ispos : forall (x:Qpos) (z : Z), 0 < proj1_sig x^z.
Proof.
 intros x z.
 assert (0 < proj1_sig x) as xpos by (destruct x; exact q).
 destruct (Qle_lt_or_eq
             _ _ (Qpower_pos (proj1_sig x) z (Qlt_le_weak _ _ xpos)));[assumption|].
 destruct z.
   discriminate H.
  elim (Qpower_not_0_positive (proj1_sig x) p).
  destruct x. intro abs. simpl in abs. clear H xpos. rewrite abs in q.
  exact (Qlt_irrefl 0 q).
  symmetry; assumption.
 elim (Qpower_not_0_positive (/proj1_sig x) p).
  change (~proj1_sig (Qpos_inv x) == 0).
  destruct (Qpos_inv x). intro abs. simpl in abs. clear H xpos. rewrite abs in q.
  exact (Qlt_irrefl 0 q).
 change ((/proj1_sig x)^Z.pos p==0).
 rewrite -> Qinv_power.
 symmetry; assumption.
Qed.
Definition Qpos_power (x:Qpos) (z:Z) : Qpos
  := exist _ _ (Qpos_power_ispos x z).

Definition Qpos_ceiling (q: Qpos): positive :=
  match Qceiling (proj1_sig q) with
  | Zpos p => p
  | _ => 1%positive (* impossible *)
  end.
Lemma Qpos_mult_le_compat : forall (a b c d : Qpos),
    proj1_sig a <= proj1_sig c
    -> proj1_sig b <= proj1_sig d
    -> proj1_sig a * proj1_sig b <= proj1_sig c * proj1_sig d.
Proof.
  intros. apply (Qle_trans _ (proj1_sig c * proj1_sig b)).
  apply Qmult_le_compat_r. exact H. apply Qpos_nonneg.
  rewrite Qmult_comm. rewrite (Qmult_comm (proj1_sig c)).
  apply Qmult_le_compat_r. exact H0. apply Qpos_nonneg.
Qed.


(**
** Example of a Total Order: <Qpos, Qpos_le, Qpos_min, Qpos_max>
*)

Definition Qpos_le_total (x y : Qpos)
  : {proj1_sig x <= proj1_sig y} + {proj1_sig y <= proj1_sig x} :=
match Qlt_le_dec_fast (proj1_sig x) (proj1_sig y) with
| left p => left _ (Qlt_le_weak _ _ p)
| right p => right _ p
end.

Lemma Qpos_eq_le_def : forall (x y: Qpos),
    proj1_sig x == proj1_sig y
    <-> proj1_sig x <= proj1_sig y /\ proj1_sig y <= proj1_sig x.
Proof.
 intros.
 split.
  intros H; rewrite -> H.
  firstorder using Qle_refl.
 firstorder using Qle_antisym.
Qed.

Definition Qpos_monotone : (Qpos -> Qpos) -> Prop
  := Default.monotone (fun (x y:Qpos) => proj1_sig x <= proj1_sig y).
Definition Qpos_antitone : (Qpos -> Qpos) -> Prop
  := Default.antitone (fun (x y:Qpos) => proj1_sig x <= proj1_sig y).
Definition Qpos_min : Qpos -> Qpos -> Qpos := Default.min _ _ Qpos_le_total.
Definition Qpos_max : Qpos -> Qpos -> Qpos := Default.max _ _ Qpos_le_total.

Definition Qpos_min_case :
  forall (x y:Qpos) (P : Qpos -> Type),
    (proj1_sig x <= proj1_sig y -> P x) -> (proj1_sig y <= proj1_sig x -> P y) -> P (Qpos_min x y) :=
 Default.min_case _ _ Qpos_le_total.
Definition Qpos_max_case :
  forall (x y:Qpos) (P : Qpos -> Type),
    (proj1_sig y <= proj1_sig x -> P x) -> (proj1_sig x <= proj1_sig y -> P y) -> P (Qpos_max x y) :=
 Default.max_case _ _ Qpos_le_total.

Definition QposTotalOrder : TotalOrder.
Proof.
 apply makeTotalOrder with
     Qpos QposEq (fun (x y:Qpos) => proj1_sig x <= proj1_sig y)
     Qpos_monotone Qpos_antitone Qpos_min Qpos_max.
          exact Qpos_eq_le_def.
         intros; apply Qle_refl.
        intros x y z; apply Qle_trans.
       exact Qpos_le_total.
      firstorder using PartialOrder.Default.monotone_def.
     firstorder using PartialOrder.Default.antitone_def.
    apply (TotalOrder.Default.min_def1 _ _ _ Qpos_eq_le_def Qpos_le_total).
   apply (TotalOrder.Default.min_def2 _ _ _ Qpos_eq_le_def Qpos_le_total).
  apply (TotalOrder.Default.max_def1 _ _ _ Qpos_eq_le_def Qpos_le_total).
 apply (TotalOrder.Default.max_def2 _ _ _ Qpos_eq_le_def Qpos_le_total).
Defined.
(* begin hide *)
Add Morphism Qpos_min
    with signature QposEq ==> QposEq ==> QposEq
      as Qpos_min_compat.
Proof.
  exact (@meet_compat QposTotalOrder).
Qed.

Add Morphism Qpos_max
    with signature QposEq ==> QposEq ==> QposEq
      as Qpos_max_compat.
Proof.
 exact (@join_compat QposTotalOrder).
Qed.
(* end hide *)
Section QTotalOrder.

Let Qto := QposTotalOrder.

Definition Qpos_min_lb_l : forall x y : Qpos, proj1_sig (Qpos_min x y) <= proj1_sig x
  := @meet_lb_l Qto.
Definition Qpos_min_lb_r : forall x y : Qpos, proj1_sig (Qpos_min x y) <= proj1_sig y
  := @meet_lb_r Qto.
Definition Qpos_min_glb : forall x y z : Qpos,
    proj1_sig z <= proj1_sig x -> proj1_sig z <= proj1_sig y -> proj1_sig z <= proj1_sig (Qpos_min x y)
  := @meet_glb Qto.
Definition Qpos_min_comm : forall x y : Qpos, QposEq (Qpos_min x y) (Qpos_min y x)
  := @meet_comm Qto.
Definition Qpos_min_assoc : forall x y z : Qpos, QposEq (Qpos_min x (Qpos_min y z)) (Qpos_min (Qpos_min x y) z)
  := @meet_assoc Qto.
Definition Qpos_min_idem : forall x : Qpos, QposEq (Qpos_min x x) x
  := @meet_idem Qto.
Definition Qpos_le_min_l : forall x y : Qpos, proj1_sig x <= proj1_sig y <-> QposEq (Qpos_min x y) x
  := @le_meet_l Qto.
Definition Qpos_le_min_r : forall x y : Qpos, proj1_sig y <= proj1_sig x <-> QposEq (Qpos_min x y) y
  := @le_meet_r Qto.
Definition Qpos_min_irred : forall x y: Qpos, {QposEq (Qpos_min x y) x} + {QposEq (Qpos_min x y) y}
  := @meet_irred Qto.
Definition Qpos_min_monotone_r : forall a : Qpos, Qpos_monotone (Qpos_min a) :=
 @meet_monotone_r Qto.
Definition Qpos_min_monotone_l : forall a : Qpos, Qpos_monotone (fun x => Qpos_min x a) :=
 @meet_monotone_l Qto.
Definition Qpos_min_le_compat :
  forall w x y z : Qpos, proj1_sig w <= proj1_sig y -> proj1_sig x <= proj1_sig z
                    -> proj1_sig (Qpos_min w x) <= proj1_sig (Qpos_min y z) :=
 @meet_le_compat Qto.

Definition Qpos_max_ub_l : forall x y : Qpos, proj1_sig x <= proj1_sig (Qpos_max x y)
  := @join_ub_l Qto.
Definition Qpos_max_ub_r : forall x y : Qpos, proj1_sig y <= proj1_sig (Qpos_max x y)
  := @join_ub_r Qto.
Definition Qpos_max_glb : forall x y z : Qpos, proj1_sig x <= proj1_sig z -> proj1_sig y <= proj1_sig z -> proj1_sig (Qpos_max x y) <= proj1_sig z
  := @join_lub Qto.
Definition Qpos_max_comm : forall x y : Qpos, QposEq (Qpos_max x y) (Qpos_max y x)
  := @join_comm Qto.
Definition Qpos_max_assoc : forall x y z : Qpos, QposEq (Qpos_max x (Qpos_max y z)) (Qpos_max (Qpos_max x y) z)
  := @join_assoc Qto.
Definition Qpos_max_idem : forall x : Qpos, QposEq (Qpos_max x x) x := @join_idem Qto.
Definition Qpos_le_max_l : forall x y : Qpos, proj1_sig y <= proj1_sig x <-> QposEq (Qpos_max x y) x
  := @le_join_l Qto.
Definition Qpos_le_max_r : forall x y : Qpos, proj1_sig x <= proj1_sig y <-> QposEq (Qpos_max x y) y
  := @le_join_r Qto.
Definition Qpos_max_irred : forall x y: Qpos, {QposEq (Qpos_max x y) x} + {QposEq (Qpos_max x y) y} := @join_irred Qto.
Definition Qpos_max_monotone_r : forall a : Qpos, Qpos_monotone (Qpos_max a) :=
 @join_monotone_r Qto.
Definition Qpos_max_monotone_l : forall a : Qpos, Qpos_monotone (fun x => Qpos_max x a) :=
 @join_monotone_l Qto.
Definition Qpos_max_le_compat :
 forall w x y z : Qpos, proj1_sig w<=proj1_sig y -> proj1_sig x<=proj1_sig z -> proj1_sig (Qpos_max w x) <= proj1_sig (Qpos_max y z) :=
 @join_le_compat Qto.

Definition Qpos_min_max_absorb_l_l : forall x y : Qpos, QposEq (Qpos_min x (Qpos_max x y)) x
  := @meet_join_absorb_l_l Qto.
Definition Qpos_max_min_absorb_l_l : forall x y : Qpos, QposEq (Qpos_max x (Qpos_min x y)) x :=
 @join_meet_absorb_l_l Qto.
Definition Qpos_min_max_absorb_l_r : forall x y : Qpos, QposEq (Qpos_min x (Qpos_max y x)) x :=
 @meet_join_absorb_l_r Qto.
Definition Qpos_max_min_absorb_l_r : forall x y : Qpos, QposEq (Qpos_max x (Qpos_min y x)) x :=
 @join_meet_absorb_l_r Qto.
Definition Qpos_min_max_absorb_r_l : forall x y : Qpos, QposEq (Qpos_min (Qpos_max x y) x) x :=
 @meet_join_absorb_r_l Qto.
Definition Qpos_max_min_absorb_r_l : forall x y : Qpos, QposEq (Qpos_max (Qpos_min x y) x) x :=
 @join_meet_absorb_r_l Qto.
Definition Qpos_min_max_absorb_r_r : forall x y : Qpos, QposEq (Qpos_min (Qpos_max y x) x) x :=
 @meet_join_absorb_r_r Qto.
Definition Qpos_max_min_absorb_r_r : forall x y : Qpos, QposEq (Qpos_max (Qpos_min y x) x) x :=
 @join_meet_absorb_r_r Qto.

Definition Qpos_min_max_eq : forall x y : Qpos,
    QposEq (Qpos_min x y) (Qpos_max x y) -> QposEq x y :=
 @meet_join_eq Qto.

Definition Qpos_max_min_distr_r : forall x y z : Qpos,
    QposEq (Qpos_max x (Qpos_min y z)) (Qpos_min (Qpos_max x y) (Qpos_max x z))
  := @join_meet_distr_r Qto.
Definition Qpos_max_min_distr_l : forall x y z : Qpos,
    QposEq (Qpos_max (Qpos_min y z) x) (Qpos_min (Qpos_max y x) (Qpos_max z x))
  := @join_meet_distr_l Qto.
Definition Qpos_min_max_distr_r : forall x y z : Qpos,
    QposEq (Qpos_min x (Qpos_max y z)) (Qpos_max (Qpos_min x y) (Qpos_min x z))
  := @meet_join_distr_r Qto.
Definition Qpos_min_max_distr_l : forall x y z : Qpos,
    QposEq (Qpos_min (Qpos_max y z) x) (Qpos_max (Qpos_min y x) (Qpos_min z x))
  := @meet_join_distr_l Qto.

(*I don't know who wants modularity laws, but here they are *)
Definition Qpos_max_min_modular_r : forall x y z : Qpos,
    QposEq (Qpos_max x (Qpos_min y (Qpos_max x z))) (Qpos_min (Qpos_max x y) (Qpos_max x z))
  := @join_meet_modular_r Qto.
Definition Qpos_max_min_modular_l : forall x y z : Qpos,
    QposEq (Qpos_max (Qpos_min (Qpos_max x z) y) z) (Qpos_min (Qpos_max x z) (Qpos_max y z))
  := @join_meet_modular_l Qto.
Definition Qpos_min_max_modular_r : forall x y z : Qpos,
    QposEq (Qpos_min x (Qpos_max y (Qpos_min x z))) (Qpos_max (Qpos_min x y) (Qpos_min x z))
  := @meet_join_modular_r Qto.
Definition Qpos_min_max_modular_l : forall x y z : Qpos,
    QposEq (Qpos_min (Qpos_max (Qpos_min x z) y) z) (Qpos_max (Qpos_min x z) (Qpos_min y z))
  := @meet_join_modular_l Qto.

Definition Qpos_min_max_disassoc : forall x y z : Qpos,
    proj1_sig (Qpos_min (Qpos_max x y) z) <= proj1_sig (Qpos_max x (Qpos_min y z))
  := @meet_join_disassoc Qto.

Lemma Qplus_monotone_r : forall a, Qpos_monotone (Qpos_plus a).
Proof.
 intros a x y Hxy.
 repeat rewrite -> Q_Qpos_plus.
 apply Qplus_le_compat. apply Qle_refl. assumption.
Qed.
Lemma Qplus_monotone_l : forall a, Qpos_monotone (fun x => Qpos_plus x a).
Proof.
 intros a x y Hxy.
 repeat rewrite Q_Qpos_plus.
 apply Qplus_le_compat. assumption. apply Qle_refl.
Qed.

Local Open Scope Qpos_scope.

Definition Qpos_min_plus_distr_r :
  forall x y z : Qpos, QposEq (Qpos_plus x (Qpos_min y z)) (Qpos_min (Qpos_plus x y) (Qpos_plus x z))
  := fun a => @monotone_meet_distr Qto _ (Qplus_monotone_r a).
Definition Qpos_min_plus_distr_l :
  forall x y z : Qpos, QposEq (Qpos_plus (Qpos_min y z) x) (Qpos_min (Qpos_plus y x) (Qpos_plus z x))
  := fun a => @monotone_meet_distr Qto _ (Qplus_monotone_l a).
Definition Qpos_max_plus_distr_r :
  forall x y z : Qpos, QposEq (Qpos_plus x (Qpos_max y z)) (Qpos_max (Qpos_plus x y) (Qpos_plus x z))
  := fun a => @monotone_join_distr Qto _ (Qplus_monotone_r a).
Definition Qpos_max_plus_distr_l :
  forall x y z : Qpos, QposEq (Qpos_plus (Qpos_max y z) x) (Qpos_max (Qpos_plus y x) (Qpos_plus z x))
  := fun a => @monotone_join_distr Qto _ (Qplus_monotone_l a).

End QTotalOrder.

Lemma Q_Qpos_min : forall (x y:Qpos),
    proj1_sig (Qpos_min x y) == Qmin (proj1_sig x) (proj1_sig y).
Proof.
 intros x y.
 unfold Qpos_min.
 unfold Qmin.
 unfold Default.min.
 destruct (Qpos_le_total x y) as [H|H]; destruct (Qle_total (proj1_sig x) (proj1_sig y)) as [H0|H0]; try reflexivity;
   apply Qle_antisym; auto.
Qed.
(* begin hide *)
Hint Rewrite Q_Qpos_min : QposElim.
(* end hide *)
Lemma Q_Qpos_max : forall (x y:Qpos),
    proj1_sig (Qpos_max x y) == Qmax (proj1_sig x) (proj1_sig y).
Proof.
 intros x y.
 unfold Qpos_max.
 unfold Qmax.
 unfold Default.max.
 destruct (Qpos_le_total y x) as [H|H];
   destruct (Qle_total (proj1_sig y) (proj1_sig x)) as [H0|H0]; try reflexivity;
   apply Qle_antisym; auto.
Qed.
(* begin hide *)
Hint Rewrite Q_Qpos_max : QposElim.
(* end hide *)

Lemma Qpos_min_mult_distr_r : forall x y z : Qpos,
    QposEq (Qpos_mult  x (Qpos_min y z)) (Qpos_min (Qpos_mult x y) (Qpos_mult x z)).
Proof.
  intros x y z. unfold QposEq. rewrite Q_Qpos_min.
  simpl. rewrite Q_Qpos_min.
  apply Qmin_mult_pos_distr_r.
  apply Qlt_le_weak. destruct x. exact q.
Qed.
Lemma Qpos_min_mult_distr_l : forall x y z : Qpos,
    QposEq (Qpos_mult (Qpos_min y z) x) (Qpos_min (Qpos_mult y x) (Qpos_mult z x)).
Proof.
  intros x y z. unfold QposEq. rewrite Q_Qpos_min.
  simpl. rewrite Q_Qpos_min.
  apply Qmin_mult_pos_distr_l.
  apply Qlt_le_weak. destruct x. exact q.
Qed.
Lemma Qpos_max_mult_distr_r : forall x y z : Qpos,
    QposEq (Qpos_mult x (Qpos_max y z)) (Qpos_max (Qpos_mult x y) (Qpos_mult x z)).
Proof.
  intros x y z. unfold QposEq. rewrite Q_Qpos_max.
  simpl. rewrite Q_Qpos_max.
  apply Qmax_mult_pos_distr_r.
  apply Qlt_le_weak. destruct x. exact q.
Qed.
Lemma Qpos_max_mult_distr_l : forall x y z : Qpos,
    QposEq (Qpos_mult (Qpos_max y z) x) (Qpos_max (Qpos_mult y x) (Qpos_mult z x)).
Proof.
  intros x y z. unfold QposEq. rewrite Q_Qpos_max.
  simpl. rewrite Q_Qpos_max.
  apply Qmax_mult_pos_distr_l.
  apply Qlt_le_weak. destruct x. exact q.
Qed.
