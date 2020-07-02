(*
Copyright © 2008 Russell O’Connor

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

Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Export CoRN.model.totalorder.QposMinMax.
Require Export CoRN.reals.fast.CRArith.
Require Import CoRN.model.metric2.Qmetric.
Require Import Coq.QArith.Qabs.
Require Import CoRN.model.totalorder.QMinMax.
Require Import CoRN.logic.Stability.

Local Open Scope Q_scope.
(**
** Absolute Value
*)
Lemma Qabs_uc_prf : is_UniformlyContinuousFunction
 (Qabs:Q_as_MetricSpace -> Q_as_MetricSpace) Qpos2QposInf.
Proof.
 intros e a b Hab.
 simpl in *.
 unfold Qball in *.
 rewrite <- AbsSmall_Qabs in *.
 apply Qabs_case.
  intros _.
  eapply Qle_trans;[|apply Hab].
  apply Qabs_triangle_reverse.
 intros _.
 setoid_replace (- (Qabs a - Qabs b))
   with (Qabs b - Qabs a)
   by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; ring).
 rewrite Qabs_Qminus in Hab.
 eapply Qle_trans;[|apply Hab].
 apply Qabs_triangle_reverse.
Qed.

Local Open Scope uc_scope.

Definition Qabs_uc : Q_as_MetricSpace --> Q_as_MetricSpace :=
Build_UniformlyContinuousFunction Qabs_uc_prf.

Definition CRabs : CR --> CR := Cmap QPrelengthSpace Qabs_uc.

Lemma approximate_CRabs (x: CR) (e: Qpos):
  approximate (CRabs x) e = Qabs (approximate x e).
Proof. reflexivity. Qed.

Lemma CRabs_AbsSmall : forall a b : CR, (CRabs b <= a)%CR <-> (-a <= b /\ b <= a)%CR.
Proof.
  split.
  - intros. split.
    + intro e. simpl. unfold Cap_raw. simpl. 
      specialize (H e). simpl in H.
      unfold Cap_raw in H. simpl in H.
      apply (Qle_trans _ _ _ H).
      rewrite Qopp_involutive, Qplus_comm.
      apply Qplus_le_l.
      rewrite <- (Qopp_involutive (approximate b ((1#2)*e)%Qpos)) at 2.
      apply Qopp_le_compat.
      rewrite <- Qabs_opp. apply Qle_Qabs.
    + intro e. simpl. unfold Cap_raw. simpl. 
      specialize (H e). simpl in H.
      unfold Cap_raw in H. simpl in H.
      apply (Qle_trans _ _ _ H).
      apply Qplus_le_r, Qopp_le_compat, Qle_Qabs.
  - intros [H H0]. intro e. simpl. unfold Cap_raw. simpl.
    specialize (H e). simpl in H.
    unfold Cap_raw in H. simpl in H.
    specialize (H0 e). simpl in H0.
    unfold Cap_raw in H0. simpl in H0.
    apply (Qplus_le_l _ _ (Qabs (approximate b ((1 # 2) * e)%Qpos) + proj1_sig e)).
    simpl. ring_simplify.
    apply Qabs_Qle_condition. split.
    + apply (Qplus_le_l _ _ (- approximate a ((1 # 2) * e)%Qpos)) in H.
      simpl in H. ring_simplify in H. ring_simplify. exact H.
    + apply (Qplus_le_l _ _ (proj1_sig e + approximate b ((1 # 2) * e)%Qpos)) in H0.
      simpl in H0. ring_simplify in H0. exact H0.
Qed.

Local Open Scope CR_scope.

Lemma CRabs_pos : forall x:CR, 0 <= x -> CRabs x == x.
Proof.
  intros x H. apply CRle_def. split.
  - apply CRabs_AbsSmall. split. 2: apply CRle_refl.
    apply (@CRle_trans _ 0). 2: exact H.
    rewrite <- CRopp_0. apply CRopp_le_compat, H.
  - intro e. simpl. unfold Cap_raw; simpl.
    apply (Qle_trans _ 0).
    apply (Qopp_le_compat 0), Qpos_nonneg.
    rewrite <- Qle_minus_iff. apply Qle_Qabs.
Qed.

Lemma CRabs_0: CRabs 0 == 0.
Proof. apply CRabs_pos, CRle_refl. Qed.

Lemma CRabs_neg: forall x, x <= 0 -> CRabs x == - x.
Proof.
  intros x H. apply CRle_def. split.
  - apply CRabs_AbsSmall. split.
    apply (CRplus_le_l _ _ (-x)). ring_simplify.
    apply CRle_refl.
    apply (@CRle_trans _ 0). exact H.
    rewrite <- CRopp_0. apply CRopp_le_compat, H.
  - intro e. simpl. unfold Cap_raw; simpl.
    apply (Qle_trans _ 0).
    apply (Qopp_le_compat 0), Qpos_nonneg.
    rewrite <- Qle_minus_iff, <- Qabs_opp.
    apply Qle_Qabs.
Qed.

Lemma CRabs_cases
  (P: CR -> Prop)
  {Pp: Proper (@st_eq _ ==> iff) P}
  {Ps: forall x, Stable (P x)}:
    forall x, ((0 <= x -> P x) /\ (x <= 0 -> P (- x))) <-> P (CRabs x).
Proof with auto.
 intros.
 apply from_DN.
 apply (DN_bind (CRle_dec x 0)).
 intro.
 apply DN_return.
 destruct H.
  rewrite (CRabs_neg _ c)...
  intuition.
  revert H.
  rewrite (proj2 (CRle_def x 0))...
  rewrite CRopp_0...
 rewrite (CRabs_pos _ c)...
 intuition.
 revert H.
 rewrite (proj2 (CRle_def x 0))...
 rewrite CRopp_0...
Qed.

Lemma CRabs_opp (x: CR): CRabs (-x) == CRabs x.
Proof with auto.
 intros.
 apply from_DN.
 apply (DN_bind (CRle_dec x 0)).
 intros [A | B]; apply DN_return.
  rewrite (CRabs_neg _ A).
  apply CRabs_pos.
  change (-0 <= -x).
  apply -> CRle_opp...
 rewrite (CRabs_pos _ B).
 rewrite CRabs_neg.
  apply CRopp_opp.
 change (-x <= -0).
 apply -> CRle_opp...
Qed.

Lemma CRabs_nonneg (x: CR): 0 <= CRabs x.
Proof.
  intro e. simpl. unfold Cap_raw; simpl.
  rewrite Qplus_0_r. apply (Qle_trans _ 0).
  apply (Qopp_le_compat 0), Qpos_nonneg.
  apply Qabs_nonneg.
Qed.

Lemma CRabs_scale (a : Q) (x : CR) : CRabs (scale a x) == scale (Qabs a) (CRabs x).
Proof.
apply lift_eq_complete with (f := uc_compose CRabs (scale a)) (g := uc_compose (scale (Qabs a)) CRabs).
intros q e1 e2. change (@ball Q_as_MetricSpace (proj1_sig e1 + proj1_sig e2) (Qabs (a * q)) (Qabs a * Qabs q)%Q).
apply <- ball_eq_iff. apply Qabs_Qmult.
apply (Qpos_ispos (e1+e2)).
Qed.

(* begin hide *)
(* Another proof *)

Lemma CRabs_scale' (a : Q) (x : CR) : CRabs (scale a x) == scale (Qabs a) (CRabs x).
Proof.
unfold CRabs, scale. setoid_rewrite <- fast_MonadLaw2.
apply map_eq_complete. intro q. apply Qabs_Qmult.
Qed.

(* end hide *)

Lemma CRabs_CRmult_Q (a : Q) (x : CR) : CRabs ('a * x) == '(Qabs a) * (CRabs x).
Proof. rewrite !CRmult_scale. apply CRabs_scale. Qed.

Definition CRdistance (x y: CR): CR := CRabs (x - y).

Lemma CRdistance_CRle (r x y: CR): x - r <= y /\ y <= x + r <-> CRdistance x y <= r.
Proof.
 intros. unfold CRdistance.
 rewrite CRabs_AbsSmall.
 simpl.
 rewrite (CRplus_le_l (x - r) y (r - y)).
 CRring_replace (r - y + (x - r)) (x - y).
 CRring_replace (r - y + y) r.
 rewrite (CRplus_le_l y (x + r) (-r - y)).
 CRring_replace (-r - y + y) (-r).
 CRring_replace (- r - y + (x + r)) (x - y).
 intuition.
Qed.

Lemma CRdistance_comm (x y: CR): CRdistance x y == CRdistance y x.
Proof.
 unfold CRdistance. intros.
 CRring_replace (x - y) (-(y - x)).
 apply CRabs_opp.
Qed.

Import MathClasses.interfaces.canonical_names.

Instance CR_abs : Abs CR.
Proof.
  intro x. exists (CRabs x).
  split; [apply CRabs_pos | apply CRabs_neg].
Defined.

