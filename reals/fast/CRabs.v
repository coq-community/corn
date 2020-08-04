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

Lemma CRle_abs : forall x:CR, (x <= CRabs x)%CR.
Proof.
  intros x e1. simpl.
  unfold Cap_raw. simpl.
  apply (Qle_trans _ (approximate x ((1 # 2) * e1)%Qpos + - approximate x ((1 # 2) * e1)%Qpos)).
  rewrite Qplus_opp_r.
  apply (Qopp_le_compat 0), Qpos_nonneg.
  apply Qplus_le_l. apply Qabs.Qle_Qabs.
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

Lemma CRabs_triangle : forall (x y : CR),
    CRabs (x+y) <= CRabs x + CRabs y.
Proof.
  intros. apply CRabs_AbsSmall. split.
  2: apply CRplus_le_compat; apply CRle_abs.
  rewrite CRopp_plus_distr.
  apply CRplus_le_compat; apply CRopp_le_cancel;
    rewrite CRopp_opp; rewrite <- CRabs_opp; apply CRle_abs.
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

Lemma CRdistance_triangle : forall (x y z : CR),
    CRdistance x z <= CRdistance x y + CRdistance y z.
Proof.
  intros. unfold CRdistance.
  setoid_replace (x-z) with (x-y + (y-z))
    by (unfold canonical_names.equiv; ring).
  apply CRabs_triangle.
Qed. 

Lemma regFunBall_e2 : forall (X: MetricSpace) (x y:Complete X) (e:Q),
    (forall d:Qpos, ball (proj1_sig d + e)
                    (approximate x ((1#2)*d)%Qpos)
                    (approximate y ((1#2)*d)%Qpos))
    -> ball e x y.
Proof.
 intros X x y e H.
 apply ball_closed.
 intros d dpos.
 setoid_replace (e + d)%Q
   with ((1#2)*((1#2)*d)
         + ((1#2)*((1#2)*d) + e+(1#2)*((1#2)*d))
         + (1#2)*((1#2)*d))%Q
   by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; ring).
 apply (regFunBall_ball
          x y 
          ((1 # 2) * ((1#2)*d) + e + (1 # 2) * ((1#2)*d))%Q
          ((1#2)*((1#2)*exist _ _ dpos))%Qpos
          ((1#2)*((1#2)*exist _ _ dpos))%Qpos ).
 setoid_replace ((1 # 2) * ((1 # 2) * d) + e + (1 # 2) * ((1 # 2) * d))%Q
   with ((1 # 2) * d + e)%Q
   by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; ring). 
 apply (H ((1#2)*(exist _ _ dpos))%Qpos).
Qed.

Lemma CRabs_ball : forall (x y : CR) (e:Q),
    ball e x y <-> (CRabs (x-y) <= 'e)%CR.
Proof.
  assert (forall (x y:CR) e d,
             ball e x y -> 
             (- proj1_sig d <=
              e + approximate x ((1 # 2) * d)%Qpos + - approximate y ((1 # 2) * d)%Qpos)%Q).
  { intros.
    specialize (H ((1#2)*d)%Qpos ((1#2)*d)%Qpos).
    apply AbsSmall_Qabs in H.
    simpl (proj1_sig ((1 # 2) * d)%Qpos) in H.
    rewrite Qabs_Qminus in H.
    apply (Qle_trans _ _ _ (Qle_Qabs _)) in H.
    apply (Qplus_le_r _ _ (proj1_sig d + approximate y ((1#2)*d)%Qpos)).
    ring_simplify.
    setoid_replace ((1 # 2) * proj1_sig d + e + (1 # 2) * proj1_sig d)%Q
      with (proj1_sig d + e)%Q in H
      by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; ring).
    apply (Qplus_le_l _ _ (approximate x ((1#2)*d)%Qpos)) in H.
    ring_simplify in H.
    rewrite (Qplus_comm (proj1_sig d + e)), Qplus_assoc.
    exact H. }
  split.
  - intro H0. 
    rewrite <- (CRdistance_CRle ('e)%CR x y). split.
    + apply (CRplus_le_r _ _ ('e)%CR). ring_simplify.
      rewrite CRplus_translate.
      intro d. simpl. unfold Cap_raw. simpl.
      apply H, ball_sym, H0.
    + rewrite CRplus_comm, CRplus_translate.
      intro d. simpl. unfold Cap_raw. simpl.
      apply H, H0.
  - intros H0. apply regFunBall_e2. intro d.
    simpl.
    apply CRdistance_CRle in H0. destruct H0.
    rewrite CRplus_comm, CRplus_translate in H1.
    rewrite (CRplus_le_r _ _ ('e)%CR) in H0.
    ring_simplify in H0. rewrite CRplus_translate in H0.
    apply AbsSmall_Qabs, Qabs_Qle_condition. split.
    + specialize (H1 d). simpl in H1.
      unfold Cap_raw in H1. simpl in H1.
      apply (Qplus_le_l _ _ (approximate y ((1#2)*d)%Qpos
                             + proj1_sig d + e)).
      simpl. ring_simplify.
      apply (Qplus_le_l _ _ (approximate y ((1 # 2) * d)%Qpos + proj1_sig d)) in H1.
      simpl in H1. ring_simplify in H1.
      exact H1.
    + specialize (H0 d). simpl in H0.
      unfold Cap_raw in H0. simpl in H0.
      apply (Qplus_le_l _ _ (approximate y ((1#2)*d)%Qpos)).
      simpl. ring_simplify.
      apply (Qplus_le_l _ _ (approximate x ((1 # 2) * d)%Qpos + proj1_sig d)) in H0.
      simpl in H0. ring_simplify in H0.
      rewrite <- Qplus_assoc, Qplus_comm. exact H0.
Qed.


Import MathClasses.interfaces.canonical_names.

Instance CR_abs : Abs CR.
Proof.
  intro x. exists (CRabs x).
  split; [apply CRabs_pos | apply CRabs_neg].
Defined.

