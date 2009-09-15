(*
Copyright © 2007-2008 Russell O’Connor

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

Require Export StepQsec.
Require Import Prelength.
Require Import L1metric.
Require Export LinfMetricMonad.
Require Import OpenUnit.
Require Import QArith.
Require Import QMinMax.
Require Import Qabs.
Require Import Qordfield.
Require Import Qmetric.
Require Import COrdFields2.
Require Import CornTac.

Set Implicit Arguments.

Open Local Scope sfstscope.
Open Local Scope StepQ_scope.

Opaque Qmax Qabs.

(**
*** Sup for Step Functions on Q.
*)
Definition StepQSup : (StepQ)->Q := StepFfold (fun x => x) (fun b (x y:QS) => Qmax x y)%Q.

(** The Sup of the glue of two step functions. *)
Lemma StepQSup_glue : forall o s t, (StepQSup (glue o s t) = Qmax (StepQSup s) (StepQSup t))%Q.
Proof.
reflexivity.
Qed.

(** The sup of the split of a step function. *)
Lemma StepQSupSplit : forall (o:OpenUnit) x, 
 (StepQSup x == Qmax (StepQSup (SplitL x o)) (StepQSup (SplitR x o)))%Q.
Proof.
intros o x.
revert o.
induction x using StepF_ind.
 intros o.
 change (x == Qmax x x)%Q.
 rewrite Qmax_idem.
 reflexivity.
intros s.
apply SplitLR_glue_ind; intros H.
  change (Qmax (StepQSup x1) (StepQSup x2) == Qmax (StepQSup (SplitL x1 (OpenUnitDiv s o H)))
    (Qmax (StepQSup (SplitR x1 (OpenUnitDiv s o H))) (StepQSup x2)))%Q.
  rewrite Qmax_assoc.
  rewrite <- IHx1.
  reflexivity.
 change (Qmax (StepQSup x1) (StepQSup x2) == Qmax (Qmax (StepQSup x1) (StepQSup (SplitL x2 (OpenUnitDualDiv s o H))))
   (StepQSup (SplitR x2 (OpenUnitDualDiv s o H))))%Q.
 rewrite <- Qmax_assoc.
 rewrite <- IHx2.
 reflexivity.
reflexivity.
Qed. 
(* begin hide *)
Add Morphism StepQSup 
  with signature  (@StepF_eq _) ==>  Qeq
 as StepQSup_wd.
unfold IntegralQ.
induction x using StepF_ind.
intros x2 H. simpl. induction x2 using StepF_ind.
  simpl.  auto with *.
 change (StepQSup (glue o x2_1 x2_2))%Q with
  (Qmax (StepQSup x2_1) (StepQSup x2_2)).
 destruct H as [H0 H1] using (eq_glue_ind x2_1).
 rewrite <- IHx2_1; auto with *.
 rewrite <- IHx2_2; auto with *.
intros y H.
destruct H as [H0 H1] using (glue_eq_ind x1).
change (StepQSup (glue o x1 x2))%Q with
 (Qmax (StepQSup x1) (StepQSup x2)).
rewrite (IHx1 _ H0).
rewrite (IHx2 _ H1).
symmetry.
apply StepQSupSplit.
Qed.
(* end hide *)
(** How the sup interacts with various arithmetic operations on step functions. *)
Lemma StepQSup_resp_le : forall x y, x <= y -> (StepQSup x <= StepQSup y)%Q.
Proof.
apply: StepF_ind2; auto.
 intros s s0 t t0 Hs Ht.
 rewrite Hs Ht; auto.
intros o s s0 t t0 H0 H1.
unfold StepQ_le.
rewriteStepF.
intros [Hl Hr].
repeat rewrite StepQSup_glue.
apply Qmax_le_compat; auto.
Qed.

Lemma StepQSup_plus : forall x y, (StepQSup (x + y) <= StepQSup x + StepQSup y )%Q.
Proof.
apply StepF_ind2; auto with *.
 intros s s0 t t0 Hs Ht.
 rewrite Hs Ht; auto.
intros o s s0 t t0 H0 H1.
unfold StepQplus.
rewriteStepF.
repeat rewrite StepQSup_glue.
eapply Qle_trans;[apply Qmax_le_compat;[apply H0|apply H1]|].
rewrite Qmax_plus_distr_l.
apply Qmax_le_compat;
 apply: plus_resp_leEq_lft; simpl; auto with *.
Qed.

(** The Linf metric on step function over Q. *)
Definition LinfStepQ : MetricSpace := StepFSup Q_as_MetricSpace.

Definition LinfStepQPrelengthSpace := StepFSupPrelengthSpace QPrelengthSpace.

(** Sup is uniformly continuous. *)
Lemma sup_uc_prf : is_UniformlyContinuousFunction (StepQSup:LinfStepQ -> Q) Qpos2QposInf.
Proof.
intros e x y.
simpl.
rewrite Qball_Qabs.
revert x y.
apply: StepF_ind2.
  intros s s0 t t0 Hs Ht.
  simpl.
  rewrite Hs Ht.
  auto.
 intros x y.
 rewrite <- Qball_Qabs.
 auto.
intros o s s0 t t0 H0 H1 H2.
simpl in *.
repeat rewrite StepQSup_glue.
assert (X:forall a b, (-(a-b)==b-a)%Q).
 intros; ring.
unfold StepFSupBall in H2.
revert H2.
rewriteStepF.
intros [H2a H2b].
apply Qabs_case; intros H;
[|rewrite <- Qabs_opp in H0, H1; rewrite -> X in *];
 (rewrite Qmax_minus_distr_l;
 unfold Qminus;
 apply Qmax_lub;[|clear H0; rename H1 into H0];
  (eapply Qle_trans;[|apply H0; auto]);
  (eapply Qle_trans;[|apply Qle_Qabs]);
  unfold Qminus;
  apply: plus_resp_leEq_lft; simpl; auto with *).
Qed.

Open Local Scope uc_scope.

Definition StepQSup_uc : LinfStepQ --> Q_as_MetricSpace
:= Build_UniformlyContinuousFunction sup_uc_prf.

(** There is an injection from Linf to L1. *)
Lemma LinfAsL1_uc_prf : is_UniformlyContinuousFunction (fun (x:LinfStepQ) => (x:L1StepQ)) Qpos2QposInf.
Proof.
intros e.
apply: StepF_ind2.
  simpl.
  intros s s0 t t0 Hs Ht H.
  rewrite <- Hs , <- Ht.
  assumption.
 intros x y Hxy.
 change (Qball e x y) in Hxy.
 rewrite ->  Qball_Qabs in Hxy.
 apply Hxy.
intros o s s0 t t0 Hst Hst0 H.
simpl.
unfold L1Ball.
unfold L1Distance.
unfold L1Norm.
unfold StepQminus.
rewrite MapGlue.
rewrite ApGlueGlue.
unfold StepQabs.
rewrite MapGlue.
rewrite Integral_glue.
setoid_replace (e:Q) with (o*e + (1-o)*e)%Q by ring.
simpl in H.
unfold StepFSupBall, StepFfoldProp in H.
simpl in H.
rewrite MapGlue in H.
rewrite ApGlueGlue in H.
destruct H as [H0 H1].
apply Qplus_le_compat.
 repeat rewrite (Qmult_comm o).
 apply Qmult_le_compat_r; auto with *.
 apply Hst.
 assumption.
repeat rewrite (Qmult_comm (1-o)).
apply Qmult_le_compat_r; auto with *.
apply Hst0.
assumption.
Qed.

Definition LinfAsL1 : LinfStepQ --> L1StepQ
:= Build_UniformlyContinuousFunction LinfAsL1_uc_prf.