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

Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Export CoRN.model.structures.StepQsec.
Require Import CoRN.metric2.Prelength.
Require Import CoRN.model.metric2.L1metric.
Require Export CoRN.model.metric2.LinfMetricMonad.
Require Import CoRN.model.structures.OpenUnit.
From Coq Require Import QArith.
Require Import CoRN.model.totalorder.QMinMax.
From Coq Require Import Qabs.
Require Import CoRN.model.ordfields.Qordfield.
Require Import CoRN.model.metric2.Qmetric.
Require Import CoRN.algebra.COrdFields2.
Require Import CoRN.tactics.CornTac.

Set Implicit Arguments.

Local Open Scope sfstscope.
Local Open Scope StepQ_scope.

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
 induction x.
  intros o.
  change (x == Qmax x x)%Q.
  rewrite -> Qmax_idem.
  reflexivity.
 intros s.
 apply SplitLR_glue_ind; intros H.
   change (Qmax (StepQSup x1) (StepQSup x2) == Qmax (StepQSup (SplitL x1 (OpenUnitDiv s o H)))
     (Qmax (StepQSup (SplitR x1 (OpenUnitDiv s o H))) (StepQSup x2)))%Q.
   rewrite -> Qmax_assoc.
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
Proof.
 unfold IntegralQ.
 induction x.
  intros x2 H. simpl. induction x2.
  simpl.  auto with *.
   change (StepQSup (glue o x2_1 x2_2))%Q with (Qmax (StepQSup x2_1) (StepQSup x2_2)).
  destruct H as [H0 H1] using (eq_glue_ind x2_1).
  rewrite <- IHx2_1; auto with *.
  rewrite <- IHx2_2; auto with *.
 intros y H.
 destruct H as [H0 H1] using (glue_eq_ind x1).
 change (StepQSup (glue o x1 x2))%Q with (Qmax (StepQSup x1) (StepQSup x2)).
 rewrite -> (IHx1 _ H0).
 rewrite -> (IHx2 _ H1).
 symmetry.
 apply StepQSupSplit.
Qed.
(* end hide *)
(** How the sup interacts with various arithmetic operations on step functions. *)
Lemma StepQSup_resp_le : forall x y, x <= y -> (StepQSup x <= StepQSup y)%Q.
Proof.
 apply: StepF_ind2; auto.
  intros s s0 t t0 Hs Ht.
  rewrite -> Hs, Ht; auto.
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
  rewrite -> Hs, Ht; auto.
 intros o s s0 t t0 H0 H1.
 unfold StepQplus.
 rewriteStepF.
 repeat rewrite StepQSup_glue.
 eapply Qle_trans;[apply Qmax_le_compat;[apply H0|apply H1]|].
 rewrite -> Qmax_plus_distr_l.
 apply Qmax_le_compat; apply: plus_resp_leEq_lft; simpl; auto with *.
Qed.

(** The Linf metric on step function over Q. *)
Definition LinfStepQ : MetricSpace := StepFSup Q_as_MetricSpace.

Definition LinfStepQPrelengthSpace := StepFSupPrelengthSpace QPrelengthSpace.

Lemma StepF_eq_change_base_setoid_const
  : forall (s : StepFunction.StepF Q) (q : Q),
    (@StepF_eq (msp_as_RSetoid Q_as_MetricSpace) (constStepF q) s)
    <-> (@StepF_eq QS (constStepF q) s).
Proof.
  induction s.
  - intro q. apply Qball_0.
  - split.
    + intro metricEq. symmetry.
      apply (@glue_StepF_eq QS).
      unfold SplitL, StepFunction.SplitL. simpl.
      apply SplitL_resp_Xeq with (a:=o) in metricEq.
      rewrite (StepFunction.SplitLGlue) in metricEq.
      unfold StepFunction.SplitL in metricEq.
      simpl in metricEq. symmetry. apply (IHs1 q), metricEq.
      unfold SplitR, StepFunction.SplitR. simpl.
      apply SplitR_resp_Xeq with (a:=o) in metricEq.
      rewrite StepFunction.SplitRGlue in metricEq.
      unfold StepFunction.SplitR in metricEq.
      simpl in metricEq. symmetry. apply (IHs2 q), metricEq.
    + intro stdEq. symmetry.
      apply (@glue_StepF_eq (msp_as_RSetoid (Q_as_MetricSpace))).
      unfold SplitL, StepFunction.SplitL. simpl.
      apply SplitL_resp_Xeq with (a:=o) in stdEq.
      rewrite (StepFunction.SplitLGlue) in stdEq.
      unfold StepFunction.SplitL in stdEq.
      simpl in stdEq. symmetry. apply (IHs1 q), stdEq.
      unfold SplitR, StepFunction.SplitR. simpl.
      apply SplitR_resp_Xeq with (a:=o) in stdEq.
      rewrite StepFunction.SplitRGlue in stdEq.
      unfold StepFunction.SplitR in stdEq.
      simpl in stdEq. symmetry. apply (IHs2 q), stdEq.
Qed.

Lemma StepF_eq_change_base_setoid
  : forall s t : StepFunction.StepF Q,
    (@StepF_eq (msp_as_RSetoid Q_as_MetricSpace) s t) <-> (@StepF_eq QS s t).
Proof.
  induction s.
  - intro t. apply StepF_eq_change_base_setoid_const.
  - intro t. split.
    + intro metricEq. apply glue_StepF_eq.
      apply SplitL_resp_Xeq with (a:=o) in metricEq.
      rewrite StepFunction.SplitLGlue in metricEq.
      apply IHs1 in metricEq.
      exact metricEq.
      apply SplitR_resp_Xeq with (a:=o) in metricEq.
      rewrite StepFunction.SplitRGlue in metricEq.
      apply IHs2 in metricEq.
      exact metricEq.
    + intro stdEq. apply glue_StepF_eq.
      apply SplitL_resp_Xeq with (a:=o) in stdEq.
      rewrite (StepFunction.SplitLGlue) in stdEq.
      apply IHs1 in stdEq.
      exact stdEq.
      apply SplitR_resp_Xeq with (a:=o) in stdEq.
      rewrite StepFunction.SplitRGlue in stdEq.
      apply IHs2 in stdEq.
      exact stdEq.
Qed.

(** Sup is uniformly continuous. *)
Lemma sup_uc_prf :
  @is_UniformlyContinuousFunction
    LinfStepQ Q_as_MetricSpace (StepQSup:LinfStepQ -> Q) Qpos2QposInf.
Proof.
 intros e x y.
 simpl.
 rewrite -> Qball_Qabs.
 revert x y.
 apply: StepF_ind2.
   intros s s0 t t0 Hs Ht.
   simpl.
   intros H H1. rewrite <- Hs, <- Ht in H1.
   specialize (H H1). refine (Qle_trans _ _ _ _ H).
   rewrite <- (StepQSup_wd s s0).
   rewrite <- (StepQSup_wd t t0). apply Qle_refl.
   apply StepF_eq_change_base_setoid, Ht.
   apply StepF_eq_change_base_setoid, Hs.
  intros x y.
  rewrite <- Qball_Qabs.
  auto.
 intros o s s0 t t0 H0 H1 H2.
 simpl in *.
 rewrite StepQSup_glue, StepQSup_glue.
 assert (X:forall a b, (-(a-b)==b-a)%Q).
  intros; ring.
 unfold StepFSupBall in H2.
 revert H2.
 rewrite (GlueAp (ballS Q_as_MetricSpace (proj1_sig e) ^@> glue o s s0)).
 rewrite (GlueAp (constStepF (ballS Q_as_MetricSpace (proj1_sig e)))). 
 rewrite SplitLGlue, SplitRGlue.
 intros [H2a H2b].
 apply Qabs_case; intros H; [|rewrite <- Qabs_opp in H0, H1; rewrite -> X in *];
   (rewrite -> Qmax_minus_distr_l; unfold Qminus; apply Qmax_lub;[|clear H0; rename H1 into H0];
     (eapply Qle_trans;[|apply H0; auto]); (eapply Qle_trans;[|apply Qle_Qabs]); unfold Qminus;
       apply: plus_resp_leEq_lft; simpl; auto with * ).
Qed.

Local Open Scope uc_scope.

Definition StepQSup_uc : LinfStepQ --> Q_as_MetricSpace
:= Build_UniformlyContinuousFunction sup_uc_prf.

(** There is an injection from Linf to L1. *)
Lemma LinfAsL1_uc_prf : is_UniformlyContinuousFunction (fun (x:LinfStepQ) => (x:L1StepQ)) Qpos2QposInf.
Proof.
 intros e.
 apply: StepF_ind2.
   simpl.
   intros s s0 t t0 Hs Ht H.
   intro H0. rewrite <- Hs, <- Ht in H0.
   specialize (H H0). clear H0.
   unfold L1Ball.
   apply StepF_eq_change_base_setoid in Hs. 
   apply StepF_eq_change_base_setoid in Ht. 
   rewrite <- (L1Distance_wd s s0 Hs t t0 Ht).
   exact H.
  intros x y Hxy.
  change (Qball (proj1_sig e) x y) in Hxy.
  rewrite ->  Qball_Qabs in Hxy.
  apply Hxy.
 intros o s s0 t t0 Hst Hst0 H.
 simpl.
 unfold L1Ball.
 unfold L1Distance.
 unfold L1Norm.
 unfold StepQminus.
 change (@glue (msp_as_RSetoid Q_as_MetricSpace) o s s0)
   with (@glue QS o s s0).
 rewrite (MapGlue QminusS).
 change (@glue (msp_as_RSetoid Q_as_MetricSpace) o t t0)
   with (@glue QS o t t0).
 rewrite (ApGlueGlue (QminusS ^@> s) (QminusS ^@> s0)).
 unfold StepQabs.
 rewrite MapGlue.
 rewrite -> Integral_glue.
 setoid_replace (proj1_sig e)
   with (o*proj1_sig e + (1-o)*proj1_sig e)%Q; [| simpl; ring].
 simpl in H.
 unfold StepFSupBall, StepFfoldProp in H.
 simpl in H.
 rewrite (MapGlue (ballS Q_as_MetricSpace (proj1_sig e))) in H.
 rewrite (ApGlueGlue
            (ballS Q_as_MetricSpace (proj1_sig e) ^@> s)
            (ballS Q_as_MetricSpace (proj1_sig e) ^@> s0))
           in H.
 destruct H as [H0 H1].
 apply Qplus_le_compat.
  repeat rewrite -> (Qmult_comm o).
  apply Qmult_le_compat_r; auto with *.
  apply Hst.
  assumption.
 repeat rewrite -> (Qmult_comm (1-o)).
 apply Qmult_le_compat_r; auto with *.
 apply Hst0.
 assumption.
Qed.

Definition LinfAsL1 : LinfStepQ --> L1StepQ
:= Build_UniformlyContinuousFunction LinfAsL1_uc_prf.
