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

Require Export CoRN.model.metric2.IntegrableFunction.
Require Export CoRN.model.metric2.BoundedFunction.
Require Export CoRN.model.metric2.CRmetric.
Require Export CoRN.reals.fast.CRArith.
Require Import CoRN.model.metric2.LinfDistMonad.
Require Import CoRN.reals.fast.CRIR.
Require Import CoRN.ftc.Integral.
Require Import CoRN.model.structures.StepQsec.
Require Import CoRN.model.structures.OpenUnit.
Require Import CoRN.model.totalorder.QMinMax.
Require Import CoRN.model.totalorder.QposMinMax.
Require Import Coq.QArith.Qabs.
Require Import CoRN.tactics.Qauto.
Require Import Coq.QArith.Qround.
Require Import CoRN.model.metric2.L1metric.
Require Import CoRN.model.metric2.LinfMetric.
Require Import CoRN.model.ordfields.Qordfield.
Require Import CoRN.algebra.COrdFields2.
Require Import CoRN.model.metric2.Qmetric.
Require Import CoRN.reals.fast.ContinuousCorrect.
Require Import CoRN.ftc.IntegrationRules.
Require Import CoRN.ftc.MoreIntegrals.
Require Import CoRN.tactics.CornTac.

Set Implicit Arguments.

Opaque Qmax Qabs inj_Q.

Local Open Scope Q_scope.

(**
* Effective Integration
** stepSample
The first step in defining integration is to define the unit function on
[[0,1]] as a [Bounded Function].  This is defined to be the limit of
step functions approximating the unit function.

For efficenty reasons we want this approximation to be as good as we can muster because the number of steps this approximation returns will be
the number of samples that we will take of the function we want to
integrate.  Furthermore, we want the tree structure defining the step
function to be as balanced as possible.

First we create a step function with n steps that appoximates the
identity function, [stepSample]. *)

Lemma oddGluePoint (p:positive) : 0 < Pos.succ p # xI p /\ Pos.succ p # xI p < 1.
Proof.
 split; unfold Qlt.
  constructor.
 simpl.
 rewrite Pmult_comm.
 simpl.
 apply Zlt_left_rev.
 rewrite Zpos_succ_morphism, Zpos_xI.
 unfold Z.succ.
 ring_simplify.
 auto with *.
Qed.

Local Open Scope setoid_scope.
Local Open Scope sfstscope.
Local Open Scope StepQ_scope.

Definition stepSample : positive -> StepQ := positive_rect2
 (fun _ => StepQ)
 (fun p rec1 rec2 => glue (Build_OpenUnit (oddGluePoint p)) (constStepF (Pos.succ p#xI p:QS) * rec1) ((constStepF (1#(xI p):QS))*(constStepF (Pos.succ p:QS) + constStepF (p:QS)*rec2)))
 (fun p rec => glue (ou (1#2)) (constStepF (1#2:QS) * rec) (constStepF (1#2:QS) * (constStepF (1:QS) + rec)))
 (constStepF (1#2:QS)).

(** We want to prove that [stepSample n] is within (1/(2*n)) of the
identity function, but the identity function doesn't exist yet.
Instead we define the [SupDistanceToLinear] which computes what would
the distance to a linear function on [[0,1]].  This distance function
is transitive in the sense that if a step function x is within e1 of
a linear function, and a step function y is within e2 of the same
linear function, then x and y are really within (e1+e2) of each other
(in Linf).*)
Section id01.

Lemma SupDistanceToLinearBase_pos : forall (l r:Q) (H:l<r) (x:Q), 0 < Qmax (x-l) (r-x).
Proof.
 intros l r H x.
 destruct (Qlt_le_dec_fast l x) as [H0|H0].
  rewrite -> Qlt_minus_iff in H0.
  unfold Qminus.
  eapply Qlt_le_trans; [|apply Qmax_ub_l].
  assumption.
 rewrite -> Qlt_minus_iff in H.
 eapply Qlt_le_trans; [|apply Qmax_ub_r].
 eapply Qlt_le_trans.
  apply H.
 unfold Qminus.
 apply: plus_resp_leEq_lft;simpl;auto with *.
Qed.

Definition SupDistanceToLinear := StepFfold
 (fun (x:QS) (l r:Q) (H:l < r) => mkQpos (SupDistanceToLinearBase_pos H x))
 (fun b f g l r H =>
  (Qpos_max (f _ _ (affineCombo_gt (OpenUnitDual b) H)) (g _ _ (affineCombo_lt (OpenUnitDual b) H)))).

(** Various properties of [SupDistanceToLinear] *)
Lemma SupDistanceToLinear_glue : forall o l r a b (H:a < b),
 (SupDistanceToLinear (glue o l r) H ==
 Qmax (SupDistanceToLinear l (affineCombo_gt (OpenUnitDual o) H))
      (SupDistanceToLinear r (affineCombo_lt (OpenUnitDual o) H)))%Q.
Proof.
 intros o l r a b H.
 unfold SupDistanceToLinear at 1.
 simpl.
 autorewrite with QposElim.
 reflexivity.
Qed.

Lemma SupDistanceToLinear_wd1 : forall x l1 r1 (H1:l1 < r1) l2 r2 (H2:l2 < r2),
 (l1 == l2 -> r1 == r2 ->
  SupDistanceToLinear x H1 == SupDistanceToLinear x H2)%Q.
Proof.
 induction x using StepF_ind; intros l1 r1 H1 l2 r2 H2 Hl Hr.
  unfold SupDistanceToLinear.
  simpl.
  autorewrite with QposElim.
  rewrite -> Hl.
  rewrite -> Hr.
  reflexivity.
 do 2 rewrite -> SupDistanceToLinear_glue.
 assert (X:(affineCombo (OpenUnitDual o) l1 r1==affineCombo (OpenUnitDual o) l2 r2)%Q).
  rewrite -> Hl.
  rewrite -> Hr.
  reflexivity.
 apply Qmax_compat.
  apply IHx1; auto.
 apply IHx2; auto.
Qed.

Lemma Qmax_affineCombo : forall x a b o, a < b -> (Qmax (Qmax (x - a) (affineCombo o a b - x))
   (Qmax (x - affineCombo o a b) (b - x)) == Qmax (x - a) (b - x))%Q.
Proof.
 intros x a b o H.
 rewrite <- Qmax_assoc.
 rewrite -> (Qmax_assoc (affineCombo o a b - x)).
 rewrite -> (Qmax_comm (affineCombo o a b - x)).
 rewrite <- (Qmax_assoc (x - affineCombo o a b)).
 rewrite -> Qmax_assoc.
 apply Qmax_compat.
  rewrite <- Qle_max_l.
  apply: plus_resp_leEq_lft;simpl; auto with *.
 rewrite <- Qle_max_r.
 apply: plus_resp_leEq;simpl;auto with *.
Qed.

Lemma SupDistanceToLinear_split :
 forall x o a b c (H0:a < c) (H1:c < b),
 (c == affineCombo (OpenUnitDual o) a b)%Q ->
(Qmax (SupDistanceToLinear (SplitL x o) H0)
   (SupDistanceToLinear (SplitR x o) H1) ==
 SupDistanceToLinear x (Qlt_trans _ _ _ H0 H1))%Q.
Proof.
 induction x using StepF_ind.
  intros o a b c H0 H1 Hc.
  unfold SupDistanceToLinear.
  simpl.
  autorewrite with QposElim.
  rewrite -> Hc.
  apply Qmax_affineCombo; auto with *.
  apply Qlt_trans with c; assumption.
 intros p a b c H0 H1 Hc.
 apply SplitLR_glue_ind; intros H.
   do 2 rewrite -> SupDistanceToLinear_glue.
   rewrite -> Qmax_assoc.
   rewrite -> IHx1.
    apply Qmax_compat; apply SupDistanceToLinear_wd1; try reflexivity; rewrite -> Hc; unfold affineCombo;
      simpl; field; auto with *.
   rewrite -> Hc.
   unfold affineCombo.
   simpl.
   field; auto with *.
  do 2 rewrite -> SupDistanceToLinear_glue.
  rewrite <- Qmax_assoc.
  rewrite -> IHx2.
   apply Qmax_compat; apply SupDistanceToLinear_wd1; try reflexivity; rewrite -> Hc; unfold affineCombo;
     simpl; field; auto with *.
  rewrite -> Hc.
  unfold affineCombo.
  simpl.
  field; auto with *.
 rewrite -> SupDistanceToLinear_glue.
 apply Qmax_compat; apply SupDistanceToLinear_wd1; try reflexivity; rewrite -> Hc; unfold affineCombo;
   simpl; rewrite -> H; field; auto with *.
Qed.

Lemma SupDistanceToLinear_wd2 : forall x1 x2 a b (H: a < b), x1 == x2 ->
(SupDistanceToLinear x1 H == SupDistanceToLinear x2 H)%Q.
Proof.
 induction x1 using StepF_ind.
  induction x2 using StepF_ind.
   intros a b H Hx.
   unfold SupDistanceToLinear.
   simpl in *.
   autorewrite with QposElim.
   change (x == x0)%Q in Hx.
   rewrite -> Hx.
   reflexivity.
  intros a b H Hx.
  destruct Hx as [H0 H1] using (eq_glue_ind x2_1).
  rewrite -> SupDistanceToLinear_glue.
  rewrite <- IHx2_1; auto with *.
  rewrite <- IHx2_2; auto with *.
  unfold SupDistanceToLinear.
  simpl.
  autorewrite with QposElim.
  rewrite <- Qmax_assoc.
  rewrite -> (Qmax_assoc (affineCombo (OpenUnitDual o) a b - x)).
  rewrite -> (Qmax_comm (affineCombo (OpenUnitDual o) a b - x)).
  rewrite <- (Qmax_assoc (x - affineCombo (OpenUnitDual o) a b)).
  rewrite -> Qmax_assoc.
  symmetry.
  apply Qmax_compat.
   rewrite <- Qle_max_l.
   apply: plus_resp_leEq_lft;simpl;auto with *.
  rewrite <- Qle_max_r.
  apply: plus_resp_leEq;simpl; auto with *.
 intros x2 a b H Hx.
 destruct Hx as [H0 H1] using (glue_eq_ind x1_1).
 rewrite -> SupDistanceToLinear_glue.
 rewrite -> (IHx1_1 _ _ _ (affineCombo_gt (OpenUnitDual o) H) H0).
 rewrite -> (IHx1_2 _ _ _ (affineCombo_lt (OpenUnitDual o) H) H1).
 rewrite -> SupDistanceToLinear_split; [|reflexivity].
 apply SupDistanceToLinear_wd1; try reflexivity.
Qed.

Lemma SupDistanceToLinear_translate :
 forall x c a b (H:a < b) (H0:a+c < b + c),
  (SupDistanceToLinear x H == SupDistanceToLinear (constStepF (c:QS) + x) H0)%Q.
Proof.
 induction x using StepF_ind.
  intros; unfold SupDistanceToLinear; simpl.
  autorewrite with QposElim.
  apply Qmax_compat; ring.
 intros c a b H H0.
 change (constStepF (X:=QS) c + glue o x1 x2)
   with (glue o (constStepF (c:QS) + x1) (constStepF (c:QS) + x2)).
 do 2 rewrite -> SupDistanceToLinear_glue.
 set (A:=(affineCombo_gt (OpenUnitDual o) H)).
 apply Qmax_compat.
  eapply Seq_trans.
    apply Q_Setoid. 
   apply (IHx1 c _ _ A (proj2 (Qplus_lt_l _ _ c) A)).
  apply SupDistanceToLinear_wd1; try reflexivity.
  unfold affineCombo; ring.
 set (B:=(affineCombo_lt (OpenUnitDual o) H)).
 eapply Seq_trans.
   apply Q_Setoid.
  apply (IHx2 c _ _ B (proj2 (Qplus_lt_l _ _ c) B)).
 apply SupDistanceToLinear_wd1; try reflexivity.
 unfold affineCombo; ring.
Qed.

Lemma SupDistanceToLinear_scale :
 forall x c a b (H:a < b) (H0:c*a < c*b),
  (c*SupDistanceToLinear x H == SupDistanceToLinear (constStepF (c:QS) * x) H0)%Q.
Proof.
 intros x c a b H H0.
 assert (X:0 < c).
  rewrite -> Qlt_minus_iff in *|-.
  apply: (mult_cancel_less _ 0 c (b + - a))%Q; simpl; auto with *.
  replace LHS with 0 by simpl; ring.
  replace RHS with (c* b + - (c*a))%Q by simpl; ring.
  assumption.
 revert c a b H H0 X.
 induction x using StepF_ind.
  intros; unfold SupDistanceToLinear; simpl.
  autorewrite with QposElim.
  rewrite -> Qmax_mult_pos_distr_r; auto with *.
  apply Qmax_compat; ring.
 intros c a b H H0 X.
 change (constStepF (X:=QS) c * glue o x1 x2)
   with (glue o (constStepF (c:QS) * x1) (constStepF (c:QS) * x2)).
 do 2 rewrite -> SupDistanceToLinear_glue.
 eapply Seq_trans.
   apply Q_Setoid.
  apply Qmax_mult_pos_distr_r; auto with *.
 set (A:=(affineCombo_gt (OpenUnitDual o) H)).
 apply Qmax_compat.
  eapply Seq_trans.
    apply Q_Setoid.
   apply (IHx1 c _ _ A (mult_resp_less_lft _ _ _ _ A X)); auto with *.
  apply SupDistanceToLinear_wd1; try reflexivity.
  unfold affineCombo; ring.
 set (B:=(affineCombo_lt (OpenUnitDual o) H)).
 eapply Seq_trans.
   apply Q_Setoid.
  apply (IHx2 c _ _ B (mult_resp_less_lft _ _ _ _ B X)); auto with *.
 apply SupDistanceToLinear_wd1; try reflexivity.
 unfold affineCombo; ring.
Qed.

(** This is the "transitivity" of the [SupDistanceToLinear] function. *)
Lemma SupDistanceToLinear_trans :
 forall x y a b (H:a < b), StepFSupBall (SupDistanceToLinear x H + SupDistanceToLinear y H) x y.
Proof.
 apply: StepF_ind2.
   intros s s0 t t0 Hs Ht H a b Hab.
   rewrite  <- Hs, <- Ht at 2.
   setoid_replace (SupDistanceToLinear s0 Hab + SupDistanceToLinear t0 Hab)%Qpos
     with (SupDistanceToLinear s Hab + SupDistanceToLinear t Hab)%Qpos.
    apply H.
   unfold QposEq.
   autorewrite with QposElim.
   apply Qplus_wd; apply SupDistanceToLinear_wd2; auto.
  intros x x0 a b H.
  unfold StepFSupBall, StepFfoldProp.
  simpl.
  rewrite -> Qball_Qabs.
  unfold SupDistanceToLinear.
  simpl.
  autorewrite with QposElim.
  apply Qabs_case; intros  H0.
   setoid_replace (x - x0)%Q with ((x - a) + (a - b) + (b - x0))%Q; [| now simpl; ring].
   apply: plus_resp_leEq_both; simpl; auto with *.
   replace RHS with (Qmax (x-a) (b-x) + 0)%Q by simpl; ring.
   apply: plus_resp_leEq_both; simpl; auto with *.
   apply Qlt_le_weak.
   rewrite -> Qlt_minus_iff in *.
   replace RHS with (b + -a)%Q by simpl; ring.
   assumption.
  setoid_replace (-(x - x0))%Q with ((b - x) + - (b - a) + (x0 - a))%Q; [| now simpl; ring].
  apply: plus_resp_leEq_both; simpl; auto with *.
  replace RHS with (Qmax (x-a) (b-x) + 0)%Q by simpl; ring.
  apply: plus_resp_leEq_both; simpl; auto with *.
  apply Qlt_le_weak.
  rewrite ->  Qlt_minus_iff in *.
  replace RHS with (b + -a)%Q by simpl; ring.
  assumption.
 intros o s s0 t t0 H0 H1 a b H.
 assert (X:forall (o : OpenUnit) (l r : StepQ) (a b : Q) (H : a < b),
   QposEq (SupDistanceToLinear (glue o l r) H)
     (Qpos_max (SupDistanceToLinear l (affineCombo_gt (OpenUnitDual o) H))
       (SupDistanceToLinear r (affineCombo_lt (OpenUnitDual o) H)))%Q).
  intros.
  unfold QposEq.
  autorewrite with QposElim.
  apply SupDistanceToLinear_glue.
 do 2 rewrite -> X.
 rewrite -> StepFSupBallGlueGlue.
 split.
  eapply ball_weak_le;[|simpl; apply H0].
  autorewrite with QposElim.
  apply Qplus_le_compat; apply Qmax_ub_l.
 eapply ball_weak_le;[|simpl; apply H1].
 autorewrite with QposElim.
 apply Qplus_le_compat; apply Qmax_ub_r.
Qed.

(** The [stepSample p] is as close to the virtual identity function as
we expect. *)
Lemma stepSampleDistanceToId : (forall p, QposEq (@SupDistanceToLinear (stepSample p) 0 1 (@pos_one _)) (1#(2*p))).
Proof.
 unfold QposEq.
 induction p using positive_rect2.
   replace (stepSample (xI p))
     with (glue (Build_OpenUnit (oddGluePoint p)) (constStepF (Pos.succ p#xI p:QS) * (stepSample (Pos.succ p))) ((constStepF (1#(xI p):QS))*(constStepF (Pos.succ p:QS) + constStepF (p:QS)*(stepSample p))))
       by (symmetry;apply: positive_rect2_red1).
   rewrite -> SupDistanceToLinear_glue.
   generalize (@affineCombo_gt (OpenUnitDual (Build_OpenUnit (oddGluePoint p))) 0 1 (pos_one Q_as_COrdField))
     (@affineCombo_lt (OpenUnitDual (Build_OpenUnit (oddGluePoint p))) 0 1 (pos_one Q_as_COrdField)).
   intros A B.
   set (C:=(pos_one Q_as_COrdField)) in *.
   transitivity (Qmax (1#2*xI p) (1#2*xI p))%Q;[|apply Qmax_idem].
   apply Qmax_compat.
    set (LHS := (SupDistanceToLinear (constStepF (X:=QS) (Pos.succ p # xI p) * stepSample (Pos.succ p)) A)).
    transitivity ((Pos.succ p#xI p)*(SupDistanceToLinear (stepSample (Pos.succ p)) C))%Q; [|rewrite -> IHp;
      change ((Pos.succ p * 1 * (2 * (2* p + 1)) = 2* (Pos.succ p + p * (2* (Pos.succ p))))%Z);
        repeat rewrite Zpos_succ_morphism; ring].
    assert (X:(Pos.succ p # xI p) *0 < (Pos.succ p # xI p) *1).
     constructor.
    rewrite -> (fun a => SupDistanceToLinear_scale a C X).
    apply SupDistanceToLinear_wd1.
     simpl; ring.
    unfold affineCombo; simpl; ring.
   set (LHS := (SupDistanceToLinear (constStepF (X:=QS) (1 # xI p) *
     (constStepF (X:=QS) (Pos.succ p) + constStepF (X:=QS) p * stepSample p)) B)%Q).
   transitivity ((1#xI p)*(p*(SupDistanceToLinear (stepSample (p)) C)))%Q; [|rewrite -> IHp0;
     change ((p * 1 * (2 * (2* p + 1)) = 2* (p + p * (2* p)))%Z); ring].
   assert (X0:(p *0 < p *1)).
    constructor.
   rewrite -> (fun a => SupDistanceToLinear_scale a C X0).
   assert (X1:(p*0 + Pos.succ p < p*1 + Pos.succ p)).
    apply: plus_resp_less_rht.
    assumption.
   rewrite -> (fun a => SupDistanceToLinear_translate a X0 X1).
   assert (X2:((1# xI p)*(p*0 + Pos.succ p) < (1#xI p)*(p*1 + Pos.succ p))).
    apply: mult_resp_less_lft;simpl; auto with *.
   rewrite -> (fun a => SupDistanceToLinear_scale a X1 X2).
   apply SupDistanceToLinear_wd1.
    unfold affineCombo; simpl.
    repeat rewrite -> Zpos_succ_morphism; repeat rewrite -> Qmake_Qdiv; repeat rewrite -> Zpos_xI;
      field; auto with *.
   change (2*(p*1) + 1 = ((p*1*1 + Pos.succ p*1)*1))%Z.
   rewrite Zpos_succ_morphism; ring.
  change (1#2*xO p)%Q with ((1#2)*(1#(2*p)))%Q.
  replace (stepSample (xO p)) with (glue (ou (1#2)) (constStepF (1#2:QS) * (stepSample p))
    (constStepF (1#2:QS) * (constStepF (1:QS) + (stepSample p))))
      by (symmetry;apply: positive_rect2_red2).
  rewrite -> SupDistanceToLinear_glue.
  generalize (@affineCombo_gt (OpenUnitDual (ou (1#2))) 0 1 (pos_one Q_as_COrdField))
    (@affineCombo_lt (OpenUnitDual (ou (1#2))) 0 1 (pos_one Q_as_COrdField)).
  intros A B.
  set (C:=(pos_one Q_as_COrdField)) in *.
  transitivity (Qmax ((1#2)*(1#2 * p)) ((1#2)*(1#2 * p)))%Q;[|apply Qmax_idem].
  set (D1:=(SupDistanceToLinear (constStepF (X:=QS) (1 # 2) * stepSample p) A)).
  set (D2:=(SupDistanceToLinear
    (constStepF (X:=QS) (1 # 2) * (constStepF (X:=QS) 1 + stepSample p)) B)).
  rewrite <- IHp.
  apply Qmax_compat.
   assert (X:((1#2) *0 < (1#2) *1)).
    constructor.
   rewrite -> (fun a c => SupDistanceToLinear_scale a c X).
   apply SupDistanceToLinear_wd1; constructor.
  assert (X0:0 + 1 < 1 +1).
   constructor.
  rewrite -> (fun a c => SupDistanceToLinear_translate a c X0).
  assert (X1:(1#2)*(0 + 1) < (1#2)*(1 +1)).
   constructor.
  rewrite -> (fun a => SupDistanceToLinear_scale a X0 X1).
  apply SupDistanceToLinear_wd1; constructor.
 reflexivity.
Qed.

(** Given a requested error of q, what is smallest n for [stepSample n]
that will satifiy this error requirement. *)

Definition id01_raw_help (q:QposInf) : positive :=
match q with
|QposInfinity => 1%positive
|Qpos2QposInf q => QposCeiling ((1#2)/q)
end.

Lemma id01_raw_help_le : forall (q:Qpos),
 ((1#2*id01_raw_help q) <= q)%Q.
Proof with auto with *.
 intros q.
 unfold id01_raw_help, QposCeiling.
 simpl.
 generalize (Qle_ceiling ((1#2)*/q)).
 generalize (Qceiling ((1#2)*/q)).
 intros [|p|p] H.
   elim (Qle_not_lt _ _ H).
   apply Q.Qmult_lt_0_compat...
   apply Qinv_lt_0_compat...
  autorewrite with QposElim in *.
  rewrite -> Qmake_Qdiv in *.
  rewrite Zpos_xO.
  rewrite -> Qle_minus_iff in *.
  change ((2%positive * p)%Z:Q) with (2%positive * p)%Q.
  replace RHS with (((2*q)/(2*p))*(p - 1%positive/2%positive*/q))%Q.
   apply: mult_resp_nonneg; simpl; auto with *.
   apply Qlt_le_weak.
   apply Q.Qmult_lt_0_compat...
  simpl. field. split...
 elim (Qle_not_lt _ _ H).
 apply Qlt_trans with 0...
 apply Q.Qmult_lt_0_compat...
 apply Qinv_lt_0_compat...
Qed.

(** Now define id01, the identity funciton on [[0,1]] as a bounded function,
to be the limit of these [stepSample] functions. *)
Definition id01_raw (q:QposInf) : StepQ := stepSample (id01_raw_help q).

Lemma id01_prf : is_RegularFunction (id01_raw:QposInf -> LinfStepQ).
Proof.
 intros a b.
 unfold id01_raw.
 apply ball_weak_le with ((1#2*(id01_raw_help a)) + (1#2*(id01_raw_help b)))%Qpos.
  autorewrite with QposElim.
  apply: plus_resp_leEq_both; apply id01_raw_help_le.
 simpl (ball (m:=LinfStepQ)).
 do 2 rewrite <- stepSampleDistanceToId.
 apply SupDistanceToLinear_trans.
Qed.

Definition id01 : BoundedFunction :=
Build_RegularFunction id01_prf.

End id01.

(**
** StepFunctions distribute over Completion
The distribution function maps StepF (Complete X) to Complete (StepF X).
*)
(* approximate z e is not a morphism, so we revert to using the pre-setoid version of StepF's map *)
Definition distribComplete_raw (x:StepF CR) (e:QposInf) : LinfStepQ :=
StepFunction.Map (fun z => approximate z e) x.

Lemma distribComplete_prf : forall (x:StepF CR), is_RegularFunction (distribComplete_raw x).
Proof.
 unfold distribComplete_raw.
 intros x a b.
 induction x using StepF_ind.
  apply: regFun_prf.
 simpl (ball (m:=LinfStepQ)).
 set (f:=(fun z : RegularFunction Q_as_MetricSpace => approximate z a)) in *.
 set (g:=(fun z : RegularFunction Q_as_MetricSpace => approximate z b)) in *.
 change (Map f (glue o x1 x2)) with (glue o (Map f x1:StepQ) (Map f x2)).
 change (Map g (glue o x1 x2)) with (glue o (Map g x1:StepQ) (Map g x2)).
 rewrite -> StepFSupBallGlueGlue.
 auto.
Qed.

Definition distribComplete (x:StepF CR) : BoundedFunction :=
Build_RegularFunction (distribComplete_prf x).

Local Open Scope uc_scope.

(** Given a uniformly continuous function f, and a step function g,
the composition f o g is a bounded function.  The map from g to f o g
is uniformly continuous with modulus [mu f].

The same thing does not work for integrable functions becuase
The map from g to f o g may not be uniformly continuous with modulus [mu f].
However, I have not found a counter example where f o g is not uniformly
continuous.  In fact, when f is lipschitz, then the map from g to
f o g is Lipschitz.  However Lipschitz functions haven't been
formalized yet. *)

Definition ComposeContinuous_raw (f:Q_as_MetricSpace-->CR) (z:LinfStepQ) : BoundedFunction := dist (uc_stdFun f ^@> z).
(* begin hide *)
Add Parametric Morphism f : (@ComposeContinuous_raw f) with signature (@st_eq _) ==> (@st_eq _) as ComposeContinuous_raw_wd.
Proof.
 intros x1 x2 Hx.
 unfold ComposeContinuous_raw.
 rewrite -> Hx.
 reflexivity.
Qed.
(* end hide *)
Lemma ComposeContinuous_prf (f:Q_as_MetricSpace --> CR) :
 is_UniformlyContinuousFunction (ComposeContinuous_raw f) (mu f).
Proof.
 intros e a b.
 revert a b e.
 apply: StepF_ind2.
   intros s s0 t t0 Hs Ht H e H0.
   change (st_car LinfStepQ) in s, s0, t, t0.
   rewrite <- Hs, <- Ht.
   apply H.
   destruct (mu f e); try constructor.
   change (ball q s t).
   rewrite -> Hs, Ht.
   assumption.
  intros x y e H.
  change (ball e (f x) (f y)).
  apply uc_prf.
  destruct (mu f e); try solve [constructor].
  simpl.
  assumption.
 intros o s s0 t t0 H0 H1 e H.
 unfold ComposeContinuous_raw in *.
 repeat rewrite -> MapGlue, dist_glue.
 intros d1 d2.
 apply ball_weak_le with (((1#2)*((1#2)*d1)) + e + ((1#2)*((1#2)*d2)))%Qpos.
  autorewrite with QposElim.
  Qauto_le.
 simpl.
 unfold Cap_slow_raw.
 simpl.
 rewrite -> StepFSupBallGlueGlue.
 split; [apply H0 | apply H1]; destruct (mu f e); try constructor; simpl in *;
   rewrite -> StepFSupBallGlueGlue in H; tauto.
Qed.

Definition ComposeContinuous (f:Q_as_MetricSpace --> CR) : LinfStepQ --> BoundedFunction :=
 Build_UniformlyContinuousFunction (ComposeContinuous_prf f).

(**
** Riemann-Stieltjes Integral
A measure on the reals is represented by the inverse of it's cumlative
distribution function as a bounded function.  So at the moment we
can only integrate over bounded intervals.  This effectively the
Stieltjes integral [Integral f d(g^-1)]. *)
Definition IntegrateWithMeasure (f:Q_as_MetricSpace --> CR) : BoundedFunction --> CR :=
(uc_compose IntegrableFunction.Integral
(uc_compose BoundedAsIntegrable (Cbind (LinfStepQPrelengthSpace) (ComposeContinuous f)))).

(** The Riemann Integral uses the uniform measure on [[0,1]].  The
inverse of its cumlative distribution function is [id01]. *)
Definition Integrate01 f := IntegrateWithMeasure f id01.

Definition ContinuousSup01 f :=
(uc_compose sup (Cbind (LinfStepQPrelengthSpace) (ComposeContinuous f))) id01.

(** Integrating a different range is just a matter of scaling and translating a little: *)
Definition Integrate (f: Q_as_MetricSpace --> CR) (from width: Q): CR :=
  (' width * Integrate01 (f ∘ Qplus_uc from ∘ Qscale_uc width))%CR.

(** Our integral on [[0,1]] is correct. *)
Lemma Integrate01_correct : forall F (H01:[0][<=]([1]:IR)) (HF:Continuous_I H01 F)
 (f:Q_as_MetricSpace --> CR),
 (forall (o:Q) H, (0 <= o <= 1) -> (f o == IRasCR (F (inj_Q IR o) H)))%CR ->
 (IRasCR (integral [0] [1] H01 F HF)==Integrate01 f)%CR.
Proof.
 intros F H01' HF' f Hf.
 assert (H01:(inj_Q IR 0)[<=](inj_Q IR 1)).
  apply inj_Q_leEq.
  discriminate.
 assert (HF:Continuous_I H01 F).
  apply (included_imp_contin _ _ H01').
   apply included_compact.
    apply (compact_wd _ _ H01' [0]).
     apply compact_inc_lft.
    apply eq_symmetric; apply (inj_Q_nring IR 0).
   apply (compact_wd _ _ H01' [1]).
    apply compact_inc_rht.
   rstepl (nring 1:IR).
   apply eq_symmetric; apply (inj_Q_nring IR 1).
  assumption.
 transitivity (IRasCR (integral _ _ H01 F HF)).
  apply IRasCR_wd.
  apply integral_wd'.
   apply eq_symmetric; apply (inj_Q_nring IR 0).
  rstepl (nring 1:IR).
  apply eq_symmetric; apply (inj_Q_nring IR 1).
 clear H01' HF'.
 apply ball_eq.
 intros e.
 setoid_replace e with ((1#2)*e + (1#2)*e)%Qpos; [| now QposRing].
 generalize ((1#2)*e)%Qpos.
 clear e.
 intros e.
 eapply ball_triangle; [|apply (@ball_approx_l Q_as_MetricSpace)].
 change (Cunit (approximate (Integrate01 f) e)) with ('(approximate (Integrate01 f) e))%CR.

 setoid_replace ('(approximate (Integrate01 f) e))%CR
   with ('((1-0)*(approximate (Integrate01 f) e))%Q)%CR.
  Focus 2.
  change (' approximate (Integrate01 f) e == ' ((1 - 0) * approximate (Integrate01 f) e)%Q)%CR.
  ring.
 rewrite <- CRAbsSmall_ball.
 stepl ('((1-0)*e)%Q)%CR; [| apply inject_Q_CR_wd; change ((1 - 0) * e == e)%Q; ring].
 set (z:=(integral (inj_Q IR 0) (inj_Q IR 1) H01 F HF)).
 simpl.
 unfold Cjoin_raw.
 simpl.
 unfold distribComplete_raw.
 unfold id01_raw.
 assert (X:=stepSampleDistanceToId (id01_raw_help (mu f ((1 # 2) * e)))).
 revert X.
 generalize (stepSample (id01_raw_help (mu f ((1 # 2) * e)))).
 intros s Hs.
 assert (X:QposInf_le (SupDistanceToLinear s (pos_one Q_as_COrdField)) (mu f ((1 # 2) * e))).
  destruct (mu f ((1#2) *e)); try constructor.
  unfold QposEq in Hs.
  simpl.
  rewrite -> Hs.
  apply id01_raw_help_le.
 clear Hs.
 rename X into Hs.
 revert s Hs.
 generalize (pos_one Q_as_COrdField).
 intros c s Hs.
 simpl in c, Hs.
 revert c s Hs.
 unfold z.
 clear z.
 revert H01 HF.
 revert Hf.
 generalize 0 1.
 intros a b Hf Hab HF Hab0 s Hs.
 destruct (Qpos_lt_plus Hab0) as [ba Hba].
 stepl ('(ba*e)%Qpos)%CR; [| now (apply inject_Q_CR_wd; unfold canonical_names.equiv, stdlib_rationals.Q_eq; rewrite -> Hba; QposRing)].
 revert a b Hab0 ba Hba F Hab HF Hf Hs.
 induction s using StepF_ind; intros a b Hab0 ba Hba F Hab HF Hf Hs.
  change (AbsSmall (R:=CRasCOrdField) ('(ba*e)%Qpos)%CR (IRasCR (integral _ _ Hab F HF)[-]
    ('((b-a)*(approximate (f x) ((1 # 2) * e)%Qpos))%Q)%CR)).
  rewrite -> CRAbsSmall_ball.
  rewrite <- IR_inj_Q_as_CR.
  rewrite <- CRAbsSmall_ball.
  unfold cg_minus.
  simpl.
  eapply AbsSmall_wdr;[|apply IR_minus_as_CR].
  eapply AbsSmall_wdl;[|apply IR_inj_Q_as_CR].
  rewrite <- IR_AbsSmall_as_CR.
  unfold SupDistanceToLinear in Hs.
  simpl in Hs.
  set (a0:=inj_Q IR (approximate (f x) ((1 # 2) * e)%Qpos)).
  set (e':=(inj_Q IR (e:Q))).
  assert (X:forall y : IR, Compact Hab y -> forall Hy : Dom F y, AbsSmall e' ((F y Hy)[-]a0)).
   intros y Hy Hyf.
   rewrite -> IR_AbsSmall_as_CR.
   unfold e'.
   apply AbsSmall_wdr with (IRasCR (F y Hyf)[-]IRasCR a0)%CR;[|apply eq_symmetric; apply IR_minus_as_CR].
   eapply AbsSmall_wdl;[|apply eq_symmetric; apply IR_inj_Q_as_CR].
   rewrite -> CRAbsSmall_ball.
   unfold a0; rewrite -> IR_inj_Q_as_CR.
   assert (X0:(forall (q : Q) (Hq : Dom F (inj_Q IR q)), clcr (inj_Q IR a) (inj_Q IR b) (inj_Q IR q) ->
     (Cbind QPrelengthSpace f (' q) == IRasCR (F (inj_Q IR q) Hq))%CR)).
    intros q Hq [Hq0 H1].
    rewrite -> (Cbind_correct QPrelengthSpace f (' q))%CR.
    rewrite -> (BindLaw1 f).
    apply Hf.
    split.
     apply (leEq_inj_Q IR).
     auto.
    apply (leEq_inj_Q IR).
    auto.
   assert (X:=@ContinuousCorrect (clcr (inj_Q IR a) (inj_Q IR b)) (inj_Q_less _ _ _ Hab0) F (Continuous_Int (clcr (inj_Q IR a) (inj_Q IR b)) Hab Hab F HF)
     (Cbind QPrelengthSpace f) X0 y Hyf Hy).
   set (z:=(' approximate (f x) ((1 # 2) * e)%Qpos)%CR).
   rewrite -> X.
   setoid_replace e with ((1#2)*e + (1#2)*e)%Qpos; [| now QposRing].
   apply ball_triangle with (f x); [|apply ball_approx_r].
   rewrite <- (BindLaw1 f).
   rewrite <- (Cbind_correct QPrelengthSpace f (Cunit_fun Q_as_MetricSpace x)).
   set (z0:=(Cbind QPrelengthSpace f (Cunit_fun Q_as_MetricSpace x))).
   apply: uc_prf.
   clear z X X0 Hyf.
   set (z:=(mu f ((1#2)*e)%Qpos)) in *.
   change (@mu CR CR (@Cbind Q_as_MetricSpace Q_as_MetricSpace QPrelengthSpace f)
     (Qpos_mult (QposMake xH (xO xH)) e)) with z.
   destruct z as [z|];[|constructor].
   unfold ball_ex.
   eapply ball_weak_le.
    apply Hs.
   change (Cunit_fun Q_as_MetricSpace x) with ('x)%CR.
   rewrite <- IR_inj_Q_as_CR.
   rewrite <- CRAbsSmall_ball.
   autorewrite with QposElim.
   unfold cg_minus; simpl.
   eapply AbsSmall_wdr;[|apply IR_minus_as_CR].
   eapply AbsSmall_wdl;[|apply IR_inj_Q_as_CR].
   rewrite <- IR_AbsSmall_as_CR.
   apply AbsIR_imp_AbsSmall.
   assert(X:=leEq_or_leEq _ (inj_Q IR x) y).
   rewrite -> leEq_def.
   intros Y.
   apply X.
   clear X.
   intros X.
   revert Y.
   change (Not (inj_Q IR (Qmax (x - a) (b - x))[<]AbsIR (y[-]inj_Q IR x))).
   rewrite <- leEq_def.
   apply AbsSmall_imp_AbsIR.
   destruct X as [X|X].
    apply leEq_imp_AbsSmall.
     apply shift_leEq_lft; assumption.
    apply leEq_transitive with (inj_Q IR (b - x)%Q).
     stepr ((inj_Q IR b)[-](inj_Q IR x)); [| now (apply eq_symmetric; apply inj_Q_minus)].
     apply minus_resp_leEq.
     destruct Hy; assumption.
    apply inj_Q_leEq.
    apply Qmax_ub_r.
   apply AbsSmall_minus.
   apply leEq_imp_AbsSmall.
    apply shift_leEq_lft; assumption.
   apply leEq_transitive with (inj_Q IR (x - a)%Q).
    stepr ((inj_Q IR x)[-](inj_Q IR a)); [| now (apply eq_symmetric; apply inj_Q_minus)].
    apply minus_resp_leEq_rht.
    destruct Hy; assumption.
   apply inj_Q_leEq.
   apply Qmax_ub_l.
  split.
   apply shift_leEq_minus.
   stepl (([--]e'[+]a0)[*](inj_Q IR b[-]inj_Q IR a)).
    apply lb_integral.
    intros y Hy Hyf.
    apply shift_plus_leEq.
    destruct (X y Hy Hyf); assumption.
   rstepl ([--]((inj_Q IR b[-]inj_Q IR a)[*]e') [+] (inj_Q IR b[-]inj_Q IR a)[*]a0).
   csetoid_replace (inj_Q IR b[-]inj_Q IR a) (inj_Q IR (b-a)%Q);
     [|apply eq_symmetric; apply inj_Q_minus].
   apply bin_op_wd_unfolded.
    apply un_op_wd_unfolded.
    unfold e'.
    stepl (inj_Q IR ((b-a)*e)%Q); [| now apply inj_Q_mult].
    apply: inj_Q_wd;simpl.
    autorewrite with QposElim.
    rewrite -> Hba.
    ring.
   apply eq_symmetric; apply inj_Q_mult.
  apply shift_minus_leEq.
  stepr ((e'[+]a0)[*](inj_Q IR b[-]inj_Q IR a)).
   apply ub_integral.
   intros y Hy Hyf.
   apply shift_leEq_plus.
   destruct (X y Hy Hyf); assumption.
  rstepl (((inj_Q IR b[-]inj_Q IR a)[*]e') [+] (inj_Q IR b[-]inj_Q IR a)[*]a0).
  csetoid_replace (inj_Q IR b[-]inj_Q IR a) (inj_Q IR (b-a)%Q);
    [|apply eq_symmetric; apply inj_Q_minus].
  apply bin_op_wd_unfolded.
   unfold e'.
   stepl (inj_Q IR ((b-a)*e)%Q); [| now apply inj_Q_mult].
   apply: inj_Q_wd;simpl.
   autorewrite with QposElim.
   rewrite -> Hba.
   ring.
  apply eq_symmetric; apply inj_Q_mult.
 set (z:=(IntegralQ (glue o (Map (fun z : RegularFunction Q_as_MetricSpace =>
   approximate z ((1 # 2) * e)%Qpos) (Map f s1):StepQ) (Map
     (fun z : RegularFunction Q_as_MetricSpace => approximate z ((1 # 2) * e)%Qpos) (Map f s2))))).
 change (AbsSmall (R:=CRasCOrdField) ('(ba* e)%Qpos)%CR
   (IRasCR (integral _ _ Hab F HF)[-]'((b-a)*z)%Q)%CR).
 rewrite -> CRAbsSmall_ball.
 set (c:=(affineCombo (OpenUnitDual o) a b:Q)).
 assert (Hac:inj_Q IR a[<=]inj_Q IR c).
  unfold c.
  apply inj_Q_leEq.
  simpl; auto with *.
 assert (Hcb:inj_Q IR c[<=]inj_Q IR b).
  unfold  c.
  apply inj_Q_leEq.
  simpl; auto with *.
 assert (HFl :Continuous_I Hac F).
  revert HF.
  apply included_imp_contin.
  intros x [Hxl Hxr].
  split; auto.
  apply leEq_transitive with (inj_Q IR c); auto.
 assert (HFr :Continuous_I Hcb F).
  revert HF.
  apply included_imp_contin.
  intros x [Hxl Hxr].
  split; auto.
  apply leEq_transitive with (inj_Q IR c); auto.
 setoid_replace (IRasCR (integral _ _ Hab F HF))
   with (IRasCR (integral _ _ Hac F HFl)+IRasCR (integral _ _ Hcb F HFr))%CR;
     [| now (rewrite <- IR_plus_as_CR;apply IRasCR_wd; apply eq_symmetric; apply integral_plus_integral)].
 unfold z.
 rewrite -> Integral_glue.
 clear z.
 set (zl:=IntegralQ (Map (fun z : RegularFunction Q_as_MetricSpace =>
   approximate z ((1 # 2) * e)%Qpos) (Map f s1))).
 set (zr:=IntegralQ (Map (fun z : RegularFunction Q_as_MetricSpace =>
   approximate z ((1 # 2) * e)%Qpos) (Map f s2))).
 setoid_replace ((b - a) * (o * zl + (1 - o) * zr))%Q with ((c - a)*zl + (b - c)*zr)%Q;
   [| now (unfold c, affineCombo, OpenUnitDual; simpl; ring)].
 assert (Hac0: a < c).
  unfold c; auto with*.
 assert (Hcb0: c < b).
  unfold c; auto with*.
 destruct (Qpos_lt_plus Hac0) as [ca Hca].
 destruct (Qpos_lt_plus Hcb0) as [bc Hbc].
 assert (Z:(QposEq ba (ca + bc))%Qpos).
  unfold QposEq.
  autorewrite with QposElim.
  rewrite -> Hba in Hbc.
  rewrite -> Hca in Hbc.
  replace LHS with (- a + (a + ba))%Q by simpl; ring.
  rewrite -> Hbc.
  ring.
 rewrite -> Z.
 clear Z.
 setoid_replace ((ca + bc)*e)%Qpos with (ca*e + bc*e)%Qpos; [| now QposRing].
 rewrite <- CRAbsSmall_ball.
 stepr ((IRasCR (integral (inj_Q IR a) (inj_Q IR c) Hac F HFl)[-]('((c-a)*zl))%Q)+
   ((IRasCR (integral (inj_Q IR c) (inj_Q IR b) Hcb F HFr)[-]('((b - c) * zr))))%Q)%CR.
  stepl ('(ca * e)%Qpos + '(bc * e)%Qpos)%CR.
   apply: AbsSmall_plus.
    apply (IHs1 _ _ Hac0); auto.
     intros o0 H [H0 H1].
     apply Hf.
     split; eauto with qarith.
    destruct (mu f ((1#2)*e)) as [q|];[|constructor].
    simpl in Hs|-*.
    eapply Qle_trans;[|apply Hs].
    rewrite -> SupDistanceToLinear_glue.
    replace LHS with (SupDistanceToLinear s1 (affineCombo_gt (OpenUnitDual o) Hab0):Q).
     apply Qmax_ub_l.
    apply SupDistanceToLinear_wd1; reflexivity.
   apply (IHs2 _ _ Hcb0); auto.
    intros o0 H [H0 H1].
    apply Hf.
    clear - H0 H1 Hac0.
    split; eauto with qarith.
   destruct (mu f ((1#2)*e)) as [q|];[|constructor].
   simpl in Hs|-*.
   eapply Qle_trans;[|apply Hs].
   rewrite -> SupDistanceToLinear_glue.
   replace LHS with (SupDistanceToLinear s2 (affineCombo_lt (OpenUnitDual o) Hab0):Q).
    apply Qmax_ub_r.
   apply SupDistanceToLinear_wd1; reflexivity.
  change (' (ca * e)%Qpos + ' (bc * e)%Qpos==(' (ca * e + bc * e)%Qpos))%CR.
  autorewrite with QposElim.
  ring.
 generalize (IRasCR (integral (inj_Q IR a) (inj_Q IR c) Hac F HFl))
   (IRasCR (integral (inj_Q IR c) (inj_Q IR b) Hcb F HFr)).
 intros x y.
 clear - x y.
 change ((x-' ((c - a) * zl)%Q + (y-' ((b - c) * zr)%Q))== (x + y)-(' ((c - a) * zl + (b - c) * zr)%Q))%CR.
 ring.
Qed.
