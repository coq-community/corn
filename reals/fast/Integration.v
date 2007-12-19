(*
Copyright © 2006 Russell O’Connor

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

Require Export IntegrableFunctions.
Require Export CRmetric.
Require Import CRArith.
Require Import StepQsec.
Require Import OpenUnit.
Require Import QMinMax.
Require Import QposMinMax.
Require Import Qabs.
Require Import Qauto.
Require Import Qround.
Require Import L1metric.
Require Import LinfMetric.
Require Import Qordfield.
Require Import COrdFields2.
Require Import Qmetric.
Require Import CornTac.

Set Implicit Arguments.

Opaque Qmax Qabs.

Fixpoint positive_rect2_helper
 (P : positive -> Type)
 (c1 : forall p : positive, P (Psucc p) -> P p -> P (xI p))
 (c2 : forall p : positive, P p -> P (xO p))
 (c3 : P 1%positive) 
 (b : bool) (p : positive) {struct p} : P (if b then Psucc p else p) :=
 match p return (P (if b then Psucc p else p)) with
 | xH    => if b return P (if b then (Psucc xH) else xH) then (c2 _ c3) else c3
 | xO p' => if b return P (if b then (Psucc (xO p')) else xO p') 
             then (c1 _ (positive_rect2_helper P c1 c2 c3 true _) (positive_rect2_helper P c1 c2 c3 false _))
             else (c2 _ (positive_rect2_helper P c1 c2 c3 false _))
 | xI p' => if b return P (if b then (Psucc (xI p')) else xI p') 
             then (c2 _ (positive_rect2_helper P c1 c2 c3 true _))
             else (c1 _ (positive_rect2_helper P c1 c2 c3 true _) (positive_rect2_helper P c1 c2 c3 false _))
 end.

Definition positive_rect2
 (P : positive -> Type)
 (c1 : forall p : positive, P (Psucc p) -> P p -> P (xI p))
 (c2 : forall p : positive, P p -> P (xO p))
 (c3 : P 1%positive) (p : positive) : P p :=
positive_rect2_helper P c1 c2 c3 false p.

Lemma positive_rect2_helper_bool : forall P c1 c2 c3 p,
positive_rect2_helper P c1 c2 c3 true p =
positive_rect2_helper P c1 c2 c3 false (Psucc p).
Proof.
intros P c1 c2 c3.
induction p; try reflexivity.
simpl.
rewrite IHp.
reflexivity.
Qed.

Lemma positive_rect2_red1 : forall P c1 c2 c3 p,
positive_rect2 P c1 c2 c3 (xI p) =
c1 p (positive_rect2 P c1 c2 c3 (Psucc p)) (positive_rect2 P c1 c2 c3 p).
Proof.
intros P c1 c2 c3 p.
unfold positive_rect2.
simpl.
rewrite positive_rect2_helper_bool.
reflexivity.
Qed.

Lemma positive_rect2_red2 : forall P c1 c2 c3 p,
positive_rect2 P c1 c2 c3 (xO p) =
c2 p (positive_rect2 P c1 c2 c3 p).
reflexivity.
Qed.

Lemma positive_rect2_red3 : forall P c1 c2 c3,
positive_rect2 P c1 c2 c3 (xH) = c3.
reflexivity.
Qed.

Lemma oddGluePoint (p:positive) : 0 < Psucc p # xI p /\ Psucc p # xI p < 1.
Proof.
intros p.
split; unfold Qlt.
 constructor.
simpl.
rewrite Pmult_comm.
simpl.
apply Zlt_left_rev.
rewrite Zpos_succ_morphism, Zpos_xI.
unfold Zsucc.
ring_simplify.
auto with *.
Qed.

Open Local Scope sfstscope.
Open Local Scope StepQ_scope.

Definition stepSample : positive -> StepQ := positive_rect2 
 (fun _ => StepQ)
 (fun p rec1 rec2 => glue (Build_OpenUnit (oddGluePoint p)) (constStepF (Psucc p#xI p:QS) * rec1) ((constStepF (1#(xI p):QS))*(constStepF (Psucc p:QS) + constStepF (p:QS)*rec2)))
 (fun p rec => glue (ou (1#2)) (constStepF (1#2:QS) * rec) (constStepF (1#2:QS) * (constStepF (1:QS) + rec)))
 (constStepF (1#2:QS)).

Section id01.

Lemma SupDistanceToLinearBase_pos : forall (l r:Q) (H:l<r) (x:Q), 0 < Qmax (x-l) (r-x).
Proof.
intros l r H x.
destruct (Qlt_le_dec_fast l x) as [H0|H0].
 rewrite Qlt_minus_iff in H0.
 unfold Qminus.
 eapply Qlt_le_trans; [|apply Qmax_ub_l].
 assumption.
rewrite Qlt_minus_iff in H.
eapply Qlt_le_trans; [|apply Qmax_ub_r].
eapply Qlt_le_trans.
 apply H.
unfold Qminus.
rsapply plus_resp_leEq_lft.
auto with *.
Qed.

Definition SupDistanceToLinear := StepFfold 
 (fun (x:QS) (l r:Q) (H:l < r) => mkQpos (SupDistanceToLinearBase_pos H x)) 
 (fun b f g l r H =>
  (Qpos_max (f _ _ (affineCombo_gt (OpenUnitDual b) H)) (g _ _ (affineCombo_lt (OpenUnitDual b) H)))).

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
induction x using StepF_ind;
 intros l1 r1 H1 l2 r2 H2 Hl Hr.
 unfold SupDistanceToLinear.
 simpl.
 autorewrite with QposElim.
 rewrite Hl.
 rewrite Hr.
 reflexivity.
do 2 rewrite SupDistanceToLinear_glue.
assert (X:(affineCombo (OpenUnitDual o) l1 r1==affineCombo (OpenUnitDual o) l2 r2)%Q).
 rewrite Hl.
 rewrite Hr.
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
rewrite (Qmax_assoc (affineCombo o a b - x)).
rewrite (Qmax_comm (affineCombo o a b - x)).
rewrite <- (Qmax_assoc (x - affineCombo o a b)).
rewrite Qmax_assoc.
apply Qmax_compat.
 rewrite <- Qle_max_l.
 rsapply plus_resp_leEq_lft.
 auto with *.
rewrite <- Qle_max_r.
rsapply plus_resp_leEq.
auto with *.
Qed.

Lemma affineAffine_l : forall a b o1 o2, 
(affineCombo o1 a (affineCombo o2 a b)==affineCombo (OpenUnitDualMult o1 o2) a b)%Q.
Proof.
intros a b o1 o2.
unfold affineCombo.
simpl.
ring.
Qed.

Lemma affineAffine_r : forall a b o1 o2, 
(affineCombo o1 (affineCombo o2 a b) b==affineCombo (o1*o2) a b)%Q.
Proof.
intros a b o1 o2.
unfold affineCombo.
simpl.
ring.
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
 rewrite Hc.
 apply Qmax_affineCombo; auto with *.
 apply Qlt_trans with c; assumption.
intros p a b c H0 H1 Hc.
apply SplitLR_glue_ind; intros H.
  do 2 rewrite SupDistanceToLinear_glue.
  rewrite Qmax_assoc.
  rewrite IHx1.
   rewrite Hc.
   unfold affineCombo.
   simpl.
   field; auto with *.
  apply Qmax_compat;
   apply SupDistanceToLinear_wd1; try reflexivity;
   rewrite Hc;
   unfold affineCombo;
   simpl;
   field; auto with *.
 do 2 rewrite SupDistanceToLinear_glue.
 rewrite <- Qmax_assoc.
 rewrite IHx2.
  rewrite Hc.
  unfold affineCombo.
  simpl.
  field; auto with *.
 apply Qmax_compat;
  apply SupDistanceToLinear_wd1; try reflexivity;
  rewrite Hc;
  unfold affineCombo;
  simpl;
  field; auto with *.
rewrite SupDistanceToLinear_glue.
apply Qmax_compat;
 apply SupDistanceToLinear_wd1; try reflexivity;
 rewrite Hc;
 unfold affineCombo;
 simpl;
 rewrite H;
 field; auto with *.
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
  rewrite Hx.
  reflexivity.
 intros a b H Hx.
 destruct Hx as [H0 H1] using (eq_glue_ind x2_1).
 rewrite SupDistanceToLinear_glue.
 rewrite <- IHx2_1; auto with *.
 rewrite <- IHx2_2; auto with *.
 unfold SupDistanceToLinear.
 simpl.
 autorewrite with QposElim.
 rewrite <- Qmax_assoc.
 rewrite (Qmax_assoc (affineCombo (OpenUnitDual o) a b - x)).
 rewrite (Qmax_comm (affineCombo (OpenUnitDual o) a b - x)).
 rewrite <- (Qmax_assoc (x - affineCombo (OpenUnitDual o) a b)).
 rewrite Qmax_assoc.
 symmetry.
 apply Qmax_compat.
  rewrite <- Qle_max_l.
  rsapply plus_resp_leEq_lft.
  auto with *.
 rewrite <- Qle_max_r.
 rsapply plus_resp_leEq.
 auto with *.
intros x2 a b H Hx.
destruct Hx as [H0 H1] using (glue_eq_ind x1_1).
rewrite SupDistanceToLinear_glue.
rewrite (IHx1_1 _ _ _ (affineCombo_gt (OpenUnitDual o) H) H0).
rewrite (IHx1_2 _ _ _ (affineCombo_lt (OpenUnitDual o) H) H1).
rewrite SupDistanceToLinear_split.
 reflexivity.
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
do 2 rewrite SupDistanceToLinear_glue.
set (A:=(affineCombo_gt (OpenUnitDual o) H)).
apply Qmax_compat.
 eapply Seq_trans.
  apply Q_Setoid.
 apply (IHx1 c _ _ A (Qplus_resp_Qlt _ _ A c)).
 apply SupDistanceToLinear_wd1; try reflexivity.
 unfold affineCombo; ring.
set (B:=(affineCombo_lt (OpenUnitDual o) H)).
eapply Seq_trans.
 apply Q_Setoid.
apply (IHx2 c _ _ B (Qplus_resp_Qlt _ _ B c)).
apply SupDistanceToLinear_wd1; try reflexivity.
unfold affineCombo; ring.
Qed.

Lemma SupDistanceToLinear_scale :
 forall x c a b (H:a < b) (H0:c*a < c*b),
  (c*SupDistanceToLinear x H == SupDistanceToLinear (constStepF (c:QS) * x) H0)%Q.
Proof.
intros x c a b H H0.
assert (X:0 < c).
 rewrite Qlt_minus_iff in *|-.
 rsapply (mult_cancel_less _ 0 c (b + - a))%Q; auto with *.
 replace LHS with 0 by ring.
 replace RHS with (c* b + - (c*a))%Q by ring.
 assumption.
revert c a b H H0 X.
induction x using StepF_ind.
 intros; unfold SupDistanceToLinear; simpl.
 autorewrite with QposElim.
 rewrite Qmax_mult_pos_distr_r; auto with *.
 apply Qmax_compat; ring.
intros c a b H H0 X.
change (constStepF (X:=QS) c * glue o x1 x2)
 with (glue o (constStepF (c:QS) * x1) (constStepF (c:QS) * x2)).
do 2 rewrite SupDistanceToLinear_glue.
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

Lemma SupDistanceToLinear_trans :
 forall x y a b (H:a < b), LinfBall (SupDistanceToLinear x H + SupDistanceToLinear y H) x y.
Proof.
unfold LinfBall.
intros x y a b H.
autorewrite with QposElim.
revert y a b H.
induction x using StepF_ind.
 induction y using StepF_ind; intros a b H.
  unfold LinfDistance, LinfNorm, StepQSup, SupDistanceToLinear.
  simpl.
  autorewrite with QposElim.
  apply Qabs_case; intros  H0.
   setoid_replace (x - x0)%Q with ((x - a) + (a - b) + (b - x0))%Q by ring.
   rsapply plus_resp_leEq_both; auto with *.
   replace RHS with (Qmax (x-a) (b-x) + 0)%Q by ring.
   rsapply plus_resp_leEq_both; auto with *.
   apply Qlt_le_weak.
   rewrite Qlt_minus_iff in *.
   replace RHS with (b + -a)%Q by ring.
   assumption.
  setoid_replace (-(x - x0))%Q with ((b - x) + - (b - a) + (x0 - a))%Q by ring.
  rsapply plus_resp_leEq_both; auto with *.
  replace RHS with (Qmax (x-a) (b-x) + 0)%Q by ring.
  rsapply plus_resp_leEq_both; auto with *.
  apply Qlt_le_weak.
  rewrite Qlt_minus_iff in *.
  replace RHS with (b + -a)%Q by ring.
  assumption.
 rewrite SupDistanceToLinear_glue.
 change (LinfDistance (constStepF (x:QS)) (glue o y1 y2))
  with (Qmax (LinfDistance (constStepF (x:QS)) y1)
             (LinfDistance (constStepF (x:QS)) y2)).
 rewrite Qmax_plus_distr_r.
 eapply Qle_trans.
  apply Qmax_le_compat;[apply (IHy1 _ _ (affineCombo_gt (OpenUnitDual o) H))|apply (IHy2 _ _ (affineCombo_lt (OpenUnitDual o) H))].
 apply Qmax_le_compat;
  rsapply plus_resp_leEq;
  unfold SupDistanceToLinear;
  simpl;
  autorewrite with QposElim; 
  apply Qmax_le_compat; auto with *.
  rsapply plus_resp_leEq.
  auto with *.
 rsapply plus_resp_leEq_lft.
 apply Qopp_le_compat.
 auto with *.
intros y a b H.
unfold LinfDistance.
unfold StepQminus.
rewrite MapGlue.
rewrite ApGlue.
change (LinfNorm
  (glue o (QminusS ^@> x1 <@> SplitL y o) (QminusS ^@> x2 <@> SplitR y o)))
 with (Qmax (LinfDistance x1 (SplitL y o)) (LinfDistance x2 (SplitR y o))).
rewrite SupDistanceToLinear_glue.
rewrite Qmax_plus_distr_l.
setoid_replace (SupDistanceToLinear y H:Q)
 with (SupDistanceToLinear (glue o (SplitL y o) (SplitR y  o)) H:Q).
 rewrite SupDistanceToLinear_glue.
 do 2 rewrite Qmax_plus_distr_r.
 apply Qmax_le_compat.
  eapply Qle_trans; [apply IHx1| apply Qmax_ub_l].
 eapply Qle_trans; [apply IHx2| apply Qmax_ub_r].
apply SupDistanceToLinear_wd2.
symmetry; apply glueSplit.
Qed.

Lemma stepSampleDistanceToId : (forall p, QposEq (@SupDistanceToLinear (stepSample p) 0 1 (@pos_one _)) (1#(2*p))).
Proof.
unfold QposEq.
induction p using positive_rect2.
  replace (stepSample (xI p))
   with (glue (Build_OpenUnit (oddGluePoint p)) (constStepF (Psucc p#xI p:QS) * (stepSample (Psucc p))) ((constStepF (1#(xI p):QS))*(constStepF (Psucc p:QS) + constStepF (p:QS)*(stepSample p))))
   by (symmetry;rapply positive_rect2_red1).
  rewrite SupDistanceToLinear_glue.
  generalize (@affineCombo_gt (OpenUnitDual (Build_OpenUnit (oddGluePoint p))) 0 1 (pos_one Q_as_COrdField))
    (@affineCombo_lt (OpenUnitDual (Build_OpenUnit (oddGluePoint p))) 0 1 (pos_one Q_as_COrdField)).
  intros A B.
  set (C:=(pos_one Q_as_COrdField)) in *.
  transitivity (Qmax (1#2*xI p) (1#2*xI p))%Q;[|apply Qmax_idem].
  apply Qmax_compat.
   set (LHS := (SupDistanceToLinear
    (constStepF (X:=QS) (Psucc p # xI p) * stepSample (Psucc p)) A)).
   transitivity ((Psucc p#xI p)*(SupDistanceToLinear (stepSample (Psucc p)) C))%Q;
    [|rewrite IHp;
      change ((Psucc p * 1 * (2 * (2* p + 1)) = 2* (Psucc p + p * (2* (Psucc p))))%Z);
      repeat rewrite Zpos_succ_morphism; ring].
   assert (X:(Psucc p # xI p) *0 < (Psucc p # xI p) *1).
    constructor.
   rewrite (fun a => SupDistanceToLinear_scale a C X).
   rapply SupDistanceToLinear_wd1.
    simpl; ring.
   unfold affineCombo; simpl; unfold QONE; ring.
  set (LHS := (SupDistanceToLinear
  (constStepF (X:=QS) (1 # xI p) *
   (constStepF (X:=QS) (Psucc p) + constStepF (X:=QS) p * stepSample p)) B)%Q).
  transitivity ((1#xI p)*(p*(SupDistanceToLinear (stepSample (p)) C)))%Q;
  [|rewrite IHp0;
    change ((p * 1 * (2 * (2* p + 1)) = 2* (p + p * (2* p)))%Z); ring].
  assert (X0:(p *0 < p *1)).
   constructor.
  rewrite (fun a => SupDistanceToLinear_scale a C X0).
  assert (X1:(p*0 + Psucc p < p*1 + Psucc p)).
   rsapply plus_resp_less_rht.
   assumption.
  rewrite (fun a => SupDistanceToLinear_translate a X0 X1).
  assert (X2:((1# xI p)*(p*0 + Psucc p) < (1#xI p)*(p*1 + Psucc p))).
   rsapply mult_resp_less_lft; auto with *.
  rewrite (fun a => SupDistanceToLinear_scale a X1 X2).
  rapply SupDistanceToLinear_wd1.
   unfold affineCombo; simpl; unfold QONE.
   repeat rewrite Zpos_succ_morphism;
   repeat rewrite Qmake_Qdiv;
   repeat rewrite Zpos_xI; 
   field; auto with *.
  change (2*(p*1) + 1 = ((p*1*1 + Psucc p*1)*1))%Z.
  rewrite Zpos_succ_morphism; ring.
 change (1#2*xO p)%Q with ((1#2)*(1#(2*p)))%Q.
 replace (stepSample (xO p))
   with (glue (ou (1#2))
    (constStepF (1#2:QS) * (stepSample p)) 
    (constStepF (1#2:QS) * (constStepF (1:QS) + (stepSample p))))
   by (symmetry;rapply positive_rect2_red2).
 rewrite SupDistanceToLinear_glue.
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
  rewrite (fun a c => SupDistanceToLinear_scale a c X).
  rapply SupDistanceToLinear_wd1; constructor.
 assert (X0:0 + 1 < 1 +1).
  constructor.
 rewrite (fun a c => SupDistanceToLinear_translate a c X0).
 assert (X1:(1#2)*(0 + 1) < (1#2)*(1 +1)).
  constructor.
 rewrite (fun a => SupDistanceToLinear_scale a X0 X1).
 rapply SupDistanceToLinear_wd1; constructor.
reflexivity.
Qed.

Definition id01_raw_help (q:QposInf) : positive := 
match q with
|QposInfinity => 1%positive
|Qpos2QposInf q =>
  match (Qceiling ((1#2)/q)%Qpos) with
  | Zpos p => p
  | _ => 1%positive
  end
end.

Lemma id01_raw_help_le : forall (q:Qpos),
 ((1#2*id01_raw_help q) <= q)%Q.
Proof.
intros q.
simpl.
assert (X:=Qle_ceiling ((1#2)/q)%Qpos).
revert X.
generalize (Qceiling ((1#2)/q)%Qpos).
intros [|p|p] H; try solve [elim (Qle_not_lt _ _ H); auto with *].
autorewrite with QposElim in *.
rewrite Qmake_Qdiv in *.
rewrite Zpos_xO.
rewrite Qle_minus_iff in *.
change ((2%positive * p)%Z:Q) with (2%positive * p)%Q.
replace RHS with (((2*q)/(2*p))*(p - 1%positive/2%positive*/q))%Q by (field; split; discriminate).
rsapply mult_resp_nonneg; auto with *.
Qed.

Definition id01_raw (q:QposInf) : StepQ := stepSample (id01_raw_help q).

Lemma id01_prf : is_RegularFunction (id01_raw:QposInf -> L1StepQ_as_MetricSpace).
Proof.
intros a b.
unfold id01_raw.
apply ball_weak_le with ((1#2*(id01_raw_help a)) + (1#2*(id01_raw_help b)))%Qpos.
 autorewrite with QposElim.
 rapply plus_resp_leEq_both;
  rapply id01_raw_help_le.
apply LinfL1Ball.
do 2 rewrite <- stepSampleDistanceToId.
apply SupDistanceToLinear_trans.
Qed.

Definition id01 : IntegrableFunction :=
Build_RegularFunction id01_prf.

End id01.

Definition CRSetoid : Setoid.
exists CR (@ms_eq CR).
eapply msp_Xsetoid.
apply (@msp CR).
Defined.

(* approximate z e is not a morphism, so we revert to using the pre-setoid version of StepF's map *)
Definition distribComplete_raw (x:StepF CRSetoid) (e:QposInf) : StepQ :=
StepFunction.Map (fun z => approximate z e) x.

Lemma distribComplete_prf : forall (x:StepF CRSetoid), is_RegularFunction (distribComplete_raw x).
Proof.
unfold distribComplete_raw.
intros x a b.
induction x using StepF_ind.
 change (Qabs (approximate x a - approximate x b) <= (a + b)%Qpos)%Q.
 rewrite <- Qball_Qabs.
 rapply regFun_prf.
simpl (ball (m:=L1StepQ_as_MetricSpace)).
unfold L1Ball, L1Distance.
set (f:=(fun z : RegularFunction Q_as_MetricSpace => approximate z a)) in *.
set (g:=(fun z : RegularFunction Q_as_MetricSpace => approximate z b)) in *.
change (Map f (glue o x1 x2))
 with (glue o (Map f x1:StepQ) (Map f x2)).
change (Map g (glue o x1 x2))
 with (glue o (Map g x1:StepQ) (Map g
 x2)).
unfold StepQminus.
rewrite MapGlue.
rewrite ApGlueGlue.
rewrite L1Norm_glue.
apply Qle_trans with (o*(a+b)%Qpos + (1-o)*(a+b)%Qpos)%Q;
 [|(replace LHS with ((a+b)%Qpos:Q) by ring); apply Qle_refl].
rsapply plus_resp_leEq_both;
 rsapply mult_resp_leEq_lft; auto with *.
Qed.

Definition distribComplete (x:StepF CRSetoid) : IntegrableFunction :=
Build_RegularFunction (distribComplete_prf x).

Definition ComposeContinuous_raw f (z:StepQ) := distribComplete (StepFunction.Map f z).

Open Local Scope uc_scope.

Lemma ComposeContinuous_prf (f:Q_as_MetricSpace --> CR) :
 is_UniformlyContinuousFunction (ComposeContinuous_raw f) (mu f).
Proof.
intros f e a b H d1 d2.
simpl.