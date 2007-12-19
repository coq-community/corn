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

Require Export StepQsec.
Require Import L1metric.
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

Definition StepQSup : (StepQ)->Q := StepFfold (fun x => x) (fun b (x y:QS) => Qmax x y)%Q.
Definition LinfNorm (f:StepF QS):Q:=(StepQSup (StepQabs f)).
Definition LinfDistance (f g:StepF QS):Q := (LinfNorm (f - g)).
Definition LinfBall (e:Qpos)(f g:StepF QS):Prop:=((LinfDistance f g)<=e)%Q.

Lemma StepQSup_glue : forall o s t, (StepQSup (glue o s t) = Qmax (StepQSup s) (StepQSup t))%Q.
Proof.
reflexivity.
Qed.

Hint Rewrite StepQSup_glue: StepF_rew.

Lemma StepQIntegral_le_Sup : forall x, (IntegralQ x <= StepQSup x)%Q.
Proof.
intros x.
induction x using StepF_ind.
 apply Qle_refl.
autorewrite with StepF_rew.
apply Qle_trans with (o * (StepQSup x1) + (1 - o)*(StepQSup x2))%Q.
 rsapply plus_resp_leEq_both; rsapply mult_resp_leEq_lft; auto with *.
generalize (StepQSup x1) (StepQSup x2).
clear - o.
intros a b.
replace RHS with (o*(Qmax a b) + (1-o)*(Qmax a b))%Q by ring.
rsapply plus_resp_leEq_both; rsapply mult_resp_leEq_lft; auto with *.
Qed.

Lemma L1Norm_le_LinfNorm : forall x, (L1Norm x <= LinfNorm x)%Q.
Proof.
intros x.
rapply StepQIntegral_le_Sup.
Qed.

Lemma L1Distance_le_LinfDistance : forall x y, (L1Distance x y <= LinfDistance x y)%Q.
Proof.
intros x y.
rapply StepQIntegral_le_Sup.
Qed.

Lemma LinfL1Ball : forall x y e, (LinfBall e x y -> L1Ball e x y).
Proof.
intros x y e H.
unfold L1Ball.
eapply Qle_trans.
 apply L1Distance_le_LinfDistance.
assumption.
Qed.

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

Add Morphism StepQSup 
  with signature  StepF_eq ==>  Qeq
 as StepQSup_wd.
unfold IntegralQ.
induction x1 using StepF_ind.
intros x2 H. simpl. induction x2 using StepF_ind.
  simpl.  auto with *.
 change (StepQSup (glue o x2_1 x2_2))%Q with
  (Qmax (StepQSup x2_1) (StepQSup x2_2)).
 destruct H as [H0 H1] using (eq_glue_ind x2_1).
 rewrite <- IHx2_1; auto with *.
 rewrite <- IHx2_2; auto with *.
intros x2 H.
destruct H as [H0 H1] using (glue_eq_ind x1_1).
change (StepQSup (glue o x1_1 x1_2))%Q with
 (Qmax (StepQSup x1_1) (StepQSup x1_2)).
rewrite (IHx1_1 _ H0).
rewrite (IHx1_2 _ H1).
symmetry.
apply StepQSupSplit.
Qed.

Add Morphism LinfNorm 
  with signature StepF_eq ==>  Qeq
 as LinfNorm_wd.
unfold LinfNorm.
intros x y Hxy.
rewrite Hxy.
reflexivity.
Qed.

Add Morphism LinfDistance 
  with signature StepF_eq ==> StepF_eq ==>  Qeq
 as LinfDistance_wd.
unfold LinfDistance.
intros x1 x2 Hx y1 y2 Hy.
rewrite Hx.
rewrite Hy.
reflexivity.
Qed.

Add Morphism LinfBall 
  with signature QposEq ==> StepF_eq ==> StepF_eq ==> iff
 as LinfBall_wd.
unfold LinfBall.
intros a1 a2 Ha x1 x2 Hx y1 y2 Hy.
unfold QposEq in Ha.
rewrite Ha.
rewrite Hx.
rewrite Hy.
reflexivity.
Qed.

Lemma LinfBall_refl : forall e x, (LinfBall e x x).
Proof.
intros e x.
unfold LinfBall, LinfDistance.
setoid_replace (x-x) with (constStepF (0:QS)) using relation StepF_eq by ring.
change (0 <= e)%Q.
auto with *.
Qed.

Lemma Linfball_sym : forall e x y, (LinfBall e x y) -> (LinfBall e y x).
Proof.
intros e x y.
unfold LinfBall, LinfDistance.
unfold LinfNorm.
setoid_replace (x-y) with (-(y-x)) using relation StepF_eq by ring.
rewrite StepQabsOpp.
auto.
Qed.

Lemma StepQSup_resp_le : forall x y, x <= y -> (StepQSup x <= StepQSup y)%Q.
Proof.
induction x using StepF_ind.
 induction y using StepF_ind.
  auto.
 intros [Hl Hr].
 rewrite StepQSup_glue.
 eapply Qle_trans;[|apply Qmax_ub_l].
 apply IHy1.
 assumption.
intros y.
rewrite <- (glueSplit y o).
do 2 rewrite StepQSup_glue.
intros H.
unfold StepQ_le in H.
rewrite MapGlue in H.
rewrite ApGlueGlue in H.
destruct H as [Hl Hr].
apply Qmax_le_compat; auto.
Qed.

Lemma StepQSup_plus : forall x y, (StepQSup (x + y) <= StepQSup x + StepQSup y )%Q.
Proof.
induction x using StepF_ind.
 induction y using StepF_ind.
  apply Qle_refl.
 rewrite StepQSup_glue.
 rewrite Qmax_plus_distr_r.
 rapply Qmax_le_compat; assumption.
intros y.
rewrite <- (glueSplit y o).
unfold StepQplus.
rewrite MapGlue.
rewrite ApGlueGlue.
do 3 rewrite StepQSup_glue.
change (Qmax (StepQSup (QplusS ^@> x1 <@> SplitL y o))
   (StepQSup (QplusS ^@> x2 <@> SplitR y o)))
 with (Qmax (StepQSup (x1 + SplitL y o)) (StepQSup (x2 + SplitR y o))).
eapply Qle_trans;[apply Qmax_le_compat;[apply IHx1|apply IHx2]|].
rewrite Qmax_plus_distr_l.
apply Qmax_le_compat;
 rsapply plus_resp_leEq_lft;
 auto with *.
Qed.

Lemma Linfball_triangle : forall e d x y z, (LinfBall e x y) -> (LinfBall d y z) -> (LinfBall (e+d) x z).
Proof.
intros e d x y z.
unfold LinfBall, LinfDistance.
unfold LinfNorm.
setoid_replace (x-z) with ((x-y)+(y-z)) using relation StepF_eq by ring.
intros He Hd.
autorewrite with QposElim.
apply Qle_trans with (StepQSup (StepQabs (x-y) + StepQabs (y-z)))%Q.
 apply StepQSup_resp_le.
 apply StepQabs_triangle.
eapply Qle_trans.
 apply StepQSup_plus.
rsapply plus_resp_leEq_both; assumption.
Qed.
