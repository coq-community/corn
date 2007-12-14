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
