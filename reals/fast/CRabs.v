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

Require Import Max_AbsIR.
Require Export CRArith.
Require Import Qmetric.
Require Import Qabs.
Require Import QMinMax.
Require Import CRcorrect.
Require Import CRIR.
Require Import CornTac.

Open Local Scope Q_scope.
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
replace LHS with (Qabs b - Qabs a) by ring.
setoid_replace (a - b) with (- (b - a)) in Hab by ring.
rewrite Qabs_opp in Hab.
eapply Qle_trans;[|apply Hab].
apply Qabs_triangle_reverse.
Qed.

Open Local Scope uc_scope.

Definition Qabs_uc : Q_as_MetricSpace --> Q_as_MetricSpace := 
Build_UniformlyContinuousFunction Qabs_uc_prf.

Definition CRabs : CR --> CR := Cmap QPrelengthSpace Qabs_uc.

Lemma CRabs_correct : forall x,
 (IRasCR (AbsIR x) == CRabs (IRasCR x))%CR.
Proof.
intros x.
apply stableEq.
 rapply Complete_stable.
 apply stableQ.
generalize (leEq_or_leEq _ Zero x).
cut ((x[<=]Zero or Zero[<=]x) -> (IRasCR (AbsIR x) == CRabs (IRasCR x))%CR).
 unfold Not.
 tauto.
intros [H|H].
 transitivity (IRasCR ([--]x)).
  apply IRasCR_wd.
  apply AbsIR_eq_inv_x; auto.
 rewrite IR_opp_as_CR.
 rewrite IR_leEq_as_CR in H.
 rewrite IR_Zero_as_CR in H.
 revert H.
 generalize (IRasCR x).
 intros m Hm.
 rewrite CRle_min_r in Hm.
 rewrite CRmin_boundAbove in Hm.
 setoid_replace (CRabs m)%CR with (- (- (CRabs m)))%CR using relation ms_eq by ring.
 apply CRopp_wd.
 rewrite <- Hm.
 rapply regFunEq_e.
 intros e.
 simpl. 
 rewrite Qabs_neg.
  auto with *.
 rewrite Qopp_involutive.
 rapply ball_refl.
transitivity (IRasCR x).
 apply IRasCR_wd.
 apply AbsIR_eq_x; auto.
rewrite IR_leEq_as_CR in H.
rewrite IR_Zero_as_CR in H.
revert H.
generalize (IRasCR x).
intros m Hm.
rewrite CRle_max_r in Hm.
rewrite CRmax_boundBelow in Hm.
rewrite <- Hm.
rapply regFunEq_e.
intros e.
simpl. 
rewrite Qabs_pos.
 auto with *.
rapply ball_refl.
Qed.
