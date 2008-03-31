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
** Linf metric for Step Functions
The Linf metric is measured by the sup of the absolute value of the
difference between step functions.

*** Sup for Step Functions.
*)
Definition StepQSup : (StepQ)->Q := StepFfold (fun x => x) (fun b (x y:QS) => Qmax x y)%Q.
Definition LinfNorm (f:StepF QS):Q:=(StepQSup (StepQabs f)).
Definition LinfDistance (f g:StepF QS):Q := (LinfNorm (f - g)).
Definition LinfBall (e:Qpos)(f g:StepF QS):Prop:=((LinfDistance f g)<=e)%Q.

(** The Sup of the glue of two step functions. *)
Lemma StepQSup_glue : forall o s t, (StepQSup (glue o s t) = Qmax (StepQSup s) (StepQSup t))%Q.
Proof.
reflexivity.
Qed.

(** The Linf Distance between the glue of two step functions. *)
Lemma LinfDistance_glue : forall o s s0 t t0,
 (LinfDistance (glue o s s0) (glue o t t0) == Qmax (LinfDistance s t) (LinfDistance s0 t0))%Q.
Proof.
intros o s s0 t t0.
unfold LinfDistance at 1.
unfold StepQminus.
rewrite MapGlue.
rewrite ApGlueGlue.
reflexivity.
Qed.
(* begin hide *)
Hint Rewrite StepQSup_glue: StepF_rew.
(* end hide *)
(** The integral (on [[0,1]]) is always at most the sup. *)
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

(** Hence, the L1 Norm is at most the Linf Norm. *)
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

Lemma LinfNorm_Zero : forall s, 
 (LinfNorm s <= 0)%Q -> s == (constStepF (0:QS)).
Proof.
intros s.
intros Hs.
induction s using StepF_ind.
 rapply Qle_antisym.
  eapply Qle_trans;[apply Qle_Qabs|assumption].
 rewrite <- (Qopp_involutive x).
 change 0 with (- (- 0))%Q.
 apply Qopp_le_compat.
 eapply Qle_trans;[apply Qle_Qabs|].
 rewrite Qabs_opp.
 assumption.
apply glue_StepF_eq.
 apply IHs1.
 eapply Qle_trans;[|apply Hs].
 rapply Qmax_ub_l.
apply IHs2.
eapply Qle_trans;[|apply Hs].
rapply Qmax_ub_r.
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
(* end hide *)
(** How the sup interacts with various arithmetic operations on step functions. *)
Lemma StepQSup_resp_le : forall x y, x <= y -> (StepQSup x <= StepQSup y)%Q.
Proof.
rapply StepF_ind2; auto.
 intros s s0 t t0 Hs Ht.
 rewrite Hs, Ht; auto.
intros o s s0 t t0 H0 H1.
unfold StepQ_le.
rewriteStepF.
intros [Hl Hr].
apply Qmax_le_compat; auto.
Qed.

Lemma StepQSup_plus : forall x y, (StepQSup (x + y) <= StepQSup x + StepQSup y )%Q.
Proof.
rapply StepF_ind2; auto with *.
 intros s s0 t t0 Hs Ht.
 rewrite Hs, Ht; auto.
intros o s s0 t t0 H0 H1.
unfold StepQplus.
rewriteStepF.
eapply Qle_trans;[apply Qmax_le_compat;[apply H0|apply H1]|].
rewrite Qmax_plus_distr_l.
apply Qmax_le_compat;
 rsapply plus_resp_leEq_lft;
 auto with *.
Qed.

(** The Linf ball satifies the requirements of a metric. *)
Lemma Linfball_refl : forall e x, (LinfBall e x x).
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

Lemma Linfball_closed : forall e x y, (forall d, (LinfBall (e+d) x y)) -> (LinfBall e x y).
Proof.
unfold LinfBall. intros e a b H.
assert (forall x, (forall d : Qpos, x <= e+d) -> x <= e)%Q.
 intros. rsapply shift_zero_leEq_minus'.
 rsapply inv_cancel_leEq. rsapply approach_zero_weak.
 intros. replace LHS with (x[-](e:Q)). 
  rsapply shift_minus_leEq. replace RHS with (e+e0)%Q by ring. rewrite <- (QposAsmkQpos H1).
  apply (H0 (mkQpos H1)).
 unfold cg_minus; simpl; ring.
apply H0. exact H.
Qed.

Lemma Linfball_eq : forall x y, (forall e : Qpos, LinfBall e x y) -> StepF_eq x y.
Proof.
intros x y H.
unfold LinfBall in H.
setoid_replace y with (constStepF (0:QS)+y) using relation StepF_eq by ring.
set (z:=constStepF (0:QS)).
setoid_replace x with (x - y + y) using relation StepF_eq by ring.
apply StepQplus_wd; try reflexivity.
unfold z; clear z.
rapply LinfNorm_Zero.
apply Qnot_lt_le.
intros H0.
assert (0<(1#2)*( LinfNorm (x - y))).
 rsapply mult_resp_pos; auto with *.
apply (Qle_not_lt _ _ (H (mkQpos H1))).
autorewrite with QposElim.
rewrite Qlt_minus_iff.
unfold LinfDistance.
ring_simplify.
assumption.
Qed.

(**
*** Example of a Metric Space <StepQ, LinfBall>
*)
Lemma Linf_is_MetricSpace : 
 (is_MetricSpace (@StepF_eq QS) LinfBall).
split.
     apply (StepF_Sth QS).
    rapply Linfball_refl.
   rapply Linfball_sym.
  rapply Linfball_triangle.
 rapply Linfball_closed.
rapply Linfball_eq.
Qed.
(* begin hide *)
Add Morphism LinfBall with signature QposEq ==> StepF_eq ==> StepF_eq ==> iff as L1Ball_wd.
intros x1 x2 Hx y1 y2 Hy z1 z2 Hz.
unfold LinfBall.
change (x1 == x2)%Q in Hx.
rewrite Hx.
rewrite Hy.
rewrite Hz.
reflexivity.
Qed.
(* end hide *)
Definition LinfStepQ : MetricSpace :=
Build_MetricSpace LinfBall_wd Linf_is_MetricSpace.
(* begin hide *)
Canonical Structure LinfStepQ.
(* end hide *)

(** The Linf space is a prelength space. *)
Lemma StepQSup_scale :forall q x, (0 <= q)%Q ->
 (q*(StepQSup x) == (StepQSup (QscaleS q^@>x)))%Q.
Proof.
intros q x Hq.
induction x using StepF_ind.
 reflexivity.
rewriteStepF.
rewrite <- IHx1.
rewrite <- IHx2.
apply Qmax_mult_pos_distr_r; auto.
Qed.

Lemma LinfNorm_scale : forall q s, 
 (LinfNorm (QscaleS q ^@> s) == Qabs q * LinfNorm s)%Q.
Proof.
intros q s.
unfold LinfNorm.
rewrite StepQSup_scale.
 apply Qabs_nonneg.
apply StepQSup_wd.
unfold StepF_eq.
set (g:= st_eqS QS).
set (q0 := (QscaleS q)).
set (q1 := (QscaleS (Qabs q))).
set (f:= ap
 (compose g (compose QabsS q0))
 (compose q1 QabsS)).
cut (StepFfoldProp (f ^@> s)).
 unfold f.
 evalStepF.
 tauto.
apply StepFfoldPropForall_Map.
intros a.
rapply Qabs_Qmult.
Qed.

Lemma LinfStepQPrelengthSpace : PrelengthSpace LinfStepQ.
Proof.
intros x y e d1 d2 He Hxy.
change (e < (d1+d2)%Qpos) in He.
set (d:=(d1+d2)%Qpos) in *.
simpl in *.
unfold LinfBall in *.
unfold LinfDistance in *.
pose (d1':=constStepF (d1:QS)).
pose (d2':=constStepF (d2:QS)).
pose (d':=constStepF ((/d):QS)).
set (f:=(d'*(x*d2' + y*d1'))%SQ).
assert (X:(((d1' + d2')*d')==constStepF (1:QS))%SQ).
 change (constStepF ((d1 + d2)%Qpos/(d1 + d2)%Qpos:QS)==constStepF (X:=QS) 1).
 apply constStepF_wd.
 simpl.
 field.
 apply Qpos_nonzero.
exists (f).
 setoid_replace (x - f)%SQ
  with (d1' * d' * (x - y))%SQ using relation StepF_eq.
  change ((d1' * d')%SQ * (x - y)%SQ) with
    (QscaleS (d1/d)%Qpos ^@> (x-y)%SQ).
  rewrite LinfNorm_scale.
  rewrite Qabs_pos; auto with *.
  autorewrite with QposElim.
  replace LHS with ((d1*LinfNorm (x - y))/d) by
   (field; apply Qpos_nonzero).
  apply Qle_shift_div_r; auto with *.
  rsapply mult_resp_leEq_lft; auto with *.
  apply Qle_trans with e; auto with *.
 setoid_replace (x - f) with (constStepF (1:QS)*x - f) using relation StepF_eq by ring.
 rewrite <- X.
 unfold f.
 ring.
setoid_replace (f -y)
  with (d2' * d' * (x - y))%SQ using relation StepF_eq.
 change ((d2' * d')%SQ * (x - y)%SQ) with
   (QscaleS (d2/d)%Qpos ^@> (x-y)%SQ).
 rewrite LinfNorm_scale.
 rewrite Qabs_pos; auto with *.
 autorewrite with QposElim.
 replace LHS with ((d2*LinfNorm (x - y))/d) by
  (field; apply Qpos_nonzero).
 apply Qle_shift_div_r; auto with *.
 rsapply mult_resp_leEq_lft; auto with *.
 apply Qle_trans with e; auto with *.
setoid_replace (f- y) with (f - constStepF (1:QS)*y) using relation StepF_eq by ring.
rewrite <- X.
unfold f.
ring.
Qed.

(** Sup is uniformly continuous. *)
Lemma sup_uc_prf : is_UniformlyContinuousFunction (StepQSup:LinfStepQ -> Q) Qpos2QposInf.
Proof.
intros e x y H.
simpl in *.
rewrite Qball_Qabs.
eapply Qle_trans;[|apply H].
clear H.
revert x y. 
rapply StepF_ind2.
  intros s s0 t t0 Hs Ht.
  rewrite Hs, Ht.
  auto.
 intros x y.
 apply Qle_refl.
intros o s s0 t t0 H0 H1.
rewrite LinfDistance_glue.
do 2 rewrite StepQSup_glue.
assert (X:forall a b, (-(a-b)==b-a)%Q).
 intros; ring.
apply Qabs_case; intros H;
[|rewrite <- Qabs_opp in H0, H1; rewrite X in *];
 rewrite Qmax_minus_distr_l;
 apply Qmax_le_compat;
  (eapply Qle_trans;[|apply H0 || apply H1]);
  (eapply Qle_trans;[|apply Qle_Qabs]);
  unfold Qminus;
  rsapply plus_resp_leEq_lft;
  auto with *.
Qed.

Open Local Scope uc_scope.

Definition StepQSup_uc : LinfStepQ --> Q_as_MetricSpace
:= Build_UniformlyContinuousFunction sup_uc_prf.

(** There is an injection from Q to Linf. *)
Lemma constStepF_uc_prf : is_UniformlyContinuousFunction (@constStepF QS:Q -> LinfStepQ) Qpos2QposInf.
Proof.
intros e x y H.
simpl in *.
rewrite Qball_Qabs in H.
assumption.
Qed.

Definition constStepF_uc : Q_as_MetricSpace --> LinfStepQ
:= Build_UniformlyContinuousFunction constStepF_uc_prf.

(** And there is an injection from Linf to L1. *)
Lemma LinfAsL1_uc_prf : is_UniformlyContinuousFunction (fun (x:LinfStepQ) => (x:L1StepQ)) Qpos2QposInf.
Proof.
intros e x y H.
simpl in *.
unfold L1Ball.
eapply Qle_trans.
 unfold L1Distance.
 apply L1Norm_le_LinfNorm.
assumption.
Qed.

Definition LinfAsL1 : LinfStepQ --> L1StepQ
:= Build_UniformlyContinuousFunction LinfAsL1_uc_prf.