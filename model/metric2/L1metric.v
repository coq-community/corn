Require Export StepQsec.
Require Export UniformContinuity.
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

Opaque Qred.

Definition IntegralQ:(StepQ)->Q:=(StepFfold (fun x => x) (fun b (x y:QS) => (Qred (affineCombo b x y:QS))))%Q.
Definition L1Norm(f:StepF QS):Q:=(IntegralQ (StepQabs f)).
Definition L1Distance(f g:StepF QS):Q:=(L1Norm (f - g)).
Definition L1Ball (e:Qpos)(f g:StepF QS):Prop:=(L1Distance f g)<=e.

(*
Definition test1:=(constStepF (1:QS)).
Definition test2:=(glue (ou 1/2) (constStepF (0:QS)) (constStepF (1:QS))).
Eval lazy beta zeta delta iota in (L1Distance test1 test2):Q.
Why is compute so slow?
Eval compute in (L1Distance test1 test2):Q.
Eval lazy beta zeta delta iota in (L1Distance test2 test1):Q.
Eval lazy beta zeta delta iota in (L1Ball (1#1)%Qpos test2 test1).
Eval compute in (Mesh test2).
*)

Lemma L1ball_dec : forall e a b, {L1Ball e a b}+{~L1Ball e a b}.
intros e a b.
unfold L1Ball.
set (d:=L1Distance a b).
destruct (Qlt_le_dec_fast e d) as [Hdc|Hdc].
right. abstract auto with *.
left. exact Hdc.
Defined.

Lemma Integral_glue : forall o s t, (IntegralQ (glue o s t) == o*(IntegralQ s) + (1-o)*(IntegralQ t))%Q.
Proof.
intros o s t.
unfold IntegralQ.
simpl.
rewrite Qred_correct.
reflexivity.
Qed.

Lemma IntegralSplit : forall (o:OpenUnit) x, 
 (IntegralQ x ==
 affineCombo o (IntegralQ (SplitL x o)) (IntegralQ (SplitR x o)))%Q.
Proof.
intros o x.
revert o.
induction x using StepF_ind.
unfold IntegralQ. simpl. intros. unfold affineCombo; simpl in x; ring.
intros p.
rewrite Integral_glue.
apply SplitLR_glue_ind; intros H.
  rewrite Integral_glue.
  unfold affineCombo in *.
  rewrite (IHx1 (OpenUnitDiv p o H)).
  unfold IntegralQ; simpl; fold IntegralQ. unfold affineCombo; field; auto with *. (*why does this not work*)
 rewrite Integral_glue.
 simpl. unfold IntegralQ; simpl; fold IntegralQ.
 repeat rewrite Qred_correct. 
 unfold affineCombo in *.
 rewrite (IHx2 (OpenUnitDualDiv p o H)).
 unfold IntegralQ; simpl; fold IntegralQ. unfold affineCombo; field; auto with *.
unfold affineCombo in *.
rewrite H.
reflexivity.
Qed.

Hint Resolve IntegralSplit : StepQArith.

Add Morphism IntegralQ 
  with signature  StepF_eq ==>  Qeq
 as IntegralQ_wd.
induction x1 using StepF_ind.
intros x2 H. simpl. induction x2 using StepF_ind.
  auto with *.
 rewrite Integral_glue.
 simpl.
 destruct H as [H0 H1] using (eq_glue_ind x2_1).
 rewrite <- IHx2_1; auto with *.
 rewrite <- IHx2_2; auto with *.
 simpl in x; unfold affineCombo; ring.
intros x2 H.
destruct H as [H0 H1] using (glue_eq_ind x1_1).
rewrite Integral_glue.
rewrite (IHx1_1 _ H0).
rewrite (IHx1_2 _ H1).
symmetry.
rapply IntegralSplit.
Qed.

Add Morphism L1Norm 
  with signature StepF_eq ==>  Qeq
 as L1Norm_wd.
unfold L1Norm.
intros x y Hxy.
rewrite Hxy.
reflexivity.
Qed.

Add Morphism L1Distance 
  with signature StepF_eq ==> StepF_eq ==>  Qeq
 as L1Distance_wd.
unfold L1Distance.
intros x1 x2 Hx y1 y2 Hy.
rewrite Hx.
rewrite Hy.
reflexivity.
Qed.

Hint Rewrite Integral_glue: StepF_rew.

Lemma Integral_plus:forall s t,
  ((IntegralQ s)+(IntegralQ t)==(IntegralQ (s + t)))%Q.
Proof.
apply StepF_ind2; try reflexivity.
 intros s s0 t t0 Hs Ht.
 rewrite Hs, Ht; auto.
intros o s s0 t t0 H0 H1.
unfold StepQplus.
rewriteStepF.
replace LHS
 with (o*(IntegralQ s + IntegralQ t) + (1-o)*(IntegralQ s0 + IntegralQ t0))%Q
 by ring.
rewrite H0, H1.
reflexivity.
Qed.

Lemma Integral_opp:forall s,
  (-(IntegralQ s)==(IntegralQ (- s)))%Q.
Proof.
induction s using StepF_ind.
 reflexivity.
unfold StepQopp in *.
rewriteStepF.
rewrite <- IHs1.
rewrite <- IHs2.
ring.
Qed.

Lemma Integral_minus:forall s t,
  ((IntegralQ s)-(IntegralQ t)==(IntegralQ (s - t)))%Q.
Proof.
intros s t.
unfold Qminus.
rewrite Integral_opp, Integral_plus.
apply IntegralQ_wd.
ring.
Qed.

Lemma Integral_scale :forall q x, 
 (q*(IntegralQ x) == (IntegralQ (QscaleS q^@>x)))%Q.
Proof.
intros q x.
induction x using StepF_ind.
 reflexivity.
rewriteStepF.
rewrite <- IHx1.
rewrite <- IHx2.
ring.
Qed.

Lemma Abs_Integral : forall x,
 Qabs (IntegralQ x) <= IntegralQ (QabsS ^@> x).
Proof.
intros x.
induction x using StepF_ind.
 rapply Qle_refl.
rewriteStepF.
eapply Qle_trans.
apply Qabs_triangle.
do 2 rewrite Qabs_Qmult.
rewrite (Qabs_pos o); auto with *.
rewrite (Qabs_pos (1-o)); auto with *.
rsapply plus_resp_leEq_both;
 rsapply mult_resp_leEq_lft; auto with *.
Qed.

Lemma Abs_Integral_Norm : forall x,
 Qabs (IntegralQ x) <= L1Norm x.
Proof.
exact Abs_Integral.
Qed.

Definition StepQ_le x y := (StepFfoldProp (QleS ^@> x <@> y)).

Add Morphism StepQ_le 
  with signature StepF_eq ==> StepF_eq ==> iff
 as StepQ_le_wd.
unfold StepQ_le.
intros x1 x2 Hx y1 y2 Hy.
rewrite Hx.
rewrite Hy.
reflexivity.
Qed.

Notation "x <= y" := (StepQ_le x y) (at level 70) : sfstscope.

Lemma StepQ_le_refl:forall x, (x <= x).
intros x.
unfold StepQ_le.
cut (StepFfoldProp (join QleS ^@> x)).
 evalStepF.
 tauto.
apply StepFfoldPropForall_Map.
intros.
simpl.
auto with *.
Qed.

Lemma StepQ_le_trans:forall x y z, 
 (x <= y)-> (y <= z) ->(x <= z).
intros x y z. unfold StepQ_le.
intros H.
apply StepF_imp_imp.
revert H.
rapply StepF_imp_imp.
unfold StepF_imp.
pose (f:= ap
(compose (@ap _ _ _) (compose (compose (compose (@compose _ _ _) imp)) QleS))
(compose (flip (compose (@ap _ _ _) (compose (compose imp) QleS))) QleS)).
cut (StepFfoldProp (f ^@> x <@> y <@> z)).
 unfold f.
 evalStepF.
 tauto.
apply StepFfoldPropForall_Map3.
intros a b c Hab Hbc.
clear f.
simpl in *.
eauto with qarith.
Qed.

Lemma Integral_resp_nonneg :forall x, 
 (constStepF (0:QS)) <= x -> (0 <= (IntegralQ x))%Q.
Proof.
intros x.
unfold StepQ_le.
rewriteStepF.
induction x using StepF_ind.
 auto.
rewriteStepF.
intros [Hxl Hxr].
rsapply plus_resp_nonneg;
 rsapply mult_resp_nonneg; auto with *.
Qed.

Lemma L1Norm_glue : forall o s t, (L1Norm (glue o s t) == o*L1Norm s + (1-o)*L1Norm t)%Q.
Proof.
intros o s t.
unfold L1Norm.
rewrite <- Integral_glue.
reflexivity.
Qed.

Lemma L1Norm_nonneg : forall x, (0 <= (L1Norm x))%Q.
Proof.
intros x.
rapply Integral_resp_nonneg.
unfold StepQ_le.
rewriteStepF.
set (g:=QleS 0).
cut (StepFfoldProp ((compose g QabsS) ^@> x)).
 evalStepF.
 tauto.
apply StepFfoldPropForall_Map.
intros a.
rapply Qabs_nonneg.
Qed.

Lemma Integral_resp_le :forall x y, 
 x <= y -> (IntegralQ x <= IntegralQ y)%Q.
Proof.
intros x y H.
rewrite Qle_minus_iff.
rewrite Integral_opp, Integral_plus.
apply Integral_resp_nonneg.
revert H.
rapply StepF_imp_imp.
unfold StepF_imp.
rewriteStepF.
set (g:= QleS 0).
pose (f:=(ap
 (compose (@ap _ _ _) (compose (compose imp) QleS))
 (compose (compose g) (compose (flip QplusS) QoppS)))).
cut (StepFfoldProp (f ^@> x <@> y)).
 unfold f.
 evalStepF.
 tauto.
apply StepFfoldPropForall_Map2.
intros a b.
change (a <= b -> 0 <= b + (- a))%Q.
rewrite Qle_minus_iff.
tauto.
Qed.

Lemma L1Norm_Zero : forall s, 
 (L1Norm s <= 0)%Q -> s == (constStepF (0:QS)).
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
unfold L1Norm, StepQabs in *.
rewrite MapGlue in Hs.
rewrite Integral_glue in Hs.
apply glue_StepF_eq.
 apply IHs1.
 unfold L1Norm.
 setoid_replace 0 with (0/o) by (field; auto with *).
 apply Qle_shift_div_l; auto with *.
 rewrite Qmult_comm.
 apply Qle_trans with (-((1 - o) * IntegralQ (QabsS ^@> s2)))%Q.
  rewrite Qle_minus_iff.
  rewrite Qle_minus_iff in Hs.
  replace RHS with (0 +
      - (o * IntegralQ (QabsS ^@> s1) + (1 - o) * IntegralQ (QabsS ^@> s2)))%Q by ring.
  assumption.
 change 0 with (-0)%Q.
 apply Qopp_le_compat.
 rsapply mult_resp_nonneg; auto with *.
 rapply L1Norm_nonneg.
apply IHs2.
unfold L1Norm.
setoid_replace 0 with (0/(1-o)) by (field; auto with *).
apply Qle_shift_div_l; auto with *.
rewrite Qmult_comm.
apply Qle_trans with (-(o * IntegralQ (QabsS ^@> s1)))%Q.
 rewrite Qle_minus_iff.
 rewrite Qle_minus_iff in Hs.
 replace RHS with (0 +
     - (o * IntegralQ (QabsS ^@> s1) + (1 - o) * IntegralQ (QabsS ^@> s2)))%Q by ring.
 assumption.
change 0 with (-0)%Q.
apply Qopp_le_compat.
rsapply mult_resp_nonneg; auto with *.
rapply L1Norm_nonneg.
Qed.

Lemma L1Norm_scale : forall q s, 
 (L1Norm (QscaleS q ^@> s) == Qabs q * L1Norm s)%Q.
Proof.
intros q s.
unfold L1Norm.
rewrite Integral_scale.
apply IntegralQ_wd.
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

Lemma L1ball_refl : forall e x, (L1Ball e x x).
Proof.
intros e x.
unfold L1Ball, L1Distance.
setoid_replace (x-x) with (constStepF (0:QS)) using relation StepF_eq by ring.
change (0 <= e)%Q.
auto with *.
Qed.

Lemma StepQabsOpp : forall x, StepQabs (-x) == StepQabs (x).
Proof.
intros x.
unfold StepF_eq.
set (g:=(st_eqS QS)).
set (f:=(ap
(compose g (compose QabsS QoppS))
QabsS)).
cut (StepFfoldProp (f ^@> x)).
 unfold f.
 evalStepF.
 tauto.
apply StepFfoldPropForall_Map.
intros a.
rapply Qabs_opp.
Qed.

Lemma L1ball_sym : forall e x y, (L1Ball e x y) -> (L1Ball e y x).
Proof.
intros e x y.
unfold L1Ball, L1Distance.
unfold L1Norm.
setoid_replace (x-y) with (-(y-x)) using relation StepF_eq by ring.
rewrite StepQabsOpp.
auto.
Qed.

Lemma StepQabs_triangle : forall x y, StepQabs (x+y) <= StepQabs x + StepQabs y.
Proof.
intros x y.
set (f:=(ap
(compose ap (compose (compose (compose QleS QabsS)) QplusS))
(compose (flip (@compose _ _ _) QabsS) (compose QplusS QabsS)))).
cut (StepFfoldProp (f ^@> x <@> y)).
 unfold f.
 evalStepF.
 tauto.
apply StepFfoldPropForall_Map2.
intros a b.
rapply Qabs_triangle.
Qed.

Lemma L1ball_triangle : forall e d x y z, (L1Ball e x y) -> (L1Ball d y z) -> (L1Ball (e+d) x z).
Proof.
intros e d x y z.
unfold L1Ball, L1Distance.
unfold L1Norm.
setoid_replace (x-z) with ((x-y)+(y-z)) using relation StepF_eq by ring.
intros He Hd.
autorewrite with QposElim.
apply Qle_trans with (IntegralQ (StepQabs (x-y) + StepQabs (y-z)))%Q.
 apply Integral_resp_le.
 apply StepQabs_triangle.
rewrite <- Integral_plus.
rsapply plus_resp_leEq_both; assumption.
Qed.

Lemma L1ball_closed : forall e x y, (forall d, (L1Ball (e+d) x y)) -> (L1Ball e x y).
Proof.
unfold L1Ball. intros e a b H.
assert (forall x, (forall d : Qpos, x <= e+d) -> x <= e)%Q.
 intros. rsapply shift_zero_leEq_minus'.
 rsapply inv_cancel_leEq. rsapply approach_zero_weak.
 intros. replace LHS with (x[-](e:Q)). 
  rsapply shift_minus_leEq. replace RHS with (e+e0)%Q by ring. rewrite <- (QposAsmkQpos H1).
  apply (H0 (mkQpos H1)).
 unfold cg_minus; simpl; ring.
apply H0. exact H.
Qed.

Lemma L1ball_eq : forall x y, (forall e : Qpos, L1Ball e x y) -> StepF_eq x y.
Proof.
intros x y H.
unfold L1Ball in H.
setoid_replace y with (constStepF (0:QS)+y) using relation StepF_eq by ring.
set (z:=constStepF (0:QS)).
setoid_replace x with (x - y + y) using relation StepF_eq by ring.
apply StepQplus_wd; try reflexivity.
unfold z; clear z.
rapply L1Norm_Zero.
apply Qnot_lt_le.
intros H0.
assert (0<(1#2)*( L1Norm (QminusS ^@> x <@> y))).
 rsapply mult_resp_pos; auto with *.
apply (Qle_not_lt _ _ (H (mkQpos H1))).
autorewrite with QposElim.
rewrite Qlt_minus_iff.
unfold L1Distance.
unfold StepQminus.
ring_simplify.
assumption.
Qed.

Lemma L1_is_MetricSpace : 
 (is_MetricSpace (@StepF_eq QS) L1Ball).
split.
     apply (StepF_Sth QS).
    rapply L1ball_refl.
   rapply L1ball_sym.
  rapply L1ball_triangle.
 rapply L1ball_closed.
rapply L1ball_eq.
Qed.

Add Morphism L1Ball with signature QposEq ==> StepF_eq ==> StepF_eq ==> iff as L1Ball_wd.
intros x1 x2 Hx y1 y2 Hy z1 z2 Hz.
unfold L1Ball.
change (x1 == x2)%Q in Hx.
rewrite Hx.
rewrite Hy.
rewrite Hz.
reflexivity.
Qed.

Definition L1StepQ : MetricSpace :=
Build_MetricSpace L1Ball_wd L1_is_MetricSpace.

Canonical Structure L1StepQ.

Lemma L1StepQPrelengthSpace : PrelengthSpace L1StepQ.
Proof.
intros x y e d1 d2 He Hxy.
change (e < (d1+d2)%Qpos) in He.
set (d:=(d1+d2)%Qpos) in *.
simpl in *.
unfold L1Ball in *.
unfold L1Distance in *.
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
  rewrite L1Norm_scale.
  rewrite Qabs_pos; auto with *.
  autorewrite with QposElim.
  replace LHS with ((d1*L1Norm (x - y))/d) by
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
 rewrite L1Norm_scale.
 rewrite Qabs_pos; auto with *.
 autorewrite with QposElim.
 replace LHS with ((d2*L1Norm (x - y))/d) by
  (field; apply Qpos_nonzero).
 apply Qle_shift_div_r; auto with *.
 rsapply mult_resp_leEq_lft; auto with *.
 apply Qle_trans with e; auto with *.
setoid_replace (f- y) with (f - constStepF (1:QS)*y) using relation StepF_eq by ring.
rewrite <- X.
unfold f.
ring.
Qed.

Lemma integral_uc_prf : is_UniformlyContinuousFunction IntegralQ Qpos2QposInf.
Proof.
intros e x y.
simpl in *.
rewrite Qball_Qabs.
rewrite Integral_minus.
unfold L1Ball, L1Distance.
generalize (x - y).
clear x y.
intros x.
intros Hx.
eapply Qle_trans.
 apply Abs_Integral_Norm.
assumption.
Qed.

Open Local Scope uc_scope.

Definition IntegralQ_uc : L1StepQ --> Q_as_MetricSpace
:= Build_UniformlyContinuousFunction integral_uc_prf.
