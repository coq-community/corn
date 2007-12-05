Require Export StepFunctionSetoid.
Require Export Metric.
Require Import OpenUnit.
Require Import QArith.
Require Import QMinMax.
Require Import Qabs.
Require Import Qordfield.
Require Import Qmetric.
Require Import COrdFields2.
Require Import CornTac.

Set Implicit Arguments.

Open Local Scope sfscope.

Ltac arw := autorewrite with StepF_rew.

Add Morphism StepFfoldProp
  with signature StepF_eq ==>  iff
 as StepFfoldProp_mor.
exact StepFfoldProp_morphism.
Qed.

Lemma QS:(Setoid).
exists Q Qeq.
split; eauto with qarith.
Defined.

Definition test1:=(leaf (1:QS)).
Definition test2:=(glue (ou 1/2) (leaf (0:QS)) (leaf (1:QS))).

Open Local Scope sfstscope.

Definition Supnorm:(StepF QS)->Q:=(StepFfold (Qabs:QS->QS) (fun _=> Qmax)).
Eval compute in (Supnorm test2):Q.
Definition IntegralQ:(StepF QS)->Q:=(StepFfold (fun x => x) (fun b (x y:QS) => (b*x+(1-b)*y:QS))).
Eval compute in (IntegralQ test2):Q.
Definition QabsS : QS-->QS.
exists Qabs.
abstract(
simpl; intros x1 x2 Hx;
rewrite Hx;
reflexivity).
Defined.
Definition L1Norm(f:StepF QS):Q:=(IntegralQ (QabsS ^@> f)).
Eval compute in (L1Norm test2):Q.
Definition Qminus0 : QS -> QS --> QS.
intros q.
exists (Qminus q).
abstract (
simpl; intros x1 x2 Hx;
rewrite Hx;
reflexivity).
Defined.
Definition QminusS : QS --> QS --> QS.
exists (Qminus0).
abstract (
intros x1 x2 Hx y; simpl in *;
rewrite Hx;
reflexivity).
Defined.
Definition QscaleS : QS -> QS --> QS.
intros q.
exists (Qmult q).
abstract (
intros x1 x2 Hx; simpl in *;
rewrite Hx;
reflexivity).
Defined.
Definition L1Distance(f g:StepF QS):Q:=(L1Norm (QminusS ^@> f <@> g)).
Eval lazy beta zeta delta iota in (L1Distance test1 test2):Q.
Eval lazy beta zeta delta iota in (L1Distance test2 test1):Q.
Definition L1Ball (e:Qpos)(f g:StepF QS):Prop:=(L1Distance f g)<=e.
Eval lazy beta zeta delta iota in (L1Ball (1#1)%Qpos test2 test1).
Definition Mesh (X:Setoid):(StepF X)->Q:=(StepFfold (fun x => 1)(fun b x y => (Qmax (b*x) ((1-b)*y)))).
Eval compute in (Mesh test2).

Section Equivalence1.
Variable X Y:Setoid.

End Equivalence1.

Section L1metric.

Definition StepQ := (StepF QS).

Lemma Qball_dec : forall e a b, {L1Ball e a b}+{~L1Ball e a b}.
intros e a b.
unfold L1Ball.
set (d:=L1Distance a b).
destruct (Qlt_le_dec_fast e d) as [Hdc|Hdc].
right. abstract auto with *.
left. exact Hdc.
Defined.
Require Import QArith_base.

Lemma IntegralSplit : forall (o:OpenUnit) x, 
 IntegralQ x ==
 o * IntegralQ (SplitL x o) + (1 - o) * IntegralQ (SplitR x o).
Proof.
intros o x.
revert o.
induction x using StepF_ind.
unfold IntegralQ. simpl. intros. simpl in x; ring.
intros p.
apply SplitLR_glue_ind; intros H.
  simpl.   (*This should be improved*) unfold IntegralQ; simpl; fold IntegralQ.
  rewrite (IHx1 (OpenUnitDiv p o H)).
  unfold IntegralQ; simpl; fold IntegralQ. field; auto with *. (*why does this not work*)
 simpl. unfold IntegralQ; simpl; fold IntegralQ. 
 rewrite (IHx2 (OpenUnitDualDiv p o H)).
 unfold IntegralQ; simpl; fold IntegralQ. field; auto with *.
rewrite H.
reflexivity.
Qed.

Hint Resolve IntegralSplit.

Add Morphism IntegralQ 
  with signature  StepF_eq ==>  Qeq
 as IntegralQ_wd.
unfold IntegralQ.
induction x1 using StepF_ind.
intros x2 H. simpl. induction x2 using StepF_ind.
  simpl.  auto with *.
 simpl.
 destruct H as [H0 H1] using (eq_glue_ind x2_1).
 rewrite <- IHx2_1; auto with *.
 rewrite <- IHx2_2; auto with *.
 simpl in x; ring.
intros x2 H.
destruct H as [H0 H1] using (glue_eq_ind x1_1).
simpl.
rewrite (IHx1_1 _ H0).
rewrite (IHx1_2 _ H1).
auto with *.
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

Lemma Integral_glue : forall o s t, IntegralQ (glue o s t) = o*(IntegralQ s) + (1-o)*(IntegralQ t).
Proof.
reflexivity.
Qed.

Hint Rewrite Integral_glue: StepF_rew.

Definition Qplus0 : QS -> QS --> QS.
intros q.
exists (Qplus q).
abstract (
simpl; intros x1 x2 Hx;
rewrite Hx;
reflexivity).
Defined.

Definition QplusS : QS --> QS --> QS.
exists (Qplus0).
abstract (
intros x1 x2 Hx y; simpl in *;
rewrite Hx;
reflexivity).
Defined.

Lemma Integral_plus:forall s t,
  (IntegralQ s)+(IntegralQ t)==(IntegralQ ((QplusS:QS-->QS-->QS) ^@> s <@> t)).
Proof.
induction s using StepF_ind.
 induction t using StepF_ind.
  reflexivity.
 arw.
 rewrite <- IHt1.
 rewrite <- IHt2.
 ring.
intros t.
arw.
rewrite <- IHs1.
rewrite <- IHs2.
rewrite (IntegralSplit o t).
ring.
Qed.

Definition QoppS : QS --> QS.
exists (Qopp).
abstract (
simpl; intros x1 x2 Hx; simpl in *;
rewrite Hx;
reflexivity).
Defined.

Lemma Integral_opp:forall s,
  -(IntegralQ s)==(IntegralQ (QoppS^@> s)).
Proof.
induction s using StepF_ind.
 reflexivity.
arw.
rewrite <- IHs1.
rewrite <- IHs2.
ring.
Qed.

Lemma Integral_scale :forall q x, 
 (q*(IntegralQ x) == (IntegralQ (QscaleS q^@>x))).
Proof.
intros q x.
induction x using StepF_ind.
 reflexivity.
arw.
rewrite <- IHx1.
rewrite <- IHx2.
ring.
Qed.

Definition Qle0 : QS -> QS --> iffSetoid.
intros q.
exists (Qle q).
abstract (
simpl; intros x1 x2 Hx;
rewrite Hx;
reflexivity).
Defined.

Definition QleS : QS --> QS --> iffSetoid.
exists (Qle0).
abstract (
intros x1 x2 Hx y; simpl in *;
rewrite Hx;
reflexivity).
Defined.

Definition Qge0 : QS -> QS --> iffSetoid.
intros q.
exists (Qge q).
abstract (
simpl; intros x1 x2 Hx;
rewrite Hx;
reflexivity).
Defined.

Definition QgeS : QS --> QS --> iffSetoid.
exists (Qge0).
abstract (
intros x1 x2 Hx y; simpl in *;
rewrite Hx;
reflexivity).
Defined.

Definition StepF_le x y := (StepFfoldProp (QleS ^@> x <@> y)).

Lemma StepFfoldPropForall_Ap : 
 forall X (f:StepF (X --> iffSetoid)) (x:StepF X), (forall y, StepFfoldProp (f <@> leaf y)) -> StepFfoldProp (f <@> x).
Proof.
intros X f x H.
revert f H.
induction x using StepF_ind.
 intros f H.
 rapply H.
intros f H.
rewrite <- (glueSplit f o).
rewrite ApGlueGlue.
split.
 apply IHx1.
 intros y.
 assert (H0:=H y).
 rewrite <- (glueSplit f o) in H0.
 rewrite ApGlue in H0.
 destruct H0 as [H0 _].
 assumption.
apply IHx2.
intros y.
assert (H0:=H y).
rewrite <- (glueSplit f o) in H0.
rewrite ApGlue in H0.
destruct H0 as [_ H0].
assumption.
Qed.

Lemma StepFfoldPropForall_Map : 
 forall X (f:X --> iffSetoid) (x:StepF X), (forall a, f a) -> StepFfoldProp (f ^@> x).
Proof.
intros X f x H.
apply StepFfoldPropForall_Ap.
assumption.
Qed.

Lemma StepFfoldPropForall_Map2 : 
 forall X Y (f:X --> Y --> iffSetoid) x y, (forall a b, f a b) -> StepFfoldProp (f ^@> x <@> y).
Proof.
intros X Y f x y H.
apply StepFfoldPropForall_Ap.
intros b.
rewrite <- (Map_commutative (leaf f) (leaf b)).
arw.
rapply StepFfoldPropForall_Map.
intros a.
rapply H.
Qed.

Lemma StepFfoldPropForall_Map3 : 
 forall X Y Z (f:X --> Y --> Z --> iffSetoid) x y z, (forall a b c, f a b c) -> StepFfoldProp (f ^@> x <@> y <@> z).
Proof.
intros X Y Z f x y z H.
apply StepFfoldPropForall_Ap.
intros c.
rewrite <- (Map_commutative ((leaf f) <@> x) (leaf c)).
rewrite <- Map_composition.
arw.
rewrite <- (Map_commutative (leaf (compose flip f)) (leaf c)).
arw.
rapply StepFfoldPropForall_Map2.
intros a b.
rapply H.
Qed.

Lemma StepF_le_refl:forall x, (StepF_le x x).
intros x.
unfold StepF_le.
cut (StepFfoldProp (join QleS ^@> x)).
 evalStepF.
 tauto.
apply StepFfoldPropForall_Map.
intros.
simpl.
auto with *.
Qed.

Lemma StepFfoldPropglue_rew:(forall o x y, (StepFfoldProp (glue o x y))<->((StepFfoldProp x)/\StepFfoldProp y)).
auto with *.
Qed.

Hint Rewrite StepFfoldPropglue_rew:StepF_rew.

Definition imp0:Prop->iffSetoid-->iffSetoid.
intro A.
exists (fun B:Prop=>(A->B)).
abstract (simpl; intuition).
Defined.

Definition imp:iffSetoid-->iffSetoid-->iffSetoid.
exists imp0.
abstract (simpl; unfold extEq; simpl; intuition).
Defined.

Definition StepF_imp (f g:StepF iffSetoid):Prop:=
(StepFfoldProp (imp ^@> f <@> g)).

Lemma StepF_imp_imp:forall x y:(StepF iffSetoid),
  (StepF_imp x y) ->
  ((StepFfoldProp x)->(StepFfoldProp y)).
induction x using StepF_ind. induction y  using StepF_ind.
   auto with *.
  unfold StepF_imp. unfold StepFfoldProp;simpl;intuition.
intros y.
unfold StepF_imp, Map2. arw.
intros.
rewrite <- (StepFfoldPropglue y o). arw. intuition. 
Qed.

Lemma StepF_le_trans:forall x y z, 
 (StepF_le x y)-> (StepF_le y z) ->(StepF_le x z).
intros x y z. unfold StepF_le.
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
 (StepF_le (leaf (0:QS)) x)-> 0 <= (IntegralQ x).
Proof.
intros x.
unfold StepF_le.
arw.
induction x using StepF_ind.
 auto.
arw.
intros [Hxl Hxr].
rsapply plus_resp_nonneg;
 rsapply mult_resp_nonneg; auto with *.
Qed.

Lemma L1Norm_nonneg : forall x, 0 <= (L1Norm x).
Proof.
intros x.
rapply Integral_resp_nonneg.
unfold StepF_le.
arw.
set (g:=QleS 0).
cut (StepFfoldProp ((compose g QabsS) ^@> x)).
 evalStepF.
 tauto.
apply StepFfoldPropForall_Map.
intros a.
rapply Qabs_nonneg.
Qed.

Lemma Integral_resp_le :forall x y, 
 (StepF_le x y)-> (IntegralQ x) <= (IntegralQ y).
Proof.
intros x y H.
rewrite Qle_minus_iff.
rewrite Integral_opp, Integral_plus.
apply Integral_resp_nonneg.
revert H.
rapply StepF_imp_imp.
unfold StepF_imp.
arw.
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
change (a <= b -> 0 <= b + (- a)).
rewrite Qle_minus_iff.
tauto.
Qed.

Lemma L1Norm_Zero : forall s, 
 L1Norm s <= 0 -> StepF_eq s (leaf (0:QS)).
Proof.
intros s.
intros Hs.
induction s using StepF_ind.
 rapply Qle_antisym.
  eapply Qle_trans;[apply Qle_Qabs|assumption].
 rewrite <- (Qopp_involutive x).
 change 0 with (- (- 0)).
 apply Qopp_le_compat.
 eapply Qle_trans;[apply Qle_Qabs|].
 rewrite Qabs_opp.
 assumption.
unfold L1Norm in Hs.
rewrite MapGlue in Hs.
rewrite Integral_glue in Hs.
apply glue_StepF_eq.
 apply IHs1.
 unfold L1Norm.
 setoid_replace 0 with (0/o) by (field; auto with *).
 apply Qle_shift_div_l; auto with *.
 rewrite Qmult_comm.
 apply Qle_trans with (-((1 - o) * IntegralQ (QabsS ^@> s2))).
  rewrite Qle_minus_iff.
  rewrite Qle_minus_iff in Hs.
  replace RHS with (0 +
      - (o * IntegralQ (QabsS ^@> s1) + (1 - o) * IntegralQ (QabsS ^@> s2))) by ring.
  assumption.
 change 0 with (-0).
 apply Qopp_le_compat.
 rsapply mult_resp_nonneg; auto with *.
 rapply L1Norm_nonneg.
apply IHs2.
unfold L1Norm.
setoid_replace 0 with (0/(1-o)) by (field; auto with *).
apply Qle_shift_div_l; auto with *.
rewrite Qmult_comm.
apply Qle_trans with (-(o * IntegralQ (QabsS ^@> s1))).
 rewrite Qle_minus_iff.
 rewrite Qle_minus_iff in Hs.
 replace RHS with (0 +
     - (o * IntegralQ (QabsS ^@> s1) + (1 - o) * IntegralQ (QabsS ^@> s2))) by ring.
 assumption.
change 0 with (-0).
apply Qopp_le_compat.
rsapply mult_resp_nonneg; auto with *.
rapply L1Norm_nonneg.
Qed.

Lemma L1Norm_scale : forall q s, 
 L1Norm (QscaleS q ^@> s) == Qabs q * L1Norm s.
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
unfold L1Norm.
setoid_replace (QabsS ^@> (QminusS ^@> x <@> x)) with (leaf (0:QS)) using relation StepF_eq.
 unfold IntegralQ.
 simpl.
 auto with *.
symmetry.
unfold StepF_eq.
arw.
set (g:=(st_eqS QS 0)).
set (f:=(compose g (compose QabsS (join QminusS)))).
cut (StepFfoldProp (f ^@> x)).
 unfold f.
 evalStepF.
 tauto.
apply StepFfoldPropForall_Map.
intros a.
change (0 == Qabs (a - a)).
setoid_replace (a - a) with 0 using relation Qeq by ring.
reflexivity.
Qed.

Lemma L1ball_sym : forall e x y, (L1Ball e x y) -> (L1Ball e y x).
Proof.
intros e x y.
unfold L1Ball, L1Distance.
unfold L1Norm.
setoid_replace (QabsS ^@> (QminusS ^@> x <@> y)) with (QabsS ^@> (QminusS ^@> y <@> x)) using relation StepF_eq.
 tauto.
unfold StepF_eq.
set (g:=(st_eqS QS)).
set (f:=(ap
(compose ap (compose (compose (compose g QabsS)) QminusS))
(compose (compose QabsS) (flip QminusS)))).
cut (StepFfoldProp (f ^@> x <@> y)).
 unfold f.
 evalStepF.
 tauto.
apply StepFfoldPropForall_Map2.
intros a b.
change (Qabs (a - b) == Qabs (b - a)).
rewrite <- Qabs_opp.
apply Qabs_wd.
ring.
Qed.

Lemma L1ball_triangle : forall e d x y z, (L1Ball e x y) -> (L1Ball d y z) -> (L1Ball (e+d) x z).
Proof.
intros e d x y z.
unfold L1Ball, L1Distance.
unfold L1Norm.
intros He Hd.
autorewrite with QposElim.
apply Qle_trans with (IntegralQ (QabsS ^@> (QminusS ^@> x <@> y)) + IntegralQ (QabsS ^@> (QminusS ^@> y <@> z)));
 [|rsapply plus_resp_leEq_both; assumption].
rewrite Integral_plus.
apply Integral_resp_le.
unfold StepF_le.
set (f:=ap
 (compose (@compose _ _ _) (compose ap (compose (compose (compose QleS QabsS)) QminusS)))
 (compose (flip ap (compose (compose QabsS) QminusS)) (compose (compose (compose (@compose _ _ _) (compose QplusS QabsS))) QminusS))).
cut (StepFfoldProp (f ^@> x <@> y <@> z)).
 unfold f.
 evalStepF.
 tauto.
apply StepFfoldPropForall_Map3.
intros a b c.
change (Qabs (a - c) <= Qabs (a - b) + Qabs (b - c)).
eapply Qle_trans;[|apply Qabs_triangle].
setoid_replace (a - b + (b - c)) with (a - c) by ring.
auto with *.
Qed.

Lemma L1ball_closed : forall e x y, (forall d, (L1Ball (e+d) x y)) -> (L1Ball e x y).
Proof.
unfold L1Ball. intros e a b H.
assert (forall x, (forall d : Qpos, x <= e+d) -> x <= e).
 intros. rsapply shift_zero_leEq_minus'.
 rsapply inv_cancel_leEq. rsapply approach_zero_weak.
 intros. replace LHS with (x[-](e:Q)). 
  rsapply shift_minus_leEq. replace RHS with (e+e0) by ring. rewrite <- (QposAsmkQpos H1).
  apply (H0 (mkQpos H1)).
 unfold cg_minus; simpl; ring.
apply H0. exact H.
Qed. 

Lemma L1ball_eq : forall x y, (forall e : Qpos, L1Ball e x y) -> StepF_eq x y.
Proof.
intros x y H.
unfold L1Ball in H.
cut (StepF_eq (leaf (0:QS)) (QminusS ^@>x <@> y)).
 rapply StepF_imp_imp.
 unfold StepF_imp.
 arw.
 set (g:=(st_eqS QS)).
 set (g0:= (g 0)).
 pose (f:=ap
  (compose (@ap _ _ _) (compose (compose (compose imp g0)) QminusS))
  g).
 cut (StepFfoldProp (f ^@> x <@> y)).
  unfold f.
  evalStepF.
  tauto.
 apply StepFfoldPropForall_Map2.
 intros a b.
 change (0 == a - b -> a == b).
 intros Hab.
 simpl in a, b.
 replace LHS with ((a - b) + b) by ring.
 rewrite <- Hab.
 ring.
symmetry.
rapply L1Norm_Zero.
apply Qnot_lt_le.
intros H0.
assert (0<(1#2)*( L1Norm (QminusS ^@> x <@> y))).
 rsapply mult_resp_pos; auto with *.
apply (Qle_not_lt _ _ (H (mkQpos H1))).
autorewrite with QposElim.
rewrite Qlt_minus_iff.
unfold L1Distance.
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
change (x1 == x2) in Hx.
rewrite Hx.
rewrite Hy.
rewrite Hz.
reflexivity.
Qed.

Definition L1_as_MetricSpace : MetricSpace :=
Build_MetricSpace L1Ball_wd L1_is_MetricSpace.

Canonical Structure L1_as_MetricSpace.

Lemma L1PrelengthSpace : PrelengthSpace L1_as_MetricSpace.
Proof.
intros x y e d1 d2 He Hxy.
change (e < (d1+d2)%Qpos) in He.
set (d:=(d1+d2)%Qpos) in *.
simpl in *.
unfold L1Ball in *.
unfold L1Distance in *.
pose (f0:=(fun a b => (a*d2 + b*d1)/d)).
simpl in *.
assert (f1_p:forall a x1 x2 : QS, st_eq QS x1 x2 -> st_eq QS (f0 a x1) (f0 a x2)).
 simpl.
 intros a x1 x2 Hx.
 unfold f0.
 rewrite Hx.
 reflexivity.
pose (f1:=(fun a => Build_Morphism _ _ _ (f1_p a))).
assert (f_p:forall x1 x2 : QS, st_eq QS x1 x2 -> st_eq (QS --> QS) (f1 x1) (f1 x2)).
 unfold f1, f0.
 simpl.
 intros x1 x2 Hx z.
 simpl.
 rewrite Hx.
 reflexivity.
pose (f:=Build_Morphism _ _ _ f_p: QS --> QS --> QS).
exists (f^@> x <@> y).
 setoid_replace (QminusS ^@> x <@> (f ^@> x <@> y))
  with (QscaleS ((d1/d)%Qpos) ^@> (QminusS ^@> x <@> y)) using relation StepF_eq.
  rewrite L1Norm_scale.
  rewrite Qabs_pos; auto with *.
  autorewrite with QposElim.
  replace LHS with ((d1*L1Norm (QminusS ^@> x <@> y))/d) by
   (field; apply Qpos_nonzero).
  apply Qle_shift_div_r; auto with *.
  rsapply mult_resp_leEq_lft; auto with *.
  apply Qle_trans with e; auto with *.
 unfold StepF_eq.
 set (g:= st_eqS QS).
 set (q:= QscaleS (d1/d)%Qpos).
 set (z:= ap
  (compose (@ap _ _ _) (compose (compose g) ((compose (compose (@ap _ _ _)) (@compose _ _ _)) (@compose _ _ _) QminusS f)))
  (compose (compose q) QminusS)).
 cut (StepFfoldProp (z ^@> x <@> y)).
  unfold z.
  evalStepF.
  tauto.
 apply StepFfoldPropForall_Map2.
 intros a b.
 change (a - (a * d2 + b * d1) / (d1+d2) == (d1 / (d1 + d2)) * (a - b)).
 field.
 change (~d==0).
 rapply Qpos_nonzero.
setoid_replace (QminusS ^@> (f ^@> x <@> y) <@> y)
  with (QscaleS ((d2/d)%Qpos) ^@> (QminusS ^@> x <@> y)) using relation StepF_eq.
 rewrite L1Norm_scale.
 rewrite Qabs_pos; auto with *.
 autorewrite with QposElim.
 replace LHS with ((d2*L1Norm (QminusS ^@> x <@> y))/d) by
  (field; apply Qpos_nonzero).
 apply Qle_shift_div_r; auto with *.
 rsapply mult_resp_leEq_lft; auto with *.
 apply Qle_trans with e; auto with *.
unfold StepF_eq.
set (g:= st_eqS QS).
set (q:= QscaleS (d2/d)%Qpos).
set (z:= ap
  (compose (@ap _ _ _) (compose (compose g) (compose (@join _ _) (compose (compose QminusS) f))))
  (compose (compose q) QminusS)).
cut (StepFfoldProp (z ^@> x <@> y)).
 unfold z.
 evalStepF.
 tauto.
apply StepFfoldPropForall_Map2.
intros a b.
change ((a * d2 + b * d1) / (d1+d2) - b == (d2 / (d1 + d2)) * (a - b)).
field.
change (~d==0).
rapply Qpos_nonzero.
Qed.

(* TODO:
Is a metric space
Continuity of integration
Continuity of Map, Map2
Continuous functions are in the completion, i.e. there is an injection 
from continuous functions to integrable ones.
Integration is correct. Needs mesh. 

Write a tactic Done (auto with *, etc)
Find out how simple works with fold.
*)