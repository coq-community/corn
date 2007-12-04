Require Export StepFunctionSetoid.
Require Export Metric.
Require Import OpenUnit.
Require Import QArith.
Require Import QMinMax.
Require Import Qabs.
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
Definition Distance(f g:StepF QS):Q:=(L1Norm (QminusS ^@> f <@> g)).
Eval lazy beta zeta delta iota in (Distance test1 test2):Q.
Eval lazy beta zeta delta iota in (Distance test2 test1):Q.
Definition L1Ball (e:Qpos)(f g:StepF QS):Prop:=(Distance f g)<=e.
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
set (d:=Distance a b).
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
 as IntegralQ_mor.
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

Lemma Integral_linear:forall s t,
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

Require Import QMinMax.
Require Import COrdAbs.
Require Import Qordfield.
Require Import CornTac.
Require Import Qauto.

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
 forall X (f:StepF (X --> iffSetoid)) (x:StepF X), 
(forall y, StepFfoldProp (f <@> leaf y)) 
             -> StepFfoldProp (f <@> x).
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
 forall X (f:X --> iffSetoid) (x:StepF X), 
  (forall a, f a) -> StepFfoldProp (f ^@> x).
Proof.
intros X f x H.
apply StepFfoldPropForall_Ap.
assumption.
Qed.

Lemma StepFfoldPropForall_Map2 : 
 forall X Y (f:X --> Y --> iffSetoid) x y, 
 (forall a b, f a b) -> StepFfoldProp (f ^@> x <@> y).
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
 forall X Y Z (f:X --> Y --> Z --> iffSetoid) x y z, 
 (forall a b c, f a b c) -> StepFfoldProp (f ^@> x <@> y <@> z).
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

Lemma L1ball_refl : forall e x, (L1Ball e x x).
Proof.
intros e x.
unfold L1Ball, Distance.
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
unfold L1Ball, Distance.
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

Lemma L1ball_trans : forall e d x y z, (L1Ball e x y) -> (L1Ball d y z) -> (L1Ball (e+d) x z).
Proof.
intros e d x y z.
unfold L1Ball, Distance.
unfold L1Norm.
intros He Hd.
autorewrite with QposElim.
apply Qle_trans with (IntegralQ (QabsS ^@> (QminusS ^@> x <@> y)) + IntegralQ (QabsS ^@> (QminusS ^@> y <@> z)));
 [|rsapply plus_resp_leEq_both; assumption].
Admitted.

Lemma L1_is_MetricSpace : 
 (is_MetricSpace (@StepF_eq QS) L1Ball).
split.
     apply (StepF_Sth QS).
    rapply L1ball_refl.
   (*Symm*)
   unfold symmetric. apply L1ball_sym.
  (* Trans*)
   apply L1ball_trans.
(* 
 First show that 
    Show that StepF_lt is a reflexive, transitive relation
    Show that if f<=g, then (StepF_lt (Map2 f) (Map2 g))
    (StepF_lt (Map2 | + |) (Map2 |  |+|  |))
    Show that:
    (a-b)+(b-c)= (a-c) This needs that Map2 is a morphism.
*)
(* Closed, this is copied from Qmetric*)
unfold L1Ball. intros e a b H.
assert (forall x, (forall d : Qpos, x <= e+d) -> x <= e).
 intros. rsapply shift_zero_leEq_minus'.
 rsapply inv_cancel_leEq. rsapply approach_zero_weak.
 intros. replace LHS with (x[-](e:Q)). 
  rsapply shift_minus_leEq. replace RHS with (e+e0) by ring. rewrite <- (QposAsmkQpos H1).
  apply (H0 (mkQpos H1)).
 unfold cg_minus; simpl; ring.
apply H0. exact H.
(* Equality, form Qmetric*)
unfold L1Ball.
assert (forall q:Q, 0<=q -> (forall e:Qpos, q<=e)->q==0).
assert (forall a b, ((Distance a b==0) ->(StepF_eq a b))).
Admitted.

(*
Add Morphism L1Ball with signature QposEq ==> (StepF_eq Qeq) ==> (StepF_eq Qeq) ==> iff as Qball_wd.
intros [x1 Hx1] [x2 Hx2] H x3 x4 H0 x5 x6 H1.
unfold L1Ball.
rewrite H0.
rewrite H1.
unfold QposEq in H.
simpl in H.
rewrite H.
tauto.
Qed.


Definition L1_as_MetricSpace : MetricSpace :=
Build_MetricSpace L1ball_wd L1_is_MetricSpace.

Canonical Structure L1_as_MetricSpace.

 Do we need this?
Lemma QPrelengthSpace : PrelengthSpace Q_as_MetricSpace.
Proof.
assert (forall (e d1 d2:Qpos), e < d1+d2 -> forall (a b c:Q), ball e a b -> (c == (a*d2 + b*d1)/(d1+d2)%Qpos) -> ball d1 a c).
intros e d1 d2 He a b c Hab Hc.
simpl.
unfold Qball.
apply AbsSmall_wdr with ((d1/(d1+d2)%Qpos)*(a - b)).
apply AbsSmall_wdl with ((d1/(d1+d2)%Qpos)*(d1+d2)%Qpos);
 [|simpl; field; apply Qpos_nonzero].
rsapply mult_resp_AbsSmall.
rsapply less_leEq.
rsapply (div_resp_pos _  _ (d1:Q) (@Qpos_nonzero (d1+d2)%Qpos)); apply Qpos_prf.
destruct d1; destruct d2; rsapply (AbsSmall_trans _ (e:Q)); assumption.
simpl.
rewrite Hc.
pose (@Qpos_nonzero (d1 + d2)%Qpos).
QposField.
assumption.
intros a b e d1 d2 He Hab.
pose (c:= (a * d2 + b * d1) / (d1 + d2)%Qpos).
exists c.
apply (H e d1 d2 He a b c); try assumption.
reflexivity.
apply ball_sym.
eapply H.
rewrite Qplus_comm.
apply He.
apply ball_sym.
apply Hab.
unfold c.
unfold Qdiv.
apply Qmult_comp.
ring.
apply Qinv_comp.
QposRing.
Qed.
*)

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
