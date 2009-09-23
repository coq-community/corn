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
Require Import ZBasics.
Require Import Classic.
Require Export Metric.
Require Import Classification.
Require Import List.
Require Import ZArith.
Require Import QMinMax.
Require Import QposMinMax.
Require Import Qauto.
Require Import CornTac.

Open Local Scope Q_scope.

Section HausdorffMetric.

(**
* Hausdorff Metric
This module defines a Hausdorff metric for an arbitrary predicate over
a metric space X.
*)

Variable X : MetricSpace.

(** This is the (weak) hemiMetric, which makes an asymmetric metric.
We make use of the classical quantifer in this definition.
*)
Definition hemiMetric (e:Qpos) (A B: X -> Prop) :=
 forall x:X, A x ->
 existsC X (fun y => B y /\ ball e x y).

(** This (weak) metric, makes the full symmetric metric. *)
Definition hausdorffBall (e:Qpos) (A B: X -> Prop) :=
 hemiMetric e A B /\ hemiMetric e B A.

Lemma hemiMetric_wd1 : forall (e0 e1:Qpos) A B,
 (QposEq e0 e1) -> hemiMetric e0 A B -> hemiMetric e1 A B.
Proof.
 intros e0 e1 A B He H x Hx.
 destruct (H x Hx) as [HG | y [Hy Hxy]] using existsC_ind.
  apply existsC_stable; assumption.
 apply existsWeaken.
 exists y.
 rewrite -> He in Hxy; auto.
Qed.

Lemma hausdorffBall_wd1 : forall (e0 e1:Qpos) A B,
 (QposEq e0 e1) -> hausdorffBall e0 A B -> hausdorffBall e1 A B.
Proof.
 intros e0 e1 A B He [H0 H1].
 split; apply hemiMetric_wd1 with e0; assumption.
Qed.

Lemma hemiMetric_refl : forall e A, hemiMetric e A A.
Proof.
 intros e A x Hx.
 apply existsWeaken.
 exists x.
 split; try assumption.
 apply ball_refl.
Qed.

Lemma hausdorffBall_refl : forall e A, hausdorffBall e A A.
Proof.
 intros e A.
 split; apply hemiMetric_refl.
Qed.

Lemma hausdorffBall_sym : forall e A B,
 hausdorffBall e A B -> hausdorffBall e B A.
Proof.
 intros e A B [H0 H1].
 split; assumption.
Qed.

Lemma hemiMetric_triangle : forall e0 e1 A B C,
 hemiMetric e0 A B -> hemiMetric e1 B C -> hemiMetric (e0 + e1) A C.
Proof.
 intros e0 e1 A B C H0 H1 x Hx.
 destruct (H0 x Hx) as [HG | y [Hy Hxy]] using existsC_ind.
  apply existsC_stable; assumption.
 destruct (H1 y Hy) as [HG | z [Hz Hyz]] using existsC_ind.
  apply existsC_stable; assumption.
 apply existsWeaken.
 exists z.
 split; try assumption.
 apply ball_triangle with y; assumption.
Qed.

Lemma hausdorffBall_triangle : forall e0 e1 A B C,
 hausdorffBall e0 A B -> hausdorffBall e1 B C -> hausdorffBall (e0 + e1) A C.
Proof.
 intros e0 e1 A B C [H0A H0B] [H1A H1B].
 split.
  apply hemiMetric_triangle with B; assumption.
 apply hemiMetric_wd1 with (e1 + e0)%Qpos.
  QposRing.
 apply hemiMetric_triangle with B; assumption.
Qed.

(** Unfortunately this isn't a metric for an aribitrary predicate.  More
assumptions are needed to show our definition of ball is closed.  See
FinEnum for an example of an instance of the Hausdorff metric. *)

Hypothesis stableX : stableMetric X.

Lemma hemiMetric_stable :forall e A B, ~~(hemiMetric e A B) -> hemiMetric e A B.
Proof.
 unfold hemiMetric.
 auto 7 using existsC_stable.
Qed.

Lemma hausdorffBall_stable :forall e A B, ~~(hausdorffBall e A B) -> hausdorffBall e A B.
Proof.
 unfold hausdorffBall.
 firstorder using hemiMetric_stable.
Qed.

Lemma hemiMetric_wd :forall (e1 e2:Qpos), (e1==e2) ->
 forall A1 A2, (forall x, A1 x <-> A2 x) ->
 forall B1 B2, (forall x, B1 x <-> B2 x) ->
 (hemiMetric e1 A1 B1 <-> hemiMetric e2 A2 B2).
Proof.
 cut (forall e1 e2 : Qpos, e1 == e2 -> forall A1 A2 : X -> Prop, (forall x : X, A1 x <-> A2 x) ->
   forall B1 B2 : X -> Prop, (forall x : X, B1 x <-> B2 x) ->
     (hemiMetric e1 A1 B1 -> hemiMetric e2 A2 B2)).
  intros; split.
   eauto.
  symmetry in H0.
  assert (H1':forall x : X, A2 x <-> A1 x) by firstorder.
  assert (H2':forall x : X, B2 x <-> B1 x) by firstorder.
  eauto.
 intros e1 e2 He A1 A2 HA B1 B2 HB H x Hx.
 rewrite <- HA in Hx.
 destruct (H x Hx) as [HG | y [Hy0 Hy1]] using existsC_ind.
  auto using existsC_stable.
 apply existsWeaken.
 exists y.
 change (QposEq e1 e2) in He.
 rewrite <- HB.
 rewrite <- He.
 auto.
Qed.

Lemma hausdorffBall_wd :forall (e1 e2:Qpos), (e1==e2) ->
 forall A1 A2, (forall x, A1 x <-> A2 x) ->
 forall B1 B2, (forall x, B1 x <-> B2 x) ->
 (hausdorffBall e1 A1 B1 <-> hausdorffBall e2 A2 B2).
Proof.
 intros.
 unfold hausdorffBall.
 setoid_replace (hemiMetric e1 A1 B1) with (hemiMetric e2 A2 B2).
  setoid_replace (hemiMetric e1 B1 A1) with (hemiMetric e2 B2 A2).
   reflexivity.
  apply hemiMetric_wd; auto.
 apply hemiMetric_wd; auto.
Qed.

End HausdorffMetric.

Section HausdorffMetricStrong.

Variable X : MetricSpace.
(**
** Strong Hausdorff Metric
This section introduces an alternative stronger notition of Haudorff metric
that uses a constructive existential.
*)

Definition hemiMetricStrong (e:Qpos) (A B: X -> Prop) :=
 forall x:X, A x ->
 forall d:Qpos, {y:X | B y /\ ball (e+d) x y}.

Definition hausdorffBallStrong (e:Qpos) (A B: X -> Prop) :=
 (hemiMetricStrong e A B * hemiMetricStrong e B A)%type.

Lemma hemiMetricStrong_wd1 : forall (e0 e1:Qpos) A B,
 (QposEq e0 e1) -> hemiMetricStrong e0 A B -> hemiMetricStrong e1 A B.
Proof.
 intros e0 e1 A B He H x Hx d.
 destruct (H x Hx d) as [y [Hy Hxy]].
 exists y.
 rewrite -> He in Hxy; auto.
Qed.

Lemma hausdorffBallStrong_wd1 : forall (e0 e1:Qpos) A B,
 (QposEq e0 e1) -> hausdorffBallStrong e0 A B -> hausdorffBallStrong e1 A B.
Proof.
 intros e0 e1 A B He [H0 H1].
 split; apply hemiMetricStrong_wd1 with e0; assumption.
Qed.

Lemma hemiMetricStrong_refl : forall e A, hemiMetricStrong e A A.
Proof.
 intros e A x Hx d.
 exists x.
 split; try assumption.
 apply ball_refl.
Qed.

Lemma hausdorffBallStrong_refl : forall e A, hausdorffBallStrong e A A.
Proof.
 intros e A.
 split; apply hemiMetricStrong_refl.
Qed.

Lemma hausdorffBallStrong_sym : forall e A B,
 hausdorffBallStrong e A B -> hausdorffBallStrong e B A.
Proof.
 intros e A B [H0 H1].
 split; assumption.
Qed.

Lemma hemiMetricStrong_triangle : forall e0 e1 A B C,
 hemiMetricStrong e0 A B -> hemiMetricStrong e1 B C -> hemiMetricStrong (e0 + e1) A C.
Proof.
 intros e0 e1 A B C H0 H1 x Hx d.
 destruct (H0 x Hx ((1#2)*d)%Qpos) as [y [Hy Hxy]].
 destruct (H1 y Hy ((1#2)*d)%Qpos) as [z [Hz Hyz]].
 exists z.
 split; try assumption.
 setoid_replace (e0 + e1 + d)%Qpos with ((e0 + (1 # 2) * d) +(e1 + (1 # 2) * d))%Qpos by QposRing.
 apply ball_triangle with y; assumption.
Qed.

Lemma hausdorffBallStrong_triangle : forall e0 e1 A B C,
 hausdorffBallStrong e0 A B -> hausdorffBallStrong e1 B C -> hausdorffBallStrong (e0 + e1) A C.
Proof.
 intros e0 e1 A B C [H0A H0B] [H1A H1B].
 split.
  apply hemiMetricStrong_triangle with B; assumption.
 apply hemiMetricStrong_wd1 with (e1 + e0)%Qpos.
  QposRing.
 apply hemiMetricStrong_triangle with B; assumption.
Qed.

(*
Lemma hemiMetricStrong_closed : forall e A B,
 FinitelyEnumerable X B ->
 (forall d, hemiMetricStrong (e+d) A B) ->
 hemiMetricStrong e A B.
Proof.
intros e A B HB H x Hx d.
destruct (H ((1#2)*d)%Qpos x Hx ((1#2)*d)%Qpos) as [y [Hy Hxy]].
exists y.
split; try assumption.
setoid_replace (e + d)%Qpos with (e + (1 # 2) * d + (1 # 2) * d)%Qpos by QposRing.
assumption.
Qed.

Lemma hausdorffBallStrong_closed : forall e A B,
 FinitelyEnumerable X A -> FinitelyEnumerable X B ->
 (forall d, hausdorffBallStrong (e+d) A B) ->
 hausdorffBallStrong e A B.
Proof.
intros e A B HA HB H.
split;
 apply hemiMetricStrong_closed;
 try assumption;
 intros d;
 destruct (H d);
 assumption.
Qed.
*)
(*
Lemma HemiMetricStrongHemiMetric : stableMetric X ->
 forall (e:Qpos) A B,
 SubFinite X B ->
 hemiMetricStrong e A B -> hemiMetric X e A B.
Proof.
intros HX e A B HB H.
apply hemiMetric_closed; try assumption.
unfold hemiMetric.
intros d x Hx.
apply existsWeaken.
destruct (H x Hx d) as [y Hy].
exists y.
assumption.
Qed.

Lemma HausdorffBallStrongHausdorffBall : stableMetric X ->
 forall (e:Qpos) A B,
 SubFinite X A -> SubFinite X B ->
 hausdorffBallStrong e A B -> hausdorffBall X e A B.
Proof.
intros HX e A B HA HB [H0 H1].
split; auto using HemiMetricStrongHemiMetric.
Qed.
*)
Hypothesis almostDecideX : locatedMetric X.

(*
Lemma HemiMetricHemiMetricStrong : forall (e:Qpos) A B,
 FinitelyEnumerable X B ->
 hemiMetric X e A B -> hemiMetricStrong e A B.
Proof.
intros e A B [l Hl] H x Hx.
generalize (H x Hx).
clear H.
revert B Hl x Hx.
induction l; intros B Hl x Hx H d.
 elimtype False.
 generalize H.
 apply existsC_ind.
  tauto.
 intros y [Hy0 Hy1].
 apply -> Hl.
  apply Hy0.
 auto.
destruct (almostDecideX e (e+d)%Qpos x a).
  abstract (
  autorewrite with QposElim;
  rewrite Qlt_minus_iff;
  ring_simplify;
  auto with * ).
 exists a.
 destruct (Hl a); auto with *.
set (B':=fun x => ~~In x l).
assert ({ y : X | B' y /\ ball (m:=X) (e + d) x y}).
 apply IHl; auto.
  reflexivity.
 destruct (H) as [HG | y [Hy0 Hy1]] using existsC_ind.
  auto using existsC_stable.
 apply existsWeaken.
 exists y.
 abstract (
 split; auto;
 intros Y;
 apply -> Hl;[apply Hy0|];
 intros H;
 apply Y;
 destruct H as [H|H];
 [rewrite H in n; contradiction|auto with *]).
destruct X0 as [y [Hy0 Hy1]].
exists y.
abstract (
split; auto;
apply <- Hl;
auto 7 with * ).
Defined.

Lemma HausdorffBallHausdorffBallStrong : forall (e:Qpos) A B,
 FinitelyEnumerable X A -> FinitelyEnumerable X B ->
 hausdorffBall X e A B -> hausdorffBallStrong e A B.
intros e A B HA HB [H0 H1].
split; auto using HemiMetricHemiMetricStrong.
Defined.

Definition HemiMetricStrongAlmostDecidable :
 forall (e d:Qpos) A B,
 FinitelyEnumerable X A -> FinitelyEnumerable X B ->
 e < d -> hemiMetricStrong d A B + {hemiMetricStrong e A B->False}.
Proof.
assert (P1:forall (e d : Qpos) (a:X) (B : X -> Prop),
FinitelyEnumerable X B ->
e < d -> hemiMetricStrong d (fun x=>a=x) B + (hemiMetricStrong e (fun x=>a=x) B -> False)).
 intros e d a B [lB HB].
 revert B HB.
 induction lB.
  intros B HB Hed.
  right.
  intros H.
  destruct (H a (refl_equal a) d) as [y [Hy _]].
  apply -> HB.
   apply Hy.
  auto.
 intros B HB Hed.
 destruct (IHlB (fun x => ~~In x lB)) as [H|H].
    tauto.
   assumption.
  left.
  intros x Hx d0.
  destruct (H x Hx d0) as [y [Hy0 Hy1]].
  exists y.
  split; try assumption.
  assert (Z:=HB y); auto with *.
  apply <- HB.
  auto 7 with *.
 destruct (almostDecideX ((1#2)*(e+d))%Qpos d a a0).
   autorewrite with QposElim.
   rewrite Qlt_minus_iff.
   replace RHS with ((1#2)*(d + - e)) by ring.
   rewrite Qlt_minus_iff in Hed.
   Qauto_pos.
  left.
  intros x Hx d0.
  exists a0.
  destruct (HB a0).
  split; auto with *.
  apply ball_weak.
  rewrite <- Hx.
  assumption.
 right.
 intros H0.
 destruct (Qpos_lt_plus Hed) as [c Hc].
 apply H.
 intros x Hx d0.
 destruct (H0 a (refl_equal a) (Qpos_min d0 ((1#2)*c)%Qpos)) as [y [Hy0 Hy1]].
 destruct (HB y) as [Y _].
 exists y.
 split.
  intros Z.
  apply Y.
   assumption.
  intros H1.
  apply Z; clear Z.
  destruct H1 as [H1 | H1]; try assumption.
  elim n.
  rewrite H1.
  apply ball_weak_le with (e + Qpos_min d0 ((1 # 2) * c))%Qpos; auto.
  autorewrite with QposElim.
  rewrite Hc.
  rewrite Qle_minus_iff.
  replace RHS with ((1 # 2) * c + - (Qmin d0 ((1 # 2) * c))) by ring.
  rewrite <- Qle_minus_iff.
  rapply Qpos_min_lb_r.
 apply ball_weak_le with (e + Qmin d0 ((1 # 2) * c))%Qpos; auto.
  autorewrite with QposElim.
  rewrite Qle_minus_iff.
  replace RHS with (d0 + - (Qmin d0 ((1 # 2) * c))) by ring.
  rewrite <- Qle_minus_iff.
  rapply Qmin_lb_l.
 congruence.
intros e d A B HA HB Hed.
cut (hemiMetric X d A B + {hemiMetricStrong e A B -> False}).
 clear - HB.
 intros [Y|Y].
  left.
  apply HemiMetricHemiMetricStrong; auto.
 right; auto.
destruct HA as [lA HA].
revert A HA HB Hed.
induction lA.
 intros A HA HB _.
 left.
 intros x Hx.
 destruct (HA x) as [HAx _].
 elim (HAx Hx).
 auto with *.
intros A Ha HB Hed.
pose (A':=fun x => ~~In x lA).
destruct (IHlA A') as [I|I]; try assumption.
  unfold A'; tauto.
 destruct (P1 e d a B HB Hed) as [J|J].
  left.
  intros x Hx.
  rewrite Ha in Hx.
  revert Hx.
  cut (In x (a::lA) -> existsC X (fun y : X => B y /\ ball (m:=X) d x y)).
   unfold existsC; tauto.
  intros Hx.
  destruct Hx as [Hx|Hx].
   assert (J':hemiMetric X d (fun x : X => a = x) B).
    apply HemiMetricStrongHemiMetric; auto with *.
     clear - HB.
     destruct HB as [l Hl].
     exists l.
     firstorder.
   apply J'.
   assumption.
  change (In x lA) in Hx.
  apply I.
  unfold A'; auto.
 right.
 intros H.
 apply J.
 intros x Hx d0.
 apply H.
 rewrite Ha.
 rewrite Hx.
 auto with *.
right.
intros H.
apply I.
intros x Hx d0.
apply H.
rewrite Ha.
revert Hx.
unfold A'.
auto 7 with *.
Defined.

Definition HausdorffBallStrongAlmostDecidable :
 forall (e d:Qpos) A B,
 FinitelyEnumerable X A -> FinitelyEnumerable X B ->
 e < d -> hausdorffBallStrong d A B + {hausdorffBallStrong e A B->False}.
Proof.
intros e d A B HA HB Hed.
destruct (HemiMetricStrongAlmostDecidable e d A B HA HB Hed).
 destruct (HemiMetricStrongAlmostDecidable e d B A HB HA Hed).
  left.
  split; assumption.
 right.
 intros [_ H]; auto.
right.
intros [H _]; auto.
Defined.
*)

End HausdorffMetricStrong.

(*
Definition HausdorffBallAlmostDecidable :
 forall X, locatedMetric X ->
 forall (e d:Qpos) A B,
 FinitelyEnumerable X A -> FinitelyEnumerable X B ->
 e < d -> {hausdorffBall X d A B} + {~hausdorffBall X e A B}.
Proof.
intros X HX e d A B HA HB Hed.
destruct (HausdorffBallStrongAlmostDecidable X HX e d A B HA HB Hed) as [Z|Z].
 left.
 abstract (
 apply HausdorffBallStrongHausdorffBall;
  (apply located_stable || apply FinitelyEnumerable_SubFinite || idtac);assumption).
right.
abstract (
intros H;
apply Z;
apply HausdorffBallHausdorffBallStrong; assumption).
Defined.
*)
