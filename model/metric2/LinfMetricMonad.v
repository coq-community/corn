(*
Copyright © 2007-2008 
 Russell O’Connor
 Bas Spitters

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

Require Export StepFunctionSetoid.
Require Import StepFunctionMonad.
Require Import UniformContinuity.
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

Section StepFSupBall.
Set Implicit Arguments.

Variable X:MetricSpace.

Open Local Scope setoid_scope.
Definition ballS0 (m : MetricSpace): Qpos ->  m  -> m --> iffSetoid.
intros m e x.
exists (ball e x).
intros. apply ball_wd;auto with *.
(* should be a lemma*)
apply ball_eq. intro. auto with *.
Defined.

Definition ballS (m : MetricSpace): Qpos ->  m --> m --> iffSetoid.
intros m e.
exists (ballS0  m e).
intros. simpl. split; rewrite H; auto with *.
Defined.

(** We define the sup-metric on step functions *)

Definition StepFSupBall(e:Qpos)(f:StepF X)(g:StepF X):=
StepFfoldProp ((@ballS X e)^@> f <@> g).

End StepFSupBall.

Implicit Arguments StepFSupBall [X].

Add Parametric Morphism X : (@StepFSupBall X)
  with signature QposEq ==> (@StepF_eq _) ==> (@StepF_eq _) ==> iff
 as StepFSupBall_wd.
unfold StepFSupBall.
intros a1 a2 Ha x1 x2 Hx y1 y2 Hy.
apply StepFfoldProp_morphism.
rewrite Hx.
rewrite Hy.
setoid_replace (ballS X a1) with (ballS X a2).
reflexivity.
intros x y.
simpl.
rewrite Ha.
reflexivity.
Qed.

Section SupMetric.

Variable X : MetricSpace.

Lemma StepFSupBall_refl : forall e (x:StepF X), (StepFSupBall e x x).
Proof.
intros e x.
unfold StepFSupBall.
set (b:=(@ballS X e)).
set (f:=(@join _ _) ^@> (constStepF b)).
cut (StepFfoldProp (f <@> x )).
 unfold f.
 evalStepF.
 auto.
rapply StepFfoldPropForall_Map.
simpl.
auto with *.
Qed.

Lemma StepFSupBall_sym : forall e (x y:StepF X), (StepFSupBall e x y) -> (StepFSupBall e y x).
Proof.
intros e x y.
unfold StepFSupBall.
set (b:=(@ballS X e)).
apply StepF_imp_imp.
unfold StepF_imp.
set (f:=ap
 (compose (@ap _ _ _) (compose (compose imp) b))
 (flip (b))).
cut (StepFfoldProp (f ^@> x <@> y)).
 unfold f; evalStepF; tauto.
apply StepFfoldPropForall_Map2.
intros a b0.
simpl. unfold compose0.
auto with *.
Qed.

Lemma StepFSupBall_triangle : forall e d (x y z:StepF X), 
 (StepFSupBall e x y) -> (StepFSupBall d y z) -> (StepFSupBall (e+d) x z).
Proof.
intros e d x y z.
unfold StepFSupBall.
set (be:=(@ballS X e)).
set (bd:=(@ballS X d)).
set (bed:=(@ballS X (e+d) )).
intro H. apply StepF_imp_imp. revert H.
apply StepF_imp_imp.
unfold StepF_imp.
pose (f:= ap
(compose (@ap _ _ _) (compose (compose (compose (@compose _ _ _) imp)) be))
(compose (flip (compose (@ap _ _ _) (compose (compose imp) bd))) bed)).
cut (StepFfoldProp (f ^@> x <@> y <@> z)).
 unfold f.
 evalStepF.
 tauto.
apply StepFfoldPropForall_Map3.
rapply (ball_triangle X e d).
Qed.

Lemma StepFSupBall_closed : forall e (x y:StepF X), (forall d, (StepFSupBall (e+d) x y)) -> (StepFSupBall e x y).
Proof.
intros e.
rapply (StepF_ind2).
  intros. rewrite H, H0 in H1. apply H1.
  intro. rewrite H, H0. apply H2.
 rapply ball_closed.
intros o s s0 t t0 IH0 IH1 H.
unfold StepFSupBall in *.
rewrite MapGlue. rewrite ApGlue. simpl.
split.
 rewrite SplitLGlue. apply IH0. clear IH0.
 intro d. pose (H2:=H d).
  rewrite MapGlue in H2. rewrite ApGlue in H2. rewrite SplitRGlue in H2. rewrite SplitLGlue in H2. 
 destruct H2. auto. 
rewrite SplitRGlue. apply IH1. clear IH1.
intro d. pose (H2:=H d).
rewrite MapGlue in H2. rewrite ApGlue in H2. rewrite SplitRGlue in H2. rewrite SplitLGlue in H2. 
destruct H2. auto.
Qed.

Lemma StepFSupBall_eq : forall (x y : StepF X),
(forall e : Qpos, StepFSupBall e x y) -> StepF_eq x y.
Proof.
rapply (StepF_ind2).
  intros s s0 t t0 H H0 H1 H2. rewrite H, H0 in H1. apply H1.
  intro. rewrite H, H0. apply H2.
 rapply ball_eq.
intros o s s0 t t0 H H0 H1.
unfold StepFSupBall in *. apply glue_resp_StepF_eq.
apply H. clear H.
 intro e. pose (H2:=H1 e). 
 rewrite MapGlue in H2. rewrite ApGlue in H2. rewrite SplitRGlue in H2. rewrite SplitLGlue in H2.
 destruct H2; auto.
apply H0. clear H0.
intro e. pose (H2:=H1 e).
rewrite MapGlue in H2. rewrite ApGlue in H2. rewrite SplitRGlue in H2. rewrite SplitLGlue in H2.
destruct H2; auto.
Qed.
(**
*** Example of a Metric Space <Step, StepFSupBall>
*)
Lemma StepFSupBall_is_MetricSpace : 
 (is_MetricSpace (@StepFS X) (@StepFSupBall X)).
split.
    rapply StepFSupBall_refl.
   rapply StepFSupBall_sym.
  rapply StepFSupBall_triangle.
 rapply StepFSupBall_closed.
rapply StepFSupBall_eq.
Qed.
(* begin hide 
Add Morphism StepFSupBall with signature QposEq ==> (@StepF_eq _) ==> (@StepF_eq _) ==> iff as StepFSupBall_wd.
intros x1 x2 Hx y1 y2 Hy z1 z2 Hz.
unfold LinfBall.
change (x1 == x2)%Q in Hx.
rewrite Hx.
rewrite Hy.
rewrite Hz.
reflexivity.
Qed.
end hide *)
Definition StepFSup : MetricSpace :=
@Build_MetricSpace (StepFS X) _ (@StepFSupBall_wd X) StepFSupBall_is_MetricSpace.

End SupMetric.

(* begin hide *)
Canonical Structure StepFSup.
(* end hide *)

Open Local Scope uc_scope.
(*
Definition StepQSup_uc : LinfStepQ --> Q_as_MetricSpace
:= Build_UniformlyContinuousFunction sup_uc_prf.
*)

(** There is an injection from Q to Linf. *)
Lemma constStepF_uc_prf (X:MetricSpace) : is_UniformlyContinuousFunction
 (@constStepF X:X -> StepFSup X) Qpos2QposInf.
Proof.
intros X e x y H.
simpl in *.
assumption.
Qed.

Definition constStepF_uc (X:MetricSpace) : X --> StepFSup X
:= Build_UniformlyContinuousFunction (constStepF_uc_prf X).
