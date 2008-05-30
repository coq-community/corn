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

Require Export LinfMetric.
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

Section StepFSup_sec.
Set Implicit Arguments.

Variable X:MetricSpace.

Definition msp_is_setoid:MetricSpace->Setoid.
intro m.
apply (@Build_Setoid (ms m) (@ms_eq m)). 
pose (s:=msp_Xsetoid (msp m)).
apply (@Build_equivalence); destruct s; auto.
Defined.

Coercion msp_is_setoid:MetricSpace>->Setoid.

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

Add Morphism StepFSupBall 
  with signature QposEq ==> (@StepF_eq _) ==> (@StepF_eq _) ==> iff
 as StepFSupBall_wd.
unfold StepFSupBall.
intros a1 a2 Ha x1 x2 Hx y1 y2 Hy.
unfold QposEq in Ha.
apply StepFfoldProp_morphism.
rewrite Hx.
rewrite Hy.
(* Cheat here 
rewrite Ha.
reflexivity.*)
Admitted.

Lemma StepFSupBall_refl : forall e x, (StepFSupBall e x x).
Proof.
intros e x.
unfold StepFSupBall.
set (b:=(@ballS X e)).
set (f:=(@join _ _) ^@> (constStepF b)).
cut (StepFfoldProp (f <@> x )).
 unfold f.
 evalStepF.
 auto.
apply StepFfoldPropForall_Ap.
intro y.
unfold f.
 evalStepF.
unfold StepFfoldProp.
simpl.
auto with *.
Qed.

Lemma StepFSupBall_sym : forall e x y, (StepFSupBall e x y) -> (StepFSupBall e y x).
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

Lemma StepFSupBall_triangle : forall e d x y z, 
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
intros a b c Hab Hbc.
clear f.
simpl in *.
rapply (ball_triangle X e d a b c); assumption.
Qed.

Lemma StepFSupBall_closed : forall e x y, (forall d, (StepFSupBall (e+d) x y)) -> (StepFSupBall e x y).
Admitted.
(*
Proof.
unfold StepFSupBall. intros e a b.

apply StepF_imp_imp.

Qed.
*)

Lemma StepFSupBall_eq : forall x y, 
(forall e : Qpos, StepFSupBall e x y) -> StepF_eq x y.
Admitted.
(*
Proof.
intros x y H.
unfold LinfBall in H.
setoid_replace y with (constStepF (0:QS)+y) by ring.
set (z:=constStepF (0:QS)).
setoid_replace x with (x - y + y) by ring.
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
*)
(**
*** Example of a Metric Space <Step, StepFSupBall>
*)
Lemma StepFSupBall_is_MetricSpace : 
 (is_MetricSpace (@StepF_eq X) StepFSupBall).
split.
     apply (StepF_Sth X).
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
Build_MetricSpace StepFSupBall_wd StepFSupBall_is_MetricSpace.
(* begin hide *)
Canonical Structure StepFSup.
(* end hide *)

Open Local Scope uc_scope.
(*
Definition StepQSup_uc : LinfStepQ --> Q_as_MetricSpace
:= Build_UniformlyContinuousFunction sup_uc_prf.
*)

(** There is an injection from Q to Linf. *)
Lemma constStepF_uc_prf : is_UniformlyContinuousFunction
 (@constStepF X:X -> StepFSup) Qpos2QposInf.
Proof.
intros e x y H.
simpl in *.
assumption.
Qed.
Definition constStepF_uc : X --> StepFSup
:= Build_UniformlyContinuousFunction constStepF_uc_prf.
End StepFSup_sec.