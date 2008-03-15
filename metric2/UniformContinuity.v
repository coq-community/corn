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

Require Export Metric.
Require Export QposInf.
Require Import List.
Require Import CornTac.

Set Implicit Arguments.

Definition ball_ex (X:MetricSpace) (e:QposInf) (a b:X) :=
 match e with
  | Qpos2QposInf e' => ball e' a b
  | QposInfinity => True
 end.

Implicit Arguments ball_ex [X].

Lemma ball_ex_weak_le : forall (X:MetricSpace) (e d:QposInf) (a b:X), QposInf_le e d ->  ball_ex e a b -> ball_ex d a b.
Proof.
intros X e d a b Hed Hab.
destruct d as [d|];
destruct e as [e|].
rapply (ball_weak_le X).
apply Hed.
assumption.
elim Hed.
constructor.
assumption.
Qed.

Lemma ball_ex_dec : forall (X:MetricSpace), (forall e (a b:X), {ball e a b}+{~ball e a b}) -> forall e (a b:X), {ball_ex e a b}+{~ball_ex e a b}.
Proof.
intros X ball_dec e a b.
destruct e as [e|].
apply (ball_dec e a b).
simpl.
auto.
Defined.

Section UniformlyContinuousFunction.

Variable X Y : MetricSpace.

Definition is_UniformlyContinuousFunction 
 (f: X -> Y) (mu: Qpos -> QposInf) :=
 forall e a b, ball_ex (mu e) a b -> ball e (f a) (f b).

Lemma is_UniformlyContinuousFunction_wd : forall (f1 f2:X -> Y) (mu1 mu2: Qpos -> QposInf),
 (forall x, ms_eq (f1 x) (f2 x)) ->
 (forall x, QposInf_le (mu2 x) (mu1 x)) ->
 (is_UniformlyContinuousFunction f1 mu1) ->
 (is_UniformlyContinuousFunction f2 mu2).
Proof.
intros f1 f2 mu1 mu2 Hf Hmu H e a b Hab.
do 2 rewrite <- Hf.
apply H.
eapply ball_ex_weak_le.
apply Hmu.
assumption.
Qed.

Record UniformlyContinuousFunction : Type :=
{ucFun :> X -> Y
;mu : Qpos -> QposInf
;uc_prf : is_UniformlyContinuousFunction ucFun mu
}.

Lemma uc_prf_smaller : forall (f:UniformlyContinuousFunction) (mu2 : Qpos -> QposInf),
 (forall e, QposInf_le (mu2 e) (mu f e)) ->
 is_UniformlyContinuousFunction (ucFun f) mu2.
Proof.
intros f my2 H.
eapply is_UniformlyContinuousFunction_wd.
intros; reflexivity.
apply H.
apply uc_prf.
Qed.

Definition ucEq (f g : UniformlyContinuousFunction) :=
 forall x, ms_eq (f x) (g x).


Lemma uc_setoid : Setoid_Theory UniformlyContinuousFunction ucEq.
Proof.
constructor.
intros x a.
reflexivity.
intros x y H a.
symmetry.
apply H.
intros x y z H1 H2 a.
transitivity (y a).
apply H1.
apply H2.
Qed.

Definition ucBall e (f g : UniformlyContinuousFunction) := forall a, ball e (f a) (g a).

Lemma uc_is_MetricSpace : is_MetricSpace ucEq ucBall.
Proof.
constructor.
apply uc_setoid.
firstorder using ball_refl.
firstorder using ball_sym.
intros e1 e2 f g h H1 H2 a.
apply ball_triangle with (g a); auto.
intros e f g H a.
apply ball_closed.
firstorder.
intros f g H a.
apply ball_eq.
firstorder.
Qed.

Lemma ucBall_wd : forall (e1 e2:Qpos), (QposEq e1 e2) -> 
            forall x1 x2, (ucEq x1 x2) -> 
            forall y1 y2, (ucEq y1 y2) -> 
            (ucBall e1 x1 y1 <-> ucBall e2 x2 y2).
Proof.
intros.
unfold ucEq in *.
unfold ucBall in *.
split.
intros.
rewrite <- H.
rewrite <- H0.
rewrite <- H1.
auto.
intros.
rewrite H.
rewrite H0.
rewrite H1.
auto.
Qed.

End UniformlyContinuousFunction.

Implicit Arguments is_UniformlyContinuousFunction [X Y].

(*
Add Setoid UniformlyContinuousFunction ucEq uc_setoid as uc_Setoid.
*)

Definition UniformlyContinuousSpace (X Y:MetricSpace) : MetricSpace :=
Build_MetricSpace (@ucBall_wd X Y) (@uc_is_MetricSpace X Y).

Notation "x --> y" := (UniformlyContinuousSpace x y) (at level 90, right associativity) : uc_scope.

Open Local Scope uc_scope.

Add Morphism ucFun with signature ms_eq ==> ms_eq as uc_wd.
intros X Y f x0 x1 Hx.
apply ball_eq.
intros e.
apply uc_prf.
destruct (mu f e);[|constructor].
simpl.
rewrite Hx.
apply ball_refl.
Qed.

Definition ucFun2 (X Y Z:MetricSpace) (f: X --> Y --> Z) (x:X) (y:Y) := f x y.

Add Morphism ucFun2 with signature ms_eq ==> ms_eq ==> ms_eq as ucFun2_wd.
Proof.
intros.
unfold ucFun2.
rewrite H0.
generalize x3.
change (ms_eq (f x1) (f x2)).
rewrite H.
reflexivity.
Qed.

Lemma uc_id_prf (X:MetricSpace) : is_UniformlyContinuousFunction  (fun (x:X) => x) Qpos2QposInf.
Proof.
intros X e a b Hab.
assumption.
Qed.

Definition uc_id (X:MetricSpace) : UniformlyContinuousFunction X X :=
Build_UniformlyContinuousFunction (uc_id_prf X).

Lemma uc_compose_prf (X Y Z:MetricSpace) (g: Y --> Z) (f:X --> Y) :
is_UniformlyContinuousFunction (fun x => g (f x)) (fun e => QposInf_bind (mu f) (mu g e)).
Proof.
intros X Y Z [g mu_g Hg] [f mu_f Hf] e a b Hab.
unfold is_UniformlyContinuousFunction in *.
simpl in *.
apply Hg.
clear Hg.
destruct (mu_g e) as [mge|]; firstorder.
Qed.

Definition uc_compose (X Y Z:MetricSpace) (g: Y --> Z) (f:X --> Y) : X --> Z :=
Build_UniformlyContinuousFunction (uc_compose_prf g f).

Add Morphism uc_compose with signature ms_eq ==> ms_eq ==> ms_eq as uc_compose_wd.
Proof.
intros X Y Z x1 x2 Hx y1 y2 Hy.
intros x.
simpl.
rewrite (Hx (y1 x)).
apply uc_wd.
rewrite (Hy x).
reflexivity.
Qed.
