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

Record UniformlyContinuousFunction : Type :=
{ucFun :> X -> Y
;mu : Qpos -> QposInf
;uc_prf : is_UniformlyContinuousFunction ucFun mu
}.

Lemma uc_prf_smaller : forall (f:UniformlyContinuousFunction) (mu2 : Qpos -> QposInf),
 (forall e, QposInf_le (mu2 e) (mu f e)) ->
 is_UniformlyContinuousFunction (ucFun f) mu2.
Proof.
intros [f mu1 p] mu2 H e a b Hab.
apply p.
eapply ball_ex_weak_le.
apply H.
assumption.
Qed.

Definition ucEq (f g : UniformlyContinuousFunction) :=
 forall x, ms_eq (f x) (g x).

Hypothesis plX: PrelengthSpace X.

(*Lemma 15*)
Lemma mu_sum : forall e0 (es : list Qpos) (f:UniformlyContinuousFunction) a b,
ball_ex (fold_right QposInf_plus (mu f e0) (map (mu f) es)) a b ->
ball (fold_right Qpos_plus e0 es) (f a) (f b).
Proof.
intros e0 es f a b Hab.
apply ball_closed.
intros e'.
setoid_replace (fold_right Qpos_plus e0 es + e')%Qpos with (fold_right Qpos_plus e0 (e'::es)) by (simpl;QposRing).
set (ds := map (mu f) es) in *.
set (d0 := (mu f e0)) in *.
set (d' := (mu f e')) in *.

assert (H:{ds' | (map Qpos2QposInf ds')=d0::d'::ds}+{In QposInfinity (d0::d'::ds)}).
generalize (d0::d'::ds); clear.
induction l as [|[d|] ds].
left.
exists (@nil Qpos).
reflexivity.
destruct IHds as [[ds' Hds']|Hds].
left.
exists (d::ds').
rewrite <- Hds'.
reflexivity.
firstorder.
firstorder.

destruct H as [[ds' Hds']|Hds].

destruct ds' as [|g0 [|g' gs]]; try discriminate Hds'.
inversion Hds'.
clear Hds'.
unfold d0 in *; clear d0.
unfold d' in *; clear d'.
unfold ds in *; clear ds.
replace (fold_right QposInf_plus (mu f e0) (map (mu f) es))
 with (Qpos2QposInf (fold_right Qpos_plus g0 gs)) in Hab.
simpl in Hab.
assert (H:(fold_right Qpos_plus g0 gs < QposSum ((g' :: gs)++(g0::nil)))).
simpl.
replace LHS with (QposSum (gs ++ g0::nil)).
rewrite Qlt_minus_iff.
ring_simplify.
apply Qpos_prf.
clear - g0.
induction gs.
simpl; ring.
simpl.
rewrite Q_Qpos_plus.
rewrite IHgs.
reflexivity.
case (trail plX _ _ _ Hab H).
clear Hab H.
cut (map Qpos2QposInf (g' :: gs) = map (mu f) (e' :: es)).
clear H2 H1.
generalize (e'::es) (g'::gs) a.
clear gs g' es e' a.
induction l as [|e es]; intros gs a Hes x [Ha Hb] H;
destruct gs; try discriminate Hes.
simpl in *.
apply uc_prf.
rewrite <- H0.
rewrite <- Hb.
rewrite <- Ha.
simpl.
apply (H 0%nat g0).
auto with *.
simpl.
inversion Hes; clear Hes.
eapply ball_triangle.
apply uc_prf.
rewrite <- H2.
rewrite <- Ha.
simpl; apply (H 0%nat g0).
simpl; auto with *.
apply (IHes _ (x 1%nat) H3 (fun i => x (S i))); try auto with *.
intros.
apply (H (S i) z).
simpl; auto with *.
simpl; congruence.
rewrite <- H2.
rewrite <- H0.
clear - gs.
induction gs.
reflexivity.
simpl.
rewrite <- IHgs.
reflexivity.

assert (H:forall (e:Qpos) es, e < (fold_right Qpos_plus e0 es)%Qpos -> (mu f e)=QposInfinity -> ball (m:=Y) (fold_right Qpos_plus e0 es) (f a) (f b)).
intros e esx He Hmu.
apply ball_weak_le with e;[apply Qlt_le_weak; assumption|].
apply uc_prf.
rewrite Hmu.
constructor.

case (in_inv Hds).
intros Hd0.
apply H with e0.
clear - es.
induction es.
simpl.
rewrite Q_Qpos_plus.
rewrite Qlt_minus_iff.
ring_simplify.
apply Qpos_prf.
simpl.
replace RHS with (a+(fold_right Qpos_plus e0 (e'::es))) by (simpl;QposRing).
eapply Qlt_trans.
apply IHes.
rewrite Qlt_minus_iff.
ring_simplify.
apply Qpos_prf.
assumption.
clear Hds.
change (d'::ds) with (map (mu f) (e'::es)).
induction (e'::es); intros Hds.
elim Hds.
simpl in Hds.
destruct Hds as [Ha0|Hds].
apply H with a0.
simpl.
rewrite Q_Qpos_plus.
rewrite Qlt_minus_iff.
ring_simplify.
apply Qpos_prf.
assumption.
simpl.
eapply ball_weak_le with (fold_right Qpos_plus e0 l).
rewrite Q_Qpos_plus.
rewrite Qle_minus_iff; ring_simplify.
auto with *.
auto.
Qed.

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
