(*
Copyright © 2006-2008 Russell O’Connor

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

Require Export UniformContinuity.
Require Export QposInf.
Require Export Classification.
Require Import QposMinMax.
Require Import QMinMax.
Require Import Qauto.
Require Import Qordfield.
Require Import COrdFields2.
Require Import CornTac.

Set Implicit Arguments.

Open Local Scope uc_scope.
(**
** Complete metric space
*)
Section RegularFunction.

Variable X:MetricSpace.

(**
*** Regular functions
A regular function is one way of representing elements in a complete
metric space.  A regular function that take a given error e, and returns
an approximation within e of the value it is representing.  These
approximations must be coherent and the definition belows state this
property.
*)

Definition is_RegularFunction (x:QposInf -> X) : Prop :=
 forall (e1 e2:Qpos), ball (m:=X) (e1+e2) (x e1) (x e2).

(** A regular function consists of an approximation function, and
a proof that the approximations are coherent. *)
Record RegularFunction : Type :=
{approximate : QposInf -> X
;regFun_prf : is_RegularFunction approximate
}.
(** Regular functions form a metric space *)
Definition regFunEq (f g : RegularFunction) :=
 forall e1 e2, ball (m:=X) (e1+e2) (approximate f e1) (approximate g e2).

Lemma regFunEq_e : forall (f g : RegularFunction), (forall e, ball (m:=X) (e+e) (approximate f e) (approximate g e)) -> (regFunEq f g).
Proof.
unfold regFunEq.
intros f g H e1 e2.
apply ball_closed.
intros d.
setoid_replace (e1+e2+d)%Qpos with ((e1 + ((1#4)*d) + (((1#4)*d)+((1#4)*d)) +(((1#4)*d)+e2)))%Qpos by (QposRing).
eapply ball_triangle.
eapply ball_triangle.
apply regFun_prf.
apply H.
apply regFun_prf.
Qed.

Lemma regFunEq_e_small : forall (f g : RegularFunction) (E:Qpos), (forall (e:Qpos), e <= E -> ball (m:=X) (e+e) (approximate f e) (approximate g e)) -> (regFunEq f g).
Proof.
intros f g E H.
apply regFunEq_e.
intros e.
apply ball_closed.
intros d.
set (e':=Qpos_min ((1#4)*d) E).
apply ball_weak_le with ((e+e')+(e'+e')+(e'+e))%Qpos.
autorewrite with QposElim.
setoid_replace (e+e+d) with ((e+(1#4)*d)+((1#4)*d+(1#4)*d)+((1#4)*d+e)) by QposRing.
repeat rsapply plus_resp_leEq_both;
try rapply Qpos_min_lb_l; auto with *.
apply ball_triangle with (approximate g e').
apply ball_triangle with (approximate f e').
apply regFun_prf.
apply H.
rapply Qpos_min_lb_r.
apply regFun_prf.
Qed.

Lemma regFun_setoid : Setoid_Theory RegularFunction regFunEq.
Proof.
split.
unfold Reflexive.
intros; apply regFunEq_e; intros; apply ball_refl.
unfold Symmetric, regFunEq.
intros.
apply ball_sym.
setoid_replace (e1+e2)%Qpos with (e2+e1)%Qpos by QposRing.
auto.
unfold Transitive, regFunEq.
intros.
apply ball_closed.
intros.
setoid_replace (e1+e2+d)%Qpos with ((e1 + (1#2)*d) + ((1#2)*d+e2))%Qpos by QposRing.
eapply ball_triangle.
apply H.
apply H0.
Qed.

(*
Add Setoid RegularFunction regFunEq regFun_setoid as regFun_Setoid.
*)

Definition regFunBall e (f g : RegularFunction) :=
forall d1 d2, ball (m:=X) (d1+e+d2)%Qpos (approximate f d1) (approximate g d2).

Lemma regFunBall_wd : forall (e1 e2:Qpos), (QposEq e1 e2) -> 
            forall x1 x2, (regFunEq x1 x2) -> 
            forall y1 y2, (regFunEq y1 y2) -> 
            (regFunBall e1 x1 y1 <-> regFunBall e2 x2 y2).
Proof.
assert (forall x1 x2 : Qpos,
QposEq x1 x2 ->
forall x3 x4 : RegularFunction ,
regFunEq x3 x4 ->
forall x5 x6 : RegularFunction ,
regFunEq x5 x6 -> (regFunBall x1 x3 x5 -> regFunBall x2 x4 x6)).
unfold regFunBall.
unfold regFunEq.
intros a1 a2 Ha f1 f2 Hf g1 g2 Hg H d1 d2.
rewrite <- Ha.
clear a2 Ha.
apply ball_closed.
intros d.
setoid_replace (d1 + a1 + d2 + d)%Qpos with (((1#4)*d+d1)+((1#4)*d + a1 + (1#4)*d)+((1#4)*d+d2))%Qpos by QposRing.
eapply ball_triangle.
eapply ball_triangle.
apply ball_sym.
apply Hf.
apply H.
apply Hg.
intros; split.
intros; eapply H.
apply H0.
apply H1.
apply H2.
auto.
destruct (regFun_setoid).
intros; eapply H.
unfold QposEq. symmetry.
apply H0.
apply Seq_sym.
apply regFun_setoid.
apply H1.
apply Seq_sym.
apply regFun_setoid.
apply H2.
auto.
Qed.

Lemma regFun_is_MetricSpace : is_MetricSpace regFunEq regFunBall.
Proof.
unfold regFunBall.
split.
apply regFun_setoid.
intros e f d1 d2.
setoid_replace (d1 + e + d2)%Qpos with (d1+d2+e)%Qpos by QposRing.
apply ball_weak.
apply regFun_prf.
intros e f g H d1 d2.
apply ball_sym.
setoid_replace (d1 + e + d2)%Qpos with (d2+e+d1)%Qpos by QposRing.
auto.
intros e1 e2 a b c Hab Hbc d1 d2.
apply ball_closed.
intros d3.
setoid_replace (d1+(e1+e2)+d2+d3)%Qpos with ((d1 + e1 + (1#2)*d3)+((1#2)*d3 + e2 + d2))%Qpos by QposRing.
eapply ball_triangle.
apply Hab.
apply Hbc.
intros e a b H d1 d2.
apply ball_closed.
intros d.
setoid_replace (d1+e+d2+d)%Qpos with (d1 + (e+d) + d2)%Qpos by QposRing.
auto.
unfold regFunEq.
intros a b H e1 e2.
apply ball_closed.
intros d.
setoid_replace (e1+e2+d)%Qpos with (e1+d+e2)%Qpos by QposRing.
auto.
Qed.

(** We define the completion of a metric space to be the space of
regular functions *)
Definition Complete : MetricSpace :=
Build_MetricSpace regFunBall_wd regFun_is_MetricSpace.

(** The ball of regular functions is related to the underlying ball
in ways that you would expect. *)
Lemma regFunBall_ball : forall (x y:Complete) (e0 e1 e2:Qpos), ball e0 (approximate x e1) (approximate y e2) -> ball (e1 + e0 + e2) x y.
intros x y e0 e1 e2 H d1 d2.
setoid_replace (d1+(e1+e0+e2)+d2)%Qpos with ((d1+e1)+e0+(e2+d2))%Qpos by QposRing.
eapply ball_triangle.
eapply ball_triangle.
apply regFun_prf.
apply H.
apply regFun_prf.
Qed.

Lemma regFunBall_e : forall (x y:Complete) e, (forall d, ball (d + e + d) (approximate x d) (approximate y d)) -> ball e x y.
intros x y e H.
apply ball_closed.
intros d.
setoid_replace (e + d)%Qpos with ((1#4)*d + ((1#4)*d+e+(1#4)*d) + (1#4)*d)%Qpos by QposRing.
apply regFunBall_ball.
apply H.
Qed.

(**
*** Cunit
There is an injection from the original space to the complete space
given by the constant regular function. *)
Lemma Cunit_fun_prf (x:X) : is_RegularFunction (fun _ => x).
Proof.
intros x d1 d2.
apply ball_refl.
Qed.

Definition Cunit_fun (x:X) : Complete := 
Build_RegularFunction (Cunit_fun_prf x).

Lemma Cunit_prf : is_UniformlyContinuousFunction Cunit_fun Qpos2QposInf.
Proof.
intros e a b Hab d1 d2.
simpl in *.
setoid_replace (d1+e+d2)%Qpos with (e+(d1+d2))%Qpos by QposRing.
apply ball_weak.
assumption.
Qed.

Definition Cunit : X --> Complete :=
Build_UniformlyContinuousFunction Cunit_prf.

(** This injection preserves the metric *)
Lemma ball_Cunit : forall e a b, ball e (Cunit a) (Cunit b) <-> ball e a b.
Proof.
intros e a b.
simpl.
unfold regFunBall.
simpl.
split.
intros H.
do 2 (apply ball_closed; intro).
setoid_replace (e+d+d0)%Qpos with (d+e+d0)%Qpos by QposRing.
apply H.
intros H d1 d2.
rapply Cunit_prf.
assumption.
Qed.

Lemma Cunit_eq : forall a b, ms_eq (Cunit a) (Cunit b) <-> ms_eq a b.
Proof.
intros a b.
do 2 rewrite <- ball_eq_iff.
split; intros H e;
[rewrite <- ball_Cunit | rewrite ball_Cunit];
apply H.
Qed.

Lemma ball_approx_r : forall (x:Complete) e, ball e x (Cunit (approximate x e)).
Proof.
intros x e d1 d2.
simpl.
apply ball_weak.
apply regFun_prf.
Qed.

Lemma ball_approx_l : forall (x:Complete) e, ball e (Cunit (approximate x e)) x.
Proof.
(*
Set Firstorder Depth 6.
firstorder fail with ball_sym ball_approx_r.
*)
pose ball_approx_r.
pose ball_sym.
auto.
Qed.

Lemma ball_ex_approx_r : forall (x:Complete) e, ball_ex e x (Cunit (approximate x e)).
Proof.
intros x [e|]; simpl.
apply ball_approx_r.
constructor.
Qed.

Lemma ball_ex_approx_l : forall (x:Complete) e, ball_ex e (Cunit (approximate x e)) x.
Proof.
intros x [e|]; simpl.
apply ball_approx_l.
constructor.
Qed.

Lemma regFun_prf_ex : 
 forall (r : Complete) (e1 e2 : QposInf),
  ball_ex  (e1 + e2) (approximate r e1) (approximate r e2).
Proof.
intros r [e1|] [e2|]; try constructor.
rapply regFun_prf.
Qed.

End RegularFunction.

(* begin hide *)
Implicit Arguments regFunEq_e_small [X].
Implicit Arguments is_RegularFunction [X].

Implicit Arguments Cunit [X].

Add Parametric Morphism X : (@Cunit_fun X) with signature (@ms_eq _) ==> (@ms_eq _) as Cunit_wd.
exact (@uc_wd _ _ Cunit).
Qed.
(* end hide *)

Section Faster.

Variable X : MetricSpace.
Variable x : Complete X.

(** A regular function is equivalent to the same function that returns
a better approximation with a given error.  One would not generally want
to do this when doing computation; however it is quite a useful
substitution to be able to make during reasoning. *)

Section FasterInGeneral.

Variable f : Qpos -> Qpos.
Hypothesis Hf : forall x, (f x) <= x.

Lemma fasterIsRegular : is_RegularFunction (fun e => (approximate x (QposInf_bind f e))).
Proof.
intros e1 e2.
simpl.
apply ball_weak_le with (f e1 + f e2)%Qpos.
autorewrite with QposElim.
rsapply plus_resp_leEq_both; apply Hf.
apply regFun_prf.
Qed.

Definition faster : Complete X := Build_RegularFunction fasterIsRegular.

Lemma fasterIsEq : ms_eq faster x.
Proof.
rapply regFunEq_e.
intros e.
simpl.
apply ball_weak_le with (f e + e)%Qpos.
autorewrite with QposElim.
rsapply plus_resp_leEq.
apply Hf.
apply regFun_prf.
Qed.

End FasterInGeneral.

Lemma QreduceApprox_prf : forall (e:Qpos), QposRed e <= e.
Proof.
intros e.
rewrite QposRed_correct.
apply Qle_refl.
Qed.

Definition QreduceApprox := faster QposRed QreduceApprox_prf.

Lemma QreduceApprox_Eq : ms_eq QreduceApprox x.
Proof (fasterIsEq _ _).
(** In particular, halving the error of the approximation is a common
case. *)
Lemma doubleSpeed_prf : forall (e:Qpos), ((1#2)*e)%Qpos <= e.
Proof.
intros e.
autorewrite with QposElim.
rewrite Qle_minus_iff.
ring_simplify.
rsapply mult_resp_nonneg.
discriminate.
apply Qpos_nonneg.
Qed.

Definition doubleSpeed := faster (Qpos_mult (1#2)) doubleSpeed_prf. 

Lemma doubleSpeed_Eq : ms_eq doubleSpeed x.
Proof (fasterIsEq _ _).

End Faster.

Section Cjoin.

Variable X : MetricSpace.

(**
*** Cjoin
There is an injection from a twice completed space into a once completed
space.  This injection along with [Cunit] forms an isomorphism between
a twice completed space and a once completed space.  This proves that
a complete metric space is complete. *)
Definition Cjoin_raw (x:Complete (Complete X)) (e:QposInf) :=
(approximate (approximate x (QposInf_mult (1#2) e)) (QposInf_mult (1#2) e))%Qpos.

Lemma Cjoin_fun_prf (x:Complete (Complete X)) : is_RegularFunction (Cjoin_raw x).
Proof.
intros x d1 d2.
rewrite <- ball_Cunit.
setoid_replace (d1 + d2)%Qpos with ((1#2)*d1 + ((1#2)*d1+(1#2)*d2) + (1#2)*d2)%Qpos by QposRing.
apply ball_triangle with (approximate x ((1#2)*d2))%Qpos.
apply ball_triangle with (approximate x ((1#2)*d1))%Qpos.
rapply ball_approx_l.
rapply regFun_prf.
rapply ball_approx_r.
Qed.

Definition Cjoin_fun (x:Complete (Complete X)) : Complete X :=
Build_RegularFunction (Cjoin_fun_prf x).

Lemma Cjoin_prf : is_UniformlyContinuousFunction Cjoin_fun Qpos2QposInf.
Proof.
intros e x y Hab d1 d2.
do 2 rewrite <- ball_Cunit.
setoid_replace (d1 + e + d2)%Qpos with (((1#2)*d1 + (1#2)*d1) + e + (((1#2)*d2) + (1#2)*d2))%Qpos by QposRing.
apply ball_triangle with y.
apply ball_triangle with x.
apply ball_triangle with (Cunit (approximate x ((1 # 2) * d1)%Qpos)).
rewrite ball_Cunit.
rapply ball_approx_l.
apply ball_approx_l.
assumption.
eapply ball_triangle.
apply ball_approx_r.
rewrite ball_Cunit.
rapply ball_approx_r.
Qed.

Definition Cjoin : (Complete (Complete X)) --> (Complete X) :=
Build_UniformlyContinuousFunction Cjoin_prf.

End Cjoin.

Implicit Arguments Cjoin [X].

Section Cmap.

Variable X Y : MetricSpace.
Variable f : X --> Y.

(**
*** Cmap (slow)
Uniformly continuous functions can be lifted to the completion of metric
spaces.  A faster version that works under some mild assumptions will be
given later.  But first the most generic version that we call
[Cmap_slow]. *)

Definition Cmap_slow_raw (x:Complete X) (e:QposInf) :=
f (approximate x (QposInf_mult (1#2)%Qpos (QposInf_bind (mu f) e))).

Lemma Cmap_slow_raw_strongInf : forall (x:Complete X) (d:QposInf) (e:QposInf), QposInf_le d (QposInf_mult (1#2)%Qpos (QposInf_bind (mu f) e)) ->
ball_ex e (f (approximate x d)) (Cmap_slow_raw x e).
Proof.
intros x [d|] [e|] Hd; try constructor.
 rapply uc_prf.
 simpl.
 case_eq (mu f e); simpl; trivial.
 intros q Hq.
 simpl in Hd.
 rewrite Hq in Hd.
 eapply ball_weak_le;[|apply regFun_prf].
 rewrite Q_Qpos_plus.
 replace RHS with (((1 # 2) * q)%Qpos + ((1 # 2) * q)%Qpos) by QposRing.
 rsapply plus_resp_leEq.
 assumption.
unfold Cmap_slow_raw.
simpl in *.
apply uc_prf.
destruct (mu f e) as [q|].
 contradiction.
constructor.
Qed.

Lemma Cmap_slow_raw_strong : forall (x:Complete X) (d:QposInf) (e:Qpos), QposInf_le d (QposInf_mult (1#2)%Qpos (mu f e)) ->
ball e (f (approximate x d)) (Cmap_slow_raw x e).
Proof.
intros.
rapply (Cmap_slow_raw_strongInf x d e).
assumption.
Qed.

Lemma Cmap_slow_fun_prf (x:Complete X) : is_RegularFunction (Cmap_slow_raw x).
Proof.
intros x e1 e2.
unfold Cmap_slow_raw.
cut (forall (e1 e2:Qpos), (QposInf_le (mu f e2) (mu f e1)) -> ball (m:=Y) (e1 + e2)
  (f (approximate x (QposInf_mult (1 # 2)%Qpos (QposInf_bind (mu f) e1))))
  (f (approximate x (QposInf_mult (1 # 2)%Qpos (QposInf_bind (mu f) e2))))).
 intros H.
 (* move this out *)
 assert (forall a b, {QposInf_le a b}+{QposInf_le b a}).
 intros [a|] [b|]; simpl; try tauto.
 apply Qle_total.
 destruct (H0 (mu f e2) (mu f e1)).
 auto.
 apply ball_sym.
 setoid_replace (e1+e2)%Qpos with (e2+e1)%Qpos by QposRing.
 auto.
clear e1 e2.
intros e1 e2 H.
apply ball_weak.
apply ball_sym.
simpl.
rapply Cmap_slow_raw_strong.
simpl.
destruct (mu f e1).
simpl.
destruct (mu f e2).
simpl.
autorewrite with QposElim.
rsapply mult_resp_leEq_lft.
assumption.
discriminate.
elim H.
constructor.
Qed.

Definition Cmap_slow_fun (x:Complete X) : Complete Y :=
Build_RegularFunction (Cmap_slow_fun_prf x).

Definition Cmap_slow_prf : is_UniformlyContinuousFunction Cmap_slow_fun (fun e => (QposInf_mult (1#2)(mu f e))%Qpos).
Proof.
intros e0 x y Hxy.
intros e1 e2.
simpl.
unfold Cmap_slow_raw.
set (d1:=(QposInf_bind (fun y' : Qpos => ((1 # 2) * y')%Qpos) (mu f e1))).
set (d2:=(QposInf_bind (fun y' : Qpos => ((1 # 2) * y')%Qpos) (mu f e2))).
set (d0:=(QposInf_bind (fun y' : Qpos => ((1 # 4) * y')%Qpos) (mu f e0))).
apply ball_triangle with (f (approximate y (QposInf_min d0 d2 ))).
 apply ball_triangle with (f (approximate x (QposInf_min d0 d1))).
  apply uc_prf.
  eapply ball_ex_weak_le;[|apply regFun_prf_ex].
  unfold d1.
  simpl.
  destruct (mu f e1); try constructor.
  destruct d0;
   simpl;
   autorewrite with QposElim;
   (replace RHS with (((1 # 2) * q + (1 # 2) * q)) by ring);
   try rewrite Qmin_plus_distr_r;
   auto with *.
 apply uc_prf.
 destruct (mu f e0); try constructor.
 cut (forall z0 z1:Qpos, (z0 <= (1#4)*q) -> (z1 <= (1#4)*q) -> ball q (approximate x z0) (approximate y z1)).
  intros H.
  destruct d1; destruct d2; simpl; apply H; autorewrite with  QposElim; auto with *.
 intros z0 z1 Hz0 Hz1.
 eapply ball_weak_le.
  2:apply Hxy.
 autorewrite with QposElim.
 rewrite Qle_minus_iff in *.
 replace RHS with (((1 # 4) * q + - z0) + ((1 # 4) * q + - z1)) by ring.
 Qauto_nonneg.
apply uc_prf.
eapply ball_ex_weak_le;[|apply regFun_prf_ex].
unfold d2.
simpl.
destruct (mu f e2); try constructor.
destruct d0;
 simpl;
 autorewrite with QposElim;
 (replace RHS with (((1 # 2) * q + (1 # 2) * q)) by ring);
 try rewrite Qmin_plus_distr_l;
 auto with *.
Qed.

Definition Cmap_slow : (Complete X) --> (Complete Y) :=
Build_UniformlyContinuousFunction Cmap_slow_prf.

End Cmap.

(** Cbind can be defined in terms of map and join *)
Definition Cbind_slow (X Y:MetricSpace) (f:X-->Complete Y) := uc_compose Cjoin (Cmap_slow f).

(** The completion operation, along with the map functor from a monad
in the catagory of metric spaces. *)
Section Monad_Laws.

Variable X Y Z : MetricSpace.

Notation "a =m b" := (ms_eq a b)  (at level 70, no associativity).

Lemma MonadLaw1 : forall a, Cmap_slow_fun (uc_id X) a =m a.
Proof.
intros x e1 e2.
simpl.
rapply ball_weak_le;[|apply regFun_prf].
autorewrite with QposElim.
Qauto_le.
Qed.

Lemma MonadLaw2 : forall (f:Y --> Z) (g:X --> Y) a, Cmap_slow_fun (uc_compose f g) a =m (Cmap_slow_fun f (Cmap_slow_fun g a)).
Proof.
simpl.
intros f g x e1 e2.
set (a := approximate (Cmap_slow_fun (uc_compose f g) x) e1).
set (b:=(approximate (Cmap_slow_fun f (Cmap_slow_fun g x)) e2)).
set (d0 := (QposInf_min (QposInf_mult (1#2)%Qpos (mu (uc_compose f g) e1)) ((1 # 2)%Qpos * QposInf_bind (mu g) (QposInf_mult (1 # 2)%Qpos (mu f e2))))).
apply ball_triangle with ((uc_compose f g) (approximate x d0)).
 apply ball_sym.
 rapply Cmap_slow_raw_strong.
 unfold d0.
 apply QposInf_min_lb_l.
unfold b; simpl.
unfold Cmap_slow_raw.
apply uc_prf.
simpl.
destruct (mu f e2) as [q|]; try constructor.
simpl.
apply ball_weak_le with ((1#2)*q)%Qpos.
 autorewrite with QposElim.
 Qauto_le.
rapply (Cmap_slow_raw_strong g x d0).
rapply QposInf_min_lb_r.
Qed.

Lemma MonadLaw3 : forall (f:X --> Y) a, (Cmap_slow_fun f (Cunit_fun _ a)) =m (Cunit_fun _ (f a)).
Proof.
intros f x e1 e2.
rapply regFun_prf.
Qed.

Lemma MonadLaw4 : forall (f:X --> Y) a, (Cmap_slow_fun f (Cjoin_fun a)) =m (Cjoin_fun ((Cmap_slow_fun (Cmap_slow f)) a)).
Proof.
intros f x e1 e2.
set (e2' := ((1#2)*e2)%Qpos).
set (d0 := (QposInf_min ((1#4)%Qpos*(mu f e1)) ((1#8)%Qpos*(mu f ((1#2)*e2))))%QposInf).
simpl.
unfold Cmap_slow_raw; simpl.
unfold Cjoin_raw; simpl.
unfold Cmap_slow_raw; simpl.
apply ball_triangle with (f (approximate (approximate x d0) d0)).
 apply uc_prf.
 destruct (mu f e1) as [q|]; try constructor.
 simpl.
 do 2 rewrite <- ball_Cunit.
 set (b:= (approximate (approximate x ((1 # 2) * ((1 # 2) * q))%Qpos)
     ((1 # 2) * ((1 # 2) * q))%Qpos)).
 setoid_replace q with (((1#4)*q + (1#4)*q)+ ((1#4)*q+ (1#4)*q))%Qpos by QposRing.
 unfold b; clear b.
 apply ball_triangle with x.
  apply ball_triangle with (Cunit (approximate x ((1 # 2) * ((1 # 2) * q))%Qpos)).
   rewrite ball_Cunit.
   apply ball_approx_l.
  apply ball_approx_l.
 apply ball_triangle with (Cunit (approximate x d0)).
  change (ball_ex ((1 # 4) * q)%Qpos x (Cunit (approximate x d0))).
  apply ball_ex_weak_le with (d0)%QposInf.
   rapply QposInf_min_lb_l.
  destruct d0 as [d0|]; try constructor.
  rapply ball_approx_r.
 rewrite ball_Cunit.
 change (ball_ex ((1 # 4) * q)%Qpos (approximate x d0)
  (Cunit (approximate (approximate x d0) d0))).
 apply ball_ex_weak_le with (d0)%QposInf.
  rapply QposInf_min_lb_l.
 destruct d0 as [d0|]; try constructor.
 rapply ball_approx_r.
apply ball_sym.
apply ball_weak_le with ((1#2)*e2)%Qpos.
 autorewrite with QposElim.
 Qauto_le.
apply uc_prf.
destruct (mu f ((1#2)*e2)) as [q|]; try constructor.
simpl.
do 2 rewrite <- ball_Cunit.
set (b:= (approximate (approximate x ((1 # 2) * ((1 # 2) * q))%Qpos)
    ((1 # 2) * q)%Qpos)).
setoid_replace q with (((1#2)*q + (1#4)*q)+ ((1#8)*q+ (1#8)*q))%Qpos by QposRing.
unfold b; clear b.
apply ball_triangle with x.
 apply ball_triangle with (Cunit (approximate x ((1 # 2) * ((1 # 2) * q))%Qpos)).
  rewrite ball_Cunit.
  apply ball_approx_l.
 apply ball_approx_l.
apply ball_triangle with (Cunit (approximate x d0)).
 change (ball_ex ((1 # 8) * q)%Qpos x (Cunit (approximate x d0))).
 apply ball_ex_weak_le with (d0)%QposInf.
  rapply QposInf_min_lb_r.
 destruct d0 as [d0|]; try constructor.
 rapply ball_approx_r.
rewrite ball_Cunit.
change (ball_ex ((1 # 8) * q)%Qpos (approximate x d0)
 (Cunit (approximate (approximate x d0) d0))).
apply ball_ex_weak_le with (d0)%QposInf.
 rapply QposInf_min_lb_r.
destruct d0 as [d0|]; try constructor.
rapply ball_approx_r.
Qed.

Lemma MonadLaw5 : forall a, (Cjoin_fun (X:=X) (Cunit_fun _ a)) =m a.
intros x e1 e2.
simpl.
setoid_replace (e1+e2)%Qpos with ((1#2)*e1 + e2 + (1#2)*e1)%Qpos by QposRing.
apply ball_weak.
rapply regFun_prf.
Qed.

Lemma MonadLaw6 : forall a, Cjoin_fun ((Cmap_slow_fun (X:=X) Cunit) a) =m a.
Proof.
intros a e1 e2.
simpl.
setoid_replace (e1+e2)%Qpos with ((1#2)*((1#2)*e1) + e2 + (3#4)*e1)%Qpos by QposRing.
apply ball_weak.
rapply regFun_prf.
Qed.

Lemma MonadLaw7 : forall a, Cjoin_fun ((Cmap_slow_fun (X:=Complete (Complete X)) Cjoin) a) =m Cjoin_fun (Cjoin_fun a).
Proof.
intros x e1 e2.
pose (half := fun e:Qpos => ((1#2)*e)%Qpos).
apply ball_weak_le with  ((half (half e1)) + ((half (half e1)) + (half (half e1) + (half (half e2))) + (half (half e2))) + (half e2))%Qpos.
 unfold half.
 autorewrite with QposElim.
 Qauto_le.
rapply (regFun_prf x).
Qed.

(** This final law isn't a monad law, rather it completes the isomorphism
between a twice completed metric space and a one completed metric space. *)
Lemma CunitCjoin : forall a, (Cunit_fun _ (Cjoin_fun (X:=X) a)) =m a.
Proof.
intros x e1 e2 d1 d2.
change (ball (d1 + (e1 + e2) + d2)
  (approximate (approximate x ((1 # 2) * d1)%Qpos) ((1 # 2) * d1)%Qpos)
  (approximate (approximate x e2) d2)).
apply ball_weak_le with (((1 # 2) * d1 + ((1 # 2) * d1 + e2) + d2))%Qpos.
 autorewrite with QposElim.
 rewrite Qle_minus_iff.
 ring_simplify.
 auto with *.
rapply (regFun_prf x).
Qed.

End Monad_Laws.

(** The monad laws are sometimes expressed in terms of bind and unit. *)
Lemma BindLaw1 : forall X Y (f:X--> Complete Y) a, (ms_eq (Cbind_slow f (Cunit_fun _ a)) (f a)).
Proof.
intros X Y f a.
change (ms_eq (Cjoin (Cmap_slow_fun f (Cunit_fun X a))) (f a)).
rewrite (MonadLaw3 f a).
rapply MonadLaw5.
Qed.

Lemma BindLaw2 : forall X a, (ms_eq (Cbind_slow (Cunit:X --> Complete X) a) a).
Proof.
rapply MonadLaw6.
Qed.

Lemma BindLaw3 : forall X Y Z (a:Complete X) (f:X --> Complete Y) (g:Y-->Complete Z), (ms_eq (Cbind_slow g (Cbind_slow f a)) (Cbind_slow (uc_compose (Cbind_slow g) f) a)).
Proof.
intros X Y Z a f g.
change (ms_eq (Cjoin (Cmap_slow_fun g (Cjoin_fun (Cmap_slow f a))))
  (Cjoin (Cmap_slow_fun (uc_compose (Cbind_slow g) f) a))).
rewrite (MonadLaw2 (Cbind_slow g) f).
unfold Cbind_slow.
rewrite (MonadLaw4 g).
rewrite (MonadLaw2 (Cjoin (X:=Z)) (Cmap_slow g)).
symmetry.
rapply MonadLaw7.
Qed.

(**
*** Strong Monad
The monad is a strong monad because the map function itself is
a uniformly continuous function. *)
Section Strong_Monad.

Variable X Y : MetricSpace.
Let X_Y := UniformlyContinuousSpace X Y.
Let CX_CY := UniformlyContinuousSpace (Complete X) (Complete Y).

Lemma Cmap_strong_slow_prf : is_UniformlyContinuousFunction ((Cmap_slow (Y:=Y)):(X_Y -> CX_CY)) Qpos2QposInf.
Proof.
intros e f g H x.
apply ball_closed.
intros e0.
set (he0 := ((1#2)*e0)%Qpos).
set (d0 := QposInf_min ((1#2)%Qpos*(mu f he0)) ((1#2)%Qpos*(mu g he0))).
set (a0 := approximate x d0).
setoid_replace (e+e0)%Qpos with (he0 + e + he0)%Qpos by (unfold he0;QposRing).
apply ball_triangle with (Cunit (g a0)).
apply ball_triangle with (Cunit (f a0)).
rewrite <- (MonadLaw3 f a0).
rapply uc_prf.
simpl.
destruct (mu f he0) as [d1|];[|constructor].
eapply ball_ex_weak_le with d0.
rapply QposInf_min_lb_l.
destruct d0 as [d0|];[|constructor].
rapply ball_approx_r.
rewrite ball_Cunit.
apply H.
rewrite <- (MonadLaw3 g a0).
rapply (uc_prf (Cmap_slow g)).
simpl.
destruct (mu g he0) as [d2|];[|constructor].
eapply ball_ex_weak_le with d0.
rapply QposInf_min_lb_r.
destruct d0 as [d0|];[|constructor].
rapply ball_approx_l.
Qed.

Definition Cmap_strong_slow : (X --> Y) --> (Complete X --> Complete Y) :=
Build_UniformlyContinuousFunction Cmap_strong_slow_prf.

(** Using strength we can show that [Complete] forms an applicative
functor. The [ap] function is useful for making multiple argument maps.
*) 
Definition Cap_slow_raw (f:Complete (X --> Y)) (x:Complete X) (e:QposInf) :=
 approximate (Cmap_slow (approximate f ((1#2)%Qpos*e)%QposInf) x) ((1#2)%Qpos*e)%QposInf.

Lemma Cap_slow_fun_prf (f:Complete (X --> Y)) (x:Complete X) : is_RegularFunction (Cap_slow_raw f x).
Proof.
intros f x e1 e2.
unfold Cap_slow_raw.
unfold QposInf_mult, QposInf_bind.
set (he1 := ((1 # 2) * e1)%Qpos).
set (he2 := ((1 # 2) * e2)%Qpos).
set (f1 := (approximate f he1)).
set (f2 := (approximate f he2)).
change (Cmap_slow (Y:=Y) f1) with (Cmap_strong_slow f1).
change (Cmap_slow (Y:=Y) f2) with (Cmap_strong_slow f2).
set (y1 :=(Cmap_strong_slow f1 x)).
set (y2 :=(Cmap_strong_slow f2 x)).
setoid_replace (e1 + e2)%Qpos with (he1 + (he1 + he2) + he2)%Qpos by (unfold he1, he2; QposRing).
rewrite <- ball_Cunit.
apply ball_triangle with y2;[|apply ball_approx_r].
apply ball_triangle with y1;[apply ball_approx_l|].
rapply (uc_prf Cmap_strong_slow).
rapply regFun_prf.
Qed.

Definition Cap_slow_fun (f:Complete (X --> Y)) (x:Complete X) : Complete Y :=
Build_RegularFunction (Cap_slow_fun_prf f x).

Lemma Cap_slow_help (f:Complete (X --> Y)) (x:Complete X) (e:Qpos) : 
 ball e (Cap_slow_fun f x) (Cmap_slow (approximate f e) x).
Proof.
intros f x e d1 d2.
set (d1' := ((1 # 2) * d1)%Qpos).
set (f1 := (approximate f d1')).
set (f2 := (approximate f e)).
set (y1 := (Cmap_slow f1 x)).
set (y2 := (Cmap_slow f2 x)).
change (ball (d1 + e + d2) (approximate y1 d1') (approximate y2 d2)).
setoid_replace (d1 + e + d2)%Qpos with (d1' + (d1' + e) + d2)%Qpos by (unfold d1'; QposRing).
rewrite <- ball_Cunit.
apply ball_triangle with y2;[|apply ball_approx_r].
apply ball_triangle with y1;[apply ball_approx_l|].
rapply (uc_prf Cmap_strong_slow).
rapply regFun_prf.
Qed.

Definition Cap_modulus (f:Complete (X --> Y)) (e:Qpos) : QposInf := ((1#2)%Qpos*(mu (approximate f ((1#3)*e)%Qpos) ((1#3)*e)))%QposInf.

Lemma Cap_weak_slow_prf (f:Complete (X --> Y)) : is_UniformlyContinuousFunction (Cap_slow_fun f) (Cap_modulus f).
Proof.
intros f e x y H.
set (e' := ((1#3)*e)%Qpos).
setoid_replace e with (e'+e'+e')%Qpos by (unfold e';QposRing).
apply ball_triangle with (Cmap_slow (approximate f e') y).
apply ball_triangle with (Cmap_slow (approximate f e') x).
apply Cap_slow_help.
rapply (uc_prf).
apply H.
apply ball_sym.
apply Cap_slow_help.
Qed.

Definition Cap_weak_slow (f:Complete (X --> Y)) : Complete X --> Complete Y :=
Build_UniformlyContinuousFunction (Cap_weak_slow_prf f).

Lemma Cap_slow_prf : is_UniformlyContinuousFunction Cap_weak_slow Qpos2QposInf.
Proof.
intros e f1 f2 H x.
apply ball_closed.
intros d.
setoid_replace (e+d)%Qpos with ((1#4)*d + ((1#4)*d + e + (1#4)*d) + (1#4)*d)%Qpos by QposRing.
apply ball_triangle with (Cmap_strong_slow (approximate f2 ((1#4)*d)%Qpos) x).
apply ball_triangle with (Cmap_strong_slow (approximate f1 ((1#4)*d)%Qpos) x).
rapply Cap_slow_help.
rapply (uc_prf Cmap_strong_slow).
rapply H.
apply ball_sym.
rapply Cap_slow_help.
Qed.

Definition Cap_slow : Complete (X --> Y) --> Complete X --> Complete Y :=
Build_UniformlyContinuousFunction Cap_slow_prf.

Lemma StrongMonadLaw1 : forall a b, ms_eq (Cap_slow_fun (Cunit_fun _ a) b) (Cmap_strong_slow a b).
Proof.
intros f x.
rapply regFunEq_e.
intros e.
apply ball_weak_le with ((1#2)*e+e)%Qpos.
autorewrite with QposElim.
rewrite Qle_minus_iff; ring_simplify.
rsapply mult_resp_nonneg.
discriminate.
apply Qpos_nonneg.
rapply regFun_prf.
Qed.

End Strong_Monad.

(* begin hide *)
Opaque Complete.

Add Parametric Morphism X Y : (@Cmap_slow_fun X Y) with signature (@ms_eq _) ==> (@ms_eq _) ==> (@ms_eq _) as Cmap_slow_wd.
intros x1 x2 Hx y1 y2 Hy.
transitivity (Cmap_slow_fun x1 y2).
apply (@uc_wd _ _ (Cmap_slow x1) _ _ Hy).
generalize y2.
rapply (@uc_wd _ _ (Cmap_strong_slow X Y)).
assumption.
Qed.

Add Parametric Morphism X Y : (@Cap_weak_slow X Y) with signature (@ms_eq _) ==> (@ms_eq _) as Cap_weak_slow_wd.
intros x1 x2 Hx.
rapply (@uc_wd _ _ (Cap_slow X Y)).
assumption.
Qed.

Add Parametric Morphism X Y : (@Cap_slow_fun X Y) with signature (@ms_eq _) ==> (@ms_eq _) ==> (@ms_eq _) as Cap_slow_wd.
intros x1 x2 Hx y1 y2 Hy.
transitivity (Cap_slow_fun x1 y2).
apply (@uc_wd _ _ (Cap_weak_slow x1) _ _ Hy).
generalize y2.
rapply (@uc_wd _ _ (Cap_slow X Y)).
assumption.
Qed.
Transparent Complete.
(* end hide *)

(** A binary version of map *)
Definition Cmap2_slow (X Y Z:MetricSpace) (f:X --> Y --> Z) := uc_compose (@Cap_slow Y Z) (Cmap_slow f).

(**
*** Completion and Classification
The completion operations preserve stability and locatedness, but
it does not preserve the decidability.
*)
Lemma Complete_stable : forall X, stableMetric X -> stableMetric (Complete X).
Proof.
intros X HX e x y Hb e1 e2.
apply HX.
intros H.
apply Hb.
intros H0.
apply H.
apply H0.
Qed.

Lemma Complete_located : forall X, locatedMetric X -> locatedMetric (Complete X).
Proof.
intros X Hx e d x y Hed.
destruct (Qpos_lt_plus Hed) as [c Hc].
set (c':=((1#5)*c)%Qpos).
assert (H:(c'+e+c')%Qpos < (e+(3#1)*c')%Qpos).
 abstract (
 rewrite Qlt_minus_iff;
 autorewrite with QposElim;
 ring_simplify;
 auto with *).
destruct (Hx _ _ (approximate x c') (approximate y c') H) as [H0 | H0].
 left.
 abstract (
 change (QposEq d (e+c)) in Hc;
 rewrite Hc;
 rewrite <- ball_Cunit in H0;
 (setoid_replace (e+c)%Qpos  with (c' + (e + (3 # 1) * c') + c')%Qpos by (unfold c';QposRing));
 eapply ball_triangle;[eapply ball_triangle;[|apply H0]|];
  [apply ball_approx_r|apply ball_approx_l]).
right.
abstract (
intros H1;
apply H0;
rewrite <- ball_Cunit;
eapply ball_triangle;[eapply ball_triangle;[|apply H1]|];
 [apply ball_approx_l|apply ball_approx_r]).
Defined.
