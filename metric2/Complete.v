Require Export UniformContinuity.
Require Export QposInf.
Require Import QposMinMax.
Require Import Qordfield.
Require Import COrdFields2.
Require Import CornTac.

Set Implicit Arguments.

Open Local Scope uc_scope.

Section RegularFunction.

Variable X:MetricSpace.

Definition is_RegularFunction (x:QposInf -> X) : Prop :=
 forall (e1 e2:Qpos), ball (m:=X) (e1+e2) (x e1) (x e2).

Record RegularFunction : Type :=
{approximate : QposInf -> X
;regFun_prf : is_RegularFunction approximate
}.

Definition regFunEq (f g : RegularFunction) :=
 forall e1 e2, ball (m:=X) (e1+e2) (approximate f e1) (approximate g e2).

Lemma regFunEq_e : forall (f g : RegularFunction), (forall e, ball (m:=X) (e+e) (approximate f e) (approximate g e)) -> (regFunEq f g).
Proof.
unfold regFunEq.
intros f g H e1 e2.
apply ball_closed.
Set Implicit Arguments.

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
intros; apply regFunEq_e; intros; apply ball_refl.
unfold regFunEq.
intros.
apply ball_sym.
setoid_replace (e1+e2)%Qpos with (e2+e1)%Qpos by QposRing.
auto.
unfold regFunEq.
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
apply H1.
apply Seq_sym.
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

Definition Complete : MetricSpace :=
Build_MetricSpace regFunBall_wd regFun_is_MetricSpace.

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

Hypothesis Xpl : PrelengthSpace X.

Lemma CompletePL : PrelengthSpace Complete.
Proof.
intros x y e d1 d2 He Hxy.
setoid_replace (d1+d2) with ((d1+d2)%Qpos:Q) in He by QposRing.
destruct (Qpos_lt_plus He).
pose (gA := ((1#5)*x0)%Qpos).
pose (g := Qpos_min (Qpos_min ((1#2)*d1) ((1#2)*d2)) gA).
unfold PrelengthSpace in Xpl.
assert (Hd1:g < d1).
unfold g.
eapply Qle_lt_trans.
apply Qpos_min_lb_l.
eapply Qle_lt_trans.
apply Qpos_min_lb_l.
rapply (half_3 _ (d1:Q)).
apply Qpos_prf. 
assert (Hd2:g < d2).
unfold g.
eapply Qle_lt_trans.
apply Qpos_min_lb_l.
eapply Qle_lt_trans.
apply Qpos_min_lb_r.
rapply (half_3 _ (d2:Q)).
apply Qpos_prf.
destruct (Qpos_lt_plus Hd1) as [d1' Hd1'].
destruct (Qpos_lt_plus Hd2) as [d2' Hd2'].
assert (He':(g + e + g)%Qpos < d1' + d2').
rsapply plus_cancel_less.
instantiate (1:= (g+g)).
replace RHS with ((g+d1')%Qpos+(g+d2')%Qpos) by QposRing.
unfold QposEq in *.
rewrite <- Hd1'.
rewrite <- Hd2'.
clear d1' Hd1' d2' Hd2'.
apply Qle_lt_trans with (e + 4*gA).
replace LHS with (e+4*g) by (unfold inject_Z;QposRing).
rsapply plus_resp_leEq_lft.
rsapply mult_resp_leEq_lft.
rapply Qpos_min_lb_r.
compute; discriminate.
replace RHS with ((d1+d2)%Qpos:Q) by QposRing.
rewrite q.
replace RHS with (e+1*x0) by QposRing.
rsapply plus_resp_less_lft.
replace LHS with ((4#5)*x0) by (unfold inject_Z, gA;QposRing).
rsapply mult_resp_less.
constructor.
apply Qpos_prf.
destruct (Xpl _ _ He' (Hxy g g)) as [c Hc1 Hc2].
exists (Cunit c).
rewrite <- Q_Qpos_plus in Hd1'.
change (QposEq d1 (g + d1')) in Hd1'.
rewrite Hd1'.
eapply ball_triangle.
apply ball_approx_r.
rewrite ball_Cunit.
assumption.
rewrite <- Q_Qpos_plus in Hd2'.
change (QposEq d2 (g + d2')) in Hd2'.
rewrite Hd2'.
setoid_replace (g + d2')%Qpos with (d2' + g)%Qpos by QposRing.
eapply ball_triangle with (Cunit (approximate y g)).
rewrite ball_Cunit.
assumption.
apply ball_approx_l.
Qed.

End RegularFunction.

Implicit Arguments is_RegularFunction [X].

Implicit Arguments Cunit [X].

Add Morphism Cunit_fun with signature ms_eq ==> ms_eq as Cunit_wd.
intros X.
exact (@uc_wd _ _ Cunit).
Qed.

Section Cjoin.

Variable X : MetricSpace.

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
(* apply totally sucks *)
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

(* I never got Cmap_prf for this definition of map *)
(*
Section Cmap.

Variable X Y : MetricSpace.
Variable f : X --> Y.

Definition Cmap_raw (x:Complete X) (e:QposInf) :=
f (x (QposInf_mult (1#2)%Qpos (QposInf_bind (mu f) e))).

Lemma Cmap_raw_strong : forall (x:Complete X) (d e:Qpos), QposInf_le d (QposInf_mult (1#2)%Qpos (mu f e)) ->
ball e (f (x d)) (Cmap_raw x e).
Proof.
intros x d e Hd.
rapply uc_prf.
simpl.
case_eq (mu f e); simpl; trivial.
intros q Hq.
rewrite Hq in Hd.
eapply ball_weak_le;[|apply regFun_prf].
rewrite Q_Qpos_plus.
replace RHS with (((1 # 2) * q)%Qpos + ((1 # 2) * q)%Qpos) by QposRing.
rsapply plus_resp_leEq.
assumption.
Qed.

Lemma Cmap_fun_prf (x:Complete X) : is_RegularFunction (fun e => f (x (QposInf_mult (1#2)%Qpos (QposInf_bind (mu f) e)))).
Proof.
intros x e1 e2.
cut (forall (e1 e2:Qpos), (QposInf_le (mu f e2) (mu f e1)) -> ball (m:=Y) (e1 + e2)
  (f (x (QposInf_mult (1 # 2)%Qpos (QposInf_bind (mu f) e1))))
  (f (x (QposInf_mult (1 # 2)%Qpos (QposInf_bind (mu f) e2))))).
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
case_eq (mu f e2); simpl.
intros r Hr.
rewrite Hr in *|-*.
apply ball_sym.
simpl.
rapply Cmap_raw_strong.
destruct (mu f e1).
simpl.
rsapply mult_resp_leEq_lft.
assumption.
discriminate.
constructor.
intros Hr.
rewrite Hr in H.
rapply uc_prf.
destruct (mu f e1).
elim H.
constructor.
Qed.

Definition Cmap_fun (x:Complete X) : Complete Y :=
Build_RegularFunction (Cmap_fun_prf x).

Definition Cmap_prf : is_UniformlyContinuousFunction Cmap_fun (mu f).
Proof.
intros e0 x y Hxy.
intros e1 e2.
apply ball_closed.
intros d.
cut (QposInf_le (mu f e0) (mu f (e0+d))).
intros mono.
case_eq (mu f e0).
intros e0' He0.
rewrite He0 in Hxy.
Focus 2.
intros H.
rewrite H in mono.
simpl in mono.

let g:=Qmin (mu f e0) (mu f e1)
simpl.
rapply (uc_prf f).


End Cmap.
*)

Section Cmap.

Variable X Y : MetricSpace.
Hypothesis Xpl : PrelengthSpace X.

Variable f : X --> Y.

Definition Cmap_raw (x:Complete X) (e:QposInf) :=
f (approximate x (QposInf_bind (mu f) e)).

Lemma Cmap_fun_prf (x:Complete X) : is_RegularFunction (fun e => f (approximate x (QposInf_bind (mu f) e))).
Proof.
intros x e1 e2.
simpl.
apply (mu_sum (Y:=Y) Xpl e2 (e1::nil)).
simpl.
destruct (mu f e1) as [d1|].
destruct (mu f e2) as [d2|].
rapply regFun_prf.
constructor.
constructor.
Qed.

Definition Cmap_fun (x:Complete X) : Complete Y :=
Build_RegularFunction (Cmap_fun_prf x).

Lemma Cmap_prf : is_UniformlyContinuousFunction Cmap_fun (mu f).
Proof.
intros e0 x y Hxy e1 e2.
simpl.
setoid_replace (e1+e0+e2)%Qpos with (e1+(e0+e2))%Qpos by QposRing.
apply (mu_sum (Y:=Y) Xpl e2 (e1::e0::nil)).
simpl.
destruct (mu f e1) as [d1|];[|constructor].
destruct (mu f e0) as [d0|];[|constructor].
destruct (mu f e2) as [d2|];[|constructor].
simpl in *.
setoid_replace (d1+(d0+d2))%Qpos with (d1+d0+d2)%Qpos by QposRing.
apply Hxy.
Qed.

Definition Cmap : (Complete X) --> (Complete Y) :=
Build_UniformlyContinuousFunction Cmap_prf.

End Cmap.

Definition Cbind (X Y:MetricSpace) (Xpl : PrelengthSpace X) f := uc_compose (Cjoin (X:=Y)) (Cmap Xpl f).

Section Monad_Laws.

Variable X Y Z : MetricSpace.
Hypothesis Xpl : PrelengthSpace X.
Hypothesis CXpl : PrelengthSpace (Complete X).
Hypothesis CCXpl : PrelengthSpace (Complete (Complete X)).
Hypothesis Ypl : PrelengthSpace Y.

Notation "a =m b" := (ms_eq a b)  (at level 70, no associativity).

Lemma MonadLaw1 : forall a, Cmap_fun Xpl (uc_id X) a =m a.
Proof.
intros x e1 e2.
simpl.
rapply regFun_prf.
Qed.

Lemma MonadLaw2 : forall (f:Y --> Z) (g:X --> Y) a, Cmap_fun Xpl (uc_compose f g) a =m (Cmap_fun Ypl f (Cmap_fun Xpl g a)).
Proof.
simpl.
intros f g x e1 e2.
rapply regFun_prf.
Qed.

Lemma MonadLaw3 : forall (f:X --> Y) a, (Cmap_fun Xpl f (Cunit_fun _ a)) =m (Cunit_fun _ (f a)).
Proof.
intros f x e1 e2.
rapply regFun_prf.
Qed.

Lemma MonadLaw4 : forall (f:X --> Y) a, (Cmap_fun Xpl f (Cjoin_fun a)) =m (Cjoin_fun ((Cmap_fun CXpl (Cmap Xpl f)) a)).
Proof.
intros f x e1 e2.
set (e2' := ((1#2)*e2)%Qpos).
set (d1 := mu f e1).
set (d2 := mu f e2').
set (a := approximate (approximate x ((1#2)%Qpos*d1)%QposInf) ((1#2)%Qpos*d1)%QposInf).
set (b := approximate (approximate x d2) d2).
change (ball (e1+e2) (f a) (f b)).
setoid_replace (e2)%Qpos with (e2'+e2')%Qpos by (unfold e2'; QposRing).
apply (mu_sum (Y:=Y) Xpl e2' (e1::e2'::nil)).
simpl.
fold d2.
fold d1.
destruct d1 as [d1|];[|constructor].
destruct d2 as [d2|];[|constructor].
simpl in *.
set (d1' := ((1#2)*d1)%Qpos).
setoid_replace (d1 + (d2 +d2))%Qpos with (d1' + (d1' + d2) + d2)%Qpos by (unfold d1';QposRing).
rapply (regFun_prf x).
Qed.

Lemma MonadLaw5 : forall a, (Cjoin_fun (X:=X) (Cunit_fun _ a)) =m a.
intros x e1 e2.
simpl.
setoid_replace (e1+e2)%Qpos with ((1#2)*e1 + e2 + (1#2)*e1)%Qpos by QposRing.
apply ball_weak.
rapply regFun_prf.
Qed.

Lemma MonadLaw6 : forall a, Cjoin_fun ((Cmap_fun Xpl Cunit) a) =m a.
Proof.
apply MonadLaw5.
Qed.

Lemma MonadLaw7 : forall a, Cjoin_fun ((Cmap_fun CCXpl Cjoin) a) =m Cjoin_fun (Cjoin_fun a).
Proof.
intros x e1 e2.
pose (half := fun e:Qpos => ((1#2)*e)%Qpos).
setoid_replace (e1+e2)%Qpos with ((half (half e1)) + ((half (half e1)) + (half e1 + (half (half e2))) + (half (half e2))) + (half e2))%Qpos by (unfold half; QposRing).
rapply (regFun_prf x).
Qed.

End Monad_Laws.

Section Faster.

Variable X : MetricSpace.
Variable x : Complete X.

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

Section Strong_Monad.

Variable X Y : MetricSpace.
Hypothesis Xpl : PrelengthSpace X.
Let X_Y := UniformlyContinuousSpace X Y.
Let CX_CY := UniformlyContinuousSpace (Complete X) (Complete Y).

Lemma Cmap_strong_prf : is_UniformlyContinuousFunction ((Cmap (Y:=Y) Xpl):(X_Y -> CX_CY)) Qpos2QposInf.
Proof.
intros e f g H x.
apply ball_closed.
intros e0.
set (he0 := ((1#2)*e0)%Qpos).
set (d0 := QposInf_min (mu f he0) (mu g he0)).
set (a0 := approximate x d0).
setoid_replace (e+e0)%Qpos with (he0 + e + he0)%Qpos by (unfold he0;QposRing).
apply ball_triangle with (Cunit (g a0)).
apply ball_triangle with (Cunit (f a0)).
rewrite <- (MonadLaw3 Xpl f a0).
rapply uc_prf.
simpl.
destruct (mu f he0) as [d1|];[|constructor].
eapply ball_ex_weak_le with d0.
rapply QposInf_min_lb_l.
destruct d0 as [d0|];[|constructor].
rapply ball_approx_r.
rewrite ball_Cunit.
apply H.
rewrite <- (MonadLaw3 Xpl g a0).
rapply (uc_prf (Cmap Xpl g)).
simpl.
destruct (mu g he0) as [d2|];[|constructor].
eapply ball_ex_weak_le with d0.
rapply QposInf_min_lb_r.
destruct d0 as [d0|];[|constructor].
rapply ball_approx_l.
Qed.

Definition Cmap_strong : (X --> Y) --> (Complete X --> Complete Y) :=
Build_UniformlyContinuousFunction Cmap_strong_prf.

Definition Cap_raw (f:Complete (X --> Y)) (x:Complete X) (e:QposInf) :=
 approximate (Cmap Xpl (approximate f ((1#2)%Qpos*e)%QposInf) x) ((1#2)%Qpos*e)%QposInf.

Lemma Cap_fun_prf (f:Complete (X --> Y)) (x:Complete X) : is_RegularFunction (Cap_raw f x).
Proof.
intros f x e1 e2.
unfold Cap_raw.
unfold QposInf_mult, QposInf_bind.
set (he1 := ((1 # 2) * e1)%Qpos).
set (he2 := ((1 # 2) * e2)%Qpos).
set (f1 := (approximate f he1)).
set (f2 := (approximate f he2)).
change (Cmap (Y:=Y) Xpl f1) with (Cmap_strong f1).
change (Cmap (Y:=Y) Xpl f2) with (Cmap_strong f2).
set (y1 :=(Cmap_strong f1 x)).
set (y2 :=(Cmap_strong f2 x)).
setoid_replace (e1 + e2)%Qpos with (he1 + (he1 + he2) + he2)%Qpos by (unfold he1, he2; QposRing).
rewrite <- ball_Cunit.
apply ball_triangle with y2;[|apply ball_approx_r].
apply ball_triangle with y1;[apply ball_approx_l|].
rapply (uc_prf Cmap_strong).
rapply regFun_prf.
Qed.

Definition Cap_fun (f:Complete (X --> Y)) (x:Complete X) : Complete Y :=
Build_RegularFunction (Cap_fun_prf f x).

Lemma Cap_help (f:Complete (X --> Y)) (x:Complete X) (e:Qpos) : 
 ball e (Cap_fun f x) (Cmap Xpl (approximate f e) x).
Proof.
intros f x e d1 d2.
set (d1' := ((1 # 2) * d1)%Qpos).
set (f1 := (approximate f d1')).
set (f2 := (approximate f e)).
set (y1 := (Cmap Xpl f1 x)).
set (y2 := (Cmap Xpl f2 x)).
change (ball (d1 + e + d2) (approximate y1 d1') (approximate y2 d2)).
setoid_replace (d1 + e + d2)%Qpos with (d1' + (d1' + e) + d2)%Qpos by (unfold d1'; QposRing).
rewrite <- ball_Cunit.
apply ball_triangle with y2;[|apply ball_approx_r].
apply ball_triangle with y1;[apply ball_approx_l|].
rapply (uc_prf Cmap_strong).
rapply regFun_prf.
Qed.

Definition Cap_modulus (f:Complete (X --> Y)) (e:Qpos) : QposInf := (mu (approximate f ((1#3)*e)%Qpos) ((1#3)*e)).

Lemma Cap_weak_prf (f:Complete (X --> Y)) : is_UniformlyContinuousFunction (Cap_fun f) (Cap_modulus f).
Proof.
intros f e x y H.
set (e' := ((1#3)*e)%Qpos).
setoid_replace e with (e'+e'+e')%Qpos by (unfold e';QposRing).
apply ball_triangle with (Cmap Xpl (approximate f e') y).
apply ball_triangle with (Cmap Xpl (approximate f e') x).
apply Cap_help.
rapply (uc_prf).
apply H.
apply ball_sym.
apply Cap_help.
Qed.

Definition Cap_weak (f:Complete (X --> Y)) : Complete X --> Complete Y :=
Build_UniformlyContinuousFunction (Cap_weak_prf f).

Lemma Cap_prf : is_UniformlyContinuousFunction Cap_weak Qpos2QposInf.
Proof.
intros e f1 f2 H x.
apply ball_closed.
intros d.
setoid_replace (e+d)%Qpos with ((1#4)*d + ((1#4)*d + e + (1#4)*d) + (1#4)*d)%Qpos by QposRing.
apply ball_triangle with (Cmap_strong (approximate f2 ((1#4)*d)%Qpos) x).
apply ball_triangle with (Cmap_strong (approximate f1 ((1#4)*d)%Qpos) x).
rapply Cap_help.
rapply (uc_prf Cmap_strong).
rapply H.
apply ball_sym.
rapply Cap_help.
Qed.

Definition Cap : Complete (X --> Y) --> Complete X --> Complete Y :=
Build_UniformlyContinuousFunction Cap_prf.

Lemma StrongMonadLaw1 : forall a b, ms_eq (Cap_fun (Cunit_fun _ a) b) (Cmap_strong a b).
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

Opaque Complete.
Add Morphism Cmap_fun with signature ms_eq ==> ms_eq ==> ms_eq as Cmap_wd.
intros X Y H.
intros x1 x2 Hx y1 y2 Hy.
transitivity (Cmap_fun H x1 y2).
apply (@uc_wd _ _ (Cmap H x1) _ _ Hy).
generalize y2.
rapply (@uc_wd _ _ (Cmap_strong Y H)).
assumption.
Qed.

Add Morphism Cap_weak with signature ms_eq ==> ms_eq as Cap_weak_wd.
intros X Y H.
intros x1 x2 Hx.
rapply (@uc_wd _ _ (Cap Y H)).
assumption.
Qed.

Add Morphism Cap_fun with signature ms_eq ==> ms_eq ==> ms_eq as Cap_wd.
intros X Y H.
intros x1 x2 Hx y1 y2 Hy.
transitivity (Cap_fun H x1 y2).
apply (@uc_wd _ _ (Cap_weak H x1) _ _ Hy).
generalize y2.
rapply (@uc_wd _ _ (Cap Y H)).
assumption.
Qed.
Transparent Complete.

Definition Cmap2 (X Y Z:MetricSpace) (Xpl : PrelengthSpace X) (Ypl : PrelengthSpace Y) f := uc_compose (@Cap Y Z Ypl) (Cmap Xpl f).
