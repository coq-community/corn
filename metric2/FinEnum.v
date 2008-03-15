Require Export Hausdorff.
Require Import Classic.
Require Export List.
Require Export Classification.
Require Import Complete.
Require Import Prelength.
Require Import Basics.
Require Import Qauto.
Require Import CornTac.

Set Implicit Arguments.

Section Finite.

Variable X:MetricSpace.

Fixpoint InFinEnumC (x:X) (l:list X) : Prop :=
match l with 
| nil => False
| y::ys => orC (ms_eq x y) (InFinEnumC x ys)
end.

Lemma InFinEnumC_weaken : forall x l, (In x l) -> InFinEnumC x l.
Proof.
induction l.
 contradiction.
intros [H0|H0]; rapply orWeaken.
 left.
 rewrite H0.
 reflexivity.
right.
apply IHl.
assumption.
Qed.

Lemma InFinEnumC_wd1 : forall x y l, (ms_eq x y) -> (InFinEnumC x l <-> InFinEnumC y l).
Proof.
induction l.
 simpl; tauto.
intros H.
simpl.
cut ((ms_eq (m:=X) x a)<->(ms_eq (m:=X) y a)).
 unfold orC; tauto.
rewrite H.
reflexivity.
Qed.

Lemma InFinEnumC_stable : forall x l, ~~(InFinEnumC x l) -> InFinEnumC x l.
Proof.
induction l.
 simpl; auto.
intros H H0.
apply H.
clear H.
intros H.
destruct H as [HG | H | H] using orC_ind; tauto.
Qed.

Lemma InFinEnumC_app_l : forall x l1 l2, InFinEnumC x l1 -> InFinEnumC x (l1 ++ l2).
Proof.
intros x l1 l2 H.
induction l1.
 contradiction.
destruct H as [ G | H | H] using orC_ind.
  auto using InFinEnumC_stable.
 rapply orWeaken.
 left.
 auto.
rapply orWeaken.
right.
apply IHl1.
assumption.
Qed.

Lemma InFinEnumC_app_r : forall x l1 l2, InFinEnumC x l2 -> InFinEnumC x (l1 ++ l2).
Proof.
intros x l1 l2 H.
induction l1.
 assumption.
rapply orWeaken.
right.
apply IHl1.
Qed.

Hint Resolve InFinEnumC_app_l InFinEnumC_app_r.

Lemma InFinEnumC_app_orC : forall x l1 l2, InFinEnumC x (l1 ++ l2) -> orC (InFinEnumC x l1)  (InFinEnumC x l2).
Proof.
intros x l1 l2 H.
induction l1.
 apply orWeaken.
 right.
 assumption.
destruct H as [ G | H | H] using orC_ind.
  auto using orC_stable.
 rapply orWeaken.
 left.
 rapply orWeaken.
 left.
 assumption.
destruct (IHl1 H) as [ G | IH | IH] using orC_ind.
  auto using orC_stable.
 rapply orWeaken.
 left.
 rapply orWeaken.
 right.
 assumption.
rapply orWeaken.
right.
assumption.
Qed.

Definition FinEnum_eq (a b:list X) : Prop :=
 forall x, InFinEnumC x a <-> InFinEnumC x b.

Lemma FinEnum_eq_refl : forall a, FinEnum_eq a a.
Proof.
unfold FinEnum_eq.
reflexivity.
Qed.

Lemma FinEnum_eq_sym : forall a b, FinEnum_eq a b -> FinEnum_eq b a.
Proof.
unfold FinEnum_eq.
symmetry.
auto.
Qed.

Lemma FinEnum_eq_trans : forall a b c, FinEnum_eq a b -> FinEnum_eq b c -> FinEnum_eq a c.
Proof.
unfold FinEnum_eq.
intros a b c H0 H1 x.
transitivity (InFinEnumC x b); auto.
Qed.

Hint Resolve FinEnum_eq_refl FinEnum_eq_sym FinEnum_eq_trans : FinEnum.

Definition FinEnum_ball (e:Qpos) (x y:list X) := 
 hausdorffBall X e (fun a => InFinEnumC a x) (fun a => InFinEnumC a y).

Lemma FinEnum_ball_wd : forall (e1 e2:Qpos), (e1==e2) -> 
 forall a1 a2, FinEnum_eq a1 a2 ->
 forall b1 b2, FinEnum_eq b1 b2 ->
 (FinEnum_ball e1 a1 b1 <-> FinEnum_ball e2 a2 b2).
Proof.
intros e1 e2 He a1 a2 Ha b1 b2 Hb.
rapply hausdorffBall_wd; auto with *.
Qed.

Hypothesis Xstable : stableMetric X.

Lemma hemiMetric_closed : forall e A b,
 (forall d, hemiMetric X (e+d) A (fun a => InFinEnumC a b)) ->
  hemiMetric X e A (fun a => InFinEnumC a b).
Proof.
intros e A b H x Hx.
set (P:=fun n y => ball (e+(1#(P_of_succ_nat n)))%Qpos x y).
assert (HP:(forall n, existsC X (fun x => ~~In x b /\ P n x))).
 intros n.
 unfold P.
 destruct (H (1#(P_of_succ_nat n))%Qpos x Hx) as [HG | y [Hy0 Hy1]] using existsC_ind.
  apply existsC_stable; auto.
 clear - Hy0 Hy1.
 induction b.
  contradiction.
 destruct (Hy0) as [HG | Hy0 | Hy0] using orC_ind.
   apply existsC_stable; auto.
  apply existsWeaken.
  exists a.
  split; auto 7 with *.
  rewrite <- Hy0.
  assumption.   
 destruct (IHb Hy0) as [HG | z [Hz0 Hz1]] using existsC_ind.
  apply existsC_stable; auto.
 apply existsWeaken.
 exists z.
 split; auto 7 with *.
destruct 
 (infinitePidgeonHolePrinicple _ _ P HP) as [HG | y [Hy0 Hy1]] using existsC_ind.
 apply existsC_stable; auto.
apply existsWeaken.
exists y.
split; auto using InFinEnumC_weaken.
apply ball_closed.
intros [n d].
destruct (Hy1 (nat_of_P d)) as [HG | m [Hmd Hm]] using existsC_ind.
 apply Xstable; assumption.
eapply ball_weak_le;[|apply Hm].
autorewrite with QposElim.
rewrite Qle_minus_iff.
ring_simplify.
rewrite <- Qle_minus_iff.
rapply Zmult_le_compat; auto with *.
simpl.
repeat rewrite <- inject_nat_convert.
apply inj_le.
apply le_trans with m; auto.
rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
auto.
Qed.

Lemma FinEnum_ball_closed : forall e a b,
 (forall d, FinEnum_ball (e+d) a b) ->
 FinEnum_ball e a b.
Proof.
unfold FinEnum_ball, hausdorffBall.
intros e a b Hab.
split;
 apply hemiMetric_closed;
 firstorder.
Qed.
  
Lemma FinEnum_ball_eq : 
 forall a b : list X, (forall e : Qpos, FinEnum_ball e a b) -> FinEnum_eq a b.
Proof.
unfold FinEnum_ball, FinEnum_eq.
cut (forall a b : list X,
 (forall e : Qpos, hemiMetric X e (fun a0 : X => InFinEnumC a0 a)
   (fun a0 : X => InFinEnumC a0 b)) ->
 forall x : X, InFinEnumC x a -> InFinEnumC x b).
 unfold hausdorffBall.
 split; apply H; firstorder.
induction a.
 contradiction.
intros b H x Hx.
destruct Hx as [HG | Hx | Hx] using orC_ind.
  auto using InFinEnumC_stable.
 assert (H':forall n :nat ,
     existsC X (fun y : X => InFinEnumC y b /\ ball (m:=X) (1#(P_of_succ_nat n)) x y)).
  intros e.
  apply H.
  rapply orWeaken.
  left;  assumption.
 assert (H'':forall n :nat ,
     existsC X (fun y : X => ~~In y b /\ ball (m:=X) (1#(P_of_succ_nat n)) x y)).
  intros n.
  destruct (H' n) as [HG | z [Hz0 Hz1]] using existsC_ind.
   auto using existsC_stable.
  clear - Hz1 Hz0.
  induction b.
   contradiction.
  destruct (Hz0) as [Hg | Hz0 | Hz0] using orC_ind.
    auto using existsC_stable.
   apply existsWeaken.
   exists a.
   split; auto with *.
   rewrite <- Hz0.
   assumption.
  destruct (IHb Hz0) as [HG | y [Hy0 Hy1]] using existsC_ind.
   auto using existsC_stable.
  apply existsWeaken.
  exists y.
  split; auto 7 with *.
 destruct (infinitePidgeonHolePrinicple _ _ _ H'') as [HG | y [Hy0 Hy1]] using existsC_ind.
  auto using InFinEnumC_stable.
 rewrite (InFinEnumC_wd1 x y).
  apply ball_eq.
  intros [n d].
  rewrite (anti_convert_pred_convert d).
  destruct (Hy1 (pred (nat_of_P d))) as [HG | z [Hz0 Hz1]] using existsC_ind.
   auto using Xstable. 
  apply ball_weak_le with (1 # P_of_succ_nat z)%Qpos; auto.
  rapply Zmult_le_compat; auto with *.
  simpl.
  repeat rewrite <- POS_anti_convert.
  apply inj_le.
  auto with *.
 auto using InFinEnumC_weaken.
apply IHa; auto.
intros e y Hy.
apply H.
rapply orWeaken.
right.
assumption.
Qed.

Lemma FinEnum_is_MetricSpace : is_MetricSpace FinEnum_eq FinEnum_ball.
split.
     split; auto with *.
     apply FinEnum_eq_trans.
    intros e x.
    rapply hausdorffBall_refl.
   intros e x y.
   rapply hausdorffBall_sym.
  intros e d x y z.
  rapply hausdorffBall_triangle.
 intros e x y.
 unfold FinEnum_ball.
 rapply FinEnum_ball_closed.
apply FinEnum_ball_eq.
Qed.

Definition FinEnum : MetricSpace :=
Build_MetricSpace FinEnum_ball_wd FinEnum_is_MetricSpace.

Lemma FinEnum_stable : stableMetric FinEnum.
Proof.
intros e x y.
rapply hausdorffBall_stable.
Qed.

Lemma FinEum_map_ball : forall (f:X -> X) e (s:FinEnum), 
 (forall x, ball e x (f x)) -> ball e s (map f s).
Proof.
intros f e s H.
induction s.
 split; intros a b; contradiction.
destruct IHs as [IHs0 IHs1].
split;
 intros x y;
 (destruct y as [G | y | y] using orC_ind;
    [auto using existsC_stable
    |apply existsWeaken
    |]).
   exists (f a);split.
    rapply orWeaken; left; reflexivity.
   rewrite y; apply H.
  destruct (IHs0 x y) as [G | z [Hz0 Hz1]] using existsC_ind.
   auto using existsC_stable.
  apply existsWeaken.
  exists z.
  split; auto.
  rapply orWeaken.
  right; assumption.
 exists a.
 split.
  rapply orWeaken; left; reflexivity.
 apply ball_sym.
 rewrite y.
 apply H.
destruct (IHs1 x y) as [G | z [Hz0 Hz1]] using existsC_ind.
 auto using existsC_stable.
apply existsWeaken.
exists z.
split; auto.
rapply orWeaken.
right; assumption.
Qed.


Section Strong.

Hypothesis almostDecideX : locatedMetric X.

Lemma HemiMetricHemiMetricStrong : forall (e:Qpos) A b,
 hemiMetric X e A (fun a => InFinEnumC a b) -> hemiMetricStrong X e A (fun a => InFinEnumC a b).
Proof.
intros e A b H x Hx.
generalize (H x Hx).
clear H.
revert x Hx.
induction b; intros x Hx H d.
 elimtype False.
 clear -H.
 abstract (
 generalize H;
 apply existsC_ind;[tauto|];
 intros y [Hy0 Hy1];
 apply Hy0).
destruct (@almostDecideX e (e+d)%Qpos x a).
  clear - e d.
  abstract (
  autorewrite with QposElim;
  rewrite Qlt_minus_iff;
  ring_simplify;
  auto with * ).
 exists a.
 clear - b0.
 abstract (auto using InFinEnumC_weaken with *).
assert (Z:existsC X (fun y : X => InFinEnumC y b /\ ball (m:=X) e x y)).
 clear - H n.
 abstract (
 destruct (H) as [HG | y [Hy0 Hy1]] using existsC_ind;
  [auto using existsC_stable|];
 apply existsWeaken;
 exists y;
 split; auto;
 destruct Hy0 as [HG | Hy | Hy] using orC_ind;
  [auto using InFinEnumC_stable
  |rewrite Hy in Hy1; contradiction
  |assumption]).
exists (let (y,_) := (IHb x Hx Z d) in y).
clear - IHb.
abstract (
destruct (IHb x Hx Z d) as [y [Hy0 Hy1]];
split; auto;
rapply orWeaken;
auto).
Defined.

Lemma HausdorffBallHausdorffBallStrong : forall (e:Qpos) (a b:FinEnum),
 ball e a b -> 
 hausdorffBallStrong X e (fun x => InFinEnumC x a) (fun x => InFinEnumC x b).
Proof.
intros e a b [H0 H1].
split; apply HemiMetricHemiMetricStrong; assumption.
Defined.

Lemma HemiMetricStrongAlmostDecidableBody : 
 forall (e d:Qpos) a (b : FinEnum),
 e < d -> 
 {hemiMetric X d (fun x => ms_eq x a) (fun x => InFinEnumC x b)} + 
 {~hemiMetric X e (fun x => ms_eq x a) (fun x => InFinEnumC x b)}.
Proof.
intros e d a b.
induction b.
 intros Hed.
 right.
 abstract (
 intros H;
 apply (H a); try reflexivity;
 intros x [Hx0 Hx1];
 auto using InFinEnumC_weaken with *).
intros Hed.
destruct (IHb Hed) as [H|H].
 left.
 abstract (
 intros x Hx;
 destruct (H x Hx) as [HG | z [Hz0 Hz1]] using existsC_ind;
  [apply existsC_stable; auto|];
 apply existsWeaken;
 exists z;
 split; try assumption;
 rapply orWeaken;
 auto).
destruct (almostDecideX a a0 Hed).
 left.
 abstract (
 intros x Hx;
 apply existsWeaken;
 exists a0;
 rewrite Hx;
 auto using InFinEnumC_weaken with *).
right.
abstract (
intros H0;
assert (Haa:ms_eq a a) by reflexivity;
destruct (H0 a Haa) as [HG | z [Hz0 Hz1]] using existsC_ind;
 [tauto|];
destruct (Hz0) as [HG | Hz0 | Hz0] using orC_ind;
 [tauto
 |rewrite Hz0 in Hz1; contradiction
 |];
apply H;
intros x Hx;
apply existsWeaken;
exists z;
rewrite Hx;
auto).
Defined.
 
Lemma HemiMetricStrongAlmostDecidable : 
 forall (e d:Qpos) (a b : FinEnum),
 e < d -> 
 {hemiMetric X d (fun x => InFinEnumC x a) (fun x => InFinEnumC x b)} + 
 {~hemiMetric X e (fun x => InFinEnumC x a) (fun x => InFinEnumC x b)}.
Proof.
induction a.
 intros a _.
 left.
 intros x Hx _.
 apply Hx.
intros b Hed.   
destruct (IHa b Hed) as [I|I].
 destruct (HemiMetricStrongAlmostDecidableBody a b Hed) as [J|J].
  left.
  abstract (
  intros x Hx;
  destruct (Hx) as [HG | Hx | Hx] using orC_ind;
   [auto using existsC_stable
   |apply J; assumption
   |apply I; assumption]).
 right.
 abstract (
 intros H;
 apply J;
 intros x Hx;
 apply H;
 rapply orWeaken; left; assumption).
right.
abstract (
intros H;
apply I;
intros x Hx;
apply H;
rapply orWeaken; right; assumption).
Defined.

Lemma FinEnum_located : locatedMetric FinEnum.
Proof.
intros e d a b Hed.
destruct (HemiMetricStrongAlmostDecidable a b Hed).
 destruct (HemiMetricStrongAlmostDecidable b a Hed).
  left.
  split; assumption.
 right.
 abstract (intros [_ H]; contradiction).
right.
abstract (intros [H _]; contradiction).
Defined.

Hypothesis preLengthX : PrelengthSpace X.

Lemma FinEnum_prelength : PrelengthSpace FinEnum.
Proof.
intros a b e.
revert a b.
cut (forall d1 d2 : Qpos,
       e < d1 + d2 -> 
      forall (a b:FinEnum), hemiMetricStrong X e (fun x : X => InFinEnumC x a)
       (fun x : X => InFinEnumC x b) ->
exists2 c : FinEnum, ball d1 a c &  hemiMetric X d2 (fun x : X => InFinEnumC x c) (fun x : X => InFinEnumC x b)).
 intros Z a b d1 d2 He H.
 destruct (HausdorffBallHausdorffBallStrong H) as [Hl Hr].
 clear H.
 destruct (Z _ _ He _ _ Hl) as [c0 Hc0 Hc0c].
 assert (He0:e < d2 + d1).
  clear - He.
  abstract (rewrite Qplus_comm; assumption).
 destruct (Z _ _ He0 _ _ Hr) as [c1 Hc1 Hc1c].
 clear Z Hl Hr.
 exists (c0 ++ c1).
  abstract (
  destruct Hc0 as [Hc0a Hc0b];
  destruct Hc1 as [Hc1a Hc1b];
  split; intros x Hx;
   [destruct (Hc0a x Hx) as [ G | y [Hya Hyb]] using existsC_ind;
     [auto using existsC_stable | apply existsWeaken; exists y; auto]
   |destruct (InFinEnumC_app_orC _ _ _ Hx) as [G | Hxl | Hxr] using orC_ind;
    [auto using existsC_stable
    |destruct (Hc0b x Hxl) as [ G | y [Hya Hyb]] using existsC_ind;
     [auto using existsC_stable | apply existsWeaken; exists y; auto]
    |destruct (Hc1c x Hxr) as [ G | y [Hya Hyb]] using existsC_ind;
     [auto using existsC_stable | apply existsWeaken; exists y; auto]]]).
 abstract (
  destruct Hc0 as [Hc0a Hc0b];
  destruct Hc1 as [Hc1a Hc1b];
  split; intros x Hx;
   [destruct (InFinEnumC_app_orC _ _ _ Hx) as [G | Hxl | Hxr] using orC_ind;
    [auto using existsC_stable 
    |destruct (Hc0c x Hxl) as [ G | y [Hya Hyb]] using existsC_ind;
     [auto using existsC_stable | apply existsWeaken; exists y; auto]
    |destruct (Hc1b x Hxr) as [ G | y [Hya Hyb]] using existsC_ind;
     [auto using existsC_stable | apply existsWeaken; exists y; auto]]
   |destruct (Hc1a x Hx) as [ G | y [Hya Hyb]] using existsC_ind;
    [auto using existsC_stable | apply existsWeaken; exists y; auto]]).
intros d1 d2 He a b H.
induction a.
 exists nil.
  apply ball_refl.
 intros x Hx; elim Hx.
destruct IHa as [c1 Hc1a Hc1b].
 abstract (
 intros x Hx d;
 apply (H x);
 rapply orWeaken;
 right; auto).
destruct (Qpos_lt_plus He) as [g Hg].
destruct (fun z => H a z ((1#2)*g)%Qpos) as [b0 Hb0].
 abstract (rapply orWeaken; left; reflexivity).
clear H.
destruct (@preLengthX a b0 (e + (1 # 2) * g)%Qpos d1 d2) as [c Hc0 Hc1].
  abstract ( clear - Hg;
  rewrite Hg;
  autorewrite with QposElim;
  rewrite Qlt_minus_iff;
  ring_simplify;
  Qauto_pos).
 abstract (clear - Hb0; destruct Hb0; auto).
exists (c :: c1).
 abstract (
 split; intros x Hx;
 [destruct Hx as [ G | Hx | Hx ] using orC_ind;
   [auto using existsC_stable
   |apply existsWeaken;
    exists c;
    split;
     [rapply orWeaken;left; reflexivity
     |rewrite Hx; auto]
   |destruct Hc1a as [Hc1a _];
    destruct (Hc1a x Hx) as [ G | y [Hy0 Hy1]] using existsC_ind;
     [auto using existsC_stable|];
    apply existsWeaken;
    exists y;
    split; auto;
    rapply orWeaken;
    right; auto]
 |destruct Hx as [ G | Hx | Hx ] using orC_ind;
   [auto using existsC_stable
   |apply existsWeaken;
   exists a;
    split;
     [rapply orWeaken;left; reflexivity
     |rewrite Hx; auto with *]
   |destruct Hc1a as [_ Hc1a];
    destruct (Hc1a x Hx) as [ G | y [Hy0 Hy1]] using existsC_ind;
     [auto using existsC_stable|];
    apply existsWeaken;
    exists y;
    split; auto;
    rapply orWeaken;
    right; auto]]).
abstract (
destruct Hb0 as [Hb0a Hb0b];
intros x Hx;
destruct Hx as [ G | Hx | Hx ] using orC_ind;
[auto using existsC_stable
|apply existsWeaken;
 exists b0;
 split; auto;
 rewrite Hx; auto
|apply Hc1b; auto]).
Defined.


End Strong.

End Finite.

Implicit Arguments InFinEnumC [X].

Lemma FinEnum_eq_rev : forall X (stable: stableMetric X) (f:FinEnum stable),
 ms_eq f (rev f).
Proof.
induction f.
 reflexivity.
intros x.
destruct (IHf x) as [H0 H1].
split; simpl; intros H.
 destruct H as [G|H|H] using orC_ind.
   auto using InFinEnumC_stable.
  apply InFinEnumC_app_r.
  rapply orWeaken.
  left; auto.
 apply InFinEnumC_app_l.
 auto.
destruct (InFinEnumC_app_orC _ _ _ _ H) as [G |A | A] using orC_ind.
  auto using orC_stable.
 apply orWeaken.
 right.
 auto.
destruct A as [G | A| A] using orC_ind.
  auto using orC_stable.
 apply orWeaken.
 left; auto.
contradiction.
Qed.

Open Local Scope uc_scope.

Lemma InFinEnumC_map : forall (X Y:MetricSpace) (f:X --> Y) a l, InFinEnumC a l -> InFinEnumC (f a) (map f l).
induction l.
 auto.
intros Ha.
destruct Ha as [G | Ha | Ha] using orC_ind.
  auto using InFinEnumC_stable.
 rapply orWeaken.
 left.
 rewrite Ha; reflexivity.
rapply orWeaken.
right.
apply IHl.
auto.
Qed.

Definition FinEnum_map_modulus (z:Qpos) (muf : Qpos -> QposInf) (e:Qpos) :=
match (muf e) with
| QposInfinity => z
| Qpos2QposInf d => d
end.

(* if a is empty and b is not, then (map f a) and (map f b) are not equivalent,
 even if f is the constant function *)
Lemma FinEnum_map_uc : forall z X Y (SX:stableMetric X) (SY:stableMetric Y) (f:X --> Y), is_UniformlyContinuousFunction (map f:FinEnum SX -> FinEnum SY) (FinEnum_map_modulus z (mu f)).
Proof.
intros z X Y SX SY f e.
cut (forall (a b : FinEnum SX) (d:Qpos), (QposInf_le d (mu f e)) ->
 ball d a b -> ball (m:=FinEnum SY) e (map f a) (map f b)).
 intros Z a b.
 case_eq (mu f e).
  intros d Hd H.
  apply Z with d; auto.
  rewrite Hd.
  simpl; auto with *.
 intros He H.
 apply Z with z; auto.
 rewrite He.
 constructor.
revert e.
cut (forall (e d:Qpos), (QposInf_le d (mu f e)) -> forall (s1 s2 : FinEnum SX),
  hemiMetric X d (fun a => InFinEnumC a s1) (fun a => InFinEnumC a s2) ->
  hemiMetric Y e (fun a => InFinEnumC a (map f s1:FinEnum SY))
   (fun a => InFinEnumC a (map f s2))).
 intros Z e s1 s2 d Hd [H0 H1].
 split; apply (Z e d Hd); assumption.
intros e d Hd s1 s2.
intros H a Ha.
induction s1.
 contradiction.
destruct Ha as [G | Ha | Ha] using orC_ind.
  auto using existsC_stable.
 assert (Ha0:InFinEnumC a0 (a0::s1)).
  rapply orWeaken.
  left; reflexivity.
 destruct (H a0 Ha0) as [G | y [Hy0 Hy1]] using existsC_ind.
  auto using existsC_stable.
 apply existsWeaken.
 exists (f y).
 split.
  apply InFinEnumC_map; assumption.
 rewrite Ha.
 apply (uc_prf f).
 apply ball_ex_weak_le with d; auto.
apply IHs1; auto.
intros b Hb.
 apply H.
rapply orWeaken.
right; assumption.
Qed.

Implicit Arguments FinEnum_map_uc [X Y].

Definition FinEnum_map z X Y (SX:stableMetric X) (SY:stableMetric Y) (f:X --> Y) :=
 Build_UniformlyContinuousFunction (FinEnum_map_uc z SX SY f).

Lemma FinEnum_map_Cunit : forall X (SX:stableMetric X) SCX (s1 s2:FinEnum SX) e, ball e s1 s2 <-> ball e (map Cunit s1:FinEnum SCX) (map Cunit s2).
Proof.
intros X SX SCX s1 s2 e.
split.
 intros H.
 rapply (@FinEnum_map_uc (1#1) _ _ SX SCX).
 assumption.
revert s1 s2.
cut (forall (s1 s2 : FinEnum SX) ,
   hemiMetric (Complete X) e (fun a => InFinEnumC a (map Cunit s1:FinEnum SCX))
    (fun a => InFinEnumC a (map Cunit s2)) ->
   hemiMetric X e (fun a => InFinEnumC a s1) (fun a => InFinEnumC a s2)).
 intros Z s1 s2.
 intros [H0 H1].
 split; apply Z; assumption.
intros s1 s2 H a Ha.
induction s1.
 contradiction.
destruct Ha as [G | Ha | Ha] using orC_ind.
  auto using existsC_stable.
 clear IHs1.
 assert (Ha0:InFinEnumC (Cunit a0) (map Cunit (a0::s1))).
  rapply orWeaken.
  left; reflexivity.
 destruct (H _ Ha0) as [G | y [Hy0 Hy1]] using existsC_ind.
  auto using existsC_stable.
 clear - Ha Hy0 Hy1.
 induction s2.
  contradiction.
 destruct Hy0 as [G | Hy0 | Hy0] using orC_ind.
   auto using existsC_stable.
  apply existsWeaken.
  exists a1.
  split.
   rapply orWeaken.
   left; reflexivity.
  rewrite Ha.
  rewrite <- ball_Cunit.
  rewrite <- Hy0.
  assumption.
 destruct (IHs2 Hy0) as [G | z [Hz0 Hz1]] using existsC_ind.
  auto using existsC_stable.
 apply existsWeaken.
 exists z.
 split; auto.
 rapply orWeaken.
 right; assumption.
apply IHs1; auto.
intros b Hb.
apply H.
rapply orWeaken.
right; assumption.
Qed.