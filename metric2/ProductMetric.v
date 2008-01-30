Require Export Metric.
Require Import Setoid.
Require Import Classification.
Require Import CornTac.

Set Implicit Arguments.

Section ProductMetric.

Variable X Y : MetricSpace.

Definition prod_ms_eq (a b:X*Y) :=
ms_eq (fst a) (fst b) /\ ms_eq (snd a) (snd b).

Lemma prodST : Setoid_Theory _ prod_ms_eq.
Proof.
split; unfold prod_ms_eq.
  intros; split; reflexivity.
 intros x y [H1 H2]; split; symmetry; assumption.
intros x y z [H1 H2] [H3 H4]; split.
 transitivity (fst y); assumption.
transitivity (snd y); assumption.
Qed.

Definition prod_ball e (a b:X*Y) :=
ball e (fst a) (fst b) /\ ball e (snd a) (snd b).

Lemma prod_ball_refl : forall e a, prod_ball e a a.
Proof.
intros e a.
split; auto with *.
Qed.

Lemma prod_ball_sym : forall e a b, prod_ball e a b -> prod_ball e b a.
Proof.
intros e a b [H1 H2].
split; auto with *.
Qed.

Lemma prod_ball_triangle : forall e1 e2 a b c, prod_ball e1 a b -> prod_ball e2 b c -> prod_ball (e1 + e2) a c.
Proof.
intros e1 e2 a b c [H1 H2] [H3 H4].
split; eauto with metric.
Qed.

Lemma prod_ball_closed : forall e a b, (forall d, prod_ball (e + d) a b) -> prod_ball e a b.
Proof.
intros e a b H.
unfold prod_ball in *.
split; apply ball_closed; firstorder.
Qed.

Lemma prod_ball_eq : forall a b, (forall e, prod_ball e a b) -> prod_ms_eq a b.
Proof.
intros a b H.
unfold prod_ball in *.
split; apply ball_eq; firstorder.
Qed.

Lemma prod_is_MetricSpace : is_MetricSpace prod_ms_eq prod_ball.
Proof.
split.
     apply prodST.
    rapply prod_ball_refl.
   rapply prod_ball_sym.
  rapply prod_ball_triangle.
 rapply prod_ball_closed.
rapply prod_ball_eq.
Qed.

Definition ProductMS : MetricSpace.
exists (X*Y)%type prod_ms_eq prod_ball.
 abstract (
 intros e1 e2 He a1 a2 [Ha0 Ha1] b1 b2 [Hb0 Hb1];
 unfold prod_ball;
 change (QposEq e1 e2) in He;
 rewrite He, Ha0, Ha1, Hb0, Hb1;
 reflexivity) using prod_ball_wd.
apply prod_is_MetricSpace.
Defined.

Lemma ProductMS_prelength : PrelengthSpace X -> PrelengthSpace Y -> PrelengthSpace ProductMS.
Proof.
intros HX HY a b e d1 d2 Hed Hab.
destruct (HX (fst a) (fst b) e d1 d2 Hed (proj1 Hab)) as [c1 Hc1].
destruct (HY (snd a) (snd b) e d1 d2 Hed (proj2 Hab)) as [c2 Hc2].
exists (c1,c2); split; assumption.
Defined.

Lemma ProductMS_stable : stableMetric X -> stableMetric Y -> stableMetric ProductMS.
Proof.
unfold stableMetric.
intros H0 H1 e [xl xr] [yl yr] H.
simpl in H.
unfold prod_ball in H.
split.
 apply H0; tauto.
apply H1; tauto.
Qed.

Lemma ProductMS_stableX : Y -> stableMetric ProductMS -> stableMetric X.
Proof.
unfold stableMetric.
intros a H0 e x y H.
assert (Z:~ ~ ball (m:=ProductMS) e (x,a) (y,a)).
 revert H.
 cut (ball (m:=X) e x y ->
 ball (m:=ProductMS) e (Basics.Pair x a) (Basics.Pair y a)).
  tauto.
 intros H.
 split; auto.
 apply ball_refl.
destruct (H0 _ _ _ Z).
assumption.
Qed.

Lemma ProductMS_stableY : X -> stableMetric ProductMS -> stableMetric Y.
Proof.
unfold stableMetric.
intros a H0 e x y H.
assert (Z:~ ~ ball (m:=ProductMS) e (a,x) (a,y)).
 revert H.
 cut (ball (m:=Y) e x y ->
  ball (m:=ProductMS) e (Basics.Pair a x) (Basics.Pair a y)).
  tauto.
 intros H.
 split; auto.
 apply ball_refl.
destruct (H0 _ _ _ Z).
assumption.
Qed.

Lemma ProductMS_located : locatedMetric X -> locatedMetric Y -> locatedMetric ProductMS.
Proof.
unfold locatedMetric.
intros H0 H1 e d x y Hed.
destruct (H0 _ _ (fst x) (fst y) Hed) as [A | A].
 destruct (H1 _ _ (snd x) (snd y) Hed) as [B | B].
  left.
  split; assumption.
 right; intros [_ H].
 apply B; assumption.
right; intros [H _].
apply A; assumption.
Defined.

Lemma ProductMS_decidable : decidableMetric X -> decidableMetric Y -> decidableMetric ProductMS.
unfold decidableMetric.
intros H0 H1 e x y.
destruct (H0 e (fst x) (fst y)) as [A | A].
 destruct (H1 e (snd x) (snd y)) as [B | B].
  left.
  split; assumption.
 right; intros [_ H].
 apply B; assumption.
right; intros [H _].
apply A; assumption.
Defined.

Definition PairMS (x:X) (y:Y) : ProductMS := (x,y).

End ProductMetric.

Implicit Arguments PairMS [X Y].

Add Morphism PairMS with signature ms_eq ==> ms_eq ==> ms_eq as PairMS_wd.
Proof.
intros.
split; assumption.
Qed.