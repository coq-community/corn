Require Export Metric.
Require Import Qauto.

Definition stableMetric (ms:MetricSpace) := 
 forall e (x y:ms), ~~(ball e x y) -> ball e x y.

Definition locatedMetric (ms:MetricSpace) := 
 forall (e d:Qpos) (x y:ms), e < d -> {ball d x y}+{~ball e x y}.

Definition decidableMetric (ms:MetricSpace) := 
 forall e (x y:ms), {ball e x y}+{~ball e x y}.

Lemma decidable_located : forall ms,
 decidableMetric ms -> locatedMetric ms.
Proof.
intros ms H e d x y Hed.
destruct (H e x y).
 left.
 abstract (
 apply ball_weak_le with e; try assumption;
 apply Qlt_le_weak; assumption).
right; assumption.
Defined.

Lemma located_stable : forall ms,
 locatedMetric ms -> stableMetric ms.
Proof.
intros ms H e x y Hxy.
apply ball_closed.
intros d.
destruct (H e (e+d)%Qpos x y); try (assumption || contradiction).
autorewrite with QposElim.
rewrite Qlt_minus_iff; ring_simplify; auto with *.
Qed.
