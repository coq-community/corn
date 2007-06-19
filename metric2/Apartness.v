Require Export Metric.

Set Implicit Arguments.

Section Apartness.

Variable X : MetricSpace.
Hypothesis stable : forall e (a b:X), ~~ball e a b -> ball e a b.

Definition ms_ap (a b:X) := {e:Qpos | ~ball e a b}.

Lemma ms_ap_half_tight : forall a b, ms_ap a b -> ms_eq a b -> False.
Proof.
intros a b [e He] H.
apply He.
rewrite H.
apply ball_refl.
Qed.

Lemma ms_ap_tight : forall a b, (ms_ap a b -> False) <-> ms_eq a b.
intros a b.
split.
intros H.
apply ball_eq.
intros e.
apply stable.
intros H1.
apply H.
exists e.
assumption.
intros H H1.
apply ms_ap_half_tight with a b; assumption.
Qed.

End Apartness.
