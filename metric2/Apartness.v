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
