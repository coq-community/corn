(*
Copyright © 2008 Russell O’Connor

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
Require Import CoRN.model.totalorder.QposMinMax. 
Require Export CoRN.metric2.Metric.

Local Open Scope Q_scope.

(**
** Classification of metric spaces

A metric space is located if you can choose
between ball d x y and ~ball e x y for e < d. Every located metric
is a stable metric. This translates the located property of the real
numbers e < d -> (e < d(x,y) \/ d(x,y) < d). *)
Definition locatedMetric (ms:MetricSpace) :=
  forall (e d:Q) (x y:ms),
    e < d -> {ball d x y}+{~ball e x y}.

(** At the top level a metric space is decidable if its ball relation
is decidable.  Every decidable metric is a located metric. *)
Definition decidableMetric (ms:MetricSpace) :=
 forall e (x y:ms), {ball e x y}+{~ball e x y}.

Lemma decidable_located : forall ms,
 decidableMetric ms -> locatedMetric ms.
Proof.
 intros ms H e d x y Hed.
 destruct (H e x y).
  left.
  abstract ( apply ball_weak_le with e;
             try assumption; apply Qlt_le_weak; assumption).
 right; assumption.
Defined.

