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

Require Export CoRN.metric2.Complete.
Require Import CoRN.model.metric2.CRmetric.
Require Import CoRN.model.metric2.L1metric.
Require Import CoRN.model.metric2.LinfMetric.
Require Import CoRN.model.metric2.Qmetric.
Require Import CoRN.tactics.CornTac.
Require Import CoRN.model.metric2.BoundedFunction.

Set Implicit Arguments.

Open Local Scope uc_scope.
(**
** Example of a Complete Metric Space: IntegrableFunction
*)
Definition IntegrableFunction := Complete L1StepQ.

Definition Integral : IntegrableFunction --> CR :=
 Cmap L1StepQPrelengthSpace IntegralQ_uc.

(** Every bounded function is integrable. *)
Definition BoundedAsIntegrable : BoundedFunction --> IntegrableFunction :=
 Cmap LinfStepQPrelengthSpace LinfAsL1.
