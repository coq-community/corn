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

Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import CoRN.model.totalorder.QposMinMax.
Require Import Coq.setoid_ring.Ring_theory.
Require Import Coq.Setoids.Setoid.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qround.
Require Export CoRN.model.reals.CRreal.
Require Import CoRN.metric2.Complete.
Require Export CoRN.reals.fast.CRFieldOps.
Require Import CoRN.model.rings.Qring.
Require Import CoRN.algebra.CRing_Homomorphisms.
Require Import CoRN.model.metric2.Qmetric.
Require Import CoRN.tactics.CornTac.
Require Import CoRN.logic.Stability.
Require Import Coq.Logic.ConstructiveEpsilon.
Require Import CoRN.util.Qdlog.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.
Require Import CRArith.

Local Open Scope CR_scope.


Lemma inject_Q_product (l: list Q): (' cr_Product l) [=] cr_Product (map inject_Q_CR l).
Proof.
 induction l.
  reflexivity.
 change (' (a * cr_Product l)%Q[=]cr_Product (map inject_Q_CR (a :: l))).
 rewrite <- CRmult_Qmult.
 rewrite IHl.
 reflexivity.
Qed.

Lemma inject_Qred_ap (x y: Q): Qred x <> Qred y -> ' x [#] ' y.
Proof with auto.
 intro.
 apply Qap_CRap.
 intro.
 apply H.
 apply Qred_complete...
Qed.

Lemma inject_Q_strext : fun_strext inject_Q_CR.
Proof.
 intros x y [Hxy|Hxy].
  apply: Qlt_not_eq.
  apply Qnot_le_lt.
  intros H.
  absurd ('y[<=]'x).
   rewrite -> leEq_def.
   auto with *.
  rewrite -> CRle_Qle.
  auto.
 apply ap_symmetric.
 apply: Qlt_not_eq.
 apply Qnot_le_lt.
 intros H.
 absurd ('x[<=]'y).
  rewrite -> leEq_def.
  auto with *.
 rewrite -> CRle_Qle.
 auto.
Qed.

Definition inject_Q_csf := Build_CSetoid_fun _ _ _ inject_Q_strext.

Lemma inject_Q_hom : RingHom Q_as_CRing CRasCRing.
Proof.
 exists (inject_Q_csf).
   apply: CRplus_Qplus.
  intros x y.
  apply eq_symmetric.
  apply CRmult_Qmult.
 apply eq_reflexive.
Defined.

