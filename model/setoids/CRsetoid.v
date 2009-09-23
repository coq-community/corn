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

Require Import CRcorrect.
Require Export CRmetric.
Require Export CSetoids.
Require Import CornTac.

(**
** Example of a setoid: [CR]
*** [CR]
*)

Lemma CRisCSetoid : is_CSetoid CR (@st_eq CR) CRapart.
Proof.
 split;simpl.
    intros x H.
    eapply ap_irreflexive.
    apply CR_ap_as_Cauchy_IR_ap_1.
    apply H.
   intros x y H.
   apply CR_ap_as_Cauchy_IR_ap_2.
   eapply ap_symmetric.
   apply CR_ap_as_Cauchy_IR_ap_1.
   apply H.
  intros x y H1 z.
  destruct (ap_cotransitive _ _ _ (CR_ap_as_Cauchy_IR_ap_1 _ _ H1) (CRasCauchy_IR z));[left|right];
    apply CR_ap_as_Cauchy_IR_ap_2; assumption.
 intros x y.
 change (Not (CRapart x y)<->(x==y)%CR).
 rewrite <- CR_eq_as_Cauchy_IR_eq.
 destruct (ap_tight _ (CRasCauchy_IR x) (CRasCauchy_IR y)) as [A B].
 split.
  intros H.
  apply A.
  intros X.
  apply H.
  apply CR_ap_as_Cauchy_IR_ap_2.
  assumption.
 intros H X.
 apply (B H).
 apply CR_ap_as_Cauchy_IR_ap_1.
 apply X.
Qed.

Definition CRasCSetoid : CSetoid := makeCSetoid CR _ CRisCSetoid.

Canonical Structure CRasCSetoid.
