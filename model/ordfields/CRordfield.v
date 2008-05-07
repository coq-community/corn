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

Require Export CRFieldOps.
Require Export CRfield.
Require Export COrdFields.
Require Import CRcorrect.
Require Import CornTac.

Open Local Scope uc_scope.

Lemma CRlt_strext : Crel_strext CRasCField CRlt.
Proof.
intros x1 x2 y1 y2 H.
destruct (Ccsr_strext _ _ _ (CRasCauchy_IR x2) _ (CRasCauchy_IR y2) (CR_lt_as_Cauchy_IR_lt_1 _ _ H)) as[H0|H0].
left.
apply CR_lt_as_Cauchy_IR_lt_2.
assumption.
right.
destruct H0;[left|right];
apply CR_ap_as_Cauchy_IR_ap_2; assumption.
Qed.

Definition CRltasCCsetoidRelation : CCSetoid_relation CRasCField :=
Build_CCSetoid_relation _ _ CRlt_strext.

Lemma CRisCOrdField : is_COrdField CRasCField
 CRltasCCsetoidRelation CRle
 (default_greater _ CRltasCCsetoidRelation) (default_grEq CRasCField CRle).
Proof.
split.

split.
intros x y z H0 H1.
apply CR_lt_as_Cauchy_IR_lt_2.
apply less_transitive_unfolded with (CRasCauchy_IR y);
 apply CR_lt_as_Cauchy_IR_lt_1; assumption.
intros x y H0 H1.
apply (less_antisymmetric_unfolded _ (CRasCauchy_IR x) (CRasCauchy_IR y));
 apply CR_lt_as_Cauchy_IR_lt_1; assumption.

intros x y H z.
change (x+z < y + z)%CR.
apply CR_lt_as_Cauchy_IR_lt_2.
stepl ((CRasCauchy_IR x)[+](CRasCauchy_IR z)) by
 rapply CR_plus_as_Cauchy_IR_plus.
stepr ((CRasCauchy_IR y)[+](CRasCauchy_IR z)) by
 rapply CR_plus_as_Cauchy_IR_plus.
apply plus_resp_less_rht.
apply CR_lt_as_Cauchy_IR_lt_1.
assumption.

intros x y Hx Hy.
change ((' 0%Q) < x*y)%CR.
apply CR_lt_as_Cauchy_IR_lt_2.
stepr ((CRasCauchy_IR x)[*](CRasCauchy_IR y)) by
 rapply CR_mult_as_Cauchy_IR_mult.
rapply less_wdl;[|apply (CR_inject_Q_as_Cauchy_IR_inject_Q 0)].
rapply mult_resp_pos;(
 rapply less_wdl;[|apply eq_symmetric;apply (CR_inject_Q_as_Cauchy_IR_inject_Q 0)];
 apply CR_lt_as_Cauchy_IR_lt_1;assumption).

intros x y.
split.
intros H.
destruct (ap_imp_less _ _ _ (CR_ap_as_Cauchy_IR_ap_1 _ _ H));[left|right];
 rapply CR_lt_as_Cauchy_IR_lt_2; assumption.
intros [H|H];
 apply CR_ap_as_Cauchy_IR_ap_2;
 [apply less_imp_ap|apply Greater_imp_ap];
 apply CR_lt_as_Cauchy_IR_lt_1;assumption.

intros x y.
rewrite <- CR_le_as_Cauchy_IR_le.
split.
intros H0 H1.
apply H0.
rapply CR_lt_as_Cauchy_IR_lt_1.
assumption.
intros H0 H1.
apply H0.
rapply CR_lt_as_Cauchy_IR_lt_2.
assumption.

intros x y.
split; intros; assumption.

reflexivity.
Qed.

Definition CRasCOrdField : COrdField :=
Build_COrdField _ _ _ _ _ CRisCOrdField.

Canonical Structure CRasCOrdField.
