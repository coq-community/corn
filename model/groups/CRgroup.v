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

Require Export CRGroupOps.
Require Export CRmonoid.
Require Import CRcorrect.
Require Import CornTac.

(**
** Example of a group: $\langle$#&lang;#[CR],[+]$\rangle$#&rang;#
*)

Open Local Scope uc_scope.

Lemma CRopp_strext : un_op_strext CRasCSetoid CRopp.
Proof.
intros x y H.
change (CRapart x y)%CR.
apply CR_ap_as_Cauchy_IR_ap_2.
apply: un_op_strext_unfolded.
stepl (CRasCauchy_IR (-x)%CR) by
 apply eq_symmetric; apply CR_opp_as_Cauchy_IR_opp.
stepr (CRasCauchy_IR (-y)%CR) by
 apply eq_symmetric; apply CR_opp_as_Cauchy_IR_opp.
apply CR_ap_as_Cauchy_IR_ap_1.
apply H.
Qed.

Definition CRoppasUnOp : CSetoid_un_op CRasCSetoid :=
Build_CSetoid_fun _ _ _ CRopp_strext.

Lemma CRisCGroup : is_CGroup CRasCMonoid CRoppasUnOp.
Proof.
split.
change (x-x==(inject_Q 0%Q))%CR.
rewrite <- CR_eq_as_Cauchy_IR_eq.
stepl ((CRasCauchy_IR x)[+](CRasCauchy_IR (- x)%CR)) by
 apply CR_plus_as_Cauchy_IR_plus.
stepl ((CRasCauchy_IR x)[+][--](CRasCauchy_IR x)) by
 apply plus_resp_eq; apply CR_opp_as_Cauchy_IR_opp.
apply: eq_transitive.
apply cg_rht_inv_unfolded.
apply: CR_inject_Q_as_Cauchy_IR_inject_Q.

change (-x + x==(inject_Q 0%Q))%CR.
rewrite <- CR_eq_as_Cauchy_IR_eq.
stepl ((CRasCauchy_IR (-x)%CR)[+](CRasCauchy_IR x)) by
 apply CR_plus_as_Cauchy_IR_plus.
stepl ([--](CRasCauchy_IR x)[+](CRasCauchy_IR x)) by
 apply bin_op_is_wd_un_op_lft; apply CR_opp_as_Cauchy_IR_opp.
apply: eq_transitive.
apply cg_lft_inv_unfolded.
apply: CR_inject_Q_as_Cauchy_IR_inject_Q.
Qed.

Definition CRasCGroup : CGroup :=
Build_CGroup _ _ CRisCGroup.

Canonical Structure CRasCGroup.
