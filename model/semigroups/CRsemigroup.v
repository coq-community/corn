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
Require Export CRsetoid.
Require Export CGroups.
Require Import CRcorrect.
Require Import CornTac.

(**
** Examples of semi-groups: $\langle$#&lang;#[CR],[+]$\rangle$#&rang;#
*** $\langle$#&lang;#[CR],[+]$\rangle$#&rang;#
*)

Open Local Scope uc_scope.

Lemma CRplus_strext : bin_op_strext CRasCSetoid (ucFun2 CRplus).
Proof.
 intros x1 x2 y1 y2 H.
 simpl in *.
 assert (X:(CRasCauchy_IR x1[+]CRasCauchy_IR y1)[#](CRasCauchy_IR x2[+]CRasCauchy_IR y2)).
  stepl (CRasCauchy_IR (x1+y1)%CR) by apply eq_symmetric; apply CR_plus_as_Cauchy_IR_plus.
  stepr (CRasCauchy_IR (x2+y2)%CR) by apply eq_symmetric; apply CR_plus_as_Cauchy_IR_plus.
  apply CR_ap_as_Cauchy_IR_ap_1.
  assumption.
 destruct (bin_op_strext_unfolded _ _ _ _ _ _ X);[left|right];
   apply CR_ap_as_Cauchy_IR_ap_2; assumption.
Qed.

Definition CRplusasBinOp : CSetoid_bin_op CRasCSetoid :=
Build_CSetoid_bin_fun _ _ _ _ CRplus_strext.

Lemma CRisCSemiGroup : is_CSemiGroup _ CRplusasBinOp.
Proof.
 intros x y z.
 change (x + (y+z)==(x+y)+z)%CR.
 rewrite <- CR_eq_as_Cauchy_IR_eq.
 stepl ((CRasCauchy_IR x)[+](CRasCauchy_IR (y+z)%CR)) by apply CR_plus_as_Cauchy_IR_plus.
 stepl ((CRasCauchy_IR x)[+]((CRasCauchy_IR y)[+](CRasCauchy_IR z))) by
   apply plus_resp_eq; apply CR_plus_as_Cauchy_IR_plus.
 stepr ((CRasCauchy_IR (x+y)%CR)[+](CRasCauchy_IR z)) by apply CR_plus_as_Cauchy_IR_plus.
 stepr (((CRasCauchy_IR x)[+](CRasCauchy_IR y))[+](CRasCauchy_IR z)) by
   apply bin_op_is_wd_un_op_lft; apply CR_plus_as_Cauchy_IR_plus.
 apply plus_assoc_unfolded.
Qed.

Definition CRasCSemiGroup : CSemiGroup :=
Build_CSemiGroup _ _ CRisCSemiGroup.

Canonical Structure CRasCSemiGroup.
