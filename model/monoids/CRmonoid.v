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
Require Export CRsemigroup.
Require Import CRcorrect.
Require Import CornTac.

Open Local Scope uc_scope.

(**
** Examples of monoids: $\langle$#&lang;#[CR],[+]$\rangle$#&rang;#
*** $\langle$#&lang;#[CR],[+]$\rangle$#&rang;#
We use the addition [' 0] as the unit of monoid:
*)

Lemma CRisCMonoid : is_CMonoid CRasCSemiGroup 0%CR.
Proof.
 split; intros x.
  change (x+0==x)%CR.
  rewrite <- CR_eq_as_Cauchy_IR_eq.
  stepl ((CRasCauchy_IR x)[+](CRasCauchy_IR 0%CR)); [| now apply: CR_plus_as_Cauchy_IR_plus].
  stepl ((CRasCauchy_IR x)[+][0]); [| now apply: plus_resp_eq; apply: CR_inject_Q_as_Cauchy_IR_inject_Q].
  apply cm_rht_unit.
 change (0+x==x)%CR.
 rewrite <- CR_eq_as_Cauchy_IR_eq.
 stepl ((CRasCauchy_IR 0%CR)[+](CRasCauchy_IR x)); [| now apply CR_plus_as_Cauchy_IR_plus].
 stepl ([0][+](CRasCauchy_IR x)); [| now
   apply bin_op_is_wd_un_op_lft; apply: CR_inject_Q_as_Cauchy_IR_inject_Q].
 apply cm_lft_unit.
Qed.

Definition CRasCMonoid : CMonoid :=
Build_CMonoid _ _ CRisCMonoid.

Canonical Structure CRasCMonoid.
