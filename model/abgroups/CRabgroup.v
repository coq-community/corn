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

Require Export CoRN.model.groups.CRgroup.
Require Import CoRN.reals.fast.CRcorrect.
Require Export CoRN.algebra.CAbGroups.
Require Import CoRN.tactics.CornTac.

(**
** Example of a abelian group: $\langle$#&lang;#[CR],[+]$\rangle$#&rang;#
*)

Open Local Scope uc_scope.

Lemma CRisCAbGroup : is_CAbGroup CRasCGroup.
Proof.
 intros x y.
 change (x+y==y+x)%CR.
 rewrite <- CR_eq_as_Cauchy_IR_eq.
 stepl ((CRasCauchy_IR x)[+](CRasCauchy_IR y)); [| now apply CR_plus_as_Cauchy_IR_plus].
 stepr ((CRasCauchy_IR y)[+](CRasCauchy_IR x)); [| now apply CR_plus_as_Cauchy_IR_plus].
 apply cag_commutes.
Qed.

Definition CRasCAbGroup : CAbGroup :=
Build_CAbGroup _ CRisCAbGroup.

Canonical Structure CRasCAbGroup.
