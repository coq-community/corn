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

Require Export CoRN.model.ordfields.Qordfield.
Require Import CoRN.algebra.COrdFields2.
Require Import Coq.QArith.Qpower.
Require Import Coq.QArith.Qabs.
Require Import CoRN.tactics.CornTac.

Ltac Qauto_pos :=
  repeat (first [ assumption
                | constructor
                | apply Q.Qplus_pos_compat
                | apply Q.Qmult_lt_0_compat
                | apply Qinv_lt_0_compat]);
  auto with *.

Ltac Qauto_nonneg :=
  repeat (first [assumption
               |discriminate
               |apply: Qabs_nonneg
               |apply: Qsqr_nonneg
               |apply: plus_resp_nonneg;simpl
               |apply: mult_resp_nonneg;simpl
               |apply: Qle_shift_div_l;[Qauto_pos|ring_simplify]
               |apply: Qle_shift_inv_l;[Qauto_pos|ring_simplify]]);
  auto with *.

Ltac Qauto_le :=
 rewrite -> Qle_minus_iff;ring_simplify;Qauto_nonneg.
