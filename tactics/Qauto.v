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

Require Export Qordfield.
Require Import COrdFields2.
Require Import Qpower.
Require Import CornTac.

Ltac Qauto_pos :=
  repeat (first [assumption
               |constructor
               |rsapply plus_resp_pos
               |rsapply mult_resp_pos]);
  auto with *.

Ltac Qauto_nonneg :=
  repeat (first [assumption
               |discriminate
               |rapply Qsqr_nonneg
               |rsapply plus_resp_nonneg
               |rsapply mult_resp_nonneg
               |apply Qle_shift_div_l;[Qauto_pos|ring_simplify]
               |apply Qle_shift_inv_l;[Qauto_pos|ring_simplify]]);
  auto with *.

Ltac Qauto_le :=
 rewrite Qle_minus_iff;ring_simplify;Qauto_nonneg.

