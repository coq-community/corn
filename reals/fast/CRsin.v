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

Require Import CRAlternatingSum.
Require Export CRArith.
Require Import CRIR.
Require Import Qpower.
Require Import CornTac.

Set Implicit Arguments.

Opaque CR.

Open Local Scope Q_scope.

Section CosSeries.
Variable a:Q.

Definition cosSequence := (mult_Streams (everyOther recip_factorials) (powers (a^2))).

Lemma Str_nth_cosSequence : forall n, (Str_nth n cosSequence == (1#P_of_succ_nat (pred (fac (2*n))))*a^(2*n)%nat)%Q.
Proof.
intros n.
unfold cosSequence.
unfold mult_Streams.
rewrite Str_nth_zipWith.
rewrite Str_nth_everyOther.
rewrite Str_nth_recip_factorials.
rewrite Str_nth_powers.
rewrite Qpower
reflexivity.
Qed.

Hypothesis Ha: -(1) <= a <= 1.

Lemma cosSequence_dnn : DecreasingNonNegative cosSequence.
Proof.
apply recip_factorials_dnn.
apply powers_dnn.
assumption.
Qed.

Lemma expSequence_zl : Limit expSequence 0.
Proof.
rapply mult_Streams_zl.
apply recip_factorials_zl.
apply powers_nbz.
assumption.
Defined.
