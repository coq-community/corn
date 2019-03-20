(*
Copyright © 2009 Valentin Blot

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

Require Import CPoly_Degree CPoly_Euclid RingClass CRingClass.
Import CRing_Homomorphisms.coercions.

Section RX_div.

Variable R : CRing.
Let RX := cpoly_cring R.
Add Ring r_r : (r_rt (Ring:=CRing_is_Ring R)).
Add Ring rx_r : (r_rt (Ring:=CRing_is_Ring (cpoly_cring R))).

Lemma _X_monic : forall a : R, monic 1 (_X_ [-] _C_ a).
Proof.
 split.
  reflexivity.
 intro m; destruct m.
  intro H; inversion H.
 destruct m.
  intro H; destruct (lt_irrefl _ H).
 reflexivity.
Qed.

Definition RX_div (p : RX) (a : R) : RX.
Proof.
 destruct (cpoly_div p (_X_monic a)) as [qr Hunq Heq]; exact (fst qr).
Defined.

Lemma RX_div_spec : forall (p : RX) (a : R), p [=] (RX_div p a) [*] (_X_ [-] _C_ a) [+] _C_ (p ! a).
Proof.
 intros p a.
 unfold RX_div.
 destruct (cpoly_div p (_X_monic a)) as [[q r] s [s0 d]].
 unfold fst, snd in *.
 rewrite -> s0.
 apply cs_bin_op_wd; [reflexivity|].
 destruct d.
 destruct (_X_monic a).
 destruct (degree_le_zero _ _ (d _ H0)).
 rewrite -> s2.
 apply csf_wd.
 rewrite -> plus_apply, mult_apply, minus_apply.
 rewrite -> x_apply, c_apply, c_apply; unfold cg_minus; ring.
Qed.

End RX_div.
