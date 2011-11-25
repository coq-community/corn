(*
Copyright © 2009 Valentin Blot and Bas Spitters

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
Require Export CRings RingClass.

Section cring_is_ring.
Global Instance CRing_is_Ring (CR : CRing) : Ring (@cm_unit CR) (@cr_one CR) (@csg_op CR) (@cr_mult CR) (fun x y => x [-] y) (@cg_inv CR).
Proof with auto.
 split;split;algebra.
Qed.
End cring_is_ring.

Section SubCRings.

Variable CR : CRing.
Variable P : CR -> Type.
Variable Punit : P [0].
Variable op_pres_P : bin_op_pres_pred _ P csg_op.
Variable inv_pres_P : un_op_pres_pred _ P cg_inv.
Variable Pone : P [1].
Variable mul_pres_P : bin_op_pres_pred _ P cr_mult.

Let subcrr : CAbGroup := Build_SubCAbGroup _ _ Punit op_pres_P inv_pres_P.
Let submult : CSetoid_bin_op subcrr := Build_SubCSetoid_bin_op _ _ _ mul_pres_P.

Lemma isring_scrr : is_CRing subcrr (Build_subcsetoid_crr _ _ _ Pone) submult.
Proof.
 assert (associative submult).
  intros x y z; destruct x as [x xpf]; destruct y as [y ypf]; destruct z as [z zpf]; simpl; apply mult_assoc.
 apply (Build_is_CRing _ _ _ H).
    split; intro x; destruct x as [x xpf]; simpl; algebra.
   intros x y; destruct x as [x xpf]; destruct y as [y ypf]; simpl; apply mult_commutes.
  intros x y z; destruct x as [x xpf]; destruct y as [y ypf]; destruct z as [z zpf]; simpl; apply dist.
 simpl; apply ring_non_triv.
Qed.

Definition Build_SubCRing : CRing := Build_CRing _ _ _ isring_scrr.

Global Instance SubCRing_is_SubRing : SubRing P.
Proof.
 constructor; auto.
 intros x y Px Py; apply op_pres_P; [ | apply inv_pres_P ]; assumption.
Qed.

End SubCRings.
