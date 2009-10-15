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

(** Rings as a type class *)
Require Import Setoid Ring Morphisms.
Open Scope signature_scope.

Require Import OperationClasses.

Set Implicit Arguments.
Unset Strict Implicit.

Section Definitions.

Context `{r_st : Equivalence R req}.
Class Ring (rO rI : R) (radd rmul rsub : binop R) (ropp : unop R) :=
  { r_rt : ring_theory rO rI radd rmul rsub ropp req;
    r_ree : ring_eq_ext radd rmul ropp req
}.

Context `{r_ring : Ring}.
Class SubRing (P : R -> Type) :=
  {zero_stab : P rO;
   one_stab : P rI;
   radd_int : binop_intern P radd;
   rmul_int : binop_intern P rmul;
   rsub_int : binop_intern P rsub;
   ropp_int : unop_intern P ropp}.

End Definitions.

Section Properties.

Context `{r_ring : Ring}.
Global Instance radd_morph : Proper (req==>req==>req) radd.
Proof. reduce; apply (Radd_ext r_ree); auto. Qed.
Global Instance rmul_morph : Proper (req==>req==>req) rmul.
Proof. reduce; apply (Rmul_ext r_ree); auto. Qed.
Global Instance rsub_morph : Proper (req==>req==>req) rsub.
Proof.
 reduce; rewrite -> (Rsub_def r_rt), -> (Rsub_def r_rt y y0).
 apply (Radd_ext r_ree); auto; apply (Ropp_ext r_ree); auto.
Qed.
Global Instance ropp_morph : Proper (req==>req) ropp.
Proof. reduce; apply (Ropp_ext r_ree); auto. Qed.
Global Instance radd_assoc : associative radd.
Proof. reduce; apply (Radd_assoc r_rt). Qed.
Global Instance radd_comm : commutative radd.
Proof. reduce; apply (Radd_comm r_rt). Qed.
Global Instance radd_left_comm : left_commutative radd := mulAC_comm_l.
Global Instance radd_right_comm : right_commutative radd := mulAC_comm_r.
Global Instance radd_left_unit : left_unit radd rO.
Proof. reduce; apply (Radd_0_l r_rt). Qed.
Global Instance radd_right_unit : right_unit radd rO := mulC_id_l.
Global Instance ropp_left_inverse : left_inverse radd rO ropp.
Proof. reduce; apply (Ropp_def r_rt). Qed.
Global Instance ropp_right_inverse : right_inverse radd rO ropp := mulC_inv_l.
Global Instance rmul_assoc : associative rmul.
Proof. reduce; apply (Rmul_assoc r_rt). Qed.
Global Instance rmul_comm : commutative rmul.
Proof. reduce; apply (Rmul_comm r_rt). Qed.
Global Instance rmul_left_comm : left_commutative rmul := mulAC_comm_l.
Global Instance rmul_right_comm : right_commutative rmul := mulAC_comm_r.
Global Instance rmul_left_unit : left_unit rmul rI.
Proof. reduce; apply (Rmul_1_l r_rt). Qed.
Global Instance rmul_right_unit : right_unit rmul rI := mulC_id_l.
Global Instance radd_rmul_left_distr : left_distributive radd rmul.
Proof. reduce; apply (Rdistr_l r_rt). Qed.
Global Instance radd_rmul_right_distr : right_distributive radd rmul := mulC_distr_l.
Global Instance rmul_left_zero : left_absorbing rmul rO := opA_zero_l.
Global Instance rmul_right_zero : right_absorbing rmul rO := mulC_zero_l.
End Properties.

Section SubRing_is_Ring.

Context `{SubRing}.
Add Ring r_r : r_rt (setoid r_st r_ree).

Let R' := sigT P.
Let proj1' := fun x : R' => projT1 x.
Coercion proj1' : R'>->R.
Let req' : relation R' := fun x y => req (projT1 x) (projT1 y).
Instance r_st' : Equivalence req'.
Proof.
 constructor; intro x; destruct x as [x Px]; try (intro y; destruct y as [y Py]);
   try (intro z; destruct z as [z Pz]);
     unfold req'; [ reflexivity | intro; symmetry; assumption | intros eqxy eqyz; rewrite eqxy; assumption ].
Qed.
Let rO' := existT P rO zero_stab.
Let rI' := existT P rI one_stab.
Let radd' : binop R' := fun x y => existT P (radd x y) (radd_int (projT2 x) (projT2 y)).
Let rmul' : binop R' := fun x y => existT P (rmul x y) (rmul_int (projT2 x) (projT2 y)).
Let rsub' : binop R' := fun x y => existT P (rsub x y) (rsub_int (projT2 x) (projT2 y)).
Let ropp' : unop R' := fun x => existT P (ropp x) (ropp_int (projT2 x)).
Global Instance sr_ring : @Ring R' req' r_st' rO' rI' radd' rmul' rsub' ropp'.
Proof.
 constructor.
  constructor; unfold R', req', radd', rmul', rsub', ropp', proj1'; intro x; destruct x as [ x Px ];
    try (intro y; destruct y as [ y Py ]); try (intro z; destruct z as [ z Pz ]); simpl; ring.
 constructor; unfold R', req', radd', rmul', rsub', ropp', proj1'; simpl;
   intros x x'; destruct x as [ x Px ]; destruct x' as [ x' Px' ]; simpl; intro eqx;
     try (intros y y'; destruct y as [ y Py ]; destruct y' as [ y' Py' ]; simpl; intro eqy; simpl);
       [ apply radd_morph | apply rmul_morph | apply ropp_morph ]; assumption.
Qed.

End SubRing_is_Ring.
