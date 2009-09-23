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

Require Import Setoid Morphisms.
Notation " x === y " := (Equivalence.equiv x y) (at level 70, no associativity).

Set Implicit Arguments.
Unset Strict Implicit.

Section Definitions.

Definition unop (R : Type) := R -> R.
Definition binop (R : Type) := R -> R -> R.
Context {R : Type}.
Class unop_intern (P : R -> Type) (op : unop R) :=
  unop_int : forall x : R, P x -> P (op x).
Class binop_intern (P : R -> Type) (op : binop R) :=
  binop_int : forall x y : R, P x -> P y -> P (op x y).
Context `{r_st : Equivalence R req}.

Class associative (op : binop R) :=
  assoc : forall x y z, op x (op y z) === op (op x y) z.
Class commutative (op : binop R) :=
  commut : forall x y, op x y === op y x.
Class left_commutative (op : binop R) :=
  left_commut : forall x y z, op x (op y z) === op y (op x z).
Class right_commutative (op : binop R) :=
  right_commut : forall x y z, op (op x y) z === op (op x z) y.

Class left_unit (op : binop R) (idm : R) :=
  left_id : forall x, op idm x === x.
Class right_unit (op : binop R) (idm : R) :=
  right_id : forall x, op x idm === x.
Class left_absorbing (op : binop R) (idm : R) :=
  left_zero : forall x, op idm x === idm.
Class right_absorbing (op : binop R) (idm : R) :=
  right_zero : forall x, op x idm === idm.

Class left_distributive (op mul : binop R) :=
  left_dist : forall x y z, mul (op x y) z === op (mul x z) (mul y z).
Class right_distributive (op mul : binop R) :=
  right_dist : forall x y z, mul x (op y z) === op (mul x y) (mul x z).

Class left_inverse (op : binop R) (idm : R) (inv : unop R) :=
  left_inv : forall x, op x (inv x) === idm.
Class right_inverse (op : binop R) (idm : R) (inv : unop R) :=
  right_inv : forall x, op (inv x) x === idm.

End Definitions.

Section Commutative.

Context `{r_st : Equivalence R req}.
Context {mul : binop R} {mulC : commutative mul}.
Global Instance mulC_id_l {idm : R} {H : left_unit mul idm} : right_unit mul idm.
Proof. reduce; rewrite commut; apply left_id. Qed.
Global Instance mulC_id_r {idm : R} {H : right_unit mul idm} : left_unit mul idm.
Proof. reduce; rewrite commut; apply right_id. Qed.
Global Instance mulC_zero_l {zero : R} {H : left_absorbing mul zero} : right_absorbing mul zero.
Proof. reduce; rewrite commut; apply left_zero. Qed.
Global Instance mulC_zero_r {zero : R} {H : right_absorbing mul zero} : left_absorbing mul zero.
Proof. reduce; rewrite commut; apply right_zero. Qed.
Global Instance mulC_inv_l {idm : R} {inv : unop R} {H : left_inverse mul idm inv} : right_inverse mul idm inv.
Proof. reduce; rewrite commut; apply left_inv. Qed.
Global Instance mulC_inv_r {idm : R} {inv : unop R} {H : right_inverse mul idm inv} : left_inverse mul idm inv.
Proof. reduce; rewrite commut; apply right_inv. Qed.

Section distributivity.
Context {op : binop R}.
Context {op_morph : Morphism (Equivalence.equiv==>Equivalence.equiv==>Equivalence.equiv) op}.
Global Instance mulC_distr_l {H : left_distributive op mul} : right_distributive op mul.
Proof. intros l_d x y z; rewrite (commut x (op _ _)), (commut x y), (commut x z); apply left_dist. Qed.
Global Instance mulC_distr_r {H : right_distributive op mul} : left_distributive op mul.
Proof. intros l_d x y z; rewrite (commut (op _ _) z), (commut x z), (commut y z); apply right_dist. Qed.
End distributivity.

Section Associativity.
Context {mul_morph : Morphism (Equivalence.equiv==>Equivalence.equiv==>Equivalence.equiv) mul}.
Context {mulA : associative mul}.
Global Instance mulAC_comm_l : left_commutative mul.
Proof. intros x y z; rewrite assoc, assoc, (commut x y); reflexivity. Qed.
Global Instance mulAC_comm_r : right_commutative mul.
Proof. intros x y z; rewrite <- assoc, <- assoc, (commut y z); reflexivity. Qed.
End Associativity.

End Commutative.

Section AssociativeCommutative.
Context `{r_st : Equivalence R req}.
Context {add mul : binop R} {opp : unop R} {zero : R}.
Context {add_morph : Morphism (Equivalence.equiv==>Equivalence.equiv==>Equivalence.equiv) add}.
Context {mul_morph : Morphism (Equivalence.equiv==>Equivalence.equiv==>Equivalence.equiv) mul}.
Context {opA : associative add}.
Context {opC : commutative add}.
Section Left.
Context {l_inv : left_inverse add zero opp}.
Context {op_id : left_unit add zero}.
Context {l_d : left_distributive add mul}.

(* Sinon ca marche pas... *)
Existing Instance mulC_id_l.

Global Instance opA_zero_l : left_absorbing mul zero.
Proof.
 intro; rewrite <- (left_id (mul _ _)); rewrite <- (left_id zero) at 3.
 set (e := left_inv (mul zero x)); rewrite <- e at 1 3; clear e.
 rewrite (commut (mul _ _)), <- assoc, <- assoc; apply add_morph; try reflexivity.
 rewrite <- left_dist, (left_id zero), (right_id (mul _ _)); reflexivity.
Qed.
End Left.
Section Right.
Context {r_inv : right_inverse add zero opp}.
Context {op_id : right_unit add zero}.
Context {r_d : right_distributive add mul}.

(* Sinon ca marche pas... *)
Existing Instance mulC_id_r.

Global Instance opA_zero_r : right_absorbing mul zero.
Proof.
 intro; rewrite <- (right_id (mul _ _)); rewrite <- (right_id zero) at 3.
 set (e := right_inv (mul x zero)); rewrite <- e at 2 4; clear e.
 rewrite (commut (opp _)), assoc, assoc; apply add_morph; try reflexivity.
 rewrite <- right_dist, (right_id zero), (left_id (mul _ _)); reflexivity.
Qed.
End Right.
End AssociativeCommutative.
