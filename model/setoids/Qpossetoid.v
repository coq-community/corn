(* Copyright © 1998-2006
 * Henk Barendregt
 * Luís Cruz-Filipe
 * Herman Geuvers
 * Mariusz Giero
 * Rik van Ginneken
 * Dimitri Hendriks
 * Sébastien Hinderer
 * Bart Kirkels
 * Pierre Letouzey
 * Iris Loeb
 * Lionel Mamane
 * Milad Niqui
 * Russell O’Connor
 * Randy Pollack
 * Nickolay V. Shmyrev
 * Bas Spitters
 * Dan Synek
 * Freek Wiedijk
 * Jan Zwanenburg
 * 
 * This work is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * This work is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along
 * with this work; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 *) 

Require Export Qsetoid.
Require Import CSetoidFun.
Require Export Qpossec.

(** **Example of a setoid: [Qpos]
***Setoid
We will examine the subsetoid of positive rationals of the setoid of 
rational numbers.
*)
Lemma ap_Qpos_irreflexive1 : irreflexive (A:=Qpos) Qap.
Proof.
red in |- *.
firstorder using ap_Q_irreflexive0.
Qed.

Lemma ap_Qpos_symmetric1 : Csymmetric (A:=Qpos) Qap.
red in |- *.
firstorder using ap_Q_symmetric0.
Qed.

Lemma ap_Qpos_cotransitive1 : cotransitive (A:=Qpos) Qap.
red in |- *.
intros;
apply ap_Q_cotransitive0; auto.
Qed.

Lemma ap_Qpos_tight1 : tight_apart (A:=Qpos) Qeq Qap.
red in |- *.
firstorder using ap_Q_tight0.
Qed.

Definition ap_Qpos_is_apartness := Build_is_CSetoid _ _ _
 ap_Qpos_irreflexive1 ap_Qpos_symmetric1 ap_Qpos_cotransitive1 ap_Qpos_tight1.

Definition Qpos_as_CSetoid := Build_CSetoid _ _ _ ap_Qpos_is_apartness.
Canonical Structure Qpos_as_CSetoid.

Lemma Qpos_plus_strext :  bin_fun_strext Qpos_as_CSetoid Qpos_as_CSetoid Qpos_as_CSetoid Qpos_plus.
red in |- *.
simpl in |- *.
intros x1 x2 y1 y2 H.
destruct (Qeq_dec x1 x2)as [A|A];[|tauto].
right.
autorewrite with QposElim in H.
intros B.
apply H.
rewrite A.
rewrite B.
reflexivity.
Qed.

Definition Qpos_plus_is_bin_fun := Build_CSetoid_bin_fun _ _ _ _ Qpos_plus_strext.
Canonical Structure Qpos_plus_is_bin_fun.

Lemma associative_Qpos_plus : associative Qpos_plus.
unfold associative in |- *.
intros x y z.
simpl.
autorewrite with QposElim.
apply Qplus_is_assoc.
Qed.

(** ***Multiplication
*)

Lemma Qpos_mult_strext :  bin_op_strext Qpos_as_CSetoid Qpos_mult.
red in |- *.
intros x1 x2 y1 y2 H.
simpl in *.
destruct (Qeq_dec x1 x2)as [A|A];[|tauto].
right.
autorewrite with QposElim in H.
intros B.
apply H.
rewrite A.
rewrite B.
reflexivity.
Qed.

Definition Qpos_mult_is_bin_fun : CSetoid_bin_op Qpos_as_CSetoid := Build_CSetoid_bin_fun _ _ _ _ Qpos_mult_strext.
Canonical Structure Qpos_mult_is_bin_fun.

Lemma associative_Qpos_mult : associative Qpos_mult.
unfold associative in |- *.
intros x y z.
simpl.
autorewrite with QposElim.
apply Qmult_is_assoc.
Qed.

(** ***Inverse
*)

Lemma Qpos_inv_strext : fun_strext Qpos_inv.
Proof.
unfold fun_strext in |- *.
firstorder using Qpos_inv_wd.
Qed.

Definition Qpos_inv_op := Build_CSetoid_un_op _ _ Qpos_inv_strext.
Canonical Structure Qpos_inv_op.

(** ***Special multiplication and inverse
We define [multdiv2]: $(x,y) \mapsto xy/2$ #(x,y) &#x21A6; xy/2#.
*)

Definition Qpos_div2 := projected_bin_fun _ _ _ Qpos_mult_is_bin_fun (Qpos_inv_op (2#1)%Qpos).

Definition multdiv2 := compose_CSetoid_un_bin_fun _ _ _ Qpos_mult_is_bin_fun Qpos_div2.

Lemma associative_multdiv2 : associative multdiv2.
unfold associative in |- *.
intros x y z.
simpl.
QposRing.
Qed.

(** And its inverse [multdiv4]: $x \mapsto 4/x$ #x &#x21A6; 4/x#.
*)

Definition mult4 := projected_bin_fun _ _ _ Qpos_mult_is_bin_fun (4#1)%Qpos.

Definition divmult4 := compose_CSetoid_fun _ _ _ Qpos_inv_op mult4.
