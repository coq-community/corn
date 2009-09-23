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


Require Export Zsec.
Require Export CSetoidFun.

(**
** Example of a setoid: [Z]
*** [Z]
*)

Lemma ap_Z_irreflexive : irreflexive (A:=Z) ap_Z.
Proof.
 red in |- *.
 apply ap_Z_irreflexive0.
Qed.

Lemma ap_Z_symmetric : Csymmetric ap_Z.
Proof.
 red in |- *.
 apply ap_Z_symmetric0.
Qed.

Lemma ap_Z_cotransitive : cotransitive (A:=Z) ap_Z.
Proof.
 red in |- *.
 apply ap_Z_cotransitive0.
Qed.

Lemma ap_Z_tight : tight_apart (A:=Z) (eq (A:=Z)) ap_Z.
Proof.
 red in |- *.
 apply ap_Z_tight0.
Qed.

Definition ap_Z_is_apartness := Build_is_CSetoid Z (eq (A:=Z)) ap_Z
 ap_Z_irreflexive ap_Z_symmetric ap_Z_cotransitive ap_Z_tight.


Definition Z_as_CSetoid := Build_CSetoid _ _ _ ap_Z_is_apartness.
Canonical Structure Z_as_CSetoid.

(** The term [Z_as_CSetoid] is of type [CSetoid]. Hence we have proven that [Z] is a constructive setoid.
*** Addition
We will prove now that the addition on the integers is a setoid function.
*)

Lemma Zplus_wd :
 bin_fun_wd Z_as_CSetoid Z_as_CSetoid Z_as_CSetoid Zplus.
Proof.
 red in |- *.
 simpl in |- *.
 apply Zplus_wd0.
Qed.

Lemma Zplus_strext :
 bin_fun_strext Z_as_CSetoid Z_as_CSetoid Z_as_CSetoid Zplus.
Proof.
 red in |- *.
 simpl in |- *.
 apply Zplus_strext0.
Qed.

Definition Zplus_is_bin_fun := Build_CSetoid_bin_fun
 Z_as_CSetoid Z_as_CSetoid Z_as_CSetoid Zplus Zplus_strext.
Canonical Structure Zplus_is_bin_fun.

(** What's more: the addition is also associative and commutative.
*)

Lemma Zplus_is_assoc : associative Zplus_is_bin_fun.
Proof.
 red in |- *.
 intros x y z.
 simpl in |- *.
 apply Zplus_assoc.
Qed.

Lemma Zplus_is_commut : commutes Zplus_is_bin_fun.
Proof.
 red in |- *.
 simpl in |- *.
 intros x y.
 apply Zplus_comm.
Qed.

(**
*** Opposite
Taking the opposite of an integer is a setoid function.
*)

Lemma Zopp_wd : fun_wd (S1:=Z_as_CSetoid) (S2:=Z_as_CSetoid) Zopp.
Proof.
 red in |- *.
 simpl in |- *.
 intros x y H.
 apply (f_equal Zopp H).
Qed.

Lemma Zopp_strext :
 fun_strext (S1:=Z_as_CSetoid) (S2:=Z_as_CSetoid) Zopp.
Proof.
 red in |- *.
 simpl in |- *.
 unfold ap_Z in |- *.
 intros x y H.
 intro H0.
 apply H.
 exact (f_equal Zopp H0).
Qed.

Definition Zopp_is_fun :=
  Build_CSetoid_fun Z_as_CSetoid Z_as_CSetoid Zopp Zopp_strext.
Canonical Structure Zopp_is_fun.

(**
*** Multiplication
Finally the multiplication is a setoid function and is associative and commutative.
*)

Lemma Zmult_wd :
 bin_fun_wd Z_as_CSetoid Z_as_CSetoid Z_as_CSetoid Zmult.
Proof.
 red in |- *.
 simpl in |- *.
 intros x1 x2 y1 y2 H H0.
 apply (f_equal2 Zmult (x1:=x1) (y1:=x2) (x2:=y1) (y2:=y2)).
  assumption.
 assumption.
Qed.

Lemma Zmult_strext :
 bin_fun_strext Z_as_CSetoid Z_as_CSetoid Z_as_CSetoid Zmult.
Proof.
 red in |- *.
 simpl in |- *.
 apply Zmult_strext0.
Qed.

Definition Zmult_is_bin_fun := Build_CSetoid_bin_fun
 Z_as_CSetoid Z_as_CSetoid Z_as_CSetoid Zmult Zmult_strext.
Canonical Structure Zmult_is_bin_fun.

Lemma Zmult_is_assoc : associative Zmult_is_bin_fun.
Proof.
 red in |- *.
 intros x y z.
 simpl in |- *.
 apply Zmult_assoc.
Qed.


Lemma Zmult_is_commut : commutes Zmult_is_bin_fun.
Proof.
 red in |- *.
 simpl in |- *.
 intros x y.
 apply Zmult_comm.
Qed.

(**
*** Zero
*)

Lemma is_nullary_operation_Z_0 : (is_nullary_operation Z_as_CSetoid 0%Z).
Proof.
 unfold is_nullary_operation.
 intuition.
Qed.
