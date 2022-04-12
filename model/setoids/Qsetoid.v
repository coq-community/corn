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
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; either version 2.1 of the License, or
 * (at your option) any later version.
 *
 * This work is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along
 * with this work; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 *)


Require Export CoRN.model.structures.Qsec.
Require Import CoRN.algebra.CSetoidFun.

(**
** Example of a setoid: [Q]
*** Setoid
*)
Lemma ap_Q_irreflexive1 : irreflexive (A:=Q) Qap.
Proof.
 red in |- *.
 apply ap_Q_irreflexive0.
Qed.

Lemma ap_Q_symmetric1 : Csymmetric Qap.
Proof.
 red in |- *.
 apply ap_Q_symmetric0.
Qed.

Lemma ap_Q_cotransitive1 : cotransitive (A:=Q) Qap.
Proof.
 red in |- *.
 apply ap_Q_cotransitive0.
Qed.

Lemma ap_Q_tight1 : tight_apart (A:=Q) Qeq Qap.
Proof.
 red in |- *.
 apply ap_Q_tight0.
Qed.

Definition ap_Q_is_apartness := Build_is_CSetoid Q Qeq Qap
 ap_Q_irreflexive1 ap_Q_symmetric1 ap_Q_cotransitive1 ap_Q_tight1.

Definition Q_as_CSetoid := Build_CSetoid _ _ _ ap_Q_is_apartness.
Canonical Structure Q_as_CSetoid.
Canonical Structure Q_is_Setoid := (cs_crr Q_as_CSetoid).

(**
*** Addition
*)

Lemma Qplus_wd : bin_fun_wd Q_as_CSetoid Q_as_CSetoid Q_as_CSetoid Qplus.
Proof. repeat intro. apply Qplus_comp; trivial. Qed.

Lemma Qplus_strext1 : bin_fun_strext Q_as_CSetoid Q_as_CSetoid Q_as_CSetoid Qplus.
Proof. repeat intro. apply Qplus_strext0; trivial. Qed.

Definition Qplus_is_bin_fun := Build_CSetoid_bin_fun _ _ _ _ Qplus_strext1.
(* Canonical Structure Qplus_is_bin_fun. *)

(** It is associative and commutative.
*)

Lemma Qplus_is_assoc : associative Qplus_is_bin_fun.
Proof Qplus_assoc.

Lemma Qplus_is_commut1 : commutes Qplus_is_bin_fun.
Proof Qplus_comm.

(**
*** Opposite
*)

Lemma Qopp_wd : fun_wd (S1:=Q_as_CSetoid) (S2:=Q_as_CSetoid) Qopp.
Proof. repeat intro. apply Qopp_comp; trivial. Qed.

Lemma Qopp_strext : fun_strext (S1:=Q_as_CSetoid) (S2:=Q_as_CSetoid) Qopp.
Proof. firstorder using Qopp_comp. Qed.


Definition Qopp_is_fun := Build_CSetoid_fun _ _ _ Qopp_strext.
(* Canonical Structure Qopp_is_fun. *)

(**
*** Multiplication
*)

Lemma Qmult_wd : bin_fun_wd Q_as_CSetoid Q_as_CSetoid Q_as_CSetoid Qmult.
Proof. repeat intro. apply Qmult_comp; trivial. Qed.

Lemma Qmult_strext1 : bin_fun_strext Q_as_CSetoid Q_as_CSetoid Q_as_CSetoid Qmult.
Proof. repeat intro. apply Qmult_strext0; trivial. Qed.

Definition Qmult_is_bin_fun := Build_CSetoid_bin_fun _ _ _ _ Qmult_strext1.
(* Canonical Structure Qmult_is_bin_fun. *)

(** It is associative and commutative.
*)

Lemma Qmult_is_assoc : associative Qmult_is_bin_fun.
Proof. repeat intro. apply Qmult_assoc. Qed.

Lemma Qmult_is_commut : commutes Qmult_is_bin_fun.
Proof. repeat intro. apply Qmult_comm. Qed.

(**
*** Less-than
*)

Lemma Qlt_strext : Crel_strext Q_as_CSetoid Qlt.
Proof. 
 red in |- *.
 apply Qlt_strext_unfolded.
Qed.

Definition Qlt_is_CSetoid_relation := Build_CCSetoid_relation _ _ Qlt_strext.
Canonical Structure Qlt_is_CSetoid_relation.
