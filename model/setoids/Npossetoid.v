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

Require Export CoRN.model.setoids.Nsetoid.
Require Export CoRN.model.structures.Npossec.
Require Import CoRN.algebra.CSetoidFun.
From Coq Require Import Lia.

(**
** Example of a setoid: [Npos]

*** Setoid
The positive natural numbers [Npos] will be defined as a subsetoid of the
natural numbers.
*)

Definition Npos := Build_SubCSetoid nat_as_CSetoid (fun n : nat => n <> 0).

Definition NposP := (fun n : nat_as_CSetoid => n <> 0).


(** One and two are elements of it.
*)

Definition ONEpos := Build_subcsetoid_crr _ NposP 1 (S_O 0).

Definition TWOpos := Build_subcsetoid_crr _ NposP 2 (S_O 1).


(**
*** Addition and multiplication
Because addition and multiplication preserve positivity, we can define
them on this subsetoid.
*)

Lemma plus_resp_Npos : bin_op_pres_pred _ NposP plus_is_bin_fun.
Proof.
 unfold bin_op_pres_pred in |- *.
 simpl in |- *.
 apply plus_resp_Npos0.
Qed.

Definition Npos_plus := Build_SubCSetoid_bin_op _ _ plus_is_bin_fun plus_resp_Npos.


Lemma mult_resp_Npos : bin_op_pres_pred _ NposP mult_as_bin_fun.
Proof.
 intros x y H H0.
 unfold mult_as_bin_fun, NposP in |- *.
 apply mult_resp_Npos0; auto.
Qed.

Definition Npos_mult := Build_SubCSetoid_bin_op _ _ mult_as_bin_fun mult_resp_Npos.

(** The addition has no right unit on this set.
*)

Lemma no_rht_unit_Npos1 : forall y : Npos, ~ (forall x : Npos, Npos_plus x y[=]x).
Proof.
 intro y.
 case y.
 intros scs_elem scs_prf.
 cut ((1+scs_elem) <> 1).
  intros H.
  red in |- *.
  intros H0.
  apply H.
  unfold not in H.
  generalize (H0 (Build_subcsetoid_crr nat_as_CSetoid NposP 1 (S_O 0))).
  simpl in |- *.
  intuition.
 auto.
Qed.

(** And the multiplication doesn't have an inverse, because there can't be an
inverse for 2.
*)

Lemma no_inverse_Nposmult1 : forall n : Npos, ~ (Npos_mult TWOpos n[=]ONEpos).
Proof.
 intro n.
 case n.
 simpl in |- *.
 intros.
 lia.
Qed.
