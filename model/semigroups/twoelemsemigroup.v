(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(* $Id$ *)

Require Export CSemiGroups.
Require Export twoelemsetoid.

Section p68E1b1.

(** **Example of a semigroup: semigroups with two elements
*)

Lemma M1_is_CSemiGroup:(is_CSemiGroup M1_as_CSetoid M1_mult_as_bin_fun).
unfold is_CSemiGroup.
unfold associative.
simpl.
unfold M1_CS_mult.
intros x y z.
case x.
case y.
case z.
simpl.
unfold M1_eq.
reflexivity.

simpl.
unfold M1_eq.
reflexivity.

case z.
simpl.
unfold M1_eq.
reflexivity.

simpl.
unfold M1_eq.
reflexivity.

case y.
case z.
simpl.
unfold M1_eq.
reflexivity.

simpl.
unfold M1_eq.
reflexivity.

case z.
simpl.
unfold M1_eq.
reflexivity.

simpl.
unfold M1_eq.
reflexivity.
Qed.

Lemma e1_is_lft_unit: (is_lft_unit M1_mult_as_bin_fun e1).
unfold is_lft_unit.
simpl.
unfold M1_eq.
reflexivity.
Qed.

Lemma e1_is_rht_unit:(is_rht_unit M1_mult_as_bin_fun e1).
unfold is_rht_unit.
simpl.
unfold M1_eq.
unfold M1_CS_mult.
intro x.
case x.
simpl.
reflexivity.

simpl.
reflexivity.
Qed.

Definition M1_as_CSemiGroup:CSemiGroup:=
(Build_CSemiGroup M1_as_CSetoid M1_mult_as_bin_fun M1_is_CSemiGroup).

Lemma M2_is_CSemiGroup:(is_CSemiGroup M1_as_CSetoid M2_mult_as_bin_fun).
unfold is_CSemiGroup.
unfold associative.
simpl.
intros x y z.
case x.
case y.
case z.
simpl.
unfold M1_eq.
reflexivity.

simpl.
unfold M1_eq.
reflexivity.

case z.
simpl.
unfold M1_eq.
reflexivity.

simpl.
unfold M1_eq.
reflexivity.

case y.
case z.
simpl.
unfold M1_eq.
reflexivity.

simpl.
unfold M1_eq.
reflexivity.

simpl.
unfold M1_eq.
reflexivity.
Qed.
       
Definition M2_as_CSemiGroup:=
(Build_CSemiGroup M1_as_CSetoid M2_mult_as_bin_fun M2_is_CSemiGroup).

Lemma e1_is_lft_unit_M2: (is_lft_unit M2_mult_as_bin_fun e1). 
unfold is_lft_unit.
simpl.
unfold M1_eq.
reflexivity.
Qed.

Lemma e1_is_rht_unit_M2: (is_rht_unit M2_mult_as_bin_fun e1).
unfold is_rht_unit.
simpl.
intro x.
case x.
simpl.
unfold M1_eq.
reflexivity.

simpl.
unfold M1_eq.
reflexivity.
Qed.

End  p68E1b1.
