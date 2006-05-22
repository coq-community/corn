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


Require Export Npossemigroup.
Require Import CMonoids.

(** **Non-example of a monoid: $\langle$#&lang;#[Npos],[[+]]$\rangle$#&rang;#
There is no right unit for the addition on the positive natural numbers.
*)

Lemma no_rht_unit_Npos : forall y : Npos, ~ is_rht_unit (S:=Npos) Npos_plus y.
unfold is_rht_unit in |- *.
intro y.
case y.
intros scs_elem scs_prf.
apply no_rht_unit_Npos1.
Qed.

(** Therefore the set of positive natural numbers doesn't form a group with 
addition.
*)

Lemma no_monoid_Npos : forall y : Npos, ~ is_CMonoid Npos_as_CSemiGroup y.
intro y.
red in |- *.
intro H.
set (H0 := no_rht_unit_Npos y) in *.
apply H0.
apply (runit Npos_as_CSemiGroup).
exact H.
Qed.
