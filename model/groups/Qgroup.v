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

Require Export Qmonoid.
Require Import CGroups.

(** **Example of a group: $\langle$#&lang;#[Q],[[+]]$\rangle$#&rang;#
The rational numbers with addition form a group. The inverse function is taking the opposite.
*)

Lemma Q_is_CGroup : is_CGroup Q_as_CMonoid Qopp_is_fun.
Proof.
red in |- *.
split.
apply Qplus_inverse_r.
eapply eq_transitive_unfolded.
apply Qplus_is_commut0.
apply Qplus_inverse_r.
Qed.

Definition Q_as_CGroup := Build_CGroup Q_as_CMonoid Qopp_is_fun Q_is_CGroup.
