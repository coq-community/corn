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

Require Export Zsetoid.
Require Export CSemiGroups.

(** **Examples of semi-groups: $\langle$#&lang;#[Z],[[+]]$\rangle$#&rang;# and $\langle$#&lang;#[Z],[[*]]$\rangle$#&rang;#
***$\langle$#&lang;#[Z],[[+]]$\rangle$#&rang;#
*)

Lemma Zplus_is_CSemiGroup: (is_CSemiGroup Z_as_CSetoid Zplus_is_bin_fun).
unfold is_CSemiGroup.
exact Zplus_is_assoc.
Qed.

Definition Z_as_CSemiGroup := Build_CSemiGroup _ Zplus_is_bin_fun Zplus_is_assoc.

(** The term [Z_as_CSemiGroup] is of type [CSemiGroup]. Hence we have proven that [Z] is a constructive semi-group. *)

(** ***$\langle$#&lang;#[Z],[[*]]$\rangle$#&rang;#
*)

Lemma Zmult_is_CSemiGroup: (is_CSemiGroup Z_as_CSetoid Zmult_is_bin_fun).
unfold is_CSemiGroup.
exact Zmult_is_assoc.
Qed.

Definition Z_mul_as_CSemiGroup := Build_CSemiGroup _ Zmult_is_bin_fun Zmult_is_assoc.




