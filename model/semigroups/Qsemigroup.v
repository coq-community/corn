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

Require Export Qsetoid.
Require Import CSemiGroups.

(** **Examples of semi-groups: $\langle$#&lang;#[Q],[[+]]$\rangle$#&rang;# and $\langle$#&lang;#[Q],[[*]]$\rangle$#&rang;#
***$\langle$#&lang;#[Q],[[+]]$\rangle$#&rang;#
*)

Definition Q_as_CSemiGroup := Build_CSemiGroup _ Qplus_is_bin_fun Qplus_is_assoc.

(** ***$\langle$#&lang;#[Q],[[*]]$\rangle$#&rang;#
*)

Definition Q_mul_as_CSemiGroup := Build_CSemiGroup _ Qmult_is_bin_fun Qmult_is_assoc.
