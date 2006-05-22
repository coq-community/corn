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

Require Export Qpossetoid.
Require Export CSemiGroups.

(** **Example of a semi-group: $\langle$#&lang;#[Qpos],[[*]]$\rangle$#&rang;#
The positive rationals form with the multiplication a CSemiGroup.
*)

Definition Qpos_mult_as_CSemiGroup := Build_CSemiGroup
 Qpos Qpos_mult associative_Qpos_mult.
