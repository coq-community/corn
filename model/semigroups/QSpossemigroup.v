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
Require Import CSemiGroups.

(** **Example of a semi-group: $\langle$#&lang;#[Qpos],$(x,y) \mapsto xy/2$#(x,y) &#x21A6; xy/2#$\rangle$#&rang;#
The positive rationals form with the operation
$(x,y) \mapsto xy/2$#(x,y) &#x21A6; xy/2# a CSemiGroup.
*)

Definition Qpos_multdiv2_as_CSemiGroup := Build_CSemiGroup
 Qpos multdiv2 associative_multdiv2.
