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

Require Export Nsetoid.
Require Import CSemiGroups.

(** **Example of a semi-group: $\langle$#&lang;#[nat],[[+]]$\rangle$#&rang;#
*)

(** Because addition is associative, the natural numbers form a CSemiGroup.
*)

Definition nat_as_CSemiGroup := Build_CSemiGroup _ plus_is_bin_fun plus_is_assoc.

Lemma Nmult_is_CSemiGroup : is_CSemiGroup nat_as_CSetoid mult_as_bin_fun.
unfold is_CSemiGroup in |- *.
unfold associative in |- *.
unfold mult_as_bin_fun in |- *.
simpl in |- *.
auto with arith.
Qed.

Definition Nmult_as_CSemiGroup := Build_CSemiGroup
 nat_as_CSetoid mult_as_bin_fun Nmult_is_CSemiGroup.
