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


Require Export Zgroup.
Require Import CAbGroups.

(** **Example of an abelian group: $\langle$#&lang;#[Z],[[+]]$\rangle$#&rang;#
*)

Lemma Z_is_CAbGroup : is_CAbGroup Z_as_CGroup. 
Proof.
red in |- *.
simpl in |- *.
exact Zplus_is_commut.
Qed.

Definition Z_as_CAbGroup := Build_CAbGroup Z_as_CGroup Z_is_CAbGroup.

(** The term [Z_as_CAbGroup] is of type [CAbGroup]. Hence we have proven that [Z] is a constructive Abelian group. *)
