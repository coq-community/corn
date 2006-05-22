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

Require Export Qgroup.
Require Import CAbGroups.

(** **Example of an abelian group: $\langle$#&lang;#[Q],[[+]]$\rangle$#&rang;#
*)

(** Addition is commutative, so the rationals form with the addition a 
CAbGroup.
*)

Lemma Q_is_CAbGroup : is_CAbGroup Q_as_CGroup.
Proof.
red in |- *.
exact Qplus_is_commut1.
Qed.

Definition Q_as_CAbGroup := Build_CAbGroup Q_as_CGroup Q_is_CAbGroup.
