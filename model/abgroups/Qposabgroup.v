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


Require Export Qposgroup.
Require Import CAbGroups.

(** **Example of an abelian group: $\langle$#&lang;#[Qpos],[[*]]$\rangle$#&rang;#
The positive rationals form with the multiplication a CAbgroup.
*)

Definition Qpos_mult_is_CAbGroup : is_CAbGroup Qpos_as_CGroup.
unfold is_CAbGroup in |- *.
unfold commutes in |- *.
intros x y.
case x.
case y.
simpl in |- *.
intros x0 Hx y1 Hy.
apply Qmult_sym.
Qed.

Definition Qpos_mult_as_CAbGroup := Build_CAbGroup
 Qpos_as_CGroup Qpos_mult_is_CAbGroup.
