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

Require Export Qpossemigroup.
Require Import CMonoids.

(** **Example of a monoid: $\langle$#&lang;#[Qpos],[[*]]$\rangle$#&rang;#
One is the unit for multiplication on positive integers. Therefore the positive rational numbers together with the multiplication are a CMonoid.
*)

Lemma QONEpos_is_rht_unit : is_rht_unit Qpos_mult QONEpos.
unfold is_rht_unit in |- *.
simpl in |- *.
intro x.
case x.
simpl in |- *.
intros e H.
apply Qmult_n_1.
Qed.

Lemma QONEpos_is_lft_unit : is_lft_unit Qpos_mult QONEpos.
unfold is_lft_unit in |- *.
simpl in |- *.
intro x.
case x.
simpl in |- *.
intros e H.
cut (QONE{*Q}e{=Q}e{*Q}QONE).
intro H0.
apply trans_Qeq with (e{*Q}QONE).
exact H0.
apply Qmult_n_1.
apply Qmult_sym.
Qed.


Definition Qpos_mult_is_CMonoid := Build_is_CMonoid
 Qpos_mult_as_CSemiGroup QONEpos QONEpos_is_rht_unit QONEpos_is_lft_unit.

Definition Qpos_mult_as_CMonoid := Build_CMonoid
 Qpos_mult_as_CSemiGroup QONEpos Qpos_mult_is_CMonoid.
