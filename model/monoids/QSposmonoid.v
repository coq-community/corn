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


Require Export QSpossemigroup.
Require Import CMonoids.

(** **Example of a monoid: $\langle$#&lang;#[Qpos],$(x,y) \mapsto xy/2$ #(x,y) &#x21A6; xy/2#$\rangle$#&rang;#
Two is the unit of the operation  $(x,y) \mapsto xy/2$ #(x,y) 
  &#x21A6; xy/2# on the positive rationals. So we have another monoid structure on the positive rational numbers.
*)                              

Lemma QTWOpos_is_rht_unit : is_rht_unit multdiv2 QTWOpos.
unfold is_rht_unit in |- *.
intro x.
case x.
simpl in |- *.
apply QTWOpos_is_rht_unit0.
Qed.

Lemma QTWOpos_is_lft_unit : is_lft_unit multdiv2 QTWOpos.
unfold is_lft_unit in |- *.
intro x.
case x.
simpl in |- *.
apply QTWOpos_is_left_unit0.
Qed.

Definition Qpos_multdiv2_is_CMonoid := Build_is_CMonoid
 Qpos_multdiv2_as_CSemiGroup QTWOpos QTWOpos_is_rht_unit QTWOpos_is_lft_unit.

Definition Qpos_multdiv2_as_CMonoid := Build_CMonoid
 Qpos_multdiv2_as_CSemiGroup QTWOpos Qpos_multdiv2_is_CMonoid.
