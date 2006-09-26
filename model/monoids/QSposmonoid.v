(* Copyright © 1998-2006
 * Henk Barendregt
 * Luís Cruz-Filipe
 * Herman Geuvers
 * Mariusz Giero
 * Rik van Ginneken
 * Dimitri Hendriks
 * Sébastien Hinderer
 * Bart Kirkels
 * Pierre Letouzey
 * Iris Loeb
 * Lionel Mamane
 * Milad Niqui
 * Russell O’Connor
 * Randy Pollack
 * Nickolay V. Shmyrev
 * Bas Spitters
 * Dan Synek
 * Freek Wiedijk
 * Jan Zwanenburg
 * 
 * This work is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * This work is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along
 * with this work; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 *) 


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
