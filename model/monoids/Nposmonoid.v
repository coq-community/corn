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

Require Export Npossemigroup.
Require Import CMonoids.

(** **Example of a monoid: $\langle$#&lang;#[Npos],[[*]]$\rangle$#&rang;#
One is the right unit as well as the left unit of the multiplication on the
positive natural numbers.
*)

Lemma rhtunitNpos : is_rht_unit Npos_mult ONEpos.
unfold is_rht_unit in |- *.
unfold Npos_mult in |- *.
intro x.
case x.
simpl in |- *.
intros scs_elem H.
auto with arith.
Qed.

Lemma lftunitNpos : is_lft_unit Npos_mult ONEpos.
unfold is_rht_unit in |- *.
unfold Npos_mult in |- *.
intro x.
case x.
simpl in |- *.
intros scs_elem H.
auto with arith.
Qed.

(** So, the positive natural numbers with multiplication form a CMonoid.
*)

Definition Nposmult_is_CMonoid := Build_is_CMonoid
 Nposmult_as_CSemiGroup ONEpos rhtunitNpos lftunitNpos.

Definition Nposmult_as_CMonoid := Build_CMonoid
 Nposmult_as_CSemiGroup ONEpos Nposmult_is_CMonoid.
