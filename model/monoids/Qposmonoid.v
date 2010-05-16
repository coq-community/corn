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


Require Export Qpossemigroup.
Require Import CMonoids.

(**
** Example of a monoid: $\langle$#&lang;#[Qpos],[[*]]$\rangle$#&rang;#
One is the unit for multiplication on positive integers. Therefore the positive rational numbers together with the multiplication are a CMonoid.
*)

Lemma QONEpos_is_rht_unit : is_rht_unit Qpos_mult_is_bin_fun (1%positive:Qpos).
Proof.
 intros x.
 simpl.
 ring.
Qed.

Lemma QONEpos_is_lft_unit : is_lft_unit Qpos_mult_is_bin_fun (1%positive:Qpos).
Proof.
 intros x.
 simpl.
 ring.
Qed.

Definition Qpos_mult_is_CMonoid := Build_is_CMonoid
 Qpos_mult_as_CSemiGroup _ QONEpos_is_rht_unit QONEpos_is_lft_unit.

Definition Qpos_mult_as_CMonoid := Build_CMonoid
 Qpos_mult_as_CSemiGroup _ Qpos_mult_is_CMonoid.
