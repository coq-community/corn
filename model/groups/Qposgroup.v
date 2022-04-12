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
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; either version 2.1 of the License, or
 * (at your option) any later version.
 *
 * This work is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along
 * with this work; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 *)

Require Export CoRN.model.monoids.Qposmonoid.
Require Export CoRN.algebra.CGroups.

(**
** Example of a group: $\langle$#&lang;#[Qpos],[[*]]$\rangle$#&rang;#
The positive rational numbers form a multiplicative group.
*)

Lemma Qpos_is_CGroup : is_CGroup Qpos_mult_as_CMonoid Qpos_inv_op.
Proof.
 intros x.
 split; simpl; autorewrite with QposElim; field; apply Qpos_nonzero.
Qed.


Definition Qpos_as_CGroup := Build_CGroup
 Qpos_mult_as_CMonoid Qpos_inv_op Qpos_is_CGroup.
