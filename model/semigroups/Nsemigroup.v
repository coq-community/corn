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

Require Export CoRN.model.setoids.Nsetoid.
Require Import CoRN.algebra.CSemiGroups.

(**
** Example of a semi-group: $\langle$#&lang;#[nat],[[+]]$\rangle$#&rang;#
*)

(** Because addition is associative, the natural numbers form a CSemiGroup.
*)

Definition nat_as_CSemiGroup := Build_CSemiGroup _ plus_is_bin_fun plus_is_assoc.

Canonical Structure nat_as_CSemiGroup.

Lemma Nmult_is_CSemiGroup : is_CSemiGroup nat_as_CSetoid mult_as_bin_fun.
Proof.
 unfold is_CSemiGroup in |- *.
 unfold associative in |- *.
 unfold mult_as_bin_fun in |- *.
 simpl in |- *.
 auto with arith.
Qed.

Definition Nmult_as_CSemiGroup := Build_CSemiGroup
 nat_as_CSetoid mult_as_bin_fun Nmult_is_CSemiGroup.
