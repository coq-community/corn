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


Require Export CoRN.model.monoids.Zmonoid.
Require Import CoRN.algebra.CGroups.

(**
** Example of a group: $\langle$#&lang;#[Z],[[+]]$\rangle$#&rang;#
*)

Lemma Z_is_CGroup : is_CGroup Z_as_CMonoid Zopp_is_fun.
Proof.
 red in |- *.
 simpl in |- *.
 intro x.
 split; simpl in |- *.
  apply Zplus_opp_r.
 apply Zplus_opp_l.
Qed.

Definition Z_as_CGroup := Build_CGroup Z_as_CMonoid Zopp_is_fun Z_is_CGroup.

(** The term [Z_as_CGroup] is of type [CGroup]. Hence we have proven that [Z] is a constructive group. *)

Canonical Structure Z_as_CGroup.
