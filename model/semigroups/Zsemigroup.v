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

Require Export Zsetoid.
Require Export CSemiGroups.

(** **Examples of semi-groups: $\langle$#&lang;#[Z],[[+]]$\rangle$#&rang;# and $\langle$#&lang;#[Z],[[*]]$\rangle$#&rang;#
***$\langle$#&lang;#[Z],[[+]]$\rangle$#&rang;#
*)

Lemma Zplus_is_CSemiGroup: (is_CSemiGroup Z_as_CSetoid Zplus_is_bin_fun).
unfold is_CSemiGroup.
exact Zplus_is_assoc.
Qed.

Definition Z_as_CSemiGroup := Build_CSemiGroup _ Zplus_is_bin_fun Zplus_is_assoc.

(** The term [Z_as_CSemiGroup] is of type [CSemiGroup]. Hence we have proven that [Z] is a constructive semi-group. *)

(** ***$\langle$#&lang;#[Z],[[*]]$\rangle$#&rang;#
*)

Lemma Zmult_is_CSemiGroup: (is_CSemiGroup Z_as_CSetoid Zmult_is_bin_fun).
unfold is_CSemiGroup.
exact Zmult_is_assoc.
Qed.

Definition Z_mul_as_CSemiGroup := Build_CSemiGroup _ Zmult_is_bin_fun Zmult_is_assoc.




