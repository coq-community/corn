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

Require Export Zabgroup.
Require Import CRings.

(**
** Example of a ring: $\langle$#&lang;#[Z],[[+]],[[*]]$\rangle$#&rang;#

The multiplication and the addition are distributive.
*)

Lemma Z_mult_plus_is_dist : distributive Zmult_is_bin_fun Zplus_is_bin_fun.
Proof.
 red in |- *.
 simpl in |- *.
 intros x y z.
 apply Zmult_plus_distr_r.
Qed.

Definition Z_is_CRing := Build_is_CRing Z_as_CAbGroup _ _ Zmult_is_assoc
    Z_mul_is_CMonoid Zmult_is_commut Z_mult_plus_is_dist ONE_neq_O.

Definition Z_as_CRing := Build_CRing _ _ _ Z_is_CRing.

(** The term [Z_as_CRing] is of type [CRing]. Hence we have proven that [Z] is a constructive ring. *)

Canonical Structure Z_as_CRing.
