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

Require Export Qring.
Require Import CFields.

(** **Example of a field: $\langle$#&lang;#[Q],[[+]],[[*]]$\rangle$#&rang;#
As we have seen, there is a inverse for the multiplication for non-zeroes.
So, [Q] not only forms a ring, but even a field.
*)

Lemma Q_is_CField : is_CField Q_as_CRing Qinv.
Proof.
red in |- *.
intro.
unfold is_inverse in |- *.
apply Qinv_is_inv.
Qed.

Definition Q_as_CField := Build_CField _ _ Q_is_CField Qinv_strext.

