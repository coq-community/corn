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

Require Export CSemiGroups.
Require Import Nsemigroup.
Require Export Npossetoid.

(** **Examples of semi-groups:  $\langle$#&lang;#[Npos],[[+]]$\rangle$#&rang;# and $\langle$#&lang;#[Npos],[[*]]$\rangle$#&rang;#
***$\langle$#&lang;#[Npos],[[+]]$\rangle$#&rang;#
The positive natural numbers form together with addition a subsemigroup 
 of the semigroup of the natural numbers with addition.
*)

Definition Npos_as_CSemiGroup := Build_SubCSemiGroup
 nat_as_CSemiGroup NposP plus_resp_Npos.

(** ***$\langle$#&lang;#[Npos],[[*]]$\rangle$#&rang;#
Also together with multiplication, the positive numbers form a semigroup.
*)

Lemma Nposmult_is_CSemiGroup : is_CSemiGroup Npos Npos_mult.
unfold is_CSemiGroup in |- *.
unfold associative in |- *.
unfold Npos_mult in |- *.
simpl in |- *.
intros x y z.
case x.
case y.
case z.
simpl in |- *.
intros a pa b pb c pc.
auto with arith.
Qed.

Definition Nposmult_as_CSemiGroup := Build_CSemiGroup
 Npos Npos_mult Nposmult_is_CSemiGroup.
