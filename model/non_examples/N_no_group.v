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


Require Export Nmonoid.
Require Import CGroups.

(** **Non-example of a group: $\langle$#&lang;#[nat],[[+]]$\rangle$#&rang;#
There is no inverse function for the natural numbers with addition.
*)

Lemma no_inverse_nat_plus : forall inv : CSetoid_un_op nat_as_CSetoid,
 ~ is_inverse (csg_op (c:=nat_as_CSemiGroup)) 0 2 (inv 2).
simpl in |- *.
unfold plus_is_bin_fun in |- *.
intro inv.
case inv.
unfold is_inverse in |- *.
simpl in |- *.
intros a1 a2. 
generalize no_inverse0.
simpl in |- *.
intuition.
Qed.

(** Hence they do not form a CGroup.
*)

Lemma no_group_nat_plus : forall inv : CSetoid_un_op nat_as_CMonoid,
 ~ is_CGroup nat_as_CMonoid inv.
simpl in |- *.
intro inv.
red in |- *.
unfold is_CGroup in |- *.
intro H.
set (H0 := H 2) in *.
set (H1 := no_inverse_nat_plus inv) in *.
apply H1.
exact H0.
Qed.
