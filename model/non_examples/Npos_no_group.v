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


Require Import CGroups.
Require Export Nposmonoid.

(**
** Non-example of a group: $\langle$#&lang;#[Npos],[[+]]$\rangle$#&rang;#
There is no inverse for multiplication on the positive natural numbers.
*)

Lemma no_inverse_Nposmult : forall inv : CSetoid_un_op Npos,
 ~ is_inverse Npos_mult ONEpos TWOpos (inv TWOpos).
Proof.
 intro inv.
 red in |- *.
 unfold is_inverse in |- *.
 intro H.
 elim H.
 clear H.
 intros H1 H2.
 clear H2.
 set (H3 := no_inverse_Nposmult1) in *.
 elim (H3 (inv TWOpos)).
 exact H1.
Qed.

(** Hence the natural numbers with multiplication do not form a group.
*)

Lemma no_group_Nposmult : forall inv : CSetoid_un_op Nposmult_as_CMonoid,
 ~ is_CGroup Nposmult_as_CMonoid inv.
Proof.
 simpl in |- *.
 intro inv.
 red in |- *.
 unfold is_CGroup in |- *.
 intro H.
 set (H0 := H (Build_subcsetoid_crr nat_as_CSetoid (fun n : nat => n <> 0) 2 (S_O 1))) in *.
 set (H1 := no_inverse_Nposmult inv) in *.
 apply H1.
 exact H0.
Qed.
