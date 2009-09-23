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

Require Export Nsemigroup.
Require Import CMonoids.

(**
** Example of a monoid: $\langle$#&lang;#[nat],[[+]]$\rangle$#&rang;#
Zero is an unit for the addition.
*)

Lemma O_as_rht_unit : is_rht_unit (S:=nat_as_CSetoid) plus_is_bin_fun 0.
Proof.
 red in |- *.
 simpl in |- *.
 intro x.
 symmetry  in |- *.
 apply plus_n_O.
Qed.

Lemma O_as_lft_unit : is_lft_unit (S:=nat_as_CSetoid) plus_is_bin_fun 0.
Proof.
 red in |- *.
 simpl in |- *.
 intro x.
 reflexivity.
Qed.

Definition nat_is_CMonoid := Build_is_CMonoid
 nat_as_CSemiGroup _ O_as_rht_unit O_as_lft_unit.

(**
 Whence we can define #<i>#%\emph{%the monoid of natural numbers%}%#</i>#:
*)

Definition nat_as_CMonoid := Build_CMonoid nat_as_CSemiGroup _ nat_is_CMonoid.

Canonical Structure nat_as_CMonoid.

Lemma SO_as_rht_unit : is_rht_unit (S:=nat_as_CSetoid) mult_as_bin_fun 1.
Proof.
 red in |- *.
 simpl.
 auto with arith.
Qed.

Lemma SO_as_lft_unit : is_lft_unit (S:=nat_as_CSetoid) mult_as_bin_fun 1.
Proof.
 red in |- *.
 simpl.
 auto with arith.
Qed.

Definition Nmult_is_CMonoid := Build_is_CMonoid
 Nmult_as_CSemiGroup _ SO_as_rht_unit SO_as_lft_unit.

Definition Nmult_as_CMonoid := Build_CMonoid Nmult_as_CSemiGroup _ Nmult_is_CMonoid.
