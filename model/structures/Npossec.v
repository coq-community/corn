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

(** printing Npos $\mathbb{N}^{+}$ #N<SUP>+</SUP># *)

Require Export Nsec.
Require Import Arith Omega.

(**
** [Npos]
The positive natural numbers have some nice properties. Addition as well
as multiplication preserve the feature of being positive.
*)

Lemma plus_resp_Npos0 : forall x y : nat, x <> 0 -> y <> 0 -> (x+y) <> 0.
Proof.
 intros x y H H0.
 unfold not in |- *.
 intros H1.
 unfold not in H.
 apply H.
 omega.
Qed.

Lemma Npos_is_suc : forall y : nat, y <> 0 -> exists m : nat, y = S m.
Proof.
 intros y H.
 exists (pred y).
 unfold pred in |- *.
 induction  y as [| y Hrecy].
  intuition.
 intuition.
Qed.

Lemma mult_resp_Npos0 : forall x y : nat, x <> 0 -> y <> 0 -> (x*y) <> 0.
Proof.
 intros x y H H0.
 destruct (Npos_is_suc y H0) as [y0 H2].
 rewrite H2 in H0.
 rewrite H2.
 generalize y0.
 clear H0 H2 y0 y.
 intro y0.
 induction  y0 as [| y0 Hrecy0].
  rewrite mult_comm.
  rewrite mult_1_l.
  exact H.
 rewrite <- mult_n_Sm.
 cut (0 <> (x*S y0+x) -> (x*S y0+x) <> 0).
  intro H3.
  apply H3.
  apply lt_O_neq.
  cut ((x*S y0+x) > 0).
   unfold gt in |- *.
   intuition.
  apply gt_trans with (x*S y0).
   apply gt_le_trans with (x*S y0+0).
    apply plus_gt_compat_l.
    omega.
   omega.
  unfold gt in |- *.
  apply neq_O_lt.
  cut ((x*S y0) <> 0).
   auto.
  apply Hrecy0.
 auto.
Qed.
