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

Require Export Qabgroup.
Require Import CRings.
Require Import Zring.

Open Local Scope Q_scope.

(**
** Example of a ring: $\langle$#&lang;#[Q],[[+]],[[*]]$\rangle$#&rang;#
Because [Q] forms an abelian group with addition, a monoid with
multiplication and it satisfies the distributive law, it is a ring.
*)

Lemma Q_mult_plus_is_dist : distributive Qmult_is_bin_fun Qplus_is_bin_fun.
Proof.
 red in |- *.
 simpl in |- *.
 exact Qmult_plus_distr_r.
Qed.

Definition Q_is_CRing : is_CRing Q_as_CAbGroup 1 Qmult_is_bin_fun.
Proof.
 apply Build_is_CRing with Qmult_is_assoc.
    apply Q_mul_is_CMonoid.
   apply Qmult_is_commut.
  apply Q_mult_plus_is_dist.
 apply Q_apart_0_1.
Defined.

Definition Q_as_CRing := Build_CRing _ _ _ Q_is_CRing.

Canonical Structure Q_as_CRing.

(** The following lemmas are used in the proof that [Q] is Archimeadian.
*)

Lemma injz_Nring : forall n,
 nring (R:=Q_as_CRing) n[=]inject_Z (nring (R:=Z_as_CRing) n).
Proof.
 intro n.
 induction  n as [| n Hrecn].
  change ((Zero:Q_as_CRing)[=]Zero) in |- *.
  apply eq_reflexive_unfolded.
 change (nring (R:=Q_as_CRing) n[+]One[=]inject_Z (nring (R:=Z_as_CRing) n[+]One)) in |- *.
 Step_final ((inject_Z (nring (R:=Z_as_CRing) n):Q_as_CRing)[+]One).
 astepl ((inject_Z (nring (R:=Z_as_CRing) n):Q_as_CRing)[+] inject_Z (One:Z_as_CRing)).
 apply eq_symmetric_unfolded.
 apply injz_plus.
Qed.

Lemma injZ_eq : forall x y : Z, x = y -> (inject_Z x:Q_as_CRing)[=]inject_Z y.
Proof.
 intros.
 unfold inject_Z in |- *.
 simpl in |- *.
 red in |- *.
 simpl in |- *.
 rewrite H; trivial.
Qed.

Lemma nring_Q : forall n : nat, nring (R:=Q_as_CRing) n[=]inject_Z n.
Proof.
 intro n.
 induction  n as [| n Hrecn].
  change (Qmake 0%Z 1%positive==Qmake 0%Z 1%positive) in |- *.
  change (Zero[=](Zero:Q_as_CRing)) in |- *.
  apply eq_reflexive_unfolded.
 change (nring (R:=Q_as_CRing) n[+]One[=]inject_Z (S n)) in |- *.
 Step_final ((inject_Z n:Q_as_CRing)[+]One).
 astepl ((inject_Z n:Q_as_CRing)[+]inject_Z 1).
 simpl in |- *.
 red in |- *.
 unfold Qplus in |- *.
 simpl in |- *.
 rewrite Zpos_mult_morphism in |- *.
 rewrite succ_nat in |- *.
 ring.
Qed.

Lemma zring_Q : forall z, zring (R:=Q_as_CRing) z[=]inject_Z z.
Proof.
 destruct z; simpl; try reflexivity.
  rewrite -> pring_convert.
  rewrite -> nring_Q.
  now rewrite convert_is_POS. 
 rewrite -> pring_convert.
 rewrite -> nring_Q.
 unfold Qeq. simpl.
 ring_simplify.
 rewrite min_convert_is_NEG.
 now rewrite Pmult_comm.
Qed.
