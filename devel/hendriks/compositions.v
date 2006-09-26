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

Require Export CSetoids.

(* move to CSetoids.v *)

Section compositions.

Variables A B C D E : CSetoid.

Variable f1 : CSetoid_fun C E.
Variable f2 : CSetoid_bin_fun C D E.
Variable g1 : CSetoid_fun A C.
Variable g2 : CSetoid_bin_fun A B C.
Variable h1 : CSetoid_fun B D.
Variable h2 : CSetoid_bin_fun A B D.

Let uu x := f1 (g1 x).

Lemma compose_uu_strext : fun_strext (S1:=A) (S2:=E) uu.
Proof.
intros x y H.
apply (csf_strext _ _ g1).
exact (csf_strext _ _ f1 _ _ H).
Qed.

Definition compose_uu : CSetoid_fun A E :=
  Build_CSetoid_fun A E uu compose_uu_strext.

Let ub x y := f1 (g2 x y).

Lemma compose_ub_strext : bin_fun_strext A B E ub.
Proof.
intros x1 x2 y1 y2 H.
apply (csbf_strext _ _ _ g2).
exact (csf_strext _ _ f1 _ _ H).
Qed.

Definition compose_ub : CSetoid_bin_fun A B E :=
  Build_CSetoid_bin_fun A B E ub compose_ub_strext.

Let bu x y := f2 (g1 x) (h1 y).

Lemma compose_bu_strext : bin_fun_strext A B E bu.
Proof.
intros x1 x2 y1 y2 H.
elim (csbf_strext _ _ _ f2 _ _ _ _ H); intro H0. 
left; exact (csf_strext _ _ g1 _ _ H0).
right; exact (csf_strext _ _ h1 _ _ H0).
Qed.

Definition compose_bu : CSetoid_bin_fun A B E :=
  Build_CSetoid_bin_fun A B E bu compose_bu_strext.

Let bb x y := f2 (g2 x y) (h2 x y).

Lemma compose_bb_strext : bin_fun_strext A B E bb.
Proof.
intros x1 x2 y1 y2 H.
elim (csbf_strext _ _ _ f2 _ _ _ _ H); intro H0.
elim (csbf_strext _ _ _ g2 _ _ _ _ H0); intro H1.
left; exact H1.
right; exact H1.
elim (csbf_strext _ _ _ h2 _ _ _ _ H0); intro H1.
left; exact H1.
right; exact H1.
Qed.

Definition compose_bb : CSetoid_bin_fun A B E :=
  Build_CSetoid_bin_fun A B E bb compose_bb_strext.

End compositions.

Implicit Arguments compose_uu [A C E].
Implicit Arguments compose_ub [A B C E].
Implicit Arguments compose_bu [A B C D E].
Implicit Arguments compose_bb [A B C D E].

Notation "f [ouu] g" := (compose_uu f g) (at level 20, left associativity).
Notation "f [oub] g" := (compose_ub f g) (at level 20, left associativity).
Notation "f [obu] ( g , h )" := (compose_bu f g h) (at level 20).
Notation "f [obb] ( g , h )" := (compose_bb f g h) (at level 20).

Section combinators_as_csetoid_operations.

Definition id := id_un_op.

Variables S1 S2 : CSetoid.

Let K (x:S1) (y:S2) := x.

Lemma K_strext : bin_fun_strext S1 S2 S1 K.
Proof.
intros x1 x2 y1 y2 H; left; exact H.
Qed.

Definition first := Build_CSetoid_bin_fun S1 S2 S1 K K_strext.

Let K' (x:S1) (y:S2) := y.

Lemma K'_strext : bin_fun_strext S1 S2 S2 K'.
Proof.
intros x1 x2 y1 y2 H; right; exact H.
Qed.

Definition second := Build_CSetoid_bin_fun S1 S2 S2 K' K'_strext.

End combinators_as_csetoid_operations.

Implicit Arguments id [S].
Implicit Arguments first [S1 S2].
Implicit Arguments second [S1 S2].
