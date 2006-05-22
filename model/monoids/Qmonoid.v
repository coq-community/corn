(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)



(* $Id$ *)

Require Export Qsemigroup.
Require Import CMonoids.

(** **Examples of a monoid: $\langle$#&lang;#[Q],[[+]]$\rangle$#&rang;# and $\langle$#&lang;#[Q],[[*]]$\rangle$#&rang;#
***$\langle$#&lang;#[Q],[[+]]$\rangle$#&rang;#
The rational numbers form with addition a CMonoid. [QZERO] is the unit.
*)

Lemma ZEROQ_as_rht_unit3 : is_rht_unit (S:=Q_as_CSetoid) Qplus_is_bin_fun QZERO.
Proof.
red in |- *.
simpl in |- *.
apply ZEROQ_as_rht_unit0.
Qed.

Lemma ZEROQ_as_lft_unit3 : is_lft_unit (S:=Q_as_CSetoid) Qplus_is_bin_fun QZERO.
Proof.
red in |- *.
simpl in |- *.
apply ZEROQ_as_lft_unit0.
Qed.

Definition Q_is_CMonoid := Build_is_CMonoid
 Q_as_CSemiGroup _ ZEROQ_as_rht_unit3 ZEROQ_as_lft_unit3.

Definition Q_as_CMonoid := Build_CMonoid Q_as_CSemiGroup _ Q_is_CMonoid.

(** ***$\langle$#&lang;#[Q],[[*]]$\rangle$#&rang;#
Also with multiplication Q forms a CMonoid. Here, the unit is [QONE].
*)

Lemma ONEQ_as_rht_unit : is_rht_unit (S:=Q_as_CSetoid) Qmult_is_bin_fun QONE.
Proof.
red in |- *.
simpl in |- *.
exact Qmult_n_1.
Qed.

Lemma ONEQ_as_lft_unit : is_lft_unit (S:=Q_as_CSetoid) Qmult_is_bin_fun QONE.
Proof.
red in |- *.
intro.
eapply eq_transitive_unfolded.
apply Qmult_is_commut.
apply ONEQ_as_rht_unit.
Qed.

Definition Q_mul_is_CMonoid := Build_is_CMonoid
 Q_mul_as_CSemiGroup _ ONEQ_as_rht_unit ONEQ_as_lft_unit. 

Definition Q_mul_as_CMonoid := Build_CMonoid
 Q_mul_as_CSemiGroup _ Q_mul_is_CMonoid.
