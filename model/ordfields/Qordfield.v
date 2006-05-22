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

Require Export Qfield.
Require Import COrdFields.

(** **Example of an ordered field: $\langle$#&lang;#[Q],[[+]],[[*]],[[<]]$\rangle$#&rang;#
 [Q] is an archemaedian ordered field.
*)

Definition Qlt_is_strict_order := Build_strictorder
 Qlt_is_transitive_unfolded Qlt_is_antisymmetric_unfolded.

Definition Q_is_COrdField := Build_is_COrdField Q_as_CField
 Qlt_is_CSetoid_relation Qlt_is_strict_order Qplus_resp_Qlt
 Qmult_resp_pos_Qlt Qlt_gives_apartness.

Definition Q_as_COrdField := Build_COrdField _ _ Q_is_COrdField.

Theorem Q_is_archemaedian : forall x : Q_as_COrdField, {n : nat | x [<] nring n}.
Proof.
 intros.
 case x.
 intros p q.
 
 exists (S (Zabs_nat p)). 
 astepr (inject_Z (S (Zabs_nat p))).

 unfold inject_Z in |- *.
 unfold zring in |- *.
 simpl in |- *.
 red in |- *.
 unfold num at 1 in |- *. 
 unfold den in |- *.
 apply toCProp_Zlt. 
 simpl in |- *.
 rewrite Zmult_1_r.
 apply Zlt_le_trans with (P_of_succ_nat (Zabs_nat p) * 1)%Z.
 rewrite Zmult_1_r.
 case p; simpl in |- *; auto with zarith.
 intros; rewrite P_of_succ_nat_o_nat_of_P_eq_succ; rewrite Pplus_one_succ_r.
 change (p0 < p0 + 1)%Z in |- *.
 auto with zarith.
 intros; unfold Zlt in |- *; auto.
 change
   (P_of_succ_nat (Zabs_nat p) * 1%positive <= P_of_succ_nat (Zabs_nat p) * q)%Z
  in |- *.
 apply Zmult_le_compat_l.
 change (Zsucc 0 <= q)%Z in |- *.
 apply Zgt_le_succ.
 auto with zarith.
 auto with zarith.

 apply eq_symmetric_unfolded. 
 apply nring_Q.
Qed.
