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
Require Export CoRN.reals.Series.

Section SeqProperties.

Definition seq_pos (x : nat -> IR) := forall n : nat, [0] [<] x n.
Definition seq_inf_sum (x : nat -> IR) :=
forall M : IR, {N : nat | forall m : nat, N <= m -> M [<] seq_part_sum x m}.

Lemma One_part_sum : forall (m : nat),  seq_part_sum (fun n : nat => [1]) m [=] nring m.
Proof.
 intros.
 induction m; simpl; algebra.
Qed.

Lemma One_seq_is_pos : seq_pos (fun n : nat => [1]).
Proof.
 unfold seq_pos.
 intros. apply pos_one.
Qed.

Lemma One_seq_is_inf_sum : seq_inf_sum (fun n : nat => [1]).
Proof.
 unfold seq_inf_sum.
 intros.
 assert ({N : nat | M [<] nring N}).
  apply Archimedes'.
 destruct X as [N H].
 exists N. intros.
 apply less_leEq_trans with (nring (R:=IR) N); auto.
 assert (seq_part_sum (fun n : nat => [1]) m [=] nring m).
  apply One_part_sum.
 astepr (nring (R:=IR) m).
 apply nring_leEq.
 auto.
Qed.

Lemma seq_pos_imp_sum_pos : forall (x : nat -> IR), seq_pos x -> forall n, [0] [<] seq_part_sum x (S n).
Proof.
 intros.
 induction n.
  simpl.
  astepl ([0][+][0]:IR).
  apply plus_resp_less_lft. apply X.
  simpl.
 simpl in |- *.
 apply plus_resp_pos.
  apply IHn.
 apply X.
Qed.

Lemma seq_pos_imp_sum_pos' :
    forall (x : nat -> IR) (H1 : seq_pos x) (n m : nat) (H2 : m < n),
    [0] [<] Sum m n x.
Proof.
 unfold seq_pos.
 intros.
 induction n.
  assert (~ m < 0). auto with arith. contradiction.
   elim (le_lt_eq_dec _ _ H2); intros H3.
  astepr (Sum m n x [+] x (S n)).
  apply plus_resp_pos.
   apply IHn; auto with arith.
  apply H1.
 replace n with m; auto.
 astepr (Sum m m x [+]x (S m)).
 apply plus_resp_pos.
  astepr (x m).
  apply H1.
 apply H1.
Qed.

Lemma seq_pos_imp_ap_zero : forall (x : nat -> IR), seq_pos x -> forall n, seq_part_sum x (S n) [#] [0].
Proof.
 unfold seq_pos.
 intros.
 apply ap_symmetric_unfolded.
 apply less_imp_ap.
 apply seq_pos_imp_sum_pos; auto.
Qed.

Lemma seq_inf_sum_imp_div_small :
forall (x : nat -> IR) (H1 :  seq_inf_sum x) (H2:  seq_pos x) (C e : IR)
(H4 : [0] [<] e), { N : nat |
  forall m : nat, N <= m -> AbsSmall e (C [/](seq_part_sum x (S m)) [//] (seq_pos_imp_ap_zero x H2 m))}.
Proof.
 unfold seq_inf_sum. unfold seq_pos.
 intros.
 assert ({N : nat | forall m : nat,
   N <= m -> ((AbsIR C)[/]e[//]pos_ap_zero IR e H4)[<]seq_part_sum x m}).
  apply (H1 ((AbsIR C) [/] e [//] (pos_ap_zero IR e H4))).
 destruct X as [N H].
 exists N.
 intros.
 assert (H3 : ((AbsIR C)[/]e[//]pos_ap_zero IR e H4)[<]seq_part_sum x (S m)).
  apply H; auto.
 astepr ((C [/] seq_part_sum x (S m)[//] (seq_pos_imp_ap_zero x H2 m))).
 assert (AbsSmall ((seq_part_sum x (S m))[*]e) C).
  apply AbsIR_imp_AbsSmall.
  apply less_leEq.
  apply (shift_less_mult IR (AbsIR C) (seq_part_sum x (S m)) e (pos_ap_zero IR e H4)); auto.
 rstepl ((seq_part_sum x (S m))[*]e [/] (seq_part_sum x (S m))[//]
   pos_ap_zero IR (seq_part_sum x (S m)) (seq_pos_imp_sum_pos x H2 m)).
 rstepr (C [/] (seq_part_sum x (S m))[//]
   pos_ap_zero IR (seq_part_sum x (S m)) (seq_pos_imp_sum_pos x H2 m)).
 apply div_resp_AbsSmall.
 auto.
Qed.

Lemma seq_inf_sum_ratio_bound :
forall  (y : nat->IR) (H2 : seq_pos y) (m N1: nat) (H3: S N1 < m),
AbsSmall [1] (Sum (G:=IR) (S N1) m (fun k : nat => y k)[/]
	          seq_part_sum y (S m)[//]seq_pos_imp_ap_zero y H2 m).
Proof.
 intros.
 apply leEq_imp_AbsSmall.
  apply shift_leEq_div.
   apply seq_pos_imp_sum_pos; auto.
  astepl ([0]:IR).
  apply less_leEq.
  apply seq_pos_imp_sum_pos'; auto.
 apply shift_div_leEq.
  apply seq_pos_imp_sum_pos; auto.
 astepl (Sum (G:=IR) (S N1) m y).
 astepr (seq_part_sum y (S m)).
 unfold Sum. unfold Sum1. unfold seq_part_sum.
 apply shift_zero_leEq_minus'.
 rstepr (Sum0 (G:=IR) (S N1) y).
 apply less_leEq.
 astepr (seq_part_sum y (S N1)).
 apply seq_pos_imp_sum_pos; auto.
Qed.

End SeqProperties.
