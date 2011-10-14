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
Require Export Series.
Require Export PosSeq.

Section AlgebraBits.

Lemma algebraic_transform1 : forall (l : IR) (x : nat->IR) (y : nat->IR)
(H2 : seq_pos y) (m : nat),
(seq_part_sum (fun k : nat => y k [*] (x k [-] l)) (S m)[/]
       seq_part_sum y (S m)[//]seq_pos_imp_ap_zero y H2 m) [=]
((seq_part_sum (fun k : nat => x k[*]y k) (S m)[/]
       seq_part_sum y (S m)[//]seq_pos_imp_ap_zero y H2 m)[-]l).
Proof.
 intros.
 rstepr (((seq_part_sum (fun k : nat => x k[*]y k) (S m))[-] l[*](seq_part_sum y (S m)))[/]
   seq_part_sum y (S m)[//]seq_pos_imp_ap_zero y H2 m).
 apply div_wd.
  2: apply eq_reflexive_unfolded.
 unfold seq_part_sum.
 unfold cg_minus.
 astepr (Sum0 (G:=IR) (S m) (fun k : nat => x k[*]y k)[+]
   Sum0 (G:=IR) (S m) (fun k : nat => [--]l[*]y k)).
  astepr (Sum0 (G:=IR) (S m) (fun k : nat => x k[*]y k[+][--]l[*]y k)).
   apply Sum0_wd. intros. rational.
   apply (Sum0_plus_Sum0 IR (fun k : nat => x k [*] y k) (fun k : nat => [--] l [*] y k) (S m)).
 apply plus_resp_eq.
 astepr ([--]l [*] (Sum0 (G:=IR) (S m) y)).
 apply mult_distr_sum0_lft.
Qed.

Lemma algebraic_transform2 : forall (l : IR) (x : nat->IR) (y : nat->IR)
(H2 : seq_pos y) (m N1: nat),
(( seq_part_sum (fun k : nat => y k [*] (x k [-] l)) (S N1)[+]
       Sum (S N1) m (fun k : nat => y k [*] (x k [-] l)) )[/]
       seq_part_sum y (S m)[//]seq_pos_imp_ap_zero y H2 m) [=]
(seq_part_sum (fun k : nat => y k [*] (x k [-] l)) (S m)[/]
       seq_part_sum y (S m)[//]seq_pos_imp_ap_zero y H2 m).
Proof.
 intros.
 unfold seq_part_sum.
 apply div_wd.
  2: apply eq_reflexive_unfolded.
 unfold Sum.
 unfold Sum1.
 rational.
Qed.

Lemma algebraic_transform3:  forall (eps: IR) (y : nat->IR)
(H2 : seq_pos y) (m N1: nat),
(eps[/]TwoNZ [*] (Sum (S N1) m (fun k: nat => y k)[/]
        seq_part_sum y (S m)[//]seq_pos_imp_ap_zero y H2 m)) [=]
(Sum (G:=IR) (S N1) m (fun k : nat => y k[*]eps [/]TwoNZ)[/]
  seq_part_sum y (S m)[//]seq_pos_imp_ap_zero y H2 m).
Proof.
 intros.
 astepl ((eps[/]TwoNZ [*] (Sum (S N1) m (fun k: nat => y k)))[/]
   seq_part_sum y (S m)[//]seq_pos_imp_ap_zero y H2 m).
 astepr (Sum (G:=IR) (S N1) m (fun k : nat => eps[/]TwoNZ[*]y k)[/]
   seq_part_sum y (S m)[//]seq_pos_imp_ap_zero y H2 m).
 apply div_wd.
  2: apply eq_reflexive_unfolded.
 apply eq_symmetric_unfolded.
 astepr (eps[/]TwoNZ[*]Sum (G:=IR) (S N1) m y).
 apply mult_distr_sum_lft.
Qed.

Lemma algebraic_estimate1 :
forall (e l: IR) (H1 : [0] [<] e) (x : nat -> IR) (y : nat->IR)
(H2 : seq_pos y) (m N1: nat) (H3 : S N1 <= m)
(H4 : forall i, S N1 <= i -> i <= m -> AbsSmall e (x i[-]l)),
AbsSmall
   (Sum (G:=IR) (S N1) m (fun k : nat => y k[*]e)[/]
    seq_part_sum y (S m)[//]seq_pos_imp_ap_zero y H2 m)
 (Sum (G:=IR) (S N1) m (fun k : nat => y k[*](x k[-]l))[/]
   seq_part_sum y (S m)[//]seq_pos_imp_ap_zero y H2 m).
Proof.
 intros.
 apply AbsSmall_cancel_mult with (seq_part_sum y (S m)).
  apply seq_pos_imp_sum_pos; auto.
 astepl (Sum (G:=IR) (S N1) m (fun k : nat => y k[*]e)).
 astepr (Sum (G:=IR) (S N1) m (fun k : nat => y k[*](x k[-]l))).
 apply sum_resp_AbsSmall; auto.
 intros.
 apply mult_resp_AbsSmall.
  apply less_leEq.
  apply H2.
 apply H4; auto.
Qed.

End AlgebraBits.

Section Cesaro.

Theorem cesaro_transform :
forall (l : IR) (x : nat -> IR) (y : nat -> IR)
(H1 : Cauchy_Lim_prop2 x l)
(H2 : seq_pos y) (H3 : seq_inf_sum y),
Cauchy_Lim_prop2 (fun n : nat => seq_part_sum (fun k : nat => x k [*] y k) (S n)
      [/](seq_part_sum y (S n)) [//] (seq_pos_imp_ap_zero y H2 n)) l.
Proof.
 unfold Cauchy_Lim_prop2.
 intros.
 (* Find N such that forall m > N |x - l| < eps / 2*)
 assert (H4 : [0] [<] eps[/]TwoNZ). apply pos_div_two. auto.
  assert ({N : nat | forall m, N <= m -> AbsSmall (eps[/]TwoNZ) ((x m) [-] l) }).
  apply (H1 (eps[/]TwoNZ) H4).
 destruct X0 as [N1 H5].
 (* find N1 such that a the following will be less that eps/2 also *)
 set (C := seq_part_sum (fun k : nat => y k [*] (x k [-] l)) (S N1)); assert (H7 : { N : nat |
   forall m : nat, N <= m -> AbsSmall (eps[/]TwoNZ) (C [/](seq_part_sum y (S m)) [//] (seq_pos_imp_ap_zero y H2 m))}).
  apply (seq_inf_sum_imp_div_small y H3 H2 C (eps[/]TwoNZ) H4).
 destruct H7 as [N2 H7].
 (* Now we can choose N as max of N1 and N2 *)
 exists (S (max (S N1) N2)).
 intros.
 astepr (seq_part_sum (fun k : nat => y k [*] (x k [-] l)) (S m)[/]
   seq_part_sum y (S m)[//]seq_pos_imp_ap_zero y H2 m).
  2: apply (algebraic_transform1 l x y H2 m).
 astepr ((seq_part_sum (fun k : nat => y k [*] (x k [-] l)) (S N1)[+]
   Sum (S N1) m (fun k : nat => y k [*] (x k [-] l)) )[/]
     seq_part_sum y (S m)[//]seq_pos_imp_ap_zero y H2 m).
  2: apply (algebraic_transform2 l x y H2 m).
 astepr (((seq_part_sum (fun k : nat => y k [*] (x k [-] l)) (S N1))
   [/]seq_part_sum y (S m)[//]seq_pos_imp_ap_zero y H2 m) [+]
     ((Sum (S N1) m (fun k : nat => y k [*] (x k [-] l)))[/]
       seq_part_sum y (S m)[//]seq_pos_imp_ap_zero y H2 m)).
 apply AbsSmall_eps_div_two.
  (* We are ready for estimates *)
  apply H7.
  eauto with arith.
 apply AbsSmall_leEq_trans with ((Sum (S N1) m (fun k : nat => y k [*] eps [/]TwoNZ))[/]
   seq_part_sum y (S m)[//]seq_pos_imp_ap_zero y H2 m).
  astepl (eps[/]TwoNZ [*] (Sum (S N1) m (fun k: nat => y k)[/]
    seq_part_sum y (S m)[//]seq_pos_imp_ap_zero y H2 m)).
   2: apply algebraic_transform3.
  astepr (eps[/]TwoNZ[*][1]).
  apply mult_resp_leEq_lft.
   cut (AbsSmall [1] (Sum (G:=IR) (S N1) m (fun k : nat => y k)[/]
     seq_part_sum y (S m)[//]seq_pos_imp_ap_zero y H2 m)).
    unfold AbsSmall. tauto.
    apply seq_inf_sum_ratio_bound.
   eauto with arith.
  apply less_leEq; auto.
 apply algebraic_estimate1; auto.
  eauto with arith.
 intros.
 apply H5.
 auto with arith.
Qed.

Theorem cesaro_sum :
forall (l : IR) (x : nat -> IR) (H1 : Cauchy_Lim_prop2 x l),
Cauchy_Lim_prop2 (fun n : nat => seq_part_sum x (S n)
      [/]nring (S n)[//](nringS_ap_zero _ n)) l.
Proof.
 intros.
 set (y := (fun k : nat => [1] : IR)).
 assert (H2 : seq_pos y).
  apply One_seq_is_pos.
 assert (H3 : seq_inf_sum y).
  apply One_seq_is_inf_sum.
 apply Cauchy_Lim_prop2_wd' with (fun n : nat => seq_part_sum (fun k : nat => x k[*] y k) (S n)
   [/]seq_part_sum y (S n)[//]seq_pos_imp_ap_zero y H2 n).
  apply cesaro_transform; auto.
 exists 0.
 intros.
 apply div_wd.
  unfold seq_part_sum.
  apply Sum0_wd.
  intros. unfold y. algebra.
  apply One_part_sum.
Qed.

End Cesaro.

