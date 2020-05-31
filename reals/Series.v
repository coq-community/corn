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
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; either version 2.1 of the License, or
 * (at your option) any later version.
 *
 * This work is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along
 * with this work; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 *)

(** printing seq_part_sum %\ensuremath{\sum^n}% #&sum;<sup>n</sup># *)
(** printing series_sum %\ensuremath{\sum_0^{\infty}}% #&sum;<sub>0</sub><sup>&infin;</sup># *)
(** printing pi %\ensuremath{\pi}% #&pi; *)

Require Export CoRN.reals.CSumsReals.
Require Export CoRN.reals.NRootIR.

Section Definitions.

(**
* Series of Real Numbers
In this file we develop a theory of series of real numbers.
** Definitions

A series is simply a sequence from the natural numbers into the reals.
To each such sequence we can assign a sequence of partial sums.

%\begin{convention}% Let [x:nat->IR].
%\end{convention}%
*)

Variable x : nat -> IR.

Definition seq_part_sum (n : nat) := Sum0 n x.

(**
For subsequent purposes it will be very useful to be able to write the
difference between two arbitrary elements of the sequence of partial
sums as a sum of elements of the original sequence.
*)

Lemma seq_part_sum_n : forall m n,
 0 < n -> m <= n -> seq_part_sum n[-]seq_part_sum m [=] Sum m (pred n) x.
Proof.
 intros.
 elim (le_lt_eq_dec _ _ H0); intro.
  unfold seq_part_sum in |- *.
  unfold Sum, Sum1 in |- *.
  rewrite <- S_pred with n 0; auto.
  algebra.
 rewrite b.
 astepl ZeroR.
 apply eq_symmetric_unfolded; apply Sum_empty.
 assumption.
Qed.

(** A series is convergent iff its sequence of partial Sums is a
Cauchy sequence.  To each convergent series we can assign a Sum.
*)

Definition convergent := Cauchy_prop seq_part_sum.

Definition series_sum (H : convergent) := Lim (Build_CauchySeq _ _ H).

(** Divergence can be characterized in a positive way, which will sometimes
be useful.  We thus define divergence of sequences and series and prove the
obvious fact that no sequence can be both convergent and divergent, whether
 considered either as a sequence or as a series.
*)

Definition divergent_seq (a : nat -> IR) := {e : IR | [0] [<] e |
  forall k, {m : nat | {n : nat | k <= m /\ k <= n /\ e [<=] AbsIR (a m[-]a n)}}}.

Definition divergent := divergent_seq seq_part_sum.

Lemma conv_imp_not_div : forall a, Cauchy_prop a -> Not (divergent_seq a).
Proof.
 intros a Hconv.
 intro Hdiv.
 red in Hconv, Hdiv.
 elim Hdiv; clear Hdiv; intros e He He'.
 elim (Hconv _ (pos_div_three _ _ He)); clear Hconv; intros N HN.
 elim (He' N); clear He'; intros m Hm.
 elim Hm; clear Hm; intros n Hm'.
 elim Hm'; clear Hm'; intros Hm Hn.
 elim Hn; clear Hn; intros Hn Hmn.
 rewrite -> leEq_def in Hmn; apply Hmn.
 rstepr (e [/]ThreeNZ[+]e [/]ThreeNZ[+]e [/]ThreeNZ).
 apply leEq_less_trans with (AbsIR (a m[-]a N) [+]AbsIR (a N[-]a n)).
  eapply leEq_wdl.
   apply triangle_IR.
  apply AbsIR_wd; rational.
 astepl ([0][+]AbsIR (a m[-]a N) [+]AbsIR (a N[-]a n)).
 repeat apply plus_resp_less_leEq; try apply AbsSmall_imp_AbsIR; try exact (pos_div_three _ _ He).
  auto.
 apply AbsSmall_minus; auto.
Qed.

Lemma div_imp_not_conv : forall a, divergent_seq a -> Not (Cauchy_prop a).
Proof.
 intros a H.
 red in |- *; intro H0.
 generalize H; generalize H0.
 apply conv_imp_not_div.
Qed.

Lemma convergent_imp_not_divergent : convergent -> Not divergent.
Proof.
 intro H.
 intro H0.
 red in H, H0.
 generalize H0; apply conv_imp_not_div.
 assumption.
Qed.

Lemma divergent_imp_not_convergent : divergent -> Not convergent.
Proof.
 intro H.
 intro H0.
 red in H, H0.
 generalize H0; apply div_imp_not_conv.
 assumption.
Qed.

(** Finally we have the well known fact that every convergent series converges
to zero as a sequence.
*)

Lemma series_seq_Lim : convergent -> Cauchy_Lim_prop2 x [0].
Proof.
 intros H.
 red in |- *. intros eps H0.
 red in H.
 red in H.
 elim (H _ (pos_div_two _ _ H0)).
 intros N HN.
 exists (max N 1); intros.
 apply AbsSmall_wdr_unfolded with (seq_part_sum (S m) [-]seq_part_sum m).
  apply AbsSmall_wdr_unfolded with
    (seq_part_sum (S m) [-]seq_part_sum N[+] (seq_part_sum N[-]seq_part_sum m)).
   rstepl (eps [/]TwoNZ[+]eps [/]TwoNZ).
   apply AbsSmall_plus.
    apply HN.
    apply le_trans with (max N 1); auto with arith.
   apply AbsSmall_minus; apply HN.
   apply le_trans with (max N 1); auto with arith.
  rational.
 eapply eq_transitive_unfolded.
  apply seq_part_sum_n; auto with arith.
 simpl in |- *; astepr (x m); apply Sum_one.
Qed.

Lemma series_seq_Lim' : convergent -> forall H, Lim (Build_CauchySeq _ x H) [=] [0].
Proof.
 intros.
 apply eq_symmetric_unfolded; apply Limits_unique.
 apply series_seq_Lim; auto.
Qed.

End Definitions.

Section More_Definitions.

Variable x : nat -> IR.

(** We also define absolute convergence. *)

Definition abs_convergent := convergent (fun n => AbsIR (x n)).

End More_Definitions.

Section Power_Series.

(**
** Power Series

Power series are an important special case.
*)

Definition power_series (c : IR) n := c[^]n.

(**
Specially important is the case when [c] is a real number
whose absolute value is less than 1; in this case not only the power series is convergent, but
we can also compute its sum.

%\begin{convention}% Let [c] be a real number between -1 and 1.
%\end{convention}%
*)

Variable c : IR.
Hypothesis Hc : AbsIR c [<] [1].

Lemma c_exp_Lim : Cauchy_Lim_prop2 (power_series c) [0].
Proof.
 red in |- *; intros eps H.
 elim (qi_yields_zero (AbsIR c) (AbsIR_nonneg _) Hc eps H).
 intros N Hn.
 exists N; intros.
 unfold power_series in |- *.
 astepr (c[^]m).
 apply AbsSmall_transitive with (c[^]N).
  apply AbsIR_imp_AbsSmall.
  eapply leEq_wdl.
   apply Hn.
  apply eq_symmetric_unfolded; apply (AbsIR_nexp c N).
 eapply leEq_wdl.
  2: apply eq_symmetric_unfolded; apply (AbsIR_nexp c m).
 eapply leEq_wdr.
  2: apply eq_symmetric_unfolded; apply (AbsIR_nexp c N).
 change ((AbsIR c)[^]m[<=](AbsIR c)[^]N).
 apply nexp_resp_le'.
   apply AbsIR_nonneg.
  apply less_leEq; assumption.
 assumption.
Qed.

Lemma power_series_Lim1 : forall H : [1][-]c [#] [0],
 Cauchy_Lim_prop2 (seq_part_sum (power_series c)) ([1][/] _[//]H).
Proof.
 intro.
 red in |- *.
 intros.
 unfold power_series in |- *; unfold seq_part_sum in |- *.
 cut ({N : nat | (AbsIR c)[^]N [<=] eps[*]AbsIR ([1][-]c)}).
  intro H1.
  elim H1; clear H1; intros N HN.
  exists N; intros.
  apply AbsSmall_wdr_unfolded with ( [--] (c[^]m[/] _[//]H)).
   apply inv_resp_AbsSmall.
   apply AbsIR_imp_AbsSmall.
   eapply leEq_wdl.
    2: apply eq_symmetric_unfolded.
    2: apply (AbsIR_division (c[^]m) ([1][-]c) H (AbsIR_resp_ap_zero _ H)).
   apply shift_div_leEq.
    apply AbsIR_pos; assumption.
   eapply leEq_wdl.
    2: apply eq_symmetric_unfolded; apply AbsIR_nexp_op.
   eapply leEq_transitive.
    2: apply HN.
   apply nexp_resp_le'; auto.
    apply AbsIR_nonneg.
   apply less_leEq; auto.
  astepl ( [--] (c[^]m[/] _[//]H) [+] ([1][/] _[//]H) [-] ([1][/] _[//]H)).
  apply cg_minus_wd.
   2: algebra.
  cut (c[-][1] [#] [0]). intros H2.
   apply eq_symmetric_unfolded; eapply eq_transitive_unfolded.
    apply Sum0_c_exp with (H := H2).
   rational.
  apply minus_ap_zero.
  apply ap_symmetric.
  apply zero_minus_apart.
  assumption.
 apply qi_yields_zero.
   apply AbsIR_nonneg.
  assumption.
 apply less_wdl with ([0][*]AbsIR ([1][-]c)).
  apply mult_resp_less.
   assumption.
  apply AbsIR_pos.
  assumption.
 apply cring_mult_zero_op.
Qed.

Lemma power_series_conv : convergent (power_series c).
Proof.
 intros.
 red in |- *.
 apply Cauchy_prop2_prop.
 cut ([1][-]c [#] [0]).
  intro H.
  exists ([1][/] _[//]H).
  apply power_series_Lim1.
 apply minus_ap_zero.
 apply Greater_imp_ap.
 eapply leEq_less_trans.
  apply leEq_AbsIR.
 assumption.
Qed.

Lemma power_series_sum : forall H Hc,
 series_sum (power_series c) Hc [=] ([1][/] [1][-]c[//]H).
Proof.
 intros.
 unfold series_sum in |- *.
 apply eq_symmetric_unfolded; apply Limits_unique.
 apply power_series_Lim1.
Qed.

End Power_Series.

Section Operations.

(**
** Operations

Some operations with series preserve convergence.  We start by defining
the series that is zero everywhere.
*)

Lemma conv_zero_series : convergent (fun n => [0]).
Proof.
 exists 0.
 intros.
 simpl in |- *.
 eapply AbsSmall_wdr_unfolded.
  apply zero_AbsSmall; apply less_leEq; assumption.
 unfold seq_part_sum in |- *.
 induction  m as [| m Hrecm].
  simpl in |- *; algebra.
 simpl in |- *.
 eapply eq_transitive_unfolded.
  apply Hrecm; auto with arith.
 rational.
Qed.

Lemma series_sum_zero : forall H : convergent (fun n => [0]), series_sum _ H [=] [0].
Proof.
 intro.
 unfold series_sum in |- *.
 apply eq_symmetric_unfolded; apply Limits_unique.
 exists 0.
 intros.
 simpl in |- *.
 eapply AbsSmall_wdr_unfolded.
  apply zero_AbsSmall; apply less_leEq; assumption.
 unfold seq_part_sum in |- *.
 induction  m as [| m Hrecm].
  simpl in |- *; algebra.
 simpl in |- *.
 eapply eq_transitive_unfolded.
  apply Hrecm; auto with arith.
 rational.
Qed.

(** Next we consider extensionality, as well as the sum and difference
of two convergent series.

%\begin{convention}% Let [x,y:nat->IR] be convergent series.
%\end{convention}%
*)

Variables x y : nat -> IR.

Hypothesis convX : convergent x.
Hypothesis convY : convergent y.

Lemma convergent_wd : (forall n, x n [=] y n) -> convergent x -> convergent y.
Proof.
 intros H H0.
 red in |- *; red in H0.
 apply Cauchy_prop_wd with (seq_part_sum x).
  assumption.
 intro.
 unfold seq_part_sum in |- *.
 apply Sum0_wd.
 assumption.
Qed.

Lemma series_sum_wd : (forall n, x n [=] y n) -> series_sum _ convX [=] series_sum _ convY.
Proof.
 intros.
 unfold series_sum in |- *.
 apply Lim_wd'.
 intro; simpl in |- *.
 unfold seq_part_sum in |- *.
 apply Sum0_wd; assumption.
Qed.

Lemma conv_series_plus : convergent (fun n => x n[+]y n).
Proof.
 red in |- *.
 red in convX, convY.
 eapply Cauchy_prop_wd.
  apply Cauchy_plus with (seq1 := Build_CauchySeq _ _ convX) (seq2 := Build_CauchySeq _ _ convY).
 simpl in |- *.
 unfold seq_part_sum in |- *.
 intro.
 apply eq_symmetric_unfolded; apply Sum0_plus_Sum0.
Qed.

Lemma series_sum_plus : forall H : convergent (fun n => x n[+]y n),
 series_sum _ H [=] series_sum _ convX[+]series_sum _ convY.
Proof.
 intros.
 unfold series_sum in |- *.
 eapply eq_transitive_unfolded.
  2: apply Lim_plus.
 apply Lim_wd'.
 intro; simpl in |- *.
 unfold seq_part_sum in |- *.
 apply Sum0_plus_Sum0.
Qed.

Lemma conv_series_minus : convergent (fun n => x n[-]y n).
Proof.
 red in |- *.
 red in convX, convY.
 eapply Cauchy_prop_wd.
  apply Cauchy_minus with (seq1 := Build_CauchySeq _ _ convX) (seq2 := Build_CauchySeq _ _ convY).
 simpl in |- *.
 unfold seq_part_sum in |- *.
 intro.
 apply eq_symmetric_unfolded; unfold cg_minus in |- *.
 eapply eq_transitive_unfolded.
  apply Sum0_plus_Sum0 with (g := fun n : nat => [--] (y n)).
 apply bin_op_wd_unfolded.
  algebra.
 apply inv_Sum0.
Qed.

Lemma series_sum_minus : forall H : convergent (fun n => x n[-]y n),
 series_sum _ H [=] series_sum _ convX[-]series_sum _ convY.
Proof.
 intros.
 unfold series_sum in |- *.
 eapply eq_transitive_unfolded.
  2: apply Lim_minus.
 apply Lim_wd'.
 intro; simpl in |- *.
 unfold seq_part_sum in |- *.
 unfold cg_minus in |- *.
 eapply eq_transitive_unfolded.
  apply Sum0_plus_Sum0 with (g := fun n : nat => [--] (y n)).
 apply bin_op_wd_unfolded.
  algebra.
 apply inv_Sum0.
Qed.

(** Multiplication by a scalar [c] is also permitted. *)

Variable c : IR.

Lemma conv_series_mult_scal : convergent (fun n => c[*]x n).
Proof.
 red in |- *.
 red in convX.
 eapply Cauchy_prop_wd.
  apply Cauchy_mult with (seq2 := Build_CauchySeq _ _ convX) (seq1 := Cauchy_const c).
 simpl in |- *.
 unfold seq_part_sum in |- *.
 intro.
 apply eq_symmetric_unfolded.
 apply Sum0_comm_scal'.
Qed.

Lemma series_sum_mult_scal : forall H : convergent (fun n => c[*]x n),
 series_sum _ H [=] c[*]series_sum _ convX.
Proof.
 intros.
 unfold series_sum in |- *.
 apply eq_transitive_unfolded with (Lim (Cauchy_const c) [*]Lim (Build_CauchySeq _ _ convX)).
  2: apply mult_wdl; apply eq_symmetric_unfolded; apply Lim_const.
 eapply eq_transitive_unfolded.
  2: apply Lim_mult.
 apply Lim_wd'.
 intro; simpl in |- *.
 unfold seq_part_sum in |- *.
 apply Sum0_comm_scal'.
Qed.

End Operations.

Section More_Operations.

Variable x : nat -> IR.
Hypothesis convX : convergent x.

(** As a corollary, we get the series of the inverses. *)

Lemma conv_series_inv : convergent (fun n => [--] (x n)).
Proof.
 red in |- *.
 red in convX.
 eapply Cauchy_prop_wd.
  apply Cauchy_minus with (seq1 := Cauchy_const [0]) (seq2 := Build_CauchySeq _ _ convX).
 simpl in |- *.
 unfold seq_part_sum in |- *.
 intro.
 apply eq_symmetric_unfolded;
   apply eq_transitive_unfolded with ([0][+]Sum0 n (fun n : nat => [--] (x n))).
  algebra.
 unfold cg_minus in |- *; apply bin_op_wd_unfolded.
  algebra.
 apply inv_Sum0.
Qed.

Lemma series_sum_inv : forall H : convergent (fun n => [--] (x n)),
 series_sum _ H [=] [--] (series_sum _ convX).
Proof.
 intros.
 set (y := Cauchy_const [0]) in *.
 cut (convergent y). intros H0.
  eapply eq_transitive_unfolded.
   apply series_sum_wd with (y := fun n : nat => y n[-]x n) (convY := conv_series_minus _ _ H0 convX).
   intro; unfold y in |- *; simpl in |- *; algebra.
  cut (series_sum y H0 [=] [0]); intros.
   astepr ([0][-]series_sum x convX).
   astepr (series_sum y H0[-]series_sum x convX).
   apply series_sum_minus.
  apply series_sum_zero.
 apply conv_zero_series.
Qed.

End More_Operations.

Section Almost_Everywhere.

(**
** Almost Everywhere

In this section we strengthen some of the convergence results for sequences
and derive an important corollary for series.

Let [x,y : nat->IR] be equal after some natural number.
*)

Variables x y : nat -> IR.

Definition aew_eq := {n : nat | forall k, n <= k -> x k [=] y k}.

Hypothesis aew_equal : aew_eq.

Lemma aew_Cauchy : Cauchy_prop x -> Cauchy_prop y.
Proof.
 intro H.
 red in |- *; intros e H0.
 elim (H _ (pos_div_two _ _ H0)).
 intros N HN.
 elim aew_equal; intros n Hn.
 exists (max n N).
 intros.
 apply AbsSmall_wdr_unfolded with (x m[-]x (max n N)).
  rstepr (x m[-]x N[+] (x N[-]x (max n N))).
  rstepl (e [/]TwoNZ[+]e [/]TwoNZ).
  apply AbsSmall_plus.
   apply HN; apply le_trans with (max n N); auto with arith.
  apply AbsSmall_minus; apply HN; apply le_trans with (max n N); auto with arith.
 apply cg_minus_wd; apply Hn.
  apply le_trans with (max n N); auto with arith.
 apply le_max_l.
Qed.

Lemma aew_Cauchy2 : forall c, Cauchy_Lim_prop2 x c -> Cauchy_Lim_prop2 y c.
Proof.
 intros c H.
 red in |- *; intros eps H0.
 elim (H eps H0).
 intros N HN.
 elim aew_equal; intros n Hn.
 exists (max n N).
 intros.
 apply AbsSmall_wdr_unfolded with (x m[-]c).
  apply HN; apply le_trans with (max n N); auto with arith.
 apply cg_minus_wd; [ apply Hn | algebra ].
 apply le_trans with (max n N); auto with arith.
Qed.

Lemma aew_series_conv : convergent x -> convergent y.
Proof.
 intro H.
 red in |- *; red in |- *; intros. rename X into H0.
 elim (H _ (pos_div_two _ _ H0)); intros N HN.
 elim aew_equal; intros n Hn.
 set (k := max (max n N) 1) in *.
 exists k; intros.
 apply AbsSmall_wdr_unfolded with (seq_part_sum x m[-]seq_part_sum x k).
  rstepr (seq_part_sum x m[-]seq_part_sum x N[+] (seq_part_sum x N[-]seq_part_sum x k)).
  rstepl (e [/]TwoNZ[+]e [/]TwoNZ).
  apply AbsSmall_plus.
   apply HN; cut (N <= k).
    omega.
   apply le_trans with (max n N); unfold k in |- *; auto with arith.
  apply AbsSmall_minus; apply HN; auto.
  apply le_trans with (max n N); unfold k in |- *; auto with arith.
 cut (1 <= k); intros.
  eapply eq_transitive_unfolded.
   apply seq_part_sum_n; auto.
   apply lt_le_trans with k; auto.
  eapply eq_transitive_unfolded.
   2: apply eq_symmetric_unfolded; apply seq_part_sum_n; auto.
   2: apply lt_le_trans with k; auto.
  apply Sum_wd'.
   rewrite <- S_pred with m 0; auto with arith.
   apply lt_le_trans with k; auto.
  intros; apply Hn.
  apply le_trans with (max n N); auto with arith.
  apply le_trans with k; unfold k in |- *; auto with arith.
 unfold k in |- *; apply le_max_r.
Qed.

End Almost_Everywhere.

Section Cauchy_Almost_Everywhere.

(** Suppose furthermore that [x,y] are Cauchy sequences. *)

Variables x y : CauchySeq IR.

Hypothesis aew_equal : aew_eq x y.

Lemma aew_Lim : Lim x [=] Lim y.
Proof.
 intros.
 cut (Cauchy_Lim_prop2 x (Lim y)).
  intro.
  apply eq_symmetric_unfolded.
  apply Limits_unique; assumption.
 apply aew_Cauchy2 with (y:nat -> IR).
  elim aew_equal; intros n Hn; exists n; intros.
  apply eq_symmetric_unfolded; apply Hn; auto.
 apply Cauchy_complete.
Qed.

End Cauchy_Almost_Everywhere.

Section Convergence_Criteria.

(**
** Convergence Criteria

%\begin{convention}% Let [x:nat->IR].
%\end{convention}%
*)

Variable x : nat -> IR.

(** We include the comparison test for series, both in a strong and in a less
general (but simpler) form.
*)

Lemma str_comparison : forall y, convergent y ->
 {k : nat | forall n, k <= n -> AbsIR (x n) [<=] y n} -> convergent x.
Proof.
 intros y H H0.
 elim H0; intros k Hk.
 red in |- *; red in |- *; intros.
 cut {N : nat | k < N /\
   (forall m : nat, N <= m -> AbsSmall e (seq_part_sum y m[-]seq_part_sum y N))}. intros H2.
  elim H2; clear H2.
  intros N HN; elim HN; clear HN; intros HN' HN.
  exists N; intros.
  apply AbsIR_imp_AbsSmall.
  apply leEq_transitive with (seq_part_sum y m[-]seq_part_sum y N).
   apply leEq_transitive with (Sum N (pred m) (fun n : nat => AbsIR (x n))).
    apply leEq_wdl with (AbsIR (Sum N (pred m) x)).
     2: apply AbsIR_wd; apply eq_symmetric_unfolded; apply seq_part_sum_n; auto.
     2: apply lt_le_trans with N; auto; apply le_lt_trans with k; auto with arith.
    apply triangle_SumIR.
    rewrite <- (S_pred m k); auto with arith.
    apply lt_le_trans with N; auto.
   eapply leEq_wdr.
    2: apply eq_symmetric_unfolded; apply seq_part_sum_n; auto.
    2: apply le_lt_trans with k; auto with arith; apply lt_le_trans with N; auto.
   apply Sum_resp_leEq.
    rewrite <- (S_pred m k); auto with arith.
    apply lt_le_trans with N; auto.
   intros.
   apply Hk; apply le_trans with N; auto with arith.
  eapply leEq_transitive.
   apply leEq_AbsIR.
  apply AbsSmall_imp_AbsIR.
  apply HN; assumption. rename X into H1.
 elim (H _ (pos_div_two _ _ H1)).
 intros N HN; exists (S (max N k)).
 cut (N <= max N k); [ intro | apply le_max_l ].
 cut (k <= max N k); [ intro | apply le_max_r ].
 split.
  auto with arith.
 intros.
 rstepr (seq_part_sum y m[-]seq_part_sum y N[+] (seq_part_sum y N[-]seq_part_sum y (S (max N k)))).
 rstepl (e [/]TwoNZ[+]e [/]TwoNZ).
 apply AbsSmall_plus.
  apply HN; apply le_trans with (max N k); auto with arith.
 apply AbsSmall_minus; apply HN; auto with arith.
Qed.

Lemma comparison : forall y,
 convergent y -> (forall n, AbsIR (x n) [<=] y n) -> convergent x.
Proof.
 intros y H H0.
 apply str_comparison with y.
  assumption.
 exists 0; intros; apply H0.
Qed.

(** As a corollary, we get that every absolutely convergent series converges. *)

Lemma abs_imp_conv : abs_convergent x -> convergent x.
Proof.
 intros H.
 apply Convergence_Criteria.comparison with (fun n : nat => AbsIR (x n)).
  apply H.
 intro; apply leEq_reflexive.
Qed.

(** Next we have the ratio test, both as a positive and negative result. *)

Lemma divergent_crit : {r : IR | [0] [<] r | forall n, {m : nat | n <= m | r [<=] AbsIR (x m)}} ->
 divergent x.
Proof.
 intro H.
 elim H; clear H; intros r Hr H.
 exists r.
  assumption.
 intro.
 elim (H k); clear H; intros m Hm Hrm.
 exists (S m).
 exists m.
 split.
  auto.
 split.
  assumption.
 eapply leEq_wdr.
  apply Hrm.
 apply AbsIR_wd.
 apply eq_symmetric_unfolded.
 eapply eq_transitive_unfolded.
  apply seq_part_sum_n; auto with arith.
 apply Sum_one.
Qed.

Lemma tail_series : forall y, convergent y ->
 {k : nat | {N : nat | forall n, N <= n -> x n [=] y (n + k)}} -> convergent x.
Proof.
 red in |- *. intros y H H0.
 elim H0; intros k Hk.
 elim Hk; intros N HN.
 clear Hk H0.
 red in |- *. intros e H0.
 elim (H (e [/]TwoNZ) (pos_div_two _ _ H0)); intros M HM.
 exists (S (max N M)); intros.
 rstepl (e [/]TwoNZ[+]e [/]TwoNZ).
 apply AbsSmall_wdr_unfolded with (seq_part_sum y (m + k) [-]seq_part_sum y (S (max N M) + k)).
  rstepr (seq_part_sum y (m + k) [-]seq_part_sum y M[+]
    (seq_part_sum y M[-]seq_part_sum y (S (max N M) + k))).
  apply AbsSmall_plus.
   apply HM.
   apply le_trans with (max N M); auto with arith.
  apply AbsSmall_minus.
  apply HM.
  auto with arith.
 unfold seq_part_sum in |- *.
 apply eq_transitive_unfolded with (Sum (S (max N M) + k) (pred (m + k)) y).
  unfold Sum, Sum1 in |- *.
  rewrite <- S_pred with (m := 0).
   algebra.
  apply lt_le_trans with (S (max N M)); auto with arith.
 astepr (Sum (S (max N M)) (pred m) x).
  2: unfold Sum, Sum1 in |- *.
  2: rewrite <- S_pred with (m := 0).
   2: algebra.
  2: apply lt_le_trans with (S (max N M)); auto with arith.
 replace (pred (m + k)) with (pred m + k).
  apply eq_symmetric_unfolded; apply Sum_big_shift.
   intros; apply HN.
   apply le_trans with (max N M); auto with arith.
  rewrite <- S_pred with (m := 0); auto.
  apply lt_le_trans with (S (max N M)); auto with arith.
 omega.
Qed.

Lemma join_series : convergent x -> forall y,
 {k : nat | {N : nat | forall n, N <= n -> x n [=] y (n + k)}} -> convergent y.
Proof.
 red in |- *; intros H y H0.
 elim H0; intros k Hk.
 elim Hk; intros N HN.
 clear Hk H0.
 red in |- *; intros e H0.
 elim (H (e [/]TwoNZ) (pos_div_two _ _ H0)); intros M HM.
 exists (S (max N M + k)); intros.
 rstepl (e [/]TwoNZ[+]e [/]TwoNZ).
 apply AbsSmall_wdr_unfolded with (seq_part_sum x (m - k) [-]seq_part_sum x (S (max N M + k) - k)).
  rstepr (seq_part_sum x (m - k) [-]seq_part_sum x M[+]
    (seq_part_sum x M[-]seq_part_sum x (S (max N M + k) - k))).
  apply AbsSmall_plus.
   apply HM.
   apply (fun p n m : nat => plus_le_reg_l n m p) with k.
   rewrite <- le_plus_minus.
    apply le_trans with (max N M + k); auto with arith.
    rewrite plus_comm; auto with arith.
   apply le_trans with (S (max N M + k)); auto with arith.
  apply AbsSmall_minus.
  apply HM.
  apply (fun p n m : nat => plus_le_reg_l n m p) with k.
  rewrite <- le_plus_minus.
   apply le_trans with (max N M + k); auto.
   rewrite plus_comm; auto with arith.
  apply le_trans with (S (max N M + k)); auto with arith.
 unfold seq_part_sum in |- *.
 apply eq_transitive_unfolded with (Sum (S (max N M + k) - k) (pred (m - k)) x).
  unfold Sum, Sum1 in |- *.
  rewrite <- S_pred with (m := 0).
   algebra.
  omega.
 astepr (Sum (S (max N M + k)) (pred m) y).
  2: unfold Sum, Sum1 in |- *.
  2: rewrite <- S_pred with (m := 0).
   2: algebra.
  2: omega.
 replace (pred m) with (pred (m - k) + k).
  2: omega.
 pattern (S (max N M + k)) at 2 in |- *; replace (S (max N M + k)) with (S (max N M + k) - k + k).
  2: omega.
 apply Sum_big_shift.
  intros; apply HN.
  apply le_trans with (max N M); auto with arith.
  omega.
 rewrite <- S_pred with (m := 0); auto.
  omega.
 apply lt_le_trans with (S (max N M)); auto with arith.
 omega.
Qed.

End Convergence_Criteria.

Section More_CC.

Variable x : nat -> IR.

Lemma ratio_test_conv : {N : nat |
 {c : IR | c [<] [1] | [0] [<=] c /\ (forall n, N <= n -> AbsIR (x (S n)) [<=] c[*]AbsIR (x n))}} ->
 convergent x.
Proof.
 intro H.
 elim H; clear H; intros N H.
 elim H; clear H; intros c Hc1 H.
 elim H; clear H; intros H0c H.
 cut (forall n : nat, N <= n -> AbsIR (x n) [<=] AbsIR (x N) [*]c[^] (n - N)).
  intro.
  apply str_comparison with (fun n : nat => AbsIR (x N) [*]c[^] (n - N)).
   2: exists N; assumption.
  apply conv_series_mult_scal with (x := fun n : nat => c[^] (n - N)).
  apply join_series with (power_series c).
   apply power_series_conv.
   apply AbsIR_less.
    assumption.
   apply less_leEq_trans with [0].
    rstepr ([--][0]:IR).
    apply inv_resp_less.
    apply pos_one.
   assumption.
  exists N.
  exists 0.
  intro.
  rewrite plus_comm; rewrite Minus.minus_plus.
  algebra.
 simple induction n.
  intro.
  cut (N = 0); [ intro | auto with arith ].
  rewrite H1.
  apply eq_imp_leEq.
  simpl in |- *; algebra.
 clear n; intros.
 cut ({N < S n} + {N = S n}).
  2: apply le_lt_eq_dec; assumption.
 intro; inversion_clear H2.
  apply leEq_transitive with (c[*]AbsIR (x n)).
   apply H; auto with arith.
  rewrite <- minus_Sn_m.
   astepr (AbsIR (x N) [*] (c[*]c[^] (n - N))).
   rstepr (c[*] (AbsIR (x N) [*]c[^] (n - N))).
   apply mult_resp_leEq_lft.
    apply H0; auto with arith.
   assumption.
  auto with arith.
 rewrite H3.
 rewrite <- minus_n_n.
 apply eq_imp_leEq.
 simpl in |- *; algebra.
Qed.

Lemma ratio_test_div : {N : nat |
 {c : IR | [1] [<=] c | forall n, N <= n -> c[*]AbsIR (x n) [<] AbsIR (x (S n))}} ->
 divergent x.
Proof.
 intros H.
 elim H; clear H; intros N H.
 elim H; clear H; intros c Hc Hn.
 apply divergent_crit.
 exists (AbsIR (x (S N))).
  apply leEq_less_trans with (c[*]AbsIR (x N)).
   astepl (c[*][0]); apply mult_resp_leEq_lft.
    apply AbsIR_nonneg.
   apply less_leEq; eapply less_leEq_trans; [ apply pos_one | assumption ].
  apply Hn; auto with arith.
 cut (forall n : nat, S N <= n -> {m : nat | n <= m /\ AbsIR (x (S N)) [<=] AbsIR (x m)}).
  intro H.
  clear Hn.
  intro n.
  cut (S N <= max (S N) n); [ intro | apply le_max_l ].
  elim (H _ H0); intros m Hm; elim Hm; clear H Hm; intros Hm H; exists m.
   apply le_trans with (max (S N) n); auto with arith.
  assumption.
 intros; exists n.
 split.
  auto.
 induction  n as [| n Hrecn].
  inversion H.
 clear Hrecn; induction  n as [| n Hrecn].
  inversion H.
   rewrite <- H1; apply eq_imp_leEq; algebra.
  inversion H1.
 elim (le_lt_eq_dec _ _ H); intro.
  apply leEq_transitive with (AbsIR (x (S n))).
   apply Hrecn; auto with arith.
  apply less_leEq; apply leEq_less_trans with (c[*]AbsIR (x (S n))).
   astepl ([1][*]AbsIR (x (S n))); apply mult_resp_leEq_rht.
    assumption.
   apply AbsIR_nonneg.
  apply Hn; auto with arith.
 rewrite b; apply eq_imp_leEq; algebra.
Qed.

End More_CC.

Section Alternate_Series.

(**
** Alternate Series

Alternate series are a special case.  Suppose that [x] is nonnegative and
decreasing convergent to 0.
*)

Variable x : nat -> IR.

Hypothesis pos_x : forall n : nat, [0] [<=] x n.
Hypothesis Lim_x : Cauchy_Lim_prop2 x [0].
Hypothesis mon_x : forall n : nat, x (S n) [<=] x n.

(* begin hide *)
Let y (n : nat) := [--][1][^]n[*]x n.

Let alternate_lemma1 :
  forall n m : nat, [--][1][^]n[*]Sum n (n + (m + m)) y [<=] x n.
Proof.
 intros; induction  m as [| m Hrecm].
  cut (n = n + (0 + 0)); [ intro | auto with arith ].
  rewrite <- H.
  apply eq_imp_leEq.
  cut (Sum n n y [=] y n); [ intro | apply Sum_one ].
  astepl ( [--][1][^]n[*]y n).
  unfold y in |- *; simpl in |- *.
  apply eq_transitive_unfolded with ( [--]OneR[^] (n + n) [*]x n).
   astepl ( [--][1][^]n[*][--][1][^]n[*]x n).
   apply mult_wdl.
   apply nexp_plus.
  astepr ([1][*]x n).
  apply mult_wdl.
  apply inv_one_even_nexp.
  auto with arith.
 cut (n + (S m + S m) = S (S (n + (m + m))));
   [ intro | simpl in |- *; repeat rewrite plus_n_Sm; auto ].
 rewrite H.
 apply leEq_wdl with ( [--][1][^]n[*]Sum n (n + (m + m)) y[+]
   [--][1][^]n[*] (y (S (n + (m + m))) [+]y (S (S (n + (m + m)))))).
  apply leEq_transitive with (x n[+][--][1][^]n[*] (y (S (n + (m + m))) [+]y (S (S (n + (m + m)))))).
   apply plus_resp_leEq.
   apply Hrecm.
  apply shift_plus_leEq'; astepr ZeroR.
  unfold y in |- *.
  eapply leEq_wdl.
   2: apply eq_symmetric_unfolded; apply ring_dist_unfolded.
  apply leEq_wdl with ( [--] (x (S (n + (m + m)))) [+]x (S (S (n + (m + m))))).
   apply shift_plus_leEq'; rstepr (x (S (n + (m + m)))).
   apply mon_x.
  apply bin_op_wd_unfolded.
   rstepl ( [--][1][*]x (S (n + (m + m)))).
   rstepr ( [--][1][^]n[*][--][1][^]S (n + (m + m)) [*]x (S (n + (m + m)))).
   apply mult_wdl.
   apply eq_symmetric_unfolded.
   eapply eq_transitive_unfolded.
    apply nexp_plus.
   apply inv_one_odd_nexp.
   cut (n + S (n + (m + m)) = S (n + n + (m + m))); [ intro | rewrite <- plus_n_Sm; auto with arith ].
   rewrite H0.
   auto with arith.
  astepl ([1][*]x (S (S (n + (m + m))))).
  rstepr ( [--][1][^]n[*][--][1][^]S (S (n + (m + m))) [*]x (S (S (n + (m + m))))).
  apply mult_wdl.
  apply eq_symmetric_unfolded.
  eapply eq_transitive_unfolded.
   apply nexp_plus.
  apply inv_one_even_nexp.
  cut (n + S (S (n + (m + m))) = S (S (n + n + (m + m)))); [ intro | omega ].
  rewrite H0.
  auto with arith.
 unfold Sum in |- *; simpl in |- *.
 unfold Sum1 in |- *; simpl in |- *.
 rational.
Qed.

Let alternate_lemma2 :
  forall n m : nat, [--][1][^]n[*]Sum n (n + S (m + m)) y [<=] x n.
Proof.
 intros.
 cut (n + S (m + m) = S (n + (m + m))); [ intro | auto with arith ].
 rewrite H.
 apply leEq_wdl with ( [--][1][^]n[*]Sum n (n + (m + m)) y[+][--][1][^]n[*]y (S (n + (m + m)))).
  apply leEq_transitive with (x n[+][--][1][^]n[*]y (S (n + (m + m)))).
   apply plus_resp_leEq.
   apply alternate_lemma1.
  apply shift_plus_leEq'; rstepr (ZeroR[*]x (S (n + (m + m)))).
  unfold y in |- *.
  rstepl ( [--][1][^]n[*][--][1][^]S (n + (m + m)) [*]x (S (n + (m + m)))).
  apply mult_resp_leEq_rht.
   apply leEq_wdl with ( [--]OneR).
    astepr ( [--]ZeroR); apply less_leEq; apply inv_resp_less; apply pos_one.
   apply eq_symmetric_unfolded; eapply eq_transitive_unfolded.
    apply nexp_plus.
   apply inv_one_odd_nexp.
   cut (n + S (n + (m + m)) = S (n + n + (m + m))); [ intro | rewrite <- plus_n_Sm; auto with arith ].
   rewrite H0.
   auto with arith.
  apply pos_x.
 eapply eq_transitive_unfolded.
  apply eq_symmetric_unfolded; apply ring_dist_unfolded.
 apply mult_wdr.
 unfold Sum in |- *; unfold Sum1 in |- *; simpl in |- *; rational.
Qed.

Let alternate_lemma3 :
  forall n m : nat, [0] [<=] [--][1][^]n[*]Sum n (n + S (m + m)) y.
Proof.
 intros; induction  m as [| m Hrecm].
  cut (S n = n + S (0 + 0)); [ intro | rewrite <- plus_n_Sm; auto ].
  rewrite <- H.
  cut (Sum n (S n) y [=] y n[+]y (S n)).
   intro; astepr ( [--][1][^]n[*] (y n[+]y (S n))).
   unfold y in |- *.
   eapply leEq_wdr.
    2: apply eq_symmetric_unfolded; apply ring_dist_unfolded.
   apply leEq_wdr with (x n[-]x (S n)).
    apply shift_leEq_minus; astepl (x (S n)).
    apply mon_x.
   unfold cg_minus in |- *; apply bin_op_wd_unfolded.
    astepl ([1][*]x n).
    astepr ( [--][1][^]n[*][--][1][^]n[*]x n).
    apply mult_wdl.
    apply eq_symmetric_unfolded.
    eapply eq_transitive_unfolded.
     apply nexp_plus.
    apply inv_one_even_nexp.
    auto with arith.
   rstepl ( [--][1][*]x (S n)).
   astepr ( [--][1][^]n[*][--][1][^]S n[*]x (S n)).
   apply mult_wdl.
   apply eq_symmetric_unfolded.
   eapply eq_transitive_unfolded.
    apply nexp_plus.
   apply inv_one_odd_nexp.
   cut (n + S n = S (n + n)); [ intro | auto with arith ].
   rewrite H1.
   auto with arith.
  unfold Sum, Sum1 in |- *; simpl in |- *; rational.
 cut (n + S (S m + S m) = S (S (n + S (m + m))));
   [ intro | simpl in |- *; repeat rewrite <- plus_n_Sm; auto with arith ].
 rewrite H.
 apply leEq_wdr with ( [--][1][^]n[*] (Sum n (n + S (m + m)) y[+]
   (y (S (n + S (m + m))) [+]y (S (S (n + S (m + m))))))).
  eapply leEq_wdr.
   2: apply eq_symmetric_unfolded; apply ring_dist_unfolded.
  astepl (ZeroR[+][0]).
  apply plus_resp_leEq_both.
   apply Hrecm.
  unfold y in |- *.
  eapply leEq_wdr.
   2: apply eq_symmetric_unfolded; apply ring_dist_unfolded.
  apply leEq_wdr with (x (S (n + S (m + m))) [-]x (S (S (n + S (m + m))))).
   apply shift_leEq_minus; astepl (x (S (S (n + S (m + m))))); apply mon_x.
  unfold cg_minus in |- *; apply bin_op_wd_unfolded.
   eapply eq_transitive_unfolded.
    2: apply eq_symmetric_unfolded; apply mult_assoc_unfolded.
   astepl ([1][*]x (S (n + S (m + m)))); apply mult_wdl.
   apply eq_symmetric_unfolded.
   eapply eq_transitive_unfolded; [ apply nexp_plus | apply inv_one_even_nexp ].
   cut (n + S (n + S (m + m)) = S (S (n + n + (m + m))));
     [ intro | simpl in |- *; repeat rewrite <- plus_n_Sm; auto with arith ].
   rewrite H0.
   auto with arith.
  eapply eq_transitive_unfolded.
   2: apply eq_symmetric_unfolded; apply mult_assoc_unfolded.
  rstepl ( [--][1][*]x (S (S (n + S (m + m))))); apply mult_wdl.
  apply eq_symmetric_unfolded.
  eapply eq_transitive_unfolded; [ apply nexp_plus | apply inv_one_odd_nexp ].
  cut (n + S (S (n + S (m + m))) = S (S n + S n + (m + m))); [ intro
    | simpl in |- *; repeat rewrite <- plus_n_Sm; simpl in |- *; auto with arith ].
  rewrite H0.
  auto with arith.
 apply mult_wdr.
 unfold Sum, Sum1 in |- *; simpl in |- *; rational.
Qed.

Let alternate_lemma4 :
  forall n m : nat, [0] [<=] [--][1][^]n[*]Sum n (n + (m + m)) y.
Proof.
 intros.
 case m.
  cut (n + (0 + 0) = n); [ intro | auto ].
  rewrite H.
  cut (Sum n n y [=] y n); [ intro | apply Sum_one ].
  astepr ( [--][1][^]n[*]y n).
  unfold y in |- *.
  eapply leEq_wdr.
   2: apply eq_symmetric_unfolded; apply mult_assoc_unfolded.
  astepl ([0][*]x n).
  apply mult_resp_leEq_rht.
   apply leEq_wdr with OneR.
    apply less_leEq; apply pos_one.
   apply eq_symmetric_unfolded; eapply eq_transitive_unfolded.
    apply nexp_plus.
   apply inv_one_even_nexp; auto with arith.
  apply pos_x.
 clear m; intro m.
 cut (n + (S m + S m) = S (n + S (m + m))); [ intro | simpl in |- *; rewrite <- plus_n_Sm; auto ].
 rewrite H.
 apply leEq_wdr with ( [--][1][^]n[*]Sum n (n + S (m + m)) y[+] [--][1][^]n[*]y (S (n + S (m + m)))).
  apply leEq_transitive with ([0][+][--][1][^]n[*]y (S (n + S (m + m)))).
   astepr ( [--][1][^]n[*]y (S (n + S (m + m)))).
   unfold y in |- *.
   eapply leEq_wdr.
    2: apply eq_symmetric_unfolded; apply mult_assoc_unfolded.
   astepl ([0][*]x (S (n + S (m + m)))).
   apply mult_resp_leEq_rht.
    apply leEq_wdr with OneR.
     apply less_leEq; apply pos_one.
    apply eq_symmetric_unfolded; eapply eq_transitive_unfolded.
     apply nexp_plus.
    cut (n + S (n + S (m + m)) = n + n + (S m + S m)); [ intro
      | simpl in |- *; repeat rewrite <- plus_n_Sm; simpl in |- *; auto with arith ].
    rewrite H0; apply inv_one_even_nexp.
    auto with arith.
   apply pos_x.
  apply plus_resp_leEq.
  apply alternate_lemma3.
 eapply eq_transitive_unfolded.
  apply eq_symmetric_unfolded; apply ring_dist_unfolded.
 apply mult_wdr.
 unfold Sum in |- *; unfold Sum1 in |- *; simpl in |- *; rational.
Qed.
(* end hide *)

Lemma alternate_series_conv : convergent (fun n => [--][1][^]n[*]x n).
Proof.
 red in |- *.
 red in |- *.
 intros e H.
 elim (Lim_x e H).
 intros N' HN'.
 cut {N : nat | 0 < N | forall m : nat, N <= m -> AbsSmall e (x m)}.
  intro H0.
  elim H0; clear H0; intros N HNm HN.
  exists N; intros.
  apply AbsSmall_transitive with (x N).
   apply HN; auto.
  cut (AbsIR (seq_part_sum (fun n : nat => [--][1][^]n[*]x n) m[-]
    seq_part_sum (fun n : nat => [--][1][^]n[*]x n) N) [=] AbsIR ( [--][1][^]N[*]Sum N (pred m) y)).
   intro.
   apply leEq_wdl with (AbsIR ( [--][1][^]N[*]Sum N (pred m) y)).
    eapply leEq_wdr.
     2: apply eq_symmetric_unfolded; apply AbsIR_eq_x; apply pos_x.
    cut ({N < m} + {N = m}); intros.
     2: apply le_lt_eq_dec; assumption.
    apply leEq_wdl with (Max ( [--][1][^]N[*]Sum N (pred m) y) [--] ( [--][1][^]N[*]Sum N (pred m) y)).
     apply Max_leEq.
      inversion_clear H2.
       cut {j : nat &  {pred m = N + (j + j)} + {pred m = N + S (j + j)}}.
        2: apply even_or_odd_plus_gt; apply le_2; auto.
       intro.
       elim H2; intros j Hj.
       clear H2; inversion_clear Hj.
        rewrite H2; apply alternate_lemma1.
       rewrite H2; apply alternate_lemma2.
      rewrite <- H3.
      cut (Sum N (pred N) y [=] [0]); [ intro | apply Sum_empty; auto ].
      astepl ( [--][1][^]N[*]ZeroR).
      astepl ZeroR; apply pos_x.
     astepr ( [--][--] (x N)); apply inv_resp_leEq.
     apply leEq_transitive with ZeroR.
      astepr ( [--]ZeroR); apply inv_resp_leEq; apply pos_x.
     inversion_clear H2.
      cut {j : nat &  {pred m = N + (j + j)} + {pred m = N + S (j + j)}}.
       2: apply even_or_odd_plus_gt; apply le_2; auto.
      intro.
      elim H2; intros j Hj.
      clear H2; inversion_clear Hj.
       rewrite H2; apply alternate_lemma4.
      rewrite H2; apply alternate_lemma3.
     rewrite <- H3.
     cut (Sum N (pred N) y [=] [0]); [ intro | apply Sum_empty; auto ].
     astepr ( [--][1][^]N[*]ZeroR).
     astepr ZeroR; apply leEq_reflexive.
    simpl in |- *; unfold ABSIR in |- *; apply eq_reflexive_unfolded.
   apply eq_symmetric_unfolded; assumption.
  elim (even_odd_dec N); intro.
   apply AbsIR_wd.
   eapply eq_transitive_unfolded.
    apply seq_part_sum_n; auto; apply lt_le_trans with N; auto.
   eapply eq_transitive_unfolded.
    2: apply Sum_comm_scal'.
   apply Sum_wd.
   intro.
   unfold y in |- *.
   eapply eq_transitive_unfolded.
    2: apply eq_symmetric_unfolded; apply mult_assoc_unfolded.
   apply mult_wdl.
   astepl (OneR[*][--][1][^]i).
   apply mult_wdl.
   apply eq_symmetric_unfolded; apply inv_one_even_nexp; assumption.
  eapply eq_transitive_unfolded.
   2: apply eq_symmetric_unfolded; apply AbsIR_inv.
  apply AbsIR_wd.
  eapply eq_transitive_unfolded.
   apply seq_part_sum_n; auto; apply lt_le_trans with N; auto.
  rstepr ( [--] ( [--][1][^]N) [*]Sum N (pred m) y).
  eapply eq_transitive_unfolded.
   2: apply Sum_comm_scal'.
  apply Sum_wd.
  intro.
  unfold y in |- *.
  eapply eq_transitive_unfolded.
   2: apply eq_symmetric_unfolded; apply mult_assoc_unfolded.
  apply mult_wdl.
  astepl (OneR[*][--][1][^]i).
  apply mult_wdl.
  apply eq_symmetric_unfolded.
  rstepl ( [--]OneR[^]1[*][--][1][^]N).
  eapply eq_transitive_unfolded.
   apply nexp_plus.
  apply inv_one_even_nexp.
  simpl in |- *.
  auto with arith.
 exists (S N').
  auto with arith.
 intros.
 astepr (x m[-][0]); apply HN'; auto with arith.
Qed.

End Alternate_Series.

Section Important_Numbers.

(**
** Important Numbers

We end this chapter by defining two important numbers in mathematics: [pi]
and $e$#e#, both as sums of convergent series.
*)

Definition e_series (n : nat) := [1][/] _[//]nring_fac_ap_zero IR n.

Lemma e_series_conv : convergent e_series.
Proof.
 apply ratio_test_conv.
 exists 1.
 exists (OneR [/]TwoNZ).
  apply pos_div_two'; apply pos_one.
 split.
  apply less_leEq; apply pos_div_two; apply pos_one.
 intros.
 unfold e_series in |- *.
 eapply leEq_wdr.
  2: apply mult_commutes.
 eapply leEq_wdr.
  2: apply AbsIR_mult_pos.
  2: apply less_leEq; apply pos_div_two; apply pos_one.
 eapply leEq_wdl.
  2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
  eapply leEq_wdr.
   2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
   rstepr ([1][*][1][/] _[//] mult_resp_ap_zero _ _ _ (two_ap_zero IR) (nring_fac_ap_zero _ n)).
   rstepr ([1][/] _[//] mult_resp_ap_zero _ _ _ (two_ap_zero IR) (nring_fac_ap_zero _ n)).
   apply recip_resp_leEq.
    astepl ((Two:IR) [*][0]); apply mult_resp_less_lft.
     apply pos_nring_fac.
    apply pos_two.
   cut (fact (S n) = S n * fact n).
    2: simpl in |- *; auto with arith.
   intro.
   rewrite H0.
   eapply leEq_wdr.
    2: apply eq_symmetric_unfolded; apply nring_comm_mult.
   apply mult_resp_leEq_rht.
    apply nring_leEq; auto with arith.
   apply less_leEq; apply pos_nring_fac.
  apply less_leEq; apply mult_resp_pos; apply recip_resp_pos.
   apply pos_nring_fac.
  apply pos_two.
 apply less_leEq; apply recip_resp_pos; apply pos_nring_fac.
Qed.

Definition E := series_sum _ e_series_conv.

Definition pi_series n :=
 [--][1][^]n[*] ([1][/] _[//]Greater_imp_ap IR _ _ (pos_nring_S _ (n + n))).

Lemma pi_series_conv : convergent pi_series.
Proof.
 unfold pi_series in |- *.
 apply alternate_series_conv with (x := fun n : nat =>
   [1][/] _[//]Greater_imp_ap IR _ _ (pos_nring_S _ (n + n))).
   intro; apply less_leEq.
   apply recip_resp_pos; apply pos_nring_S.
  apply Cauchy_Lim_prop3_prop2.
  red in |- *; intros.
  exists (S k); intros.
  apply AbsIR_imp_AbsSmall.
  apply less_leEq.
  apply less_wdl with ([1][/] _[//]Greater_imp_ap IR _ _ (pos_nring_S _ (m + m))).
   unfold one_div_succ, Snring in |- *.
   apply recip_resp_less.
    apply pos_nring_S.
   apply nring_less; auto with arith.
  apply eq_symmetric_unfolded.
  apply eq_transitive_unfolded
    with (AbsIR ([1][/] _[//]Greater_imp_ap IR _ _ (pos_nring_S _ (m + m)))).
   apply AbsIR_wd; algebra.
  apply AbsIR_eq_x; apply less_leEq.
  apply recip_resp_pos; apply pos_nring_S.
 intros.
 apply less_leEq; apply recip_resp_less.
  apply pos_nring_S.
 apply nring_less; simpl in |- *; rewrite <- plus_n_Sm; auto with arith.
Qed.

Definition pi := Four[*]series_sum _ pi_series_conv.

End Important_Numbers.
