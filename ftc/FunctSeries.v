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

Require Export CoRN.ftc.FunctSequence.
Require Export CoRN.reals.Series.

(** printing fun_seq_part_sum %\ensuremath{\sum^n}% #&sum;<sup>n</sup># *)
(** printing Fun_Series_Sum %\ensuremath{\sum_0^{\infty}}% #&sum;<sub>0</sub><sup>&infin;</sup># *)

Section Definitions.

(**
* Series of Functions

We now turn our attention to series of functions.  Like it was already
the case for sequences, we will mainly rewrite the results we proved
for series of real numbers in a different way.

%\begin{convention}% Throughout this section:
 - [a] and [b] will be real numbers and the interval [[a,b]] will be denoted
by [I];
 - [f, g] and [h] will denote sequences of continuous functions;
 - [F, G] and [H] will denote continuous functions.

%\end{convention}%

** Definitions

As before, we will consider only sequences of continuous functions
defined in a compact interval.  For this, partial sums are defined and
convergence is simply the convergence of the sequence of partial sums.
*)

Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Variable f : nat -> PartIR.

Definition fun_seq_part_sum (n : nat) := FSum0 n f.

Lemma fun_seq_part_sum_cont : (forall n, Continuous_I Hab (f n)) -> forall n,
 Continuous_I Hab (fun_seq_part_sum n).
Proof.
 intros; unfold fun_seq_part_sum in |- *.
 Contin.
Qed.

Definition fun_series_convergent := {contf : _ |
  Cauchy_fun_seq _ _ Hab fun_seq_part_sum (fun_seq_part_sum_cont contf)}.

(**
For what comes up next we need to know that the convergence of a
series of functions implies pointwise convergence of the corresponding
real number series.
*)

Lemma fun_series_conv_imp_conv : fun_series_convergent ->
 forall x, I x -> forall Hx, convergent (fun n => f n x (Hx n)).
Proof.
 intros H x H0 Hx e He.
 elim H; intros incF convF.
 elim (convF _ He).
 intros N HN.
 exists N; intros.
 apply AbsIR_imp_AbsSmall.
 simpl in HN.
 eapply leEq_wdl.
  apply (HN m N H1 (le_n N) x H0).
 apply AbsIR_wd.
 apply cg_minus_wd; unfold seq_part_sum in |- *; apply Sum0_wd; intros; rational.
Qed.

(** We then define the sum of the series as being the pointwise sum of
the corresponding series.
*)

(* begin show *)
Hypothesis H : fun_series_convergent.
(* end show *)

(* begin hide *)
Let contf := ProjT1 H.
Let incf (n : nat) := contin_imp_inc _ _ _ _ (contf n).
(* end hide *)

Lemma Fun_Series_Sum_strext : forall x y Hx Hy,
 series_sum _ (fun_series_conv_imp_conv H x Hx (fun n => incf n x Hx)) [#]
  series_sum _ (fun_series_conv_imp_conv H y Hy (fun n => incf n y Hy)) -> x [#] y.
Proof.
 intros x y Hx Hy H0.
 unfold series_sum in H0.
 elim (Lim_strext _ _ H0); intros m Hm.
 simpl in Hm; unfold seq_part_sum in Hm.
 elim (Sum0_strext _ _ _ _ Hm); intros i H1 H2.
 exact (pfstrx _ _ _ _ _ _ H2).
Qed.

Definition Fun_Series_Sum : PartIR.
Proof.
 apply Build_PartFunct with (pfpfun := fun (x : IR) (Hx : I x) => series_sum _
   (fun_series_conv_imp_conv H x Hx (fun n : nat => incf n x Hx))).
  unfold I in |- *; apply compact_wd.
 exact Fun_Series_Sum_strext.
Defined.

End Definitions.

Arguments Fun_Series_Sum [a b Hab f].

#[global]
Hint Resolve fun_seq_part_sum_cont: continuous.

Section More_Definitions.

Variables a b : IR.
Hypothesis Hab : a [<=] b.

Variable f : nat -> PartIR.

(** A series can also be absolutely convergent. *)

Definition fun_series_abs_convergent := fun_series_convergent _ _ Hab
 (fun n => FAbs (f n)).

End More_Definitions.

Section Operations.

(* **Algebraic Properties

All of these are analogous to the properties for series of real numbers, so we won't comment much about them.
*)

Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Lemma fun_seq_part_sum_n : forall f (H' : forall n, Continuous_I Hab (f n)) m n,
 0 < n -> m <= n -> Feq I (fun_seq_part_sum f n{-}fun_seq_part_sum f m) (FSum m (pred n) f).
Proof.
 intros.
 unfold fun_seq_part_sum in |- *.
 apply eq_imp_Feq.
   unfold I in |- *; apply contin_imp_inc; Contin.
  unfold I in |- *; apply contin_imp_inc; Contin.
 intros; simpl in |- *.
 unfold Sum, Sum1 in |- *.
 rewrite <- (Nat.lt_succ_pred 0 n); auto.
 apply cg_minus_wd; apply Sum0_wd; intros; rational.
Qed.

Lemma conv_fun_const_series : forall x, convergent x ->
 fun_series_convergent _ _ Hab (fun n => [-C-] (x n)).
Proof.
 intros x H.
 exists (fun n : nat => Continuous_I_const _ _ Hab (x n)).
 apply Cauchy_fun_seq2_seq.
 red in |- *; intros e He.
 elim (H e He); intros N HN.
 exists N; intros.
 simpl in |- *.
 apply AbsSmall_imp_AbsIR.
 apply AbsSmall_wdr_unfolded with (seq_part_sum x m[-]seq_part_sum x N).
  apply HN; assumption.
 unfold seq_part_sum in |- *; simpl in |- *.
 apply cg_minus_wd; apply Sum0_wd; algebra.
Qed.

Lemma fun_const_series_sum : forall y H
 (H' : fun_series_convergent _ _ Hab (fun n => [-C-] (y n))) x Hx, Fun_Series_Sum H' x Hx [=] series_sum y H.
Proof.
 intros.
 simpl in |- *.
 apply series_sum_wd.
 algebra.
Qed.

Lemma conv_zero_fun_series : fun_series_convergent _ _ Hab (fun n => [-C-][0]).
Proof.
 apply conv_fun_const_series with (x := fun n : nat => ZeroR).
 apply conv_zero_series.
Qed.

Lemma Fun_Series_Sum_zero : forall (H : fun_series_convergent _ _ Hab (fun n => [-C-][0]))
 x Hx, Fun_Series_Sum H x Hx [=] [0].
Proof.
 intros.
 simpl in |- *.
 apply series_sum_zero.
Qed.

(* begin show *)
Variables f g : nat -> PartIR.
(* end show *)

Lemma fun_series_convergent_wd : (forall n, Feq I (f n) (g n)) ->
 fun_series_convergent _ _ Hab f -> fun_series_convergent _ _ Hab g.
Proof.
 intros H H0.
 elim H0; intros contF convF.
 cut (forall n : nat, Continuous_I Hab (g n)). intro H1.
  exists H1.
  apply Cauchy_fun_seq_wd with (fun_seq_part_sum f) (fun_seq_part_sum_cont _ _ _ _ contF).
   2: assumption.
  intros.
  apply eq_imp_Feq.
    apply contin_imp_inc; Contin.
   apply contin_imp_inc; Contin.
  intros x H2 Hx Hx'; simpl in |- *.
  apply Sum0_wd.
  intro i; elim (H i); intros.
  inversion_clear b0; auto.
 intro; apply Continuous_I_wd with (f n); auto.
Qed.

(* begin show *)
Hypothesis convF : fun_series_convergent _ _ Hab f.
Hypothesis convG : fun_series_convergent _ _ Hab g.
(* end show *)

Lemma Fun_Series_Sum_wd' : (forall n, Feq I (f n) (g n)) -> Feq I (Fun_Series_Sum convF) (Fun_Series_Sum convG).
Proof.
 intro H.
 apply eq_imp_Feq.
   Included.
  Included.
 intros x H0 Hx Hx'; simpl in |- *.
 apply series_sum_wd.
 intro; elim (H n); intros.
 inversion_clear b0; auto.
Qed.

Lemma conv_fun_series_plus : fun_series_convergent _ _ Hab (fun n => f n{+}g n).
Proof.
 elim convF; intros contF convF'.
 elim convG; intros contG convG'.
 assert (H := fun n : nat => Continuous_I_plus _ _ _ _ _ (contF n) (contG n)); exists H.
 cut (forall n : nat, Continuous_I Hab (fun_seq_part_sum f n{+}fun_seq_part_sum g n));
   [ intro H0 | Contin ].
 apply Cauchy_fun_seq_wd with (f := fun n : nat => fun_seq_part_sum f n{+}fun_seq_part_sum g n)
   (contf := H0).
  2: eapply fun_Cauchy_prop_plus; auto; [ apply convF' | apply convG' ].
 intros; apply eq_imp_Feq.
   Included.
  apply contin_imp_inc; Contin.
 intros; simpl in |- *.
 apply eq_symmetric_unfolded; eapply eq_transitive_unfolded.
  2: apply Sum0_plus_Sum0.
 apply Sum0_wd; intros; rational.
Qed.

Lemma Fun_Series_Sum_plus : forall H : fun_series_convergent _ _ Hab (fun n => f n{+}g n),
 Feq I (Fun_Series_Sum H) (Fun_Series_Sum convF{+}Fun_Series_Sum convG).
Proof.
 intros.
 apply eq_imp_Feq.
   Included.
  Included.
 intros x H0 Hx Hx'; simpl in |- *.
 elim convF; intros contF convF'.
 elim convG; intros contG convG'.
 cut (convergent (fun n : nat => Part _ _ (contin_imp_inc _ _ _ _ (contF n) x (ProjIR1 Hx')) [+]
   Part _ _ (contin_imp_inc _ _ _ _ (contG n) x (ProjIR2 Hx')))). intro H1.
  eapply eq_transitive_unfolded.
   2: apply series_sum_plus with (x := fun n : nat =>
     Part _ _ (contin_imp_inc _ _ _ _ (contF n) x (ProjIR1 Hx'))) (y := fun n : nat =>
       Part _ _ (contin_imp_inc _ _ _ _ (contG n) x (ProjIR2 Hx'))) (H := H1).
  apply series_sum_wd; intro; rational.
 intros e H1.
 elim H; intros cont H'.
 elim (H' _ H1); intros N HN.
 exists N; intros.
 apply AbsIR_imp_AbsSmall.
 eapply leEq_wdl.
  apply (HN m N H2 (le_n N) x H0).
 apply AbsIR_wd; unfold fun_seq_part_sum in |- *.
 simpl in |- *.
 unfold seq_part_sum in |- *; apply cg_minus_wd; apply Sum0_wd; intros; rational.
Qed.

Lemma conv_fun_series_minus : fun_series_convergent _ _ Hab (fun n => f n{-}g n).
Proof.
 elim convF; intros contF convF'.
 elim convG; intros contG convG'.
 assert (H := fun n : nat => Continuous_I_minus _ _ _ _ _ (contF n) (contG n)); exists H.
 cut (forall n : nat, Continuous_I Hab (fun_seq_part_sum f n{-}fun_seq_part_sum g n));
   [ intro H0 | Contin ].
 apply Cauchy_fun_seq_wd with (f := fun n : nat => fun_seq_part_sum f n{-}fun_seq_part_sum g n)
   (contf := H0).
  2: eapply fun_Cauchy_prop_minus; auto; [ apply convF' | apply convG' ].
 intros; apply eq_imp_Feq.
   Included.
  apply contin_imp_inc; Contin.
 intros; simpl in |- *.
 apply eq_symmetric_unfolded.
 apply eq_transitive_unfolded with (Sum0 n (fun i : nat => f i x (ProjIR1 Hx i)) [+]
   Sum0 n (fun i : nat => [--] (g i x (ProjIR2 Hx i)))).
  eapply eq_transitive_unfolded.
   2: apply Sum0_plus_Sum0.
  apply Sum0_wd; intros; rational.
 unfold cg_minus in |- *.
 apply bin_op_wd_unfolded.
  algebra.
 eapply eq_transitive_unfolded.
  2: apply inv_Sum0.
 apply Sum0_wd; algebra.
Qed.

Lemma Fun_Series_Sum_min : forall H : fun_series_convergent _ _ Hab (fun n => f n{-}g n),
 Feq I (Fun_Series_Sum H) (Fun_Series_Sum convF{-}Fun_Series_Sum convG).
Proof.
 intros.
 apply eq_imp_Feq.
   Included.
  Included.
 intros x H0 Hx Hx'; simpl in |- *.
 elim convF; intros contF convF'.
 elim convG; intros contG convG'.
 cut (convergent (fun n : nat => Part _ _ (contin_imp_inc _ _ _ _ (contF n) x (ProjIR1 Hx')) [-]
   Part _ _ (contin_imp_inc _ _ _ _ (contG n) x (ProjIR2 Hx')))). intro H1.
  apply eq_transitive_unfolded with (series_sum _
    (fun_series_conv_imp_conv _ _ _ _ convF x (ProjIR1 Hx')
      (fun n : nat => contin_imp_inc _ _ _ _ (contF n) x (ProjIR1 Hx'))) [-] series_sum _
        (fun_series_conv_imp_conv _ _ _ _ convG x (ProjIR2 Hx')
          (fun n : nat => contin_imp_inc _ _ _ _ (contG n) x (ProjIR2 Hx')))).
   eapply eq_transitive_unfolded.
    2: apply series_sum_minus with (x := fun n : nat =>
      Part _ _ (contin_imp_inc _ _ _ _ (contF n) x (ProjIR1 Hx'))) (y := fun n : nat =>
        Part _ _ (contin_imp_inc _ _ _ _ (contG n) x (ProjIR2 Hx'))) (H := H1).
   apply series_sum_wd; intro; rational.
  apply cg_minus_wd; apply series_sum_wd; intro; rational.
 intros e H1.
 elim H; intros cont H'.
 elim (H' _ H1); intros N HN.
 exists N; intros.
 apply AbsIR_imp_AbsSmall.
 eapply leEq_wdl.
  apply (HN m N H2 (le_n N) x H0).
 apply AbsIR_wd; unfold fun_seq_part_sum in |- *.
 simpl in |- *.
 unfold seq_part_sum in |- *; apply cg_minus_wd; apply Sum0_wd; intros; rational.
Qed.

(**
%\begin{convention}% Let [c:IR].
%\end{convention}%
*)

Variable c : IR.
Variable H : PartIR.
Hypothesis contH : Continuous_I Hab H.

Lemma conv_fun_series_scal : fun_series_convergent _ _ Hab (fun n => H{*}f n).
Proof.
 elim convF; intros contF convF'.
 set (H' := fun n : nat => Continuous_I_mult _ _ _ _ _ contH (contF n)) in *; exists H'.
 cut (forall n : nat, Continuous_I Hab (fun_seq_part_sum f n)); [ intro H0 | Contin ].
 cut (forall n : nat, Continuous_I Hab (H{*}fun_seq_part_sum f n)); [ intro H1 | Contin ].
 unfold I in |- *; apply Cauchy_fun_seq_wd with (fun n : nat => H{*}fun_seq_part_sum f n) H1.
  2: apply fun_Cauchy_prop_mult with (f := fun n : nat => H) (contf := fun n : nat => contH)
    (g := fun_seq_part_sum f) (contg := H0).
   intro; FEQ.
    apply contin_imp_inc; Contin.
   simpl in |- *.
   unfold seq_part_sum in |- *.
   apply eq_symmetric_unfolded.
   eapply eq_transitive_unfolded.
    2: apply Sum0_comm_scal' with (s := fun m : nat => f m x (ProjIR2 Hx m)).
   apply Sum0_wd; intros; rational.
  apply fun_Cauchy_prop_const.
 apply Cauchy_fun_seq_wd with (f := fun_seq_part_sum f)
   (contf := fun_seq_part_sum_cont _ _ _ _ contF).
  2: assumption.
 intro; apply Feq_reflexive; Included.
Qed.

Lemma Fun_Series_Sum_scal : forall H' : fun_series_convergent _ _ Hab (fun n => H{*}f n),
 Feq I (Fun_Series_Sum H') (H{*}Fun_Series_Sum convF).
Proof.
 elim convF; intros contF convF'.
 intros.
 unfold I in |- *; FEQ. try rename X into H0.
 cut (convergent (fun n : nat => Part H x (ProjIR1 Hx') [*]
   f n x (contin_imp_inc _ _ _ _ (contF n) _ (ProjIR2 Hx')))). intro H1.
  apply eq_transitive_unfolded with (series_sum (fun n : nat => Part H x (ProjIR1 Hx') [*]
    f n x (contin_imp_inc _ _ _ _ (contF n) _ (ProjIR2 Hx'))) H1).
   2: simpl in |- *; apply series_sum_mult_scal with (x := fun n : nat =>
     f n x (contin_imp_inc _ _ _ _ (contF n) _ (ProjIR2 Hx'))).
  simpl in |- *; unfold series_sum in |- *.
  apply Lim_wd'; intros; simpl in |- *.
  unfold seq_part_sum in |- *; apply Sum0_wd; intros; rational.
 intros e H1.
 elim H'; intros H'' H'''.
 elim (H''' _ H1); intros N HN.
 exists N; intros.
 apply AbsIR_imp_AbsSmall.
 eapply leEq_wdl.
  apply (HN m N H2 (le_n N) x Hx).
 apply AbsIR_wd; simpl in |- *.
 unfold seq_part_sum in |- *; apply cg_minus_wd; apply Sum0_wd; intros; rational.
Qed.

End Operations.

Section More_Operations.

Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Variable f : nat -> PartIR.
Hypothesis convF : fun_series_convergent _ _ Hab f.

Lemma conv_fun_series_inv : fun_series_convergent _ _ Hab (fun n => {--} (f n)).
Proof.
 elim convF; intros contF convF'.
 exists (fun n : nat => Continuous_I_inv _ _ _ _ (contF n)).
 cut (forall n : nat, Continuous_I Hab {--} (fun_seq_part_sum f n)). intro H.
  apply Cauchy_fun_seq_wd with (f := fun n : nat => {--} (fun_seq_part_sum f n)) (contf := H).
   2: apply fun_Cauchy_prop_inv with (fun_seq_part_sum_cont _ _ _ _ contF).
   intro; FEQ.
    apply contin_imp_inc; Contin.
   simpl in |- *; unfold seq_part_sum in |- *.
   apply eq_symmetric_unfolded; eapply eq_transitive_unfolded.
    2: apply inv_Sum0.
   apply Sum0_wd; intro; rational.
  assumption.
 Contin.
Qed.

Lemma Fun_Series_Sum_inv : forall H : fun_series_convergent _ _ Hab (fun n => {--} (f n)),
 Feq I (Fun_Series_Sum H) {--} (Fun_Series_Sum convF).
Proof.
 intros.
 FEQ. try rename X into H0.
 cut (convergent (fun n : nat =>
   [--] (f n x (contin_imp_inc _ _ _ _ (ProjT1 convF n) x Hx')))). intro H1.
  simpl in |- *; apply eq_transitive_unfolded with (series_sum _ H1).
   2: apply series_sum_inv with (x := fun n : nat =>
     f n x (contin_imp_inc _ _ _ _ (ProjT1 convF n) x Hx')).
  unfold series_sum in |- *; apply Lim_wd'; intros; simpl in |- *.
  unfold seq_part_sum in |- *; apply Sum0_wd; intros.
  rational.
 apply conv_series_inv with (x := fun n : nat =>
   f n x (contin_imp_inc _ _ _ _ (ProjT1 convF n) x Hx')).
 apply fun_series_conv_imp_conv with (Hab := Hab)
   (Hx := fun n : nat => contin_imp_inc _ _ _ _ (ProjT1 convF n) x Hx'); assumption.
Qed.

End More_Operations.

Section Other_Results.

Variables a b : IR.
Hypothesis Hab : a [<=] b.

Variable f : nat -> PartIR.

Hypothesis convF : fun_series_convergent a b Hab f.

(**
The following relate the sum series with the limit of the sequence of
partial sums; as a corollary we get the continuity of the sum of the
series.
*)

Lemma Fun_Series_Sum_char' : forall contf H,
 Feq (Compact Hab) (Fun_Series_Sum convF) (Cauchy_fun_seq_Lim _ _ Hab (fun_seq_part_sum f) contf H).
Proof.
 intros.
 FEQ.
 simpl in |- *; unfold series_sum in |- *.
 apply Lim_wd'; simpl in |- *; intros.
 unfold seq_part_sum in |- *; apply Sum0_wd; intros; algebra.
Qed.

Lemma fun_series_conv : forall H H',
 conv_fun_seq' a b Hab (fun_seq_part_sum f) (Fun_Series_Sum convF) H H'.
Proof.
 intros.
 inversion_clear convF. try rename X into H0.
 apply conv_fun_seq'_wdr with (contf := fun_seq_part_sum_cont _ _ _ _ x)
   (contF := Cauchy_cont_Lim _ _ _ _ _ H0).
  2: apply Cauchy_conv_fun_seq'.
 apply Feq_symmetric; apply Fun_Series_Sum_char'.
Qed.

Lemma Fun_Series_Sum_cont : Continuous_I Hab (Fun_Series_Sum convF).
Proof.
 intros.
 inversion_clear convF. try rename X into H.
 eapply Continuous_I_wd.
  apply Feq_symmetric; apply
    (Fun_Series_Sum_char' (fun n : nat => fun_seq_part_sum_cont _ _ _ _ x n) H).
 Contin.
Qed.

Lemma Fun_Series_Sum_char : Feq (Compact Hab)
 (Cauchy_fun_seq_Lim _ _ Hab (fun_seq_part_sum f) _ (ProjT2 convF)) (Fun_Series_Sum convF).
Proof.
 intros.
 FEQ.
 simpl in |- *.
 unfold series_sum in |- *; apply Lim_wd'.
 intro; simpl in |- *.
 unfold seq_part_sum in |- *; apply Sum0_wd; intros; algebra.
Qed.

Lemma Fun_Series_Sum_as_Lim : forall Hf H',
 conv_fun_seq' _ _ Hab (fun_seq_part_sum f) (Fun_Series_Sum convF) Hf H'.
Proof.
 intros.
 apply conv_fun_seq'_wdr with (fun_seq_part_sum_cont _ _ _ _ (ProjT1 convF))
   (Cauchy_fun_seq_Lim _ _ _ _ _ (ProjT2 convF)) (Cauchy_cont_Lim _ _ _ _ _ (ProjT2 convF)).
  apply Fun_Series_Sum_char.
 apply Cauchy_conv_fun_seq'.
Qed.

End Other_Results.

#[global]
Hint Resolve Fun_Series_Sum_cont: continuous.

Section Convergence_Criteria.

(**
** Convergence Criteria

Most of the convergence criteria for series of real numbers carry over to series of real-valued functions, so again we just present them without comments.
*)

Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Variable f : nat -> PartIR.
Hypothesis contF : forall n : nat, Continuous_I Hab (f n).

Lemma fun_str_comparison : forall g, fun_series_convergent _ _ Hab g ->
 {k : nat | forall n, k <= n -> forall x, I x -> forall Hx Hx', AbsIR (f n x Hx) [<=] g n x Hx'} ->
 fun_series_convergent _ _ Hab f.
Proof.
 set (H0 := contF) in *.
 intros g H H1.
 elim H1; intros k Hk.
 exists H0.
 apply Cauchy_fun_seq2_seq.
 intros e H2.
 elim H; intros contG convG.
 cut {N : nat | k < N /\ (forall m : nat, N <= m -> forall x : IR, I x -> forall Hx Hx', AbsSmall e
   (Part (fun_seq_part_sum g m) x Hx[-]Part (fun_seq_part_sum g N) x Hx'))}. intro H3.
  elim H3; clear H3.
  intros N HN; elim HN; clear HN; intros HN' HN.
  exists N; intros.
  assert (H' := fun n : nat => contin_imp_inc _ _ _ _ (fun_seq_part_sum_cont _ _ _ _ contG n)).
  apply leEq_transitive with (Part (fun_seq_part_sum g m) x (H' m x Hx) [-]
    Part (fun_seq_part_sum g N) x (H' N x Hx)).
   cut (forall n : nat, included (Compact Hab) (Dom (FAbs (f n)))). intro H4.
    cut (Dom (FSum N (pred m) (fun n : nat => FRestr (H4 n))) x). intro H5.
     apply leEq_transitive with (Part (FSum N (pred m) (fun n : nat => FRestr (H4 n))) x H5).
      cut (Dom (FSum N (pred m) (fun n : nat => FRestr (contin_imp_inc _ _ _ _ (H0 n)))) x). intro H6.
       apply leEq_wdl with (AbsIR (Part (FSum N (pred m)
         (fun n : nat => FRestr (contin_imp_inc _ _ _ _ (H0 n)))) x H6)).
        Opaque Frestr.
        simpl in |- *.
        Transparent Frestr.
        eapply leEq_wdr.
         apply triangle_SumIR.
         rewrite -> (Nat.lt_succ_pred k m); auto; apply Nat.lt_le_trans with N; auto.
        apply Sum_wd; intros.
        Opaque FAbs.
        simpl in |- *.
        Transparent FAbs.
        apply eq_symmetric_unfolded.
        eapply eq_transitive_unfolded.
         apply FAbs_char with (Hx' := contin_imp_inc _ _ _ _ (contF i) x Hx).
        apply AbsIR_wd; rational.
       apply AbsIR_wd; apply eq_symmetric_unfolded.
       cut (Dom (fun_seq_part_sum f m{-}fun_seq_part_sum f N) x). intro H7.
        Opaque fun_seq_part_sum.
        apply eq_transitive_unfolded with (Part _ _ H7).
         simpl in |- *; rational.
        unfold Frestr in |- *.
        apply Feq_imp_eq with I.
         apply Feq_transitive with (FSum N (pred m) f).
          unfold I in |- *; apply fun_seq_part_sum_n; auto with arith.
          apply Nat.le_lt_trans with k; [ idtac | apply Nat.lt_le_trans with N ]; auto with arith.
         apply eq_imp_Feq.
           unfold I in |- *; apply contin_imp_inc; Contin.
          simpl in |- *.
          red in |- *; intros; auto.
         simpl in |- *.
         intros. apply Sum_wd; intros; rational.
        auto.
       split; simpl in |- *.
        apply (contin_imp_inc _ _ _ _ (fun_seq_part_sum_cont _ _ _ _ H0 m)); auto.
       apply (contin_imp_inc _ _ _ _ (fun_seq_part_sum_cont _ _ _ _ H0 N)); auto.
      simpl in |- *; auto.
     cut (Dom (FSum N (pred m) g) x). intro H6.
      apply leEq_wdr with (Part _ _ H6).
       apply FSum_resp_leEq.
        rewrite -> (Nat.lt_succ_pred k m); auto; apply Nat.lt_le_trans with N; auto.
       intros.
       Opaque FAbs.
       simpl in |- *.
       eapply leEq_wdl.
        2: apply eq_symmetric_unfolded;
          apply FAbs_char with (Hx' := contin_imp_inc _ _ _ _ (contF i) x0 (HxF i)).
       apply Hk.
        apply Nat.le_trans with N; auto with arith.
       simpl in HxF.
       apply (HxF 0).
      cut (Dom (fun_seq_part_sum g m{-}fun_seq_part_sum g N) x). intro H7.
       apply eq_symmetric_unfolded.
       apply eq_transitive_unfolded with (Part _ _ H7).
        simpl in |- *; rational.
       apply Feq_imp_eq with I.
        unfold I in |- *; apply fun_seq_part_sum_n; auto with arith.
        apply Nat.le_lt_trans with k; [ idtac | apply Nat.lt_le_trans with N ]; auto with arith.
       auto.
      split; simpl in |- *.
       apply (contin_imp_inc _ _ _ _ (fun_seq_part_sum_cont _ _ _ _ contG m)); auto.
      apply (contin_imp_inc _ _ _ _ (fun_seq_part_sum_cont _ _ _ _ contG N)); auto.
     simpl in |- *; intro; apply (contin_imp_inc _ _ _ _ (contG n)); auto.
    Transparent FAbs.
    simpl in |- *; auto.
   Opaque FAbs.
   unfold I in |- *; simpl in |- *; Included.
  eapply leEq_transitive.
   apply leEq_AbsIR.
  apply AbsSmall_imp_AbsIR.
  apply HN; assumption.
 elim (convG _ H2).
 intros N HN; exists (S (Nat.max N k)).
 cut (N <= Nat.max N k); [ intro | apply Nat.le_max_l ].
 cut (k <= Nat.max N k); [ intro | apply Nat.le_max_r ].
 split.
  auto with arith.
 intros m H5 x H6 Hx Hx'.
 apply AbsIR_imp_AbsSmall.
 cut (N <= m); [ intro | apply Nat.le_trans with (Nat.max N k); auto with arith ].
 eapply leEq_wdl.
  Transparent fun_seq_part_sum.
  simpl in Hx'.
  apply (HN m _ H7 (le_S _ _ H3) x H6).
 Opaque fun_seq_part_sum.
 apply AbsIR_wd; rational.
Qed.

Transparent FAbs.

Lemma fun_comparison : forall g, fun_series_convergent _ _ Hab g ->
 (forall n x,  I x -> forall Hx Hx', AbsIR (f n x Hx) [<=] g n x Hx') ->
 fun_series_convergent _ _ Hab f.
Proof.
 intros g H H0.
 apply fun_str_comparison with g; auto.
 exists 0; intros; apply H0; auto.
Qed.

Lemma abs_imp_conv : fun_series_abs_convergent _ _ Hab f ->
 fun_series_convergent _ _ Hab f.
Proof.
 intro H.
 apply fun_comparison with (fun n : nat => FAbs (f n)).
  apply H.
 intros; apply eq_imp_leEq; apply eq_symmetric_unfolded; apply FAbs_char.
Qed.

Lemma fun_ratio_test_conv : {N : nat | {c : IR | c [<] [1] | [0] [<=] c /\
 (forall x, I x -> forall n, N <= n -> forall Hx Hx', AbsIR (f (S n) x Hx') [<=] c[*]AbsIR (f n x Hx))}} ->
 fun_series_convergent _ _ Hab f.
Proof.
 intro H.
 elim H; clear H; intros N H.
 elim H; clear H; intros c Hc1 H.
 elim H; clear H; intros H0c H.
 cut (forall x : IR, I x -> forall n : nat, N <= n ->
   forall Hx Hx', AbsIR (f n x Hx') [<=] AbsIR (f N x Hx) [*]c[^] (n - N)).
  intro H0.
  apply fun_str_comparison with (fun n : nat => FAbs (f N) {*} [-C-] (c[^] (n - N))).
   2: exists N; intros.
   2: eapply leEq_wdr.
    2: apply H0 with (Hx' := Hx) (Hx := ProjIR1 (ProjIR1 Hx')); auto with arith.
   Opaque FAbs.
   2: simpl in |- *; apply mult_wd; [ apply eq_symmetric_unfolded; apply FAbs_char | algebra ].
  apply conv_fun_series_scal with (f := fun n : nat => [-C-] (c[^] (n - N))).
   apply conv_fun_const_series with (x := fun n : nat => c[^] (n - N)).
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
   rewrite Nat.add_comm; rewrite Minus.minus_plus.
   algebra.
  Contin.
 intros x H0 n; induction  n as [| n Hrecn].
  intro.
  cut (N = 0); [ intro | auto with arith ].
  rewrite H2.
  intros.
  apply eq_imp_leEq.
  simpl in |- *.
  astepl (AbsIR (Part _ _ Hx') [*][1]); apply mult_wdl; apply AbsIR_wd; algebra.
 intro.
 elim (le_lt_eq_dec _ _ H1); intro.
  intros; apply leEq_transitive with (c[*]AbsIR (f n x (contin_imp_inc _ _ _ _ (contF n) x H0))).
   apply H; auto with arith.
  apply leEq_wdr with (AbsIR (f N x Hx) [*]c[^] (n - N) [*]c).
   rstepr (c[*] (AbsIR (Part _ _ Hx) [*]c[^] (n - N))).
   apply mult_resp_leEq_lft.
    apply Hrecn; auto with arith.
   assumption.
  rewrite Nat.sub_succ_l.
   simpl in |- *; rational.
  auto with arith.
 rewrite b0; intros.
 rewrite Nat.sub_diag.
 apply eq_imp_leEq.
 simpl in |- *; eapply eq_transitive_unfolded.
  2: apply eq_symmetric_unfolded; apply mult_one.
 apply AbsIR_wd; algebra.
Qed.

End Convergence_Criteria.
