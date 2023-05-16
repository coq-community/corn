(* Copyright © 1998-2008
 * Henk Barendregt
 * Luís Cruz-Filipe
 * Herman Geuvers
 * Mariusz Giero
 * Rik van Ginneken
 * Dimitri Hendriks
 * Sébastien Hinderer
 * Cezary Kaliszyk
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

Require Import CoRN.tactics.CornTac.
Require Export CoRN.transc.SinCos.

Section Properties_of_Pi.

(** printing Pi %\ensuremath{\pi}% #&pi;# *)

(**
** Definition of Pi

[Pi] is defined as twice the first positive zero of the cosine.  In order to do this, we follow the construction described in Bishop 1969, section 7.
*)

Fixpoint pi_seq (n : nat) : IR :=
  match n with
  | O => [0]
  | S p => pi_seq p[+]Cos (pi_seq p)
  end.

Opaque Cosine.

(* begin hide *)
Lemma pi_seq_lemma : forall n, [0] [<=] pi_seq n
  and (forall t : IR, [0] [<=] t -> t [<=] pi_seq n -> [0] [<] Cos t).
Proof.
 intro; induction  n as [| n Hrecn].
  split; intros.
   simpl in |- *; apply leEq_reflexive.
  simpl in H0.
  cut (t [=] [0]); [ intro | apply leEq_imp_eq; auto ].
  astepr (Cos [0]).
  astepr OneR.
  apply pos_one.
 inversion_clear Hrecn; split.
  astepr (pi_seq n[+]Cos (pi_seq n)).
  astepl (ZeroR[+][0]); apply plus_resp_leEq_both.
   auto.
  apply less_leEq; apply X; auto.
  apply leEq_reflexive.
 simpl in |- *.
 rename X into H0. intros t H1 H2.
 apply Continuous_imp_pos with (Hac := leEq_transitive _ _ _ _ H1 H2) (b := pi_seq n); auto.
    simpl in |- *.
    apply shift_less_plus'; astepl ZeroR.
    simpl in H0; apply H0; auto.
    apply leEq_reflexive.
   apply included_imp_Continuous with realline; Contin.
  intros.
  apply less_wdr with (Cos t0).
   2: simpl in |- *; algebra.
  auto.
 clear H2 H1 t; intros t H1 H2 Ht.
 set (x := pi_seq n) in *.
 apply less_wdr with (Cosine x I[+] ( {--}Cosine x I[-] {--}Cosine t Ht)).
  2: simpl in |- *; rational.
 assert (H3 : Derivative realline I {--}Cosine Sine).
  apply Derivative_wdr with ( {--}{--}Sine).
   Opaque Sine.
   FEQ. Deriv.
  assert (H4 : Continuous_I (Min_leEq_Max x t) Sine).
  apply included_imp_Continuous with realline; Contin.
 set (B := Barrow _ _ Continuous_Sin I {--}Cosine) in *.
 set (B' := B H3 x t H4 I I) in *.
 apply less_wdr with (Cosine x I[-]Integral H4).
  2: unfold cg_minus at 1 in |- *; apply bin_op_wd_unfolded.
   2: algebra.
  2: rstepr ( [--] ( {--}Cosine t Ht[-] {--}Cosine x I)).
  2: apply un_op_wd_unfolded; eapply eq_transitive.
   2: apply B'.
  2: algebra.
 clear B' B H3.
 apply less_wdl with (Cos (pi_seq n) [-] (pi_seq (S n) [-]pi_seq n)).
  2: simpl in |- *; rational.
 unfold cg_minus at 1 3 in |- *.
 apply plus_resp_less_lft.
 apply inv_resp_less.
 apply less_leEq_trans with (t[-]x).
  2: apply minus_resp_leEq; auto.
 eapply leEq_less_trans.
  apply leEq_AbsIR.
 eapply less_leEq_trans.
  apply (ub_Integral _ _ _ _ H4 (less_imp_ap _ _ _ H1) [1]) with x I.
    intros.
    apply leEq_wdl with (AbsIR (Sin x0)).
     apply AbsIR_Sin_leEq_One.
    apply AbsIR_wd; simpl in |- *; algebra.
   apply compact_map2 with (Hab := less_leEq _ _ _ H1).
   apply compact_inc_lft.
  apply less_wdl with (AbsIR (Sin x)).
   2: simpl in |- *; algebra.
  apply AbsIR_Sin_less_One.
  apply H0; auto.
  apply leEq_reflexive.
 apply eq_imp_leEq.
 astepl (AbsIR (t[-]x)).
 apply AbsIR_eq_x.
 apply shift_leEq_minus; apply less_leEq.
 astepl x; auto.
Qed.
(* end hide *)

(**
This sequence is nonnegative and the cosine of any number between
[[0]] and any of its values is strictly positive; therefore the
sequence is strictly increasing.
*)

Lemma pi_seq_nonneg : forall n : nat, [0] [<=] pi_seq n.
Proof.
 intro; elim (pi_seq_lemma n); auto.
Qed.

Lemma cos_pi_seq_pos : forall n t, [0] [<=] t -> t [<=] pi_seq n -> [0] [<] Cos t.
Proof.
 intro; elim (pi_seq_lemma n); auto.
Qed.

Lemma pi_seq_incr : forall n : nat, pi_seq n [<] pi_seq (S n).
Proof.
 intro; astepr (pi_seq n[+]Cos (pi_seq n)).
 apply shift_less_plus'; astepl ZeroR.
 apply cos_pi_seq_pos with n.
  apply pi_seq_nonneg.
 apply leEq_reflexive.
Qed.

(** Trivial---but useful---consequences. *)

Lemma sin_pi_seq_mon : forall x y n, [0] [<=] x -> x [<=] y -> y [<=] pi_seq n -> Sin x [<=] Sin y.
Proof.
 intros; simpl in |- *.
 apply Derivative_imp_resp_leEq with realline I Cosine.
     Deriv.
    auto.
   simpl in |- *; auto.
  simpl in |- *; auto.
 intros.
 apply leEq_glb.
 intros y0 H2 Hy.
 apply less_leEq.
 apply less_wdr with (Cos y0).
  2: simpl in |- *; algebra.
 inversion_clear H2.
 apply cos_pi_seq_pos with n.
  apply leEq_transitive with x; auto.
  eapply leEq_wdl.
   apply H3.
  eapply eq_transitive.
   apply Min_comm.
  apply leEq_imp_Min_is_lft; auto.
 apply leEq_transitive with y; auto.
 eapply leEq_wdr.
  apply H4.
 eapply eq_transitive.
  apply Max_comm.
 apply leEq_imp_Max_is_rht; auto.
Qed.

Lemma sin_pi_seq_nonneg : forall n : nat, [0] [<=] Sin (pi_seq n).
Proof.
 intro.
 astepl (Sin [0]).
 apply sin_pi_seq_mon with n.
   apply leEq_reflexive.
  apply pi_seq_nonneg.
 apply leEq_reflexive.
Qed.

Lemma sin_pi_seq_gt_one : forall t n, [1] [<=] t -> t [<=] pi_seq (S n) -> Sin [1] [<=] Sin t.
Proof.
 intros.
 apply sin_pi_seq_mon with (S n); auto.
 apply less_leEq; apply pos_one.
Qed.

Lemma cos_pi_seq_mon : forall x y n, [0] [<=] x -> x [<=] y -> y [<=] pi_seq n -> Cos y [<=] Cos x.
Proof.
 intros.
 apply power_cancel_leEq with 2.
   auto.
  apply less_leEq; apply cos_pi_seq_pos with n.
   auto.
  apply leEq_transitive with y; auto.
 apply inv_cancel_leEq.
 rstepl ([1][-]Cos x[^]2[-][1]).
 rstepr ([1][-]Cos y[^]2[-][1]).
 apply minus_resp_leEq.
 apply leEq_wdl with (Sin x[^]2).
  apply leEq_wdr with (Sin y[^]2).
   apply nexp_resp_leEq.
    astepl (Sin [0]); apply sin_pi_seq_mon with n.
      apply leEq_reflexive.
     auto.
    apply leEq_transitive with y; auto.
   apply sin_pi_seq_mon with n; auto.
  astepl (Sin y[^]2[+]Cos y[^]2[-]Cos y[^]2).
  apply cg_minus_wd.
   Step_final (Cos y[^]2[+]Sin y[^]2).
  algebra.
 astepl (Sin x[^]2[+]Cos x[^]2[-]Cos x[^]2).
 apply cg_minus_wd.
  Step_final (Cos x[^]2[+]Sin x[^]2).
 algebra.
Qed.

(* begin hide *)
Lemma pi_seq_gt_one : forall n : nat, [1] [<=] pi_seq (S n).
Proof.
 intros.
 apply leEq_wdl with (pi_seq 1).
  2: simpl in |- *.
  2: Step_final (Cos [0]).
 apply local_mon_imp_mon'.
  intro; apply pi_seq_incr; auto.
 auto with arith.
Qed.

Lemma pi_seq_bnd :
  forall n : nat,
  pi_seq (S (S (S n))) [-]pi_seq (S (S n)) [<=]
  ([1][-]Sin [1]) [*] (pi_seq (S (S n)) [-]pi_seq (S n)).
Proof.
 intros.
 set (F := FId{+}Cosine) in *.
 assert (H : Derivative realline I F ( [-C-][1]{+}{--}Sine)). unfold F in |- *; Deriv.
  astepr ([0][+] ([1][-]Sin [1]) [*] (pi_seq (S (S n)) [-]pi_seq (S n))).
 apply shift_leEq_plus.
 apply approach_zero_weak; intros e H0.
 elim (Law_of_the_Mean _ _ _ _ H (pi_seq (S n)) (pi_seq (S (S n)))) with e.
    2: simpl in |- *; auto.
   2: simpl in |- *; auto.
  2: auto.
 intros t H1 H2.
 unfold F in H2.
 apply leEq_transitive with (pi_seq (S (S (S n))) [-]pi_seq (S (S n)) [-]
   ([1][-]Sin t) [*] (pi_seq (S (S n)) [-]pi_seq (S n))).
  unfold cg_minus at 1 5 in |- *; apply plus_resp_leEq_lft.
  apply inv_resp_leEq.
  apply mult_resp_leEq_rht.
   unfold cg_minus in |- *; apply plus_resp_leEq_lft.
   apply inv_resp_leEq; inversion_clear H1.
   apply sin_pi_seq_gt_one with (S (S n)).
    eapply leEq_transitive.
     2: apply H3.
    apply leEq_Min; apply pi_seq_gt_one.
   eapply leEq_transitive.
    apply H4.
   apply Max_leEq; apply less_leEq.
    eapply less_transitive_unfolded; apply pi_seq_incr.
   apply pi_seq_incr.
  apply shift_leEq_minus; apply less_leEq.
  astepl (pi_seq (S n)); apply pi_seq_incr.
 eapply leEq_transitive.
  apply leEq_AbsIR.
 set (H3 := (I, I)) in *.
 eapply leEq_wdl.
  apply (H2 H3 H3 H3).
 apply AbsIR_wd.
 Opaque Sine Cosine.
 simpl in |- *; rational.
Qed.

Lemma pi_seq_bnd' :
  forall n : nat,
  pi_seq (S (S (S n))) [-]pi_seq (S (S n)) [<=]
  ([1][-]Sin [1]) [^]S n[*] (pi_seq 2[-]pi_seq 1).
Proof.
 intro; induction  n as [| n Hrecn].
  eapply leEq_wdr.
   apply pi_seq_bnd.
  algebra.
 eapply leEq_transitive.
  apply pi_seq_bnd.
 apply leEq_wdr with (([1][-]Sin [1]) [*] (([1][-]Sin [1]) [^]S n[*] (pi_seq 2[-]pi_seq 1))).
  2: simpl in |- *; rational.
 apply mult_resp_leEq_lft.
  auto.
 apply shift_leEq_minus; astepl (Sin [1]).
 eapply leEq_transitive.
  apply leEq_AbsIR.
 apply AbsIR_Sin_leEq_One.
Qed.

Lemma pi_seq_bnd'' :
  forall n : nat,
  2 <= n ->
  pi_seq (S n) [-]pi_seq n [<=] ([1][-]Sin [1]) [^]pred n[*] (pi_seq 2[-]pi_seq 1).
Proof.
 intro; case n.
  intros; exfalso; inversion H.
 clear n.
 intro; case n; intros.
  exfalso; inversion H; inversion H1.
 eapply leEq_wdr.
  apply pi_seq_bnd'.
 algebra.
Qed.
(* end hide *)

(** An auxiliary result. *)

Lemma Sin_One_pos : [0] [<] Sin [1].
Proof.
 astepl (Sin [0]).
 simpl in |- *.
 apply Derivative_imp_resp_less with realline I Cosine.
     Deriv.
    apply pos_one.
   simpl in |- *; auto.
  simpl in |- *; auto.
 intros.
 apply less_leEq_trans with (Cos [1]).
  apply less_wdr with (Cos (pi_seq 1)).
   2: astepl (Cos ([0][+]Cos [0])); apply Cos_wd; Step_final (Cos [0]).
  apply cos_pi_seq_pos with 1.
   simpl in |- *.
   astepr (Cos [0]); astepr OneR.
   apply less_leEq; apply pos_one.
  apply leEq_reflexive.
 apply leEq_glb.
 intros y H Hy; apply leEq_wdr with (Cos y).
  2: simpl in |- *; algebra.
 inversion_clear H.
 apply cos_pi_seq_mon with 1.
   eapply leEq_wdl.
    apply H0.
   apply leEq_imp_Min_is_lft; apply less_leEq; apply pos_one.
  eapply leEq_wdr.
   apply H1.
  apply leEq_imp_Max_is_rht; apply less_leEq; apply pos_one.
 apply eq_imp_leEq; simpl in |- *.
 Step_final (Cos [0]).
Qed.

(** We can now prove that this is a Cauchy sequence.  We define [Pi] as
twice its limit.
*)

Lemma pi_seq_Cauchy : Cauchy_prop pi_seq.
Proof.
 intros e H.
 cut ([0] [<] pi_seq 2[-]pi_seq 1). intro H0.
  assert (H1 : pi_seq 2[-]pi_seq 1 [#] [0]). apply Greater_imp_ap; auto.
   cut (Sin [1] [<] [1]).
   intro Sin_One_less_One.
   elim qi_yields_zero with (e := Sin [1][*]e[/] _[//]H1) (q := [1][-]Sin [1]).
      intros N HN.
      exists (S (S N)); intros.
      apply AbsIR_imp_AbsSmall.
      apply leEq_wdl with (pi_seq m[-]pi_seq (S (S N))).
       2: apply eq_symmetric; apply AbsIR_eq_x.
       2: apply shift_leEq_minus; astepl (pi_seq (S (S N))).
       2: apply local_mon_imp_mon'.
        2: intro; apply pi_seq_incr; auto.
       2: auto.
      cut (m = S (pred m)); [ intro | apply S_pred with (S N); auto ].
      apply leEq_wdl with (Sum (S (S N)) (pred m) (fun i : nat => pi_seq (S i) [-]pi_seq i)).
       2: eapply eq_transitive.
        2: apply Mengolli_Sum_gen with (f := pi_seq).
         2: algebra.
        2: auto with arith.
       2: rewrite <- H3; algebra.
      set (z := [1][-]Sin [1]) in *.
      apply leEq_transitive with (Sum (S (S N)) (pred m)
        (fun i : nat => z[^]pred i[*] (pi_seq 2[-]pi_seq 1))).
       apply Sum_resp_leEq.
        rewrite <- H3; auto.
       intros; apply pi_seq_bnd''.
       apply Nat.le_trans with (S (S N)); auto with arith.
      eapply leEq_wdl.
       2: apply eq_symmetric; apply Sum_comm_scal with (s := fun i : nat => z[^]pred i).
      rstepl (Sum (S (S N)) (pred m) (fun i : nat => z[^]pred i) [*] (pi_seq 2[-]pi_seq 1)).
      apply shift_mult_leEq with H1.
       auto.
      apply leEq_wdl with (Sum (S N) (pred (pred m)) (fun i : nat => z[^]i)).
       2: cut (pred m = S (pred (pred m))); [ intro | apply S_pred with N; auto with arith ].
       2: pattern (pred m) at 2 in |- *; rewrite H4.
       2: apply Sum_shift; algebra.
      cut (z[-][1] [#] [0]). intro H4.
       eapply leEq_wdl.
        2: apply eq_symmetric; apply Sum_c_exp with (H := H4).
       rstepl ((z[^]S (pred (pred m)) [/] _[//]H4) [-] (z[^]S N[/] _[//]H4)).
       apply leEq_transitive with ( [--] (z[^]S N) [/] _[//]H4).
        apply shift_minus_leEq; rstepr ZeroR; apply less_leEq.
        unfold z in |- *.
        rstepl ( [--] (([1][-]Sin [1]) [^]S (pred (pred m))) [/] Sin [1][//] pos_ap_zero _ _ Sin_One_pos).
        apply shift_div_less.
         apply Sin_One_pos.
        astepr ZeroR; astepr ( [--]ZeroR).
        apply inv_resp_less.
        apply less_wdl with (ZeroR[^]S (pred (pred m))).
         2: simpl in |- *; algebra.
        apply nexp_resp_less.
          auto with arith.
         apply leEq_reflexive.
        apply shift_less_minus; astepl (Sin [1]).
        auto.
       unfold z at 2 in |- *.
       rstepl (z[^]S N[/] _[//]pos_ap_zero _ _ Sin_One_pos).
       apply shift_div_leEq.
        apply Sin_One_pos.
       eapply leEq_transitive.
        eapply leEq_transitive.
         2: apply HN.
        simpl in |- *.
        astepr (nexp IR N z[*][1]); apply mult_resp_leEq_lft.
         unfold z in |- *.
         apply shift_minus_leEq; apply shift_leEq_plus'.
         astepl ZeroR; apply less_leEq; apply Sin_One_pos.
        astepr (z[^]N); apply nexp_resp_nonneg.
        unfold z in |- *.
        apply shift_leEq_minus; astepl (Sin [1]).
        apply less_leEq; auto.
       apply eq_imp_leEq.
       rational.
      unfold z in |- *.
      rstepl ( [--] (Sin [1])).
      apply inv_resp_ap_zero.
      apply Greater_imp_ap; apply Sin_One_pos.
     apply shift_leEq_minus.
     apply less_leEq; astepl (Sin [1]); auto.
    apply shift_minus_less; apply shift_less_plus'.
    astepl ZeroR; apply Sin_One_pos.
   apply div_resp_pos.
    auto.
   apply mult_resp_pos; auto.
   apply Sin_One_pos.
  apply Sin_less_One.
  apply cos_pi_seq_pos with 1.
   apply less_leEq; apply pos_one.
  simpl in |- *.
  apply eq_imp_leEq; Step_final (Cos [0]).
 apply shift_less_minus; astepl (pi_seq 1).
 apply pi_seq_incr; auto.
Qed.

Definition Pi := Two[*]Lim (Build_CauchySeq _ _ pi_seq_Cauchy).

(**
For $x\in[0,\frac{\pi}2)$#x&isin;[0,&pi;/2)#, [(Cos x) [>] 0];
$\cos(\frac{pi}2)=0$#cos(&pi;/2)=0#.
*)

Lemma pos_cos : forall x, [0] [<=] x -> x [<] Pi [/]TwoNZ -> [0] [<] Cos x.
Proof.
 intros x H H0.
 assert (H1 : x [<] Lim (Build_CauchySeq _ _ pi_seq_Cauchy)).
  apply less_wdr with (Pi [/]TwoNZ); auto; unfold Pi in |- *; rational.
 elim (less_Lim_so_less_seq _ _ H1); intros N HN.
 apply cos_pi_seq_pos with N.
  auto.
 apply less_leEq; auto.
Qed.

Lemma Cos_HalfPi : Cos (Pi [/]TwoNZ) [=] [0].
Proof.
 transitivity (Cos (Lim (Build_CauchySeq _ _ pi_seq_Cauchy))).
  apply Cos_wd; unfold Pi in |- *; rational.
 astepr (Lim (Build_CauchySeq _ _ pi_seq_Cauchy) [-] Lim (Build_CauchySeq _ _ pi_seq_Cauchy)).
 assert (H : Cauchy_prop (fun n : nat => pi_seq (S n))).
  apply conv_seq_imp_conv_subseq with pi_seq S; auto with arith.
    intro; exists (S n); split; apply Nat.lt_succ_diag_r.
   simpl in |- *; auto.
   algebra.
  apply pi_seq_Cauchy.
 transitivity
   (Lim (Build_CauchySeq _ _ H) [-]Lim (Build_CauchySeq _ _ pi_seq_Cauchy)).
  2: apply cg_minus_wd; algebra.
  2: apply Lim_subseq_eq_Lim_seq with S; auto with arith.
    2: intro; exists (S n); split; apply Nat.lt_succ_diag_r.
   2: simpl in |- *; auto.
   2: algebra.
  2: left; intros; simpl in |- *.
  2: apply local_mon_imp_mon'; auto; apply pi_seq_incr.
 eapply eq_transitive.
  2: apply Lim_minus.
 assert (H0 : Cauchy_prop (fun n : nat => Cosine (pi_seq n) (cos_domain _))).
  apply Cauchy_prop_wd with (fun n : nat => pi_seq (S n) [-]pi_seq n).
   2: intros; simpl in |- *; rational.
  exact (Cauchy_minus (Build_CauchySeq _ _ H) (Build_CauchySeq _ _ pi_seq_Cauchy)).
 transitivity (Lim (Build_CauchySeq _ _ H0)).
  2: apply Lim_wd'; intros; simpl in |- *; rational.
 simpl in |- *.
 apply Continuous_imp_comm_Lim with (e := OneR) (x := Build_CauchySeq _ _ pi_seq_Cauchy)
   (Hxn := fun n : nat => cos_domain (pi_seq n)).
  apply pos_one.
 apply Included_imp_Continuous with realline; Contin.
Qed.

(** Convergence to [Pi [/] Two] is increasing; therefore, [Pi] is positive. *)

Lemma HalfPi_gt_pi_seq : forall n : nat, pi_seq n [<] Pi [/]TwoNZ.
Proof.
 intros.
 unfold Pi in |- *.
 rstepr (Lim (Build_CauchySeq _ _ pi_seq_Cauchy)).
 apply less_leEq_trans with (pi_seq (S n)).
  apply pi_seq_incr.
 apply str_leEq_seq_so_leEq_Lim.
 exists (S n); intros.
 apply local_mon_imp_mon'.
  apply pi_seq_incr.
 auto.
Qed.

Lemma pos_Pi : [0] [<] Pi.
Proof.
 astepr (Two[*]Pi [/]TwoNZ).
 apply mult_resp_pos.
  apply pos_two.
 astepl (pi_seq 0).
 apply HalfPi_gt_pi_seq.
Qed.

End Properties_of_Pi.

#[global]
Hint Resolve Cos_HalfPi: algebra.

Section Pi_and_Order.

(**
** Properties of Pi

The following are trivial ordering properties of multiples of [Pi]
that will be used so often that it is convenient to state as lemmas;
also, we define a hint database that automatically tries to apply this
lemmas, to make proof development easier.

A summary of what is being proved is simply:
[[
[--]Pi [<] [--]Pi[/]Two [<] [--] Pi[/]Four [<] [0] [<] Pi[/]Four [<] Pi[/]Two [<] Pi
]]

[PiSolve] will prove any of these inequalities.
*)

Lemma pos_HalfPi : [0] [<] Pi [/]TwoNZ.
Proof.
 apply pos_div_two; apply pos_Pi.
Qed.

Lemma pos_QuarterPi : [0] [<] Pi [/]FourNZ.
Proof.
 apply pos_div_four; apply pos_Pi.
Qed.

Lemma QuarterPi_less_HalfPi : Pi [/]FourNZ [<] Pi [/]TwoNZ.
Proof.
 rstepl ((Pi [/]TwoNZ) [/]TwoNZ).
 apply pos_div_two'; apply pos_HalfPi.
Qed.

Lemma HalfPi_less_Pi : Pi [/]TwoNZ [<] Pi.
Proof.
 apply pos_div_two'; apply pos_Pi.
Qed.

Lemma QuarterPi_less_Pi : Pi [/]FourNZ [<] Pi.
Proof.
 apply pos_div_four'; apply pos_Pi.
Qed.

Lemma neg_invPi : [--]Pi [<] [0].
Proof.
 astepr ( [--]ZeroR); apply inv_resp_less; apply pos_Pi.
Qed.

Lemma neg_invHalfPi : [--] (Pi [/]TwoNZ) [<] [0].
Proof.
 astepr ( [--]ZeroR); apply inv_resp_less; apply pos_HalfPi.
Qed.

Lemma neg_invQuarterPi : [--] (Pi [/]FourNZ) [<] [0].
Proof.
 astepr ( [--]ZeroR); apply inv_resp_less; apply pos_QuarterPi.
Qed.

Lemma invHalfPi_less_invQuarterPi : [--] (Pi [/]TwoNZ) [<] [--] (Pi [/]FourNZ).
Proof.
 apply inv_resp_less; apply QuarterPi_less_HalfPi.
Qed.

Lemma invPi_less_invHalfPi : [--]Pi [<] [--] (Pi [/]TwoNZ).
Proof.
 apply inv_resp_less; apply HalfPi_less_Pi.
Qed.

Lemma invPi_less_invQuarterPi : [--]Pi [<] [--] (Pi [/]FourNZ).
Proof.
 apply inv_resp_less; apply QuarterPi_less_Pi.
Qed.

Lemma invPi_less_Pi : [--]Pi [<] Pi.
Proof.
 apply less_transitive_unfolded with ZeroR.
  apply neg_invPi.
 apply pos_Pi.
Qed.

Lemma invPi_less_HalfPi : [--]Pi [<] Pi [/]TwoNZ.
Proof.
 apply less_transitive_unfolded with ZeroR.
  apply neg_invPi.
 apply pos_HalfPi.
Qed.

Lemma invPi_less_QuarterPi : [--]Pi [<] Pi [/]FourNZ.
Proof.
 apply less_transitive_unfolded with ZeroR.
  apply neg_invPi.
 apply pos_QuarterPi.
Qed.

Lemma invHalfPi_less_Pi : [--] (Pi [/]TwoNZ) [<] Pi.
Proof.
 apply less_transitive_unfolded with ZeroR.
  apply neg_invHalfPi.
 apply pos_Pi.
Qed.

Lemma invHalfPi_less_HalfPi : [--] (Pi [/]TwoNZ) [<] Pi [/]TwoNZ.
Proof.
 apply less_transitive_unfolded with ZeroR.
  apply neg_invHalfPi.
 apply pos_HalfPi.
Qed.

Lemma invHalfPi_less_QuarterPi : [--] (Pi [/]TwoNZ) [<] Pi [/]FourNZ.
Proof.
 apply less_transitive_unfolded with ZeroR.
  apply neg_invHalfPi.
 apply pos_QuarterPi.
Qed.

Lemma invQuarterPi_less_Pi : [--] (Pi [/]FourNZ) [<] Pi.
Proof.
 apply less_transitive_unfolded with ZeroR.
  apply neg_invQuarterPi.
 apply pos_Pi.
Qed.

Lemma invQuarterPi_less_HalfPi : [--] (Pi [/]FourNZ) [<] Pi [/]TwoNZ.
Proof.
 apply less_transitive_unfolded with ZeroR.
  apply neg_invQuarterPi.
 apply pos_HalfPi.
Qed.

Lemma invQuarterPi_less_QuarterPi : [--] (Pi [/]FourNZ) [<] Pi [/]FourNZ.
Proof.
 apply less_transitive_unfolded with ZeroR.
  apply neg_invQuarterPi.
 apply pos_QuarterPi.
Qed.

End Pi_and_Order.

#[global]
Hint Resolve pos_Pi pos_HalfPi pos_QuarterPi QuarterPi_less_HalfPi
  HalfPi_less_Pi QuarterPi_less_Pi neg_invPi neg_invHalfPi neg_invQuarterPi
  invHalfPi_less_invQuarterPi invPi_less_invHalfPi invPi_less_invQuarterPi
  invPi_less_Pi invPi_less_HalfPi invPi_less_QuarterPi invHalfPi_less_Pi
  invHalfPi_less_HalfPi invHalfPi_less_QuarterPi invQuarterPi_less_Pi
  invQuarterPi_less_HalfPi invQuarterPi_less_QuarterPi: piorder.

(* begin hide *)
Ltac PiSolve := try apply less_leEq; auto with piorder.
(* end hide *)

Section Sin_And_Cos.

(**
** More formulas

We now move back to trigonometric identities: sine, cosine and tangent of
the double.
*)

Lemma Cos_double : forall x : IR, Cos (Two[*]x) [=] Two[*]Cos x[^]2[-][1].
Proof.
 intros.
 astepl (Cos (x[+]x)).
 astepl (Cos x[*]Cos x[-]Sin x[*]Sin x).
 astepl (Cos x[^]2[-]Sin x[^]2).
 rstepr (Cos x[^]2[-] ([1][-]Cos x[^]2)).
 apply cg_minus_wd; algebra.
 astepr (Cos x[^]2[+]Sin x[^]2[-]Cos x[^]2); rational.
Qed.

Lemma Sin_double : forall x : IR, Sin (Two[*]x) [=] Two[*]Sin x[*]Cos x.
Proof.
 intros.
 astepl (Sin (x[+]x)).
 eapply eq_transitive_unfolded.
  apply Sin_plus.
 rational.
Qed.

Lemma Tan_double : forall x Hx Hx' H, Tan (Two[*]x) Hx' [=] (Two[*]Tan x Hx[/] [1][-]Tan x Hx[^]2[//]H).
Proof.
 intros.
 cut (Dom Tang (x[+]x)). intro H0.
  astepl (Tan (x[+]x) H0).
  cut ([1][-]Tan x Hx[*]Tan x Hx [#] [0]). intro H1.
   eapply eq_transitive_unfolded.
    apply Tan_plus with (Hx := Hx) (Hy := Hx) (H := H1).
   simpl in |- *; rational.
  astepl ([1][-]Tan x Hx[^]2). auto.
  apply dom_wd with (Two[*]x); algebra.
Qed.

(* begin hide *)
Lemma sqrt_lemma : forall Hpos H, [1] [/]TwoNZ [=] ([1][/] sqrt Two Hpos[//]H) [^]2.
Proof.
 intros.
 Step_final ([1][^]2[/] _[//]nexp_resp_ap_zero 2 H).
Qed.
(* end hide *)

(** Value of trigonometric functions at [Pi[/]Four]. *)

Lemma Cos_QuarterPi : forall Hpos H, Cos (Pi [/]FourNZ) [=] ([1][/] sqrt Two Hpos[//]H).
Proof.
 intros.
 apply square_eq_pos.
   apply recip_resp_pos.
   apply power_cancel_less with 2.
    apply sqrt_nonneg.
   astepr (Two:IR).
   simpl in |- *; fold (Two:IR) in |- *; astepl ZeroR.
   apply pos_two.
  apply pos_cos; PiSolve.
 eapply eq_transitive_unfolded.
  2: apply sqrt_lemma.
 astepr ((ZeroR[+][1]) [/]TwoNZ).
 astepr ((Cos (Pi [/]TwoNZ) [+][1]) [/]TwoNZ).
 rstepl ((Two[*]Cos (Pi [/]FourNZ) [^]2[-][1][+][1]) [/]TwoNZ).
 apply div_wd.
  2: algebra.
 apply bin_op_wd_unfolded.
  2: algebra.
 transitivity (Cos (Two[*]Pi [/]FourNZ)).
  apply eq_symmetric_unfolded; apply Cos_double.
 apply Cos_wd; rational.
Qed.

Lemma Sin_QuarterPi : forall Hpos H, Sin (Pi [/]FourNZ) [=] ([1][/] sqrt Two Hpos[//]H).
Proof.
 intros.
 apply square_eq_pos.
   apply recip_resp_pos.
   apply power_cancel_less with 2.
    apply sqrt_nonneg.
   astepr (Two:IR).
   simpl in |- *; fold (Two:IR) in |- *; astepl ZeroR.
   apply pos_two.
  apply less_leEq_trans with (Sin ([1] [/]TwoNZ)).
   cut ([0] [<] Cos ([1] [/]TwoNZ)). intro H0.
    apply less_wdr with ((Sin [1][/] _[//]pos_ap_zero _ _ H0) [/]TwoNZ).
     apply pos_div_two.
     apply div_resp_pos.
      auto.
     apply Sin_One_pos.
    rstepr ((Two[*]Sin ([1] [/]TwoNZ) [*]Cos ([1] [/]TwoNZ) [/] _[//]pos_ap_zero _ _ H0) [/]TwoNZ).
    repeat apply div_wd.
      astepl (Sin (Two[*][1] [/]TwoNZ)).
      apply Sin_double.
     algebra.
    algebra.
   apply pos_cos; PiSolve.
    apply pos_div_two; apply pos_one.
   apply less_transitive_unfolded with (pi_seq 1).
    simpl in |- *; astepr (Cos [0]); astepr OneR.
    astepl (OneR [/]TwoNZ); apply pos_div_two'; apply pos_one.
   apply HalfPi_gt_pi_seq.
  elim (less_Lim_so_less_seq (Build_CauchySeq _ _ pi_seq_Cauchy) (Pi [/]FourNZ)).
   intros N HN; apply sin_pi_seq_mon with N.
     apply less_leEq; apply pos_div_two; apply pos_one.
    apply shift_div_leEq.
     apply pos_two.
    astepl (Cos [0]); astepl ([0][+]Cos [0]).
    rstepr (Pi [/]TwoNZ).
    apply less_leEq; apply (HalfPi_gt_pi_seq 1).
   apply less_leEq; auto.
  eapply less_wdr.
   apply QuarterPi_less_HalfPi.
  unfold Pi in |- *; rational.
 eapply eq_transitive_unfolded.
  2: apply sqrt_lemma.
 rstepr ([1][-]OneR [/]TwoNZ).
 astepr (Cos (Pi [/]FourNZ) [^]2[+]Sin (Pi [/]FourNZ) [^]2[-][1] [/]TwoNZ).
 rstepl (([1][/] _[//]H) [^]2[+]Sin (Pi [/]FourNZ) [^]2[-] ([1][/] _[//]H) [^]2).
 apply cg_minus_wd.
  apply bin_op_wd_unfolded.
   apply nexp_wd.
   apply eq_symmetric; apply Cos_QuarterPi.
  algebra.
 apply eq_symmetric; apply sqrt_lemma.
Qed.

Hint Resolve Sin_QuarterPi Cos_QuarterPi: algebra.

Opaque Sine Cosine.

Lemma Tan_QuarterPi : forall H, Tan (Pi [/]FourNZ) H [=] [1].
Proof.
 intros.
 set (pos2 := less_leEq _ _ _ (pos_two IR)) in *.
 cut (sqrt Two pos2 [#] [0]).
  2: apply Greater_imp_ap.
  2: apply power_cancel_less with 2.
   2: apply sqrt_nonneg.
  2: apply less_wdl with ZeroR.
   2: astepr (Two:IR); apply pos_two.
  2: simpl in |- *; algebra.
 intro H0.
 unfold Tan in |- *; simpl in |- *.
 astepr (([1][/] _[//]H0) [/] _[//]recip_ap_zero _ _ H0).
 apply div_wd.
  astepr (Sin (Pi [/]FourNZ)).
  simpl in |- *; algebra.
 astepr (Cos (Pi [/]FourNZ)).
 simpl in |- *; algebra.
Qed.

(** Shifting sine and cosine by [Pi[/]Two] and [Pi]. *)

Lemma Sin_HalfPi : Sin (Pi [/]TwoNZ) [=] [1].
Proof.
 transitivity  (Sin (Two[*]Pi [/]FourNZ)).
  apply Sin_wd; rational.
 eapply eq_transitive.
  apply Sin_double.
 astepr ((Two:IR) [*][1] [/]TwoNZ).
 eapply eq_transitive.
  apply eq_symmetric; apply CRings.mult_assoc.
 apply mult_wdr.
 cut (sqrt _ (less_leEq _ _ _ (pos_two IR)) [#] [0]). intro H.
  eapply eq_transitive.
   2: symmetry; apply (sqrt_lemma _ H).
  simpl in |- *.
  eapply eq_transitive.
   2: apply CRings.mult_assoc.
  eapply eq_transitive.
   apply eq_symmetric; apply one_mult.
  apply mult_wdr.
  apply mult_wd.
   apply Sin_QuarterPi.
  apply Cos_QuarterPi.
 apply Greater_imp_ap; apply sqrt_less.
 simpl in |- *; astepl ZeroR; apply (pos_two IR).
Qed.

Hint Resolve Sin_HalfPi: algebra.

Lemma Sin_plus_HalfPi : forall x : IR, Sin (x[+]Pi [/]TwoNZ) [=] Cos x.
Proof.
 intro.
 eapply eq_transitive.
  apply Sin_plus.
 astepl (Sin x[*][0][+]Cos x[*][1]).
 Step_final ([0][+]Cos x).
Qed.

Lemma Sin_HalfPi_minus : forall x : IR, Sin (Pi [/]TwoNZ[-]x) [=] Cos x.
Proof.
 intros.
 unfold cg_minus in |- *.
 astepl (Sin ( [--]x[+]Pi [/]TwoNZ)).
 eapply eq_transitive.
  apply Sin_plus_HalfPi.
 algebra.
Qed.

Lemma Cos_plus_HalfPi : forall x : IR, Cos (x[+]Pi [/]TwoNZ) [=] [--] (Sin x).
Proof.
 intro.
 eapply eq_transitive.
  apply Cos_plus.
 astepl (Cos x[*][0][-]Sin x[*][1]).
 Step_final ([0][-]Sin x).
Qed.

Lemma Cos_HalfPi_minus : forall x : IR, Cos (Pi [/]TwoNZ[-]x) [=] Sin x.
Proof.
 intros.
 unfold cg_minus in |- *.
 astepl (Cos ( [--]x[+]Pi [/]TwoNZ)).
 eapply eq_transitive.
  apply Cos_plus_HalfPi.
 Step_final (Sin [--][--]x).
Qed.

Lemma Sin_Pi : Sin Pi [=] [0].
Proof.
 transitivity (Sin (Pi [/]TwoNZ[+]Pi [/]TwoNZ)).
  apply Sin_wd; rational.
 eapply eq_transitive_unfolded.
  apply Sin_plus_HalfPi.
 algebra.
Qed.

Lemma Cos_Pi : Cos Pi [=] [--][1].
Proof.
 transitivity (Cos (Pi [/]TwoNZ[+]Pi [/]TwoNZ)).
  apply Cos_wd; rational.
 eapply eq_transitive.
  apply Cos_plus_HalfPi.
 algebra.
Qed.

Lemma Sin_plus_Pi : forall x : IR, Sin (x[+]Pi) [=] [--] (Sin x).
Proof.
 intros.
 transitivity (Sin (x[+]Pi [/]TwoNZ[+]Pi [/]TwoNZ)).
  apply Sin_wd; rational.
 eapply eq_transitive.
  apply Sin_plus_HalfPi.
 apply Cos_plus_HalfPi.
Qed.

Lemma Cos_plus_Pi : forall x : IR, Cos (x[+]Pi) [=] [--] (Cos x).
Proof.
 intros.
 transitivity (Cos (x[+]Pi [/]TwoNZ[+]Pi [/]TwoNZ)).
  apply Cos_wd; rational.
 eapply eq_transitive.
  apply Cos_plus_HalfPi.
 apply un_op_wd_unfolded; apply Sin_plus_HalfPi.
Qed.

Lemma Tan_plus_HalfPi : forall x Hx Hx' H, Tan (x[+]Pi[/]TwoNZ) Hx[=]([--][1][/](Tan x Hx')[//]H).
Proof.
 intros x Hy Hx H.
 set (y:=x[+]Pi [/]TwoNZ) in *.
 assert (H0:Cos y[#][0]).
  destruct Hy as [[] [[] Hy]].
  apply (Hy I).
 assert (H1:Cos x[#][0]).
  clear H.
  destruct Hx as [[] [[] Hx]].
  apply (Hx I).
 rewrite (Tan_Sin_over_Cos y Hy H0).
 unfold y.
 assert (H2:([--](Sin x))[#][0]) by (now csetoid_rewrite_rev (Cos_plus_HalfPi x)).
 stepr (Cos x[/]([--](Sin x))[//]H2).
  apply div_wd.
   apply Sin_plus_HalfPi.
  apply Cos_plus_HalfPi.
 clear H0.
 rstepl (((Cos x[/][--](Sin x)[//]H2)[*](Tan x Hx))[/](Tan x Hx)[//]H).
 apply div_wd;[|apply eq_reflexive].
 rewrite (Tan_Sin_over_Cos x Hx H1). 
 rational.
Qed.

Hint Resolve Sin_plus_Pi Cos_plus_Pi: algebra.

(** Sine and cosine have period [Two Pi], tangent has period [Pi]. *)

Lemma Sin_periodic : forall x : IR, Sin (x[+]Two[*]Pi) [=] Sin x.
Proof.
 intro.
 transitivity (Sin (x[+]Pi[+]Pi)).
  apply Sin_wd; rational.
 astepl ( [--] (Sin (x[+]Pi))).
 Step_final ( [--][--] (Sin x)).
Qed.

Lemma Cos_periodic : forall x : IR, Cos (x[+]Two[*]Pi) [=] Cos x.
Proof.
 intro.
 transitivity (Cos (x[+]Pi[+]Pi)).
  apply Cos_wd; rational.
 astepl ( [--] (Cos (x[+]Pi))).
 Step_final ( [--][--] (Cos x)).
Qed.

Lemma Sin_periodic_Z : forall (x : IR) z, Sin (x[+]zring z[*](Two[*]Pi)) [=] Sin x.
Proof.
 intros x z; revert x; induction z using Zind; intros x.
   rational.
  unfold Z.succ.
  rewrite -> zring_plus.
  rstepl (Sin (x[+]zring z[*](Two[*]Pi)[+]Two[*]Pi)).
  rewrite -> Sin_periodic.
  auto.
 unfold Z.pred.
 rewrite -> zring_plus.
 rstepl (Sin (x[-]Two[*]Pi[+]zring z[*](Two[*]Pi))).
 rstepr (Sin (x[-]Two[*]Pi[+]Two[*]Pi)).
 rewrite -> Sin_periodic.
 auto.
Qed.

Lemma Cos_periodic_Z : forall (x : IR) z, Cos (x[+]zring z[*](Two[*]Pi)) [=] Cos x.
Proof.
 intros x z; revert x; induction z using Zind; intros x.
   rational.
  unfold Z.succ.
  rewrite -> zring_plus.
  rstepl (Cos (x[+]zring z[*](Two[*]Pi)[+]Two[*]Pi)).
  rewrite -> Cos_periodic.
  auto.
 unfold Z.pred.
 rewrite -> zring_plus.
 rstepl (Cos (x[-]Two[*]Pi[+]zring z[*](Two[*]Pi))).
 rstepr (Cos (x[-]Two[*]Pi[+]Two[*]Pi)).
 rewrite -> Cos_periodic.
 auto.
Qed.

Lemma Tan_periodic : forall (x : IR) Hx Hx', Tan (x[+]Pi) Hx' [=] Tan x Hx.
Proof.
 intros.
 cut (Cos x [#] [0]). intro H.
  assert (H0 : [--] (Cos x) [#] [0]). apply inv_resp_ap_zero; auto.
   transitivity (Sin x[/] _[//]H).
   2: unfold Tan, Tang in |- *; simpl in |- *; algebra.
  rstepr ( [--] (Sin x) [/] _[//]H0).
  assert (H1 : Cos (x[+]Pi) [#] [0]). astepl ( [--] (Cos x)); auto.
   astepr (Sin (x[+]Pi) [/] _[//]H1).
  unfold Tan, Tang in |- *; simpl in |- *; algebra.
 inversion_clear Hx.
 inversion_clear X0.
 simpl in |- *; auto.
Qed.

Lemma Cos_one_gt_0 : [0] [<] Cos [1].
Proof.
 apply cos_pi_seq_pos with (1%nat).
  apply less_leEq.
  apply pos_one.
 unfold pi_seq.
 rewrite -> Cos_zero.
 apply eq_imp_leEq.
 rational.
Qed.

Lemma Pi_gt_2 : Two [<] Pi.
Proof.
 unfold Pi.
 rstepl (Two [*] [1]:IR).
 apply mult_resp_less_lft.
  apply less_leEq_trans with ([1] [+] (Cos [1])).
   rstepl ([1] [+] [0]:IR).
   apply plus_resp_leEq_less.
    apply eq_imp_leEq.
    reflexivity.
   apply Cos_one_gt_0.
  apply str_leEq_seq_so_leEq_Lim.
  exists (2%nat).
  intros i iH.
  change ([1] [+] Cos [1][<=] pi_seq i).
  induction i.
   exfalso.
   auto with *.
  clear IHi.
  induction i.
   exfalso.
   auto with *.
  clear iH.
  clear IHi.
  induction i.
   unfold pi_seq.
   rewrite -> Cos_zero.
   setoid_replace ([0] [+] [1]:IR) with ([1]:IR); [|rational].
   apply eq_imp_leEq.
   reflexivity.
  apply leEq_transitive with (pi_seq (S (S i))).
   assumption.
  apply less_leEq.
  apply pi_seq_incr.
 apply pos_two.
Qed.

End Sin_And_Cos.

#[global]
Hint Resolve Cos_double Sin_double Tan_double Cos_QuarterPi Sin_QuarterPi
  Tan_QuarterPi Sin_Pi Cos_Pi Sin_HalfPi Sin_plus_HalfPi Sin_HalfPi_minus
  Cos_plus_HalfPi Cos_HalfPi_minus Sin_plus_Pi Cos_plus_Pi Sin_periodic
  Cos_periodic Tan_periodic: algebra.
