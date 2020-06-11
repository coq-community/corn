(*
Copyright © 2006 Russell O’Connor

Permission is hereby granted, free of charge, to any person obtaining a copy of
this proof and associated documentation files (the "Proof"), to deal in
the Proof without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Proof, and to permit persons to whom the Proof is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Proof.

THE PROOF IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE PROOF OR THE USE OR OTHER DEALINGS IN THE PROOF.
*)

Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import CoRN.model.totalorder.QMinMax.
Require Import CoRN.reals.fast.CRAlternatingSum.
Require Import CoRN.reals.fast.CRseries.
Require Import CoRN.reals.fast.CRpi.
Require Export CoRN.reals.fast.CRArith.
Require Import CoRN.reals.fast.CRIR.
Require Import Coq.QArith.Qpower.
Require Import CoRN.model.ordfields.Qordfield.
Require Import Coq.QArith.Qround.
Require Import CoRN.transc.Pi.
Require Import CoRN.reals.fast.ModulusDerivative.
Require Import CoRN.reals.fast.ContinuousCorrect.
Require Import CoRN.model.metric2.Qmetric.
Require Import CoRN.transc.PowerSeries.
Require Import CoRN.transc.SinCos.
Require Import Coq.NArith.Ndigits.
Require Import CoRN.reals.fast.Compress.
Require Import CoRN.reals.fast.PowerBound.
Require Import CoRN.tactics.CornTac.
Require Import MathClasses.interfaces.abstract_algebra.

Import MathClasses.theory.CoqStreams.

Set Implicit Arguments.

Local Open Scope Q_scope.
Local Open Scope uc_scope.

Opaque inj_Q CR Qmin Qmax.

(**
** Sine
Sine is defined in terms of its alternating Taylor's series.
*)
Section SinSeries.
Variable a:Q.

Definition sinSequence := (mult_Streams (everyOther (tl Qrecip_factorials)) (powers_help (a^2) a)).

Lemma Str_nth_sinSequence : forall n, (Str_nth n sinSequence == (1#P_of_succ_nat (pred (fact (1+2*n))))*a^(1+2*n)%nat)%Q.
Proof.
 intros n.
 unfold sinSequence.
 unfold mult_Streams.
 rewrite Str_nth_zipWith.
 rewrite Str_nth_everyOther.
 change (tl Qrecip_factorials) with (Str_nth_tl 1 Qrecip_factorials).
 rewrite Str_nth_plus.
 rewrite plus_comm.
 rewrite Str_nth_Qrecip_factorials.
 rewrite -> (Str_nth_powers_help_int_pow _ (cast nat Z)).
 rewrite <- Qpower_mult.
 rewrite inj_plus.
 rewrite -> Qpower_plus';[|rewrite <- inj_plus; auto with *].
 rewrite inj_mult.
 reflexivity.
Qed.

(** Sine is first defined on [[0,1]]. *)
Hypothesis Ha: 0 <= a <= 1.

Lemma square_zero_one : 0 <= a^2 <= 1.
Proof.
 split.
  replace RHS with ((1*a)*a) by simpl; ring.
  apply (sqr_nonneg Q_as_COrdField a).
 rewrite -> Qle_minus_iff.
 replace RHS with ((1-a)*(1+a)) by simpl; ring.
 destruct Ha as [Ha0 Ha1].
 apply: mult_resp_nonneg; [unfold Qminus|replace RHS with (a + - (-(1))) by simpl; ring];
   rewrite <- Qle_minus_iff; try assumption.
 apply Qle_trans with 0.
  discriminate.
 assumption.
Qed.

Lemma sinSequence_dnn : DecreasingNonNegative sinSequence.
Proof. 
 apply mult_Streams_dnn.
  apply _.
 apply powers_help_dnn.
  apply square_zero_one; assumption.
 destruct Ha; assumption.
Qed.

Lemma sinSequence_zl : Limit sinSequence 0.
Proof.
 unfold sinSequence.
 apply mult_Streams_zl with (1#1)%Qpos.
  apply _.
 apply powers_help_nbz; try apply square_zero_one; assumption.
Defined.

End SinSeries.

Definition rational_sin_small_pos (a:Q) (p: 0 <= a <= 1) : CR :=
 @InfiniteAlternatingSum _ (sinSequence_dnn p) (sinSequence_zl p).

Lemma rational_sin_small_pos_correct : forall (a:Q) Ha,
 (@rational_sin_small_pos a Ha == IRasCR (Sin (inj_Q IR a)))%CR.
Proof.
 intros a Ha.
 unfold rational_sin_small_pos.
 simpl.
 generalize (fun_series_conv_imp_conv (inj_Q IR a) (inj_Q IR a)
   (leEq_reflexive IR (inj_Q IR a)) sin_ps
     (sin_conv (inj_Q IR a) (inj_Q IR a) (leEq_reflexive IR (inj_Q IR a))
       (compact_single_iprop realline (inj_Q IR a) I)) (inj_Q IR a)
         (compact_single_prop (inj_Q IR a))
           (fun_series_inc_IR realline sin_ps sin_conv (inj_Q IR a) I)).
 intros H.
 rewrite -> InfiniteAlternatingSum_correct'.
 apply IRasCR_wd.
 unfold series_sum.
 apply Lim_seq_eq_Lim_subseq with (fun n => 2*n)%nat.
   intros; omega.
  intros n; exists (S n); omega.
 intros n.
 induction n.
  apply eq_reflexive.
 replace (2*(S n))%nat with (S (S (2*n)))%nat by omega.
 set (n':=(2*n)%nat) in *.
 simpl in *.
 rstepr (seq_part_sum (fun n0 : nat =>
   (sin_seq n0[/]nring (R:=IR) (fact n0)[//]nring_fac_ap_zero IR n0)[*]
     nexp IR n0 (inj_Q IR a[-][0])) n'[+](
       (sin_seq n'[/]nring (R:=IR) (fact n')[//]nring_fac_ap_zero IR n')[*]
         nexp IR n' (inj_Q IR a[-][0])[+] (sin_seq (S n')[/]nring (R:=IR) (fact n' + n' * fact n')[//]
           nring_fac_ap_zero IR (S n'))[*] (nexp IR n' (inj_Q IR a[-][0])[*](inj_Q IR a[-][0])))).
 apply bin_op_wd_unfolded.
  assumption.
 rstepl ([0][+]inj_Q IR ((- (1)) ^ n * Str_nth n (sinSequence a))).
 unfold sin_seq.
 apply bin_op_wd_unfolded.
  destruct (even_or_odd_plus n') as [m [Hm|Hm]]; simpl.
   rational.
  elim (not_even_and_odd n').
   apply (even_mult_l 2 n).
   repeat constructor.
  rewrite Hm.
  constructor.
  replace (m + m)%nat with (2*m)%nat by omega.
  apply (even_mult_l 2 m).
  repeat constructor.
 destruct (even_or_odd_plus (S n')) as [m [Hm|Hm]]; simpl.
  elim (not_even_and_odd (S n')).
   rewrite Hm.
   replace (m + m)%nat with (2*m)%nat by omega.
   apply (even_mult_l 2 m).
   repeat constructor.
  constructor.
  apply (even_mult_l 2 n).
  repeat constructor.
 inversion Hm.
 unfold n' in H1.
 replace m with n by omega.
 clear Hm H1.
 stepl ((inj_Q IR ((-(1))^n))[*](inj_Q IR (Str_nth n (sinSequence a)))); [| now
   (apply eq_symmetric; apply inj_Q_mult)].
 change (inj_Q IR ((- (1)) ^ n)[*]inj_Q IR (Str_nth n (sinSequence a))[=]
   (nexp IR n [--][1][/]nring (R:=IR) (fact (S n'))[//]nring_fac_ap_zero IR (S n'))[*]
     (nexp IR (S n') (inj_Q IR a[-][0]))).
 rstepr ((nexp IR n [--][1][*](nexp IR (S n') (inj_Q IR a[-][0])[/]nring (R:=IR) (fact (S n'))[//]
   nring_fac_ap_zero IR (S n')))).
 apply mult_wd.
  stepr ((inj_Q IR (-(1)))[^]n).
   apply inj_Q_power.
  apply nexp_wd.
  stepr ([--](inj_Q IR 1)).
   apply inj_Q_inv.
  apply un_op_wd_unfolded.
  rstepr (nring 1:IR).
  apply (inj_Q_nring IR 1).
 stepr (inj_Q IR ((1/P_of_succ_nat (pred (fact (1+2*n))))*a^(1+2*n)%nat)).
  apply inj_Q_wd.
  simpl.
  rewrite -> Str_nth_sinSequence.
  rewrite -> Qmake_Qdiv.
  reflexivity.
 rstepr ((nring 1[/]nring (R:=IR) (fact (S n'))[//]
   nring_fac_ap_zero IR (S n'))[*](nexp IR (S n') (inj_Q IR a[-][0]))).
 change (1+2*n)%nat with (S n').
 stepr ((inj_Q IR (1 / Zpos (P_of_succ_nat (pred (fact (S n')))))[*](inj_Q IR (a^S n')))).
  apply inj_Q_mult.
 apply mult_wd.
  rewrite <- POS_anti_convert.
  assert (X:inj_Q IR (inject_Z (Z_of_nat (S (pred (fact (S n'))))))[#][0]).
   stepr (inj_Q IR [0]).
    assert (@cs_ap Q_as_CSetoid (inject_Z (Z_of_nat (S (pred (fact (S n')))))) 0).
     discriminate.
    destruct (ap_imp_less _ _ _ X).
     apply less_imp_ap.
     apply inj_Q_less.
     assumption.
    apply Greater_imp_ap.
    apply inj_Q_less.
    assumption.
   apply (inj_Q_nring IR 0).
  stepr ((inj_Q IR 1)[/](inj_Q IR (inject_Z (Z_of_nat (S (pred (fact (S n')))))))[//]X).
   apply inj_Q_div.
  apply div_wd.
   apply (inj_Q_nring IR 1).
  stepl (inj_Q IR (nring (fact (S n')))).
   apply inj_Q_nring.
  assert (Y:=lt_O_fact (S n')).
  apply inj_Q_wd.
  stepr ((fact (S n')):Q).
   clear - n'.
   induction (fact (S n')).
    simpl; reflexivity.
   rewrite inj_S.
   unfold Z.succ.
   simpl in *.
   rewrite -> IHn0.
   rewrite -> injz_plus.
   reflexivity.
  destruct (fact (S n')).
   elimtype False; auto with *.
  simpl; reflexivity.
 stepr ((inj_Q IR a)[^](S n')).
  apply inj_Q_power.
 change (inj_Q IR a[^]S n'[=](inj_Q IR a[-][0])[^]S n').
 apply nexp_wd.
 rational.
Qed.

(** Sine's range can then be extended to [[0,3^n]] by [n] applications
of the identity [sin(x) = 3*sin(x/3) - 4*(sin(x/3))^3]. *)
Section Sin_Poly.

Definition sin_poly_fun (x:Q) :Q := x*(3 - 4*x*x).

Global Instance: Proper ((=) ==> (=)) sin_poly_fun.
Proof. unfold sin_poly_fun. solve_proper. Qed.

Lemma sin_poly_fun_correct : forall (q:Q),
 inj_Q IR (sin_poly_fun q)[=]Three[*]inj_Q IR q[-]Four[*](inj_Q IR q[^]3).
Proof.
 intros q.
 unfold sin_poly_fun.
 stepr (inj_Q IR (3*q-4*q^3)).
  apply inj_Q_wd.
  simpl; ring.
  rewrite inj_Q_minus.
 apply cg_minus_wd.
  stepr (inj_Q IR Three[*]inj_Q IR q).
   apply inj_Q_mult.
  apply mult_wdl.
  apply (inj_Q_nring IR 3).
 stepr (inj_Q IR Four[*]inj_Q IR (q^3)).
  apply inj_Q_mult.
 apply mult_wd.
  apply (inj_Q_nring IR 4).
 apply (inj_Q_power IR q 3).
Qed.

Definition sin_poly_modulus (e:Qpos) := Qpos2QposInf ((1#9)*e).

Let X:((-(1))<1)%Q.
Proof.
 constructor.
Qed.

Let D : Derivative (clcr (inj_Q IR (-(1))) (inj_Q IR (1:Q))) (inj_Q_less _ _ _ X) ((Three:IR){**}FId{-}(Four:IR){**}FId{^}3)
 ((Three:IR){**}[-C-]([1]:IR){-}(Four:IR){**}((nring 3){**}([-C-][1]{*}FId{^}2))).
Proof.
 apply Derivative_minus.
  apply Derivative_scal.
  apply Derivative_id.
 apply Derivative_scal.
 apply Derivative_nth.
 apply Derivative_id.
Qed.

Lemma sin_poly_prf : is_UniformlyContinuousFunction (fun x => sin_poly_fun (QboundAbs (1#1) x)) sin_poly_modulus.
Proof.
 apply (fun a => is_UniformlyContinuousD_Q (Some (-(1))%Q) (Some (1:Q)) X _ _ D sin_poly_fun a (9#1)).
  simpl; intros q _ _.
  apply sin_poly_fun_correct.
 simpl; intros x' _ [Hx0 Hx1].
 set (x:=(inj_Q IR x')) in *.
 stepr (Nine:IR); [| now (apply eq_symmetric; apply (inj_Q_nring IR 9))].
 stepl (ABSIR (Three[-]Twelve[*]x[*]x)); [| now (apply AbsIR_wd; rational)].
 apply AbsSmall_imp_AbsIR.
 split.
  apply shift_zero_leEq_minus'.
  rstepr (Twelve[*]((nring 1)[-]x)[*](x[-][--](nring 1))).
  repeat apply mult_resp_nonneg.
    apply (nring_nonneg IR 12).
   apply shift_zero_leEq_minus.
   stepr (inj_Q IR (nring 1)); [| now apply inj_Q_nring].
   assumption.
  apply shift_zero_leEq_minus.
  stepl (inj_Q IR (-(1))).
   assumption.
  stepr ([--](inj_Q IR 1)).
   apply inj_Q_inv.
  apply un_op_wd_unfolded.
  apply (inj_Q_nring IR 1).
 rstepr (Nine[-][0]:IR).
 apply minus_resp_leEq_both.
  apply nring_leEq.
  omega.
 rstepr (Twelve[*]x[^]2).
 apply mult_resp_nonneg.
  apply (nring_leEq  IR 0 12).
  omega.
 apply sqr_nonneg.
Qed.

Definition sin_poly_uc : Q_as_MetricSpace --> Q_as_MetricSpace :=
Build_UniformlyContinuousFunction sin_poly_prf.

Definition sin_poly : CR --> CR := uc_compose compress (Cmap QPrelengthSpace sin_poly_uc).

Lemma sin_poly_correct : forall x, AbsSmall (inj_Q IR (1)) x -> (IRasCR (Three[*]x[-]Four[*]x[^]3)==sin_poly (IRasCR x))%CR.
Proof.
 intros x Hx.
 assert (Y:Continuous (clcr (inj_Q IR (-(1))) (inj_Q IR (1:Q))) ((Three:IR){**}FId{-}(Four:IR){**}FId{^}3)).
  eapply Derivative_imp_Continuous.
  apply D.
 apply: (ContinuousCorrect (I:=(clcr (inj_Q IR (-(1))) (inj_Q IR (1:Q)))) (inj_Q_less _ _ _ X) Y);
   [|repeat constructor|].
  intros q Hq Hq0.
  transitivity (IRasCR (inj_Q IR (sin_poly_fun q)));[|apply IRasCR_wd; apply sin_poly_fun_correct].
  simpl.
  change (' q)%CR with (Cunit_fun _ q).
  rewrite -> compress_fun_correct.
  rewrite -> Cmap_fun_correct.
  rewrite -> MonadLaw3.
  rewrite -> IR_inj_Q_as_CR.
  rewrite -> CReq_Qeq.
  simpl.
  unfold sin_poly_fun.
  setoid_replace (Qmax (- (1)) (Qmin 1 q)) with q.
   reflexivity.
  setoid_replace (Qmin 1 q) with q.
   rewrite <- Qle_max_r.
   apply leEq_inj_Q with IR.
   destruct Hq0; assumption.
  rewrite <- Qle_min_r.
  apply leEq_inj_Q with IR.
  destruct Hq0; assumption.
 destruct Hx; split;[stepl [--](inj_Q IR (1:Q)); [| now apply eq_symmetric; apply inj_Q_inv] |];assumption.
Qed.

Lemma Sin_triple_angle : forall x, (Sin(Three[*]x)[=]Three[*]Sin x[-]Four[*]Sin x[^]3).
Proof.
 intros x.
 assert (H:Three[*]x[=]x[+]x[+]x) by rational.
 csetoid_rewrite H.
 csetoid_rewrite (Sin_plus (x[+]x) x).
 csetoid_rewrite (Sin_plus x x).
 csetoid_rewrite (Cos_plus x x).
 set (sx:=Sin x).
 set (cx:=Cos x).
 rstepl ((cx[^]2)[*](Three[*]sx)[-]sx[^]3).
 unfold cg_minus.
 csetoid_replace (cx[^]2) ([1][-]sx[^]2).
  rational.
 apply cg_inv_unique_2.
 rstepl ((cx[^]2[+]sx[^]2)[-][1]).
 apply x_minus_x.
 apply FFT.
Qed.

Lemma shrink_by_three : forall n a, 0 <= a <= (3^(S n))%Z -> 0 <= a/3 <= (3^n)%Z.
Proof.
 intros n a [H0 H1].
 split.
  apply: mult_resp_nonneg.
   assumption.
  discriminate.
 apply Qmult_lt_0_le_reg_r with 3.
  constructor.
 rewrite -> Zpower_Qpower; auto with *.
 rewrite (inj_S n) in H1.
 replace RHS with (3%positive^n*3^1) by simpl; ring.
 rewrite <- Qpower_plus;[|discriminate].
 replace LHS with a by (simpl; field; discriminate).
 rewrite -> Zpower_Qpower in H1; auto with *.
Qed.

Fixpoint rational_sin_pos_bounded (n:nat) (a:Q) : 0 <= a <= (3^n)%Z -> CR :=
match n return 0 <= a <= (3^n)%Z -> CR with
| O => @rational_sin_small_pos a
| S n' =>
  match (Qlt_le_dec_fast 1 a) with
  | left _ => fun H => sin_poly (rational_sin_pos_bounded n' (shrink_by_three n' H))
  | right H' => fun H => rational_sin_small_pos (conj (proj1 H) H')
  end
end.

Lemma rational_sin_pos_bounded_correct_aux a :
  sin_poly (IRasCR (Sin (inj_Q IR (a / 3))))[=]IRasCR (Sin (inj_Q IR a)).
Proof.
 rewrite <- sin_poly_correct; [|apply AbsIR_imp_AbsSmall;
   (stepr (nring 1:IR); [| now apply eq_symmetric; apply (inj_Q_nring IR 1)]); rstepr ([1]:IR);
     apply AbsIR_Sin_leEq_One].
 apply IRasCR_wd.
 stepl (Sin (inj_Q IR (a/3*3))).
  apply Sin_wd.
  apply inj_Q_wd.
  simpl; field; discriminate.
 generalize (a/3).
 intros b; clear -b.
 stepr (Sin (Three[*](inj_Q IR b))).
  apply Sin_wd.
  stepr ((inj_Q IR b)[*](inj_Q IR (3:Q))).
   apply inj_Q_mult.
  csetoid_replace (inj_Q IR (3:Q)) (Three:IR).
   rational.
  apply (inj_Q_nring IR 3).
 apply Sin_triple_angle.
Qed.

Lemma rational_sin_pos_bounded_correct :  forall n (a:Q) Ha,
 (@rational_sin_pos_bounded n a Ha == IRasCR (Sin (inj_Q IR a)))%CR.
Proof.
 induction n.
  apply rational_sin_small_pos_correct.
 intros a Ha.
 unfold rational_sin_pos_bounded; fold rational_sin_pos_bounded.
 destruct (Qlt_le_dec_fast 1 a);[|apply rational_sin_small_pos_correct].
 rewrite -> IHn.
 apply rational_sin_pos_bounded_correct_aux.
Qed.
End Sin_Poly.

(** Therefore sin works on all nonnegative numbers. *)
Definition rational_sin_pos (a:Q) (Ha:0 <= a) : CR :=
 @rational_sin_pos_bounded _ a (conj Ha (power3bound a)).

Lemma rational_sin_pos_correct : forall (a:Q) Ha,
 (@rational_sin_pos a Ha == IRasCR (Sin (inj_Q IR a)))%CR.
Proof.
 intros; apply rational_sin_pos_bounded_correct.
Qed.

(** By symmetry sin is extented to its entire range. *)
Definition rational_sin (a:Q) : CR :=
match (Qle_total 0 a) with
| left H => rational_sin_pos H
| right H => (-rational_sin_pos (Qopp_le_compat _ _ H))%CR
end.

Lemma rational_sin_correct_aux (a : Q) :
 (- IRasCR (Sin (inj_Q IR (- a)%Q)))%CR[=]IRasCR (Sin (inj_Q IR a)).
Proof.
 rewrite <- IR_opp_as_CR.
 apply IRasCR_wd.
 csetoid_rewrite_rev (Sin_inv (inj_Q IR (-a))).
 apply Sin_wd.
 csetoid_rewrite_rev (inj_Q_inv IR (-a)).
 apply inj_Q_wd.
 simpl.
 ring.
Qed.

Lemma rational_sin_correct : forall (a:Q),
 (@rational_sin a == IRasCR (Sin (inj_Q IR a)))%CR.
Proof.
 intros a.
 unfold rational_sin.
 destruct (Qle_total 0 a).
  apply rational_sin_pos_correct.
 rewrite -> rational_sin_pos_correct.
 apply rational_sin_correct_aux.
Qed.

Instance: Proper ((=) ==> (=)) rational_sin.
Proof.
 intros ? ? E.
 rewrite ?rational_sin_correct.
 now apply IRasCR_wd, Sin_wd, inj_Q_wd.
Qed.

Lemma rational_sin_poly (a : Q) :
  sin_poly (rational_sin (a / 3)) = rational_sin a.
Proof.
 rewrite ?rational_sin_correct.
 apply rational_sin_pos_bounded_correct_aux.
Qed.

Lemma rational_sin_opp (a : Q) :
  (-rational_sin (-a) = rational_sin a)%CR.
Proof.
  rewrite ?rational_sin_correct.
  now apply rational_sin_correct_aux.
Qed.

(** Sine is uniformly continuous everywhere. *)
Definition sin_uc_prf : is_UniformlyContinuousFunction rational_sin Qpos2QposInf.
Proof.
 apply (is_UniformlyContinuousFunction_wd) with (fun x => rational_sin x) (Qscale_modulus (1#1)).
   reflexivity.
  intros x.
  simpl.
  autorewrite with QposElim.
  change (/1) with 1.
  replace RHS with (proj1_sig x) by simpl; ring.
  apply Qle_refl.
 apply (is_UniformlyContinuousD None None I Sine Cosine (Derivative_Sin I) rational_sin).
  intros q [] _.
  apply rational_sin_correct.
 intros x [] _.
 stepr ([1]:IR).
  apply: AbsIR_Cos_leEq_One.
 rstepl (nring 1:IR).
 apply eq_symmetric.
 apply (inj_Q_nring IR 1).
Qed.

Definition sin_uc : Q_as_MetricSpace --> CR :=
Build_UniformlyContinuousFunction sin_uc_prf.

Definition sin_slow : CR --> CR := Cbind QPrelengthSpace sin_uc.

Lemma sin_slow_correct : forall x,
 (IRasCR (Sin x) == sin_slow (IRasCR x))%CR.
Proof.
 intros x.
 apply: (ContinuousCorrect (I:proper realline)); [apply Continuous_Sin | | constructor].
 intros q [] _.
 transitivity (rational_sin q);[|apply rational_sin_correct].
 unfold sin_slow.
 rewrite -> (Cbind_fun_correct QPrelengthSpace sin_uc).
 apply: BindLaw1.
Qed.

Definition sin (x:CR) := sin_slow (x - (compress (scale (2*Qceiling (approximate (x*(CRinv_pos (6#1) (scale 2 CRpi))) (Qpos2QposInf (1#2)) -(1#2))) CRpi)))%CR.

Lemma sin_correct : forall x,
  (IRasCR (Sin x) == sin (IRasCR x))%CR.
Proof.
 intros x.
 unfold sin.
 generalize (Qceiling (approximate (IRasCR x * CRinv_pos (6 # 1) (scale 2 CRpi))
   (Qpos2QposInf (1 # 2)) - (1 # 2)))%CR.
 intros z.
 rewrite -> compress_correct.
 rewrite <- CRpi_correct, <- CRmult_scale, <- IR_inj_Q_as_CR, <- IR_mult_as_CR,
   <- IR_minus_as_CR, <- sin_slow_correct.
 apply IRasCR_wd.
 rewrite -> inj_Q_mult.
 change (2:Q) with (@nring Q_as_CRing 2).
 rewrite -> inj_Q_nring.
 rstepr (Sin (x[+]([--](inj_Q IR z))[*](Two[*]Pi))).
 setoid_replace (inj_Q IR z) with (zring z:IR).
  rewrite <- zring_inv.
  symmetry; apply Sin_periodic_Z.
 rewrite <- inj_Q_zring.
 apply inj_Q_wd.
 symmetry; apply zring_Q.
Qed.

(* begin hide *)
Hint Rewrite sin_correct : IRtoCR.
(* end hide *)
