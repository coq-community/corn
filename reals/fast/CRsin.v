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

Require Import QMinMax.
Require Import CRAlternatingSum.
Require Export CRArith.
Require Import CRIR.
Require Import Qpower.
Require Import Qordfield.
Require Import ModulusDerivative.
Require Import ContinuousCorrect.
Require Import Qmetric.
Require Import PowerSeries.
Require Import SinCos.
Require Import Ndigits.
Require Import Compress.
Require Import PowerBound.
Require Import CornTac.

Set Implicit Arguments.

Open Local Scope Q_scope.
Open Local Scope uc_scope.

Opaque inj_Q CR Qmin Qmax.

Section SinSeries.
Variable a:Q.

Definition sinSequence := (mult_Streams (everyOther (tl recip_factorials)) (powers_help (a^2) a)).

Lemma Str_nth_sinSequence : forall n, (Str_nth n sinSequence == (1#P_of_succ_nat (pred (fac (1+2*n))))*a^(1+2*n)%nat)%Q.
Proof.
intros n.
unfold sinSequence.
unfold mult_Streams.
rewrite Str_nth_zipWith.
rewrite Str_nth_everyOther.
change (tl recip_factorials) with (Str_nth_tl 1 recip_factorials).
rewrite Str_nth_plus.
rewrite plus_comm.
rewrite Str_nth_recip_factorials.
rewrite Str_nth_powers_help.
rewrite <- Qpower_mult.
rewrite inj_plus.
rewrite Qpower_plus'.
 rewrite <- inj_plus.
 auto with *.
rewrite inj_mult.
reflexivity.
Qed.

Hypothesis Ha: 0 <= a <= 1.

Lemma square_zero_one : 0 <= a^2 <= 1.
Proof.
split.
 replace RHS with ((1*a)*a) by ring.
 rapply (sqr_nonneg _ a).
rewrite Qle_minus_iff.
replace RHS with ((1-a)*(1+a)) by ring.
destruct Ha as [Ha0 Ha1].
rsapply mult_resp_nonneg;
 [unfold Qminus|replace RHS with (a + - (-(1))) by ring];
 rewrite <- Qle_minus_iff;
 try assumption.
apply Qle_trans with 0.
 discriminate.
assumption.
Qed.

Lemma sinSequence_dnn : DecreasingNonNegative sinSequence.
Proof.
rapply mult_Streams_dnn.
 apply everyOther_dnn.
 apply dnn_tl.
 apply recip_factorials_dnn.
apply powers_help_dnn.
 apply square_zero_one; assumption.
destruct Ha; assumption.
Qed.

Lemma sinSequence_zl : Limit sinSequence 0.
Proof.
unfold sinSequence.
apply mult_Streams_zl with (1#1)%Qpos.
 apply everyOther_zl.
 rapply Limit_tl.
 apply recip_factorials_zl.
apply powers_help_nbz; try
 apply square_zero_one; assumption.
Defined.

End SinSeries.

Definition rational_sin_small_pos (a:Q) (p: 0 <= a <= 1) : CR := 
 InfiniteAlternatingSum (sinSequence_dnn p) (sinSequence_zl p).

Lemma rational_sin_small_pos_correct : forall (a:Q) Ha,
 (@rational_sin_small_pos a Ha == IRasCR (Sin (inj_Q IR a)))%CR.
Proof.
intros a Ha.
unfold rational_sin_small_pos.
simpl.
generalize (fun_series_conv_imp_conv (inj_Q IR a) (inj_Q IR a)
         (leEq_reflexive IR (inj_Q IR a)) sin_ps
         (sin_conv (inj_Q IR a) (inj_Q IR a) (leEq_reflexive IR (inj_Q IR a))
            (compact_single_iprop realline (inj_Q IR a) CI)) (inj_Q IR a)
         (compact_single_prop (inj_Q IR a))
         (fun_series_inc_IR realline sin_ps sin_conv (inj_Q IR a) CI)).
intros H.
rewrite InfiniteAlternatingSum_correct'.
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
rstepr (seq_part_sum
  (fun n0 : nat =>
   (sin_seq n0[/]nring (R:=IR) (fac n0)[//]nring_fac_ap_zero IR n0)[*]
   nexp IR n0 (inj_Q IR a[-]Zero)) n'[+](
(sin_seq n'[/]nring (R:=IR) (fac n')[//]nring_fac_ap_zero IR n')[*]
nexp IR n' (inj_Q IR a[-]Zero)[+]
(sin_seq (S n')[/]nring (R:=IR) (fac n' + n' * fac n')[//]
 nring_fac_ap_zero IR (S n'))[*]
(nexp IR n' (inj_Q IR a[-]Zero)[*](inj_Q IR a[-]Zero)))).
apply bin_op_wd_unfolded.
 assumption.
rstepl (Zero[+]inj_Q IR ((- (1)) ^ n * Str_nth n (sinSequence a))).
unfold sin_seq.
apply bin_op_wd_unfolded.
 destruct (even_or_odd_plus n') as [m [Hm|Hm]]; simpl.
   rational.
 elim (not_even_and_odd n').
  rapply (even_mult_l 2 n).
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
  rapply (even_mult_l 2 m).
  repeat constructor.
 constructor.
 apply (even_mult_l 2 n).
 repeat constructor.
inversion Hm.
unfold n' in H1.
replace m with n by omega.
clear Hm H1.
stepl ((inj_Q IR ((-(1))^n))[*](inj_Q IR (Str_nth n (sinSequence a)))) by
 (apply eq_symmetric; apply inj_Q_mult).
change (inj_Q IR ((- (1)) ^ n)[*]inj_Q IR (Str_nth n (sinSequence a))[=]
(nexp IR n [--]One[/]nring (R:=IR) (fac (S n'))[//]nring_fac_ap_zero IR (S n'))[*]
(nexp IR (S n') (inj_Q IR a[-]Zero))).
rstepr ((nexp IR n [--]One[*](nexp IR (S n') (inj_Q IR a[-]Zero)[/]nring (R:=IR) (fac (S n'))[//]
 nring_fac_ap_zero IR (S n')))).
apply mult_wd.
 stepr ((inj_Q IR (-(1)))[^]n).
  apply inj_Q_power.
 rapply nexp_wd.
 stepr ([--](inj_Q IR 1)).
  apply inj_Q_inv.
 apply un_op_wd_unfolded.
 rstepr (nring 1:IR).
 apply (inj_Q_nring IR 1).
stepr (inj_Q IR ((1/P_of_succ_nat (pred (fac (1+2*n))))*a^(1+2*n)%nat)).
 apply inj_Q_wd.
 simpl.
 rewrite Str_nth_sinSequence.
 rewrite Qmake_Qdiv.
 reflexivity.
rstepr ((nring 1[/]nring (R:=IR) (fac (S n'))[//]
 nring_fac_ap_zero IR (S n'))[*](nexp IR (S n') (inj_Q IR a[-]Zero))).
change (1+2*n)%nat with (S n').
stepr ((inj_Q IR (1 / P_of_succ_nat (pred (fac (S n'))))[*](inj_Q IR (a^S n')))).
 apply inj_Q_mult.
apply mult_wd.
 rewrite <- POS_anti_convert.
 assert (X:inj_Q IR (inject_Z (Z_of_nat (S (pred (fac (S n'))))))[#]Zero).
  stepr (inj_Q IR Zero).
   assert (inject_Z (Z_of_nat (S (pred (fac (S n')))))[#]Zero).
    discriminate.
   destruct (ap_imp_less _ _ _ X).
    apply less_imp_ap.
    apply inj_Q_less.
    assumption.
   apply Greater_imp_ap.
   apply inj_Q_less.
   assumption.
  apply (inj_Q_nring IR 0).
 stepr ((inj_Q IR 1)[/](inj_Q IR (inject_Z (Z_of_nat (S (pred (fac (S n')))))))[//]X).
  apply inj_Q_div.
 apply div_wd.
  apply (inj_Q_nring IR 1).
 stepl (inj_Q IR (nring (fac (S n')))).
  apply inj_Q_nring.
 assert (Y:=nat_fac_gtzero (S n')).
 apply inj_Q_wd.
 stepr ((fac (S n')):Q).
  clear - n'.
  induction (fac (S n')).
   simpl; reflexivity.
  rewrite inj_S.
  unfold Zsucc.
  simpl in *.
  rewrite IHn0.
  rewrite injz_plus.
  reflexivity.
 destruct (fac (S n')).
  elimtype False; auto with *.
 simpl; reflexivity.
stepr ((inj_Q IR a)[^](S n')).
 apply inj_Q_power.
change (inj_Q IR a[^]S n'[=](inj_Q IR a[-]Zero)[^]S n').
apply nexp_wd.
rational.
Qed.

Section Sin_Poly.

Definition sin_poly_fun (x:Q) :Q := x*(3 - 4*x*x).

Lemma sin_poly_fun_correct : forall (q:Q),
 inj_Q IR (sin_poly_fun q)[=]Three[*]inj_Q IR q[-]Four[*](inj_Q IR q[^]3).
Proof.
intros q.
unfold sin_poly_fun.
stepr (inj_Q IR (3*q-4*q^3)).
 apply inj_Q_wd.
 simpl; ring.
stepr (inj_Q IR (Three[*]q)[-]inj_Q IR (Four[*]q ^ 3))%Q.
 apply inj_Q_minus.
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

Definition sin_poly_modulus (e:Qpos) := Qpos2QposInf (e/(9#1)).

Let X:((-(1))<1)%Q.
constructor.
Qed.

Let D : Derivative (clcr (inj_Q IR (-(1))) (inj_Q IR (1:Q))) (inj_Q_less _ _ _ X) ((Three:IR){**}FId{-}(Four:IR){**}FId{^}3)
 ((Three:IR){**}[-C-](One:IR){-}(Four:IR){**}((nring 3){**}([-C-]One{*}FId{^}2))).
apply Derivative_minus.
 apply Derivative_scal.
 apply Derivative_id.
apply Derivative_scal.
apply Derivative_nth.
apply Derivative_id.
Qed.

Lemma sin_poly_prf : is_UniformlyContinuousFunction (fun x => sin_poly_fun (QboundAbs (1#1) x)) sin_poly_modulus.
Proof.
rapply (is_UniformlyContinuousD_Q (Some (-(1))%Q) (Some (1:Q)) X _ _ D sin_poly_fun).
 simpl; intros q _ _.
 rapply sin_poly_fun_correct.
simpl; intros x _ [Hx0 Hx1].
stepr (Nine:IR) by (apply eq_symmetric; apply (inj_Q_nring IR 9)).
stepl (ABSIR (Three[-]Twelve[*]x[*]x)) by (apply AbsIR_wd; rational).
apply AbsSmall_imp_AbsIR.
split.
 apply shift_zero_leEq_minus'.
 rstepr (Twelve[*]((nring 1)[-]x)[*](x[-][--](nring 1))).
 repeat apply mult_resp_nonneg.
   apply (nring_nonneg IR 12).
  apply shift_zero_leEq_minus.
  stepr (inj_Q IR (nring 1)) by apply inj_Q_nring.
  assumption.
 apply shift_zero_leEq_minus.
 stepl (inj_Q IR (-(1))).
  assumption.
 stepr ([--](inj_Q IR 1)).
  apply inj_Q_inv.
 rapply un_op_wd_unfolded.
 apply (inj_Q_nring IR 1).
 rstepr (Nine[-]Zero:IR).
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
rapply (ContinuousCorrect (I:=(clcr (inj_Q IR (-(1))) (inj_Q IR (1:Q)))) (inj_Q_less _ _ _ X) Y);
 [|repeat constructor|].
 intros q Hq Hq0.
 transitivity (IRasCR (inj_Q IR (sin_poly_fun q)));[|apply IRasCR_wd; rapply sin_poly_fun_correct].
 simpl.
 change (' q)%CR with (Cunit_fun _ q).
 rewrite compress_fun_correct.
 rewrite MonadLaw3.
 rewrite IR_inj_Q_as_CR.
 rewrite CReq_Qeq.
 simpl.
 unfold sin_poly_fun.
 setoid_replace (Qmax (- (1 # 1)%Qpos) (Qmin (1 # 1)%Qpos q)) with q.
  reflexivity.
 setoid_replace (Qmin (1 # 1)%Qpos q) with q.
  rewrite <- Qle_max_r.
  apply leEq_inj_Q with IR.
  destruct Hq0; assumption.
 rewrite <- Qle_min_r.
 apply leEq_inj_Q with IR.
 destruct Hq0; assumption.
destruct Hx; split;[stepl [--](inj_Q IR (1:Q)) by apply eq_symmetric; apply inj_Q_inv|];assumption.
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
csetoid_replace (cx[^]2) (One[-]sx[^]2).
 rational.
apply cg_inv_unique_2.
rstepl ((cx[^]2[+]sx[^]2)[-]One).
apply x_minus_x.
rapply FFT.
Qed.

Lemma shrink_by_three : forall n a, 0 <= a <= (3^(S n))%Z -> 0 <= a/3 <= (3^n)%Z.
Proof.
intros n a [H0 H1].
split.
 rapply mult_resp_nonneg.
  assumption.
 discriminate.
apply Qmult_lt_0_le_reg_r with 3.
 constructor.
rewrite Zpower_Qpower.
 auto with *.
rewrite (inj_S n) in H1.
replace RHS with (3%positive^n*3^1) by ring.
rewrite <- Qpower_plus.
 discriminate.
replace LHS with a by (field; discriminate).
rewrite Zpower_Qpower in H1.
 assumption.
auto with *.
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

Lemma rational_sin_pos_bounded_correct :  forall n (a:Q) Ha,
 (@rational_sin_pos_bounded n a Ha == IRasCR (Sin (inj_Q IR a)))%CR.
Proof.
induction n.
 rapply rational_sin_small_pos_correct.
intros a Ha.
unfold rational_sin_pos_bounded; fold rational_sin_pos_bounded.
destruct (Qlt_le_dec_fast 1 a);[|rapply rational_sin_small_pos_correct].
rewrite IHn.
rewrite <- sin_poly_correct.
 apply AbsIR_imp_AbsSmall.
 stepr (nring 1:IR) by (apply eq_symmetric; apply (inj_Q_nring IR 1)).
 rstepr (One:IR).
 apply AbsIR_Sin_leEq_One.
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

End Sin_Poly.

Definition rational_sin_pos (a:Q) (Ha:0 <= a) : CR :=
 @rational_sin_pos_bounded _ a (conj Ha (power3bound a)).

Lemma rational_sin_pos_correct : forall (a:Q) Ha,
 (@rational_sin_pos a Ha == IRasCR (Sin (inj_Q IR a)))%CR.
Proof.
intros; rapply rational_sin_pos_bounded_correct.
Qed.

Definition rational_sin (a:Q) : CR :=
match (Qle_total 0 a) with
| left H => rational_sin_pos H
| right H => (-rational_sin_pos (Qopp_le_compat _ _ H))%CR
end.

Lemma rational_sin_correct : forall (a:Q),
 (@rational_sin a == IRasCR (Sin (inj_Q IR a)))%CR.
Proof.
intros a.
unfold rational_sin.
destruct (Qle_total 0 a).
 apply rational_sin_pos_correct.
rewrite rational_sin_pos_correct.
rewrite <- IR_opp_as_CR.
apply IRasCR_wd.
csetoid_rewrite_rev (Sin_inv (inj_Q IR (-a))).
apply Sin_wd.
csetoid_rewrite_rev (inj_Q_inv IR (-a)).
apply inj_Q_wd.
simpl.
ring.
Qed.

Definition sin_uc_prf : is_UniformlyContinuousFunction rational_sin Qpos2QposInf.
Proof.
apply (is_UniformlyContinuousFunction_wd) with (fun x => rational_sin x) (modulusD (1#1)).
  reflexivity.
 intros x.
 simpl.
 autorewrite with QposElim.
 change (/1) with 1.
 replace RHS with (x:Q) by ring.
 apply Qle_refl.
rapply (is_UniformlyContinuousD None None I Sine Cosine (Derivative_Sin CI) rational_sin).
 intros q [] _.
 rapply rational_sin_correct.
intros x [] _.
stepr (One:IR).
 rapply AbsIR_Cos_leEq_One.
rstepl (nring 1:IR).
apply eq_symmetric.
rapply (inj_Q_nring IR 1).
Qed.

Definition sin_uc : Q_as_MetricSpace --> CR := 
Build_UniformlyContinuousFunction sin_uc_prf.

Definition sin : CR --> CR := Cbind QPrelengthSpace sin_uc.

Lemma sin_correct : forall x,
 (IRasCR (Sin x) == sin (IRasCR x))%CR.
Proof.
intros x.
rapply (ContinuousCorrect (CI:proper realline));
 [apply Continuous_Sin | | constructor].
intros q [] _.
transitivity (rational_sin q);[|rapply rational_sin_correct].
rapply BindLaw1.
Qed.

Hint Rewrite sin_correct : IRtoCR.