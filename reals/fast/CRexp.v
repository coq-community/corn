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

Require Import CRAlternatingSum.
Require Export CRArith.
Require Import CRIR.
Require Import iso_CReals.
Require Import Qpower.
Require Import COrdFields2.
Require Import Qordfield.
Require Import PowerSeries.
Require Import CornTac.

Set Implicit Arguments.

Opaque CR.

Open Local Scope Q_scope.

Section ExpSeries.
Variable a:Q.

Definition expSequence := mult_Streams recip_factorials (powers a).

Lemma Str_nth_expSequence : forall n, (Str_nth n expSequence == (1#P_of_succ_nat (pred (fac n)))*a^n)%Q.
Proof.
intros n.
unfold expSequence.
unfold mult_Streams.
rewrite Str_nth_zipWith.
rewrite Str_nth_powers.
rewrite Str_nth_recip_factorials.
reflexivity.
Qed.

Hypothesis Ha: 0 <= a <= 1.

Lemma expSequence_dnn : DecreasingNonNegative expSequence.
Proof.
rapply mult_Streams_dnn.
apply recip_factorials_dnn.
apply powers_dnn.
assumption.
Qed.

Lemma expSequence_zl : Limit expSequence 0.
Proof.
rapply mult_Streams_zl.
apply recip_factorials_zl.
apply powers_nbz.
assumption.
Defined.

End ExpSeries.

Lemma Qle_ZO_flip : forall a, -(1) <= a <= 0 -> 0 <= (-a) <= 1.
Proof.
intros a [H0 H1].
auto with *.
split.
change 0 with (-0).
apply Qopp_le_compat.
assumption.
change 1 with (- (-(1))).
apply Qopp_le_compat.
assumption.
Qed.

Definition rational_exp_small_neg (a:Q) (p:-(1) <= a <= 0) : CR 
:= let p':= (Qle_ZO_flip p) in InfiniteAlternatingSum (expSequence_dnn p') (expSequence_zl p').

Lemma rational_exp_small_neg_posH : forall (a:Q) (p:-(1) <= a <= 0),
 ('(1#3) <= rational_exp_small_neg p)%CR.
Proof.
intros a p.
unfold rational_exp_small_neg.
do 4 rewrite InfiniteAlternatingSum_step.
generalize (dnn_tl
                  (dnn_tl (dnn_tl (dnn_tl (expSequence_dnn (Qle_ZO_flip p)))))).
generalize (@Limit_tl Q_as_MetricSpace
                                (@tl Q (@tl Q (@tl Q (expSequence (Qopp a)))))
                                (Qmake Z0 xH)
                                (@Limit_tl Q_as_MetricSpace
                                   (@tl Q (@tl Q (expSequence (Qopp a))))
                                   (Qmake Z0 xH)
                                   (@Limit_tl Q_as_MetricSpace
                                      (@tl Q (expSequence (Qopp a)))
                                      (Qmake Z0 xH)
                                      (@Limit_tl Q_as_MetricSpace
                                         (expSequence (Qopp a)) (Qmake Z0 xH)
                                         (@expSequence_zl (Qopp a)
                                            (@Qle_ZO_flip a p)))))).
intros l d.
change ('(1#3) <= '1%Q + - ('(1 * (1 * - a))%Q + - 
 ('((1 # 2) * (1 * - a * - a))%Q + - ('((1 # 6) * (1 * - a * - a * - a))%Q + 
 - InfiniteAlternatingSum d l))))%CR.
cut ('0<=InfiniteAlternatingSum d l)%CR;[|apply InfiniteAlternatingSum_nonneg].
generalize (InfiniteAlternatingSum d l).
intros m Hm.
rsapply shift_leEq_rht.
unfold cg_minus;simpl.
assert (X:((' 1 -
 (' (1 * (1 * - a)) -
  (' ((1 # 2) * (1 * - a * - a)) - (' ((1 # 6) * (1 * - a * - a * - a)) - m))) -
 ' (1 # 3))==(('((1#6)*(a+1)*(1*(a+1)*(a+1)+(3#1)))%Q + m)))%CR) by (abstract ring).
rewrite X.
rsapply plus_resp_nonneg;[|assumption].
rewrite CRle_Qle.
repeat rsapply mult_resp_nonneg.
discriminate.
destruct p as [p _].
rewrite Qle_minus_iff in p.
(replace RHS with (a + - - (1)) by ring);assumption.
rsapply plus_resp_nonneg.
rsapply sqr_nonneg.
discriminate.
Qed.

Lemma rational_exp_small_neg_pos : forall (a:Q) (p:-(1) <= a <= 0),
 CRpos (rational_exp_small_neg p).
Proof.
intros a p.
exists (1#3)%Qpos.
abstract (
 autorewrite with QposElim;
 rapply rational_exp_small_neg_posH).
Defined.

Definition rational_exp_small (a:Q) (p:-(1) <= a <= 1) : CR.
intros a p.
destruct (Qlt_le_dec 0 a).
refine (CRinv_pos (1#3) (@rational_exp_small_neg (-a) _)).
abstract (destruct p;split;[apply Qopp_le_compat; assumption|apply (Qopp_le_compat 0); apply Qlt_le_weak; assumption]).
apply (rational_exp_small_neg (conj (proj1 p) q)).
Defined. 

Definition E : CR.
apply rational_exp_small with (1).
abstract (split;discriminate).
Defined.

Section Correct.

Lemma Qpower_S : forall a n, (a^S n == a*a^n).
Proof.
intros a n.
destruct (Qeq_dec a 0).
rewrite q.
rewrite Qpower_0.
discriminate.
ring.
rewrite inj_S.
unfold Zsucc.
rewrite Qpower_plus.
assumption.
ring.
Qed.

Lemma exp_ps_correct : forall a (n:nat) H, 
  inj_Q IR ((((-(1))^n)*Str_nth n (expSequence (-a)))%Q)[=]Exp_ps n (inj_Q IR a) H.
Proof.
intros a n H.
stepr (inj_Q IR ((1 # P_of_succ_nat (pred (fac n))) * a ^ n)%Q).
rsapply inj_Q_wd.
rewrite Str_nth_expSequence.
setoid_replace (a^n)%Q with ((-(1))^n*(-a)^n)%Q.
ring.
 rewrite <- Qmult_power.
 setoid_replace (- (1) * - a) with a by ring.
 reflexivity.
generalize H; clear H.
induction n.

intros H.
simpl.
unfold pring.
simpl.
rational.

intros H.
stepl ((One[/](nring (S n))[//]nringS_ap_zero IR n)[*](inj_Q IR a)[*]Exp_ps n (inj_Q IR a) H).

simpl.
change (nring (R:=IR) n[+]One) with (nring (R:=IR) (S n)).
rstepl (((One[/]nring (R:=IR) (S n)[//]nringS_ap_zero IR n)[*]
(One[/]nring (R:=IR) (fac n)[//]nring_fac_ap_zero IR n))[*]
 (nexp IR n (inj_Q IR a[-]Zero)[*]inj_Q IR a)).
apply mult_wd;[|rational].
assert (X:=(mult_resp_ap_zero _ _ _ (nringS_ap_zero IR n) (nring_fac_ap_zero IR n))).
rstepl (One[/]((nring (R:=IR) (S n))[*]nring (R:=IR) (fac n))[//]X).
apply div_wd;[rational|].
apply eq_symmetric.
change (fac n + n * fac n)%nat with (S n*(fac n))%nat.
apply nring_comm_mult.

stepl (inj_Q IR ((1#(P_of_succ_nat n))*a*((1 # P_of_succ_nat (pred (fac n))) * a ^ n))%Q).
apply inj_Q_wd.
change ((1 # P_of_succ_nat n) * a * ((1 # P_of_succ_nat (pred (fac n))) * a ^ n) ==
 (1 # P_of_succ_nat (pred (S n * fac n))) * a ^ S n)%Q.
replace (P_of_succ_nat (pred (S n * fac n))%nat) with 
 (P_of_succ_nat (pred (S n)) * P_of_succ_nat (pred (fac n)))%positive.
rewrite <- pred_Sn.
rewrite Qpower_S.
change ((1 # P_of_succ_nat n * P_of_succ_nat (pred (fac n))%positive))%Q
 with ((1 # P_of_succ_nat n) * (1#P_of_succ_nat (pred (fac n))))%Q.
ring.
apply nat_of_P_inj.
rewrite nat_of_P_mult_morphism.
repeat rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
rewrite <- pred_Sn.
rewrite S_predn.
rewrite S_predn.
reflexivity.

cut (0 < S n * fac n)%nat;[auto with *|apply (nat_fac_gtzero (S n))].
cut (0 < fac n)%nat;[auto with *|apply (nat_fac_gtzero n)].

stepl ((One[/]nring (R:=IR) (S n)[//]nringS_ap_zero IR n)[*]inj_Q IR a[*]
 inj_Q IR ((1 # P_of_succ_nat (pred (fac n))) * a ^ n)%Q);
 [rapply mult_wdr; apply IHn|].
apply eq_symmetric.
eapply eq_transitive;[apply inj_Q_mult|].
eapply eq_transitive;[apply mult_wdl;apply inj_Q_mult|].
apply mult_wdl.
apply mult_wdl.
change (1 # P_of_succ_nat n)%Q with (1/P_of_succ_nat n)%Q.
assert (A:inj_Q IR ((P_of_succ_nat n):Q)[=]nring (S n)).
stepl (inj_Q IR (nring (S n))).
apply inj_Q_nring.
apply inj_Q_wd.
simpl.
clear - n.
induction n.
reflexivity.
simpl.
rewrite IHn.
unfold Qeq.
simpl.
rewrite Pplus_one_succ_r.
repeat (rewrite Zpos_mult_morphism || rewrite Zpos_plus_distr).
ring.

assert (B:inj_Q IR (P_of_succ_nat n:Q)[#]Zero).
stepl (nring (R:=IR) (S n)).
apply nringS_ap_zero.
apply eq_symmetric;assumption.
eapply eq_transitive;[apply inj_Q_div|].
instantiate (1:=B).
apply div_wd.
rstepr (Zero[+]One:IR).
rapply (inj_Q_nring IR 1).
assumption.
Qed.

Lemma rational_exp_small_neg_correct : forall (a:Q) Ha,
 (@rational_exp_small_neg a Ha == IRasCR (Exp (inj_Q IR a)))%CR.
Proof.
intros a Ha.
unfold rational_exp_small_neg.
rapply InfiniteAlternatingSum_correct.
intros n.
clear Ha.
apply exp_ps_correct.
Qed.

End Correct.

