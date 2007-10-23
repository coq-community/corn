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
Require Import Qpower.
Require Import Qordfield.
Require Import ModulusDerivative.
Require Import ContinuousCorrect.
Require Import Qmetric.
Require Import Exponential.
Require Import CornTac.

Set Implicit Arguments.

Open Local Scope Q_scope.
Open Local Scope uc_scope.

Opaque inj_Q CR.

Section LnPlusSeries.
Variable a:Q.

(* This is the series for ln (1+a) *)

Definition lnPlusSequence := (mult_Streams (recip_positives) (tl (powers a))).

Lemma Str_nth_lnPlusSequence : forall n, (Str_nth n lnPlusSequence == (1#P_of_succ_nat n)*a^(1+n)%nat)%Q.
Proof.
intros n.
unfold lnPlusSequence.
unfold mult_Streams.
rewrite Str_nth_zipWith.
rewrite Str_nth_recip_positives.
change (Str_nth n (tl (powers a))) with  (Str_nth (S n) (powers a)).
rewrite Str_nth_powers.
reflexivity.
Qed.

Hypothesis Ha: 0 <= a <= 1.

Lemma lnPlusSequence_dnn : DecreasingNonNegative lnPlusSequence.
Proof.
rapply mult_Streams_dnn.
 apply recip_positives_dnn.
apply dnn_tl.
apply powers_dnn.
assumption.
Qed.

Lemma lnPlusSequence_zl : Limit lnPlusSequence 0.
Proof.
unfold lnPlusSequence.
apply mult_Streams_zl with (1#1)%Qpos.
 apply recip_positives_zl.
abstract (
destruct (powers_nbz Ha) as [_ H];
apply H).
Defined.

End LnPlusSeries.

Definition rational_lnPlus_small_pos (a:Q) (p: 0 <= a <= 1) : CR := 
 InfiniteAlternatingSum (lnPlusSequence_dnn p) (lnPlusSequence_zl p).

(*
Lemma rational_arcTan_small_pos_correct : forall (a:Q) Ha, a < 1 ->
 (@rational_arcTan_small_pos a Ha == IRasCR (ArcTan (inj_Q IR a)))%CR.
Proof.
intros a Ha Ha0.
unfold rational_arcTan_small_pos.
rewrite InfiniteAlternatingSum_correct'.
apply IRasCR_wd.
assert (X:(olor ([--]One) One (inj_Q IR a))).
 split.
  apply less_leEq_trans with Zero.
   apply shift_zero_less_minus'.
   rstepr (One:IR).
   apply pos_one.
  stepl (inj_Q IR 0) by rapply (inj_Q_nring IR 0).
  apply inj_Q_leEq.
  destruct Ha; assumption.
 rstepr (nring 1:IR).
 stepr (inj_Q IR 1) by rapply (inj_Q_nring IR 1).
 apply inj_Q_less.
 assumption.  
eapply eq_transitive_unfolded;
 [|apply (arctan_series (inj_Q IR a) (arctan_series_convergent_IR) X)].
rapply series_sum_wd.
intros n.
change (inj_Q IR ((- (1)) ^ n * Str_nth n (arcTanSequence a))[=]
(([--]One[^]n[/]nring (R:=IR) (S (2 * n))[//]nringS_ap_zero IR (2 * n))[*]
 (inj_Q IR a)[^](2 * n + 1))).
rstepr (([--]One[^]n)[*]((inj_Q IR a)[^](2*n+1)[/]nring (R:=IR) (S (2 * n))[//]nringS_ap_zero IR (2 * n))).
eapply eq_transitive_unfolded.
 apply inj_Q_mult.
apply mult_wd.
 eapply eq_transitive_unfolded.
  apply inj_Q_power.
 apply nexp_wd.
 eapply eq_transitive_unfolded.
  apply inj_Q_inv.
 apply un_op_wd_unfolded.
 rstepr (nring 1:IR).
 apply (inj_Q_nring IR 1).
apply mult_cancel_lft with (nring (R:=IR) (S (2 * n))).
 apply nringS_ap_zero.
rstepr (inj_Q IR a[^](2 * n + 1)).
stepr (inj_Q IR (a^(2*n+1)%nat)) by apply inj_Q_power.
stepl ((inj_Q IR (nring (S (2*n))))[*]inj_Q IR (Str_nth n (arcTanSequence a))) by
 apply mult_wdl; apply inj_Q_nring.
stepl (inj_Q IR (nring (S (2*n))[*]Str_nth n (arcTanSequence a)))
 by apply inj_Q_mult.
apply inj_Q_wd.
csetoid_rewrite (nring_Q (S (2*n))).
change (S (2 * n)*Str_nth n (arcTanSequence a)==a ^ (2 * n + 1)%nat).
rewrite Str_nth_arcTanSequence.
rewrite (Qmake_Qdiv).
rewrite plus_comm.
generalize (a^(2*n+1)%nat).
intros b.
rewrite <- POS_anti_convert.
field.
unfold Qeq; simpl.
rewrite Pmult_1_r.
rewrite <- POS_anti_convert.
auto with *.
Qed.

Definition rational_arcTan_small (a:Q) (p: -(1) <= a <= 1) : CR.
intros a.
destruct (Qle_total a 0); intros Ha.
 refine (-(@rational_arcTan_small_pos (-a)%Q _))%CR.
 abstract (
 split;
 [(replace RHS with (0+-a) by ring);
  rewrite <- Qle_minus_iff;
  assumption
 |rewrite Qle_minus_iff;
  (replace RHS with (a + - - (1)) by ring);
  rewrite <- Qle_minus_iff;
  destruct Ha; assumption]).
apply (@rational_arcTan_small_pos a).
abstract (
split;[|destruct Ha; assumption];
 apply Qnot_lt_le; apply Qle_not_lt; assumption).
Defined.

Lemma rational_arcTan_small_correct : forall (a:Q) Ha, -(1) < a -> a < 1 ->
 (@rational_arcTan_small a Ha == IRasCR (ArcTan (inj_Q IR a)))%CR.
Proof.
intros a Ha Ha0 Ha1.
unfold rational_arcTan_small.
destruct (Qle_total a 0);
 rewrite rational_arcTan_small_pos_correct.
   rewrite Qlt_minus_iff.
   replace RHS with (a + - - (1)) by ring.
   rewrite <- Qlt_minus_iff.
   assumption.
  rewrite <- IR_opp_as_CR.
  apply IRasCR_wd.
  csetoid_rewrite_rev (ArcTan_inv (inj_Q IR (-a))).
  apply ArcTan_wd.
  eapply eq_transitive.
   apply eq_symmetric; apply (inj_Q_inv IR (-a)).
  apply inj_Q_wd.
  simpl.
  ring.
 assumption.
reflexivity.
Qed.
*)