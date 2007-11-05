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
Require Import CRGeometricSum.
Require Export CRArith.
Require Import CRIR.
Require Import Qpower.
Require Import Qordfield.
Require Import Q_in_CReals.
Require Import Qmetric.
Require Import QMinMax.
Require Import ArTanH.
Require Import CRarctan_small.
Require Import Qauto.
Require Import CornTac.

Set Implicit Arguments.

Open Local Scope Q_scope.
Open Local Scope uc_scope.

Opaque inj_Q CR.

Lemma arctanSequence_Gs : forall a, GeometricSeries (a^2) (arctanSequence a).
Proof.
intros a.
rapply mult_Streams_Gs.
 apply everyOther_dnn.
 apply recip_positives_dnn.
apply powers_help_Gs.
 apply Qsqr_nonneg.
Qed.

Lemma Qsqr_lt_one : forall (a:Q), (-(1) < a) -> a < 1 -> (a^2 < 1).
Proof.
intros a H0 H1.
rewrite Qlt_minus_iff in *.
replace RHS with ((1 + - a)*(a + - -(1))) by ring.
Qauto_pos.
Qed.

Lemma artanh_DomArTanH : forall a, (a^2 < 1) -> DomArTanH (inj_Q IR a).
Proof.
intros a Ha.
split.
 stepl (inj_Q IR ([--](1))%Q).
  apply inj_Q_less; simpl.
  apply Qnot_le_lt.
  intros H.
  apply (Qlt_not_le _ _ Ha).
  rewrite Qle_minus_iff in *.
  replace RHS with ((- (1) + - a + 2)*(-(1) +- a)) by ring.
  Qauto_nonneg.
 stepr ([--](inj_Q IR 1)).
  apply inj_Q_inv.
 apply un_op_wd_unfolded.
 rstepr (nring 1:IR).
 apply (inj_Q_nring IR 1).
stepr (inj_Q IR (1)).
 apply inj_Q_less; simpl.
 apply Qnot_le_lt.
 intros H.
 apply (Qlt_not_le _ _ Ha).
 rewrite Qle_minus_iff in *.
 replace RHS with ((a + - (1) + 2)*(a +- (1))) by ring.
 Qauto_nonneg.
rstepr (nring 1:IR).
apply (inj_Q_nring IR 1).
Qed.

Definition rational_artanh_slow (a:Q) (p1: a^2 < 1) : CR := 
 InfiniteGeometricSum (Qsqr_nonneg a) p1 (arctanSequence_Gs a).

Lemma rational_artanh_slow_correct : forall (a:Q) Ha Ha0,
 (@rational_artanh_slow a Ha == IRasCR (ArTanH (inj_Q IR a) Ha0))%CR.
Proof.
intros a Ha Ha0.
unfold rational_artanh_slow.
rewrite InfiniteGeometricSum_correct'.
apply IRasCR_wd.
 eapply eq_transitive_unfolded;
 [|apply (ArTanH_series (inj_Q IR a) (ArTanH_series_convergent_IR) (artanh_DomArTanH Ha) Ha0)].
simpl.
unfold series_sum.
apply Lim_seq_eq_Lim_subseq with double.
  unfold double; auto with *.
 intros n.
 exists (S n).
 unfold double; auto with *.
intros n.
simpl.
clear - n.
induction n.
 apply eq_reflexive.
simpl.
set (A:=nexp IR (n + S n) (inj_Q IR a[-]Zero)).
rewrite plus_comm.
simpl.
fold (double n).
csetoid_rewrite_rev IHn.
clear IHn.
csetoid_replace (ArTanH_series_coef (double n)[*]nexp IR (double n) (inj_Q IR a[-]Zero)) (Zero:IR).
 csetoid_replace (ArTanH_series_coef (S (double n))[*]A) (inj_Q IR (Str_nth n (arctanSequence a))).
  rational.
 unfold ArTanH_series_coef.
 case_eq (even_odd_dec (S (double n))); intros H.
  elim (not_even_and_odd _ H).
  constructor.
  rapply even_plus_n_n.
 intros _.
 eapply eq_transitive;
  [|apply inj_Q_wd; simpl; rewrite Str_nth_arctanSequence; rewrite Qmake_Qdiv; reflexivity].
 eapply eq_transitive;
  [|apply eq_symmetric; apply inj_Q_mult].
 apply mult_wd.
  assert (X:(inj_Q IR (nring (S (double n))))[#]Zero).
   stepr (inj_Q IR Zero).
    apply inj_Q_ap.
    apply nringS_ap_zero.
   apply (inj_Q_nring IR 0).
  stepr (inj_Q IR (nring 1)[/]_[//]X).
   apply div_wd.
    rstepl (nring 1:IR).
    apply eq_symmetric.
    apply (inj_Q_nring IR 1).
   apply eq_symmetric.
   apply (inj_Q_nring).
  assert (X0:inj_Q IR ((P_of_succ_nat (2 * n)):Q)[#]Zero).
   stepr (inj_Q IR Zero).
    apply inj_Q_ap.
    discriminate.
   apply (inj_Q_nring IR 0).
  eapply eq_transitive;
   [|apply eq_symmetric; apply (fun b => inj_Q_div _ b _ X0)].
  apply div_wd.
   apply eq_reflexive.
  apply inj_Q_wd.
  rewrite <- POS_anti_convert.
  eapply eq_transitive;[apply nring_Q|].
  unfold double.
  simpl.
  replace (n+0)%nat with n by ring.
  reflexivity.
 unfold A; clear A.
 eapply eq_transitive;[|apply eq_symmetric; apply inj_Q_power].
 change ((inj_Q IR a[-]Zero)[^](n+S n)[=]inj_Q IR a[^](1 + 2 * n)).
 replace (n + S n)%nat with (1 + 2*n)%nat by ring.
  apply nexp_wd.
 rational.
unfold ArTanH_series_coef.
case_eq (even_odd_dec (double n)).
 intros _ _.
 rational.
intros o.
elim (fun x=> not_even_and_odd _ x o).
rapply even_plus_n_n.
Qed.
