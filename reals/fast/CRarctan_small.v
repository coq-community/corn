(*
Copyright © 2006-2008 Russell O’Connor

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
Require Import CoRN.reals.fast.CRAlternatingSum.
Require Import CoRN.reals.fast.CRAlternatingSum_alg.
Require Import CoRN.reals.fast.CRstreams.
Require Import CoRN.reals.fast.CRexp.
Require Export CoRN.reals.fast.CRArith.
Require Import CoRN.reals.fast.CRIR.
From Coq Require Import Qpower Qabs Qround.
Require Import CoRN.model.ordfields.Qordfield.
Require Import CoRN.reals.Q_in_CReals.
Require Import CoRN.model.metric2.Qmetric.
Require Import CoRN.model.totalorder.QMinMax.
Require Import CoRN.model.totalorder.QposMinMax.
Require Import CoRN.transc.MoreArcTan.
Require Import CoRN.tactics.CornTac.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import CoRN.stdlib_omissions.Q.
Require Import Coq.Init.Datatypes.

Set Implicit Arguments.

Local Open Scope Q_scope.
Local Open Scope uc_scope.

Opaque inj_Q CR.

Lemma Qmult_pos_neg : forall (a b : Q),
    0 <= a -> b <= 0 -> a*b <= 0.
Proof.
  intros. rewrite Qmult_comm.
  rewrite <- (Qmult_0_l a).
  apply Qmult_le_compat_r; assumption.
Qed. 

Lemma Qmult_opp_1 : forall q : Q,
    eq (-q) (-1 * q).
Proof.
  reflexivity.
Qed.

(**
** Arctangent (small)
For values between in [[-1,1]], arctangent is computed by it's alternating
taylor series.
*)
Section ArcTanSeries.
Variable a:Q.

(* (1,a) -> (3, -a^3/3) -> ...
   With a bigger state type, 1/(2i+1) could be set directly. It will be
   done in faster reals with a stream of positive*AQ*AQ. *)
Definition arctanStream (px : prod positive Q) : prod positive Q
  := let d := Pos.add 2 (fst px) in
     (d, Qred (- snd px * a * a * (fst px#d))).

Lemma arctanStream_fst : forall p,
    fst (iterate _ arctanStream p (1%positive, a)) ≡ Pos.succ (2*p).
Proof.
  apply Pos.peano_ind.
  - reflexivity.
  - intros p H. rewrite iterate_succ. 
    destruct (iterate (positive and Q) arctanStream p (1%positive, a)).
    simpl in H. subst p0.
    transitivity (Pos.add 2 (p~1)). reflexivity.
    clear q a. rewrite Pos.mul_succ_r.
    rewrite <- Pos.add_1_l, (Pos.add_comm 1).
    rewrite <- Pos.add_assoc. apply f_equal. reflexivity.
Qed.

Lemma Str_pth_arctanStream : forall p,
    Str_pth _ arctanStream p (xH, a)
    == (1#(1+2*p)) * ((-1)^p*a^(1+2*p))%Q.
Proof.
  apply Pos.peano_ind.
  - unfold arctanStream, Str_pth, iterate, snd.
    rewrite Qred_correct. simpl.
    rewrite (Qmult_comm (1#3)), Qmult_assoc, Qmult_assoc.
    reflexivity.
  - intros p pInd. unfold Str_pth.
    rewrite iterate_succ. unfold Str_pth in pInd.
    pose proof (arctanStream_fst p) as H0.
    destruct (iterate _ arctanStream p (1%positive, a)) as [p0 q].
    simpl in H0. subst p0. unfold snd in pInd. 
    unfold arctanStream, snd, fst.
    rewrite Qred_correct. rewrite pInd. clear pInd q. 
    (* Get rid of (-1)^p *)
    rewrite <- (Qmult_comm ((-1) ^ Pos.succ p * a ^ (1 + 2 * Pos.succ p))).
    rewrite <- (Pos.add_1_l p).
    rewrite Pos2Z.inj_add, (Qpower_plus (-1)%Q).
    simpl ((-1)^1). 
    rewrite Qmult_opp_1.
    do 5 rewrite <- (Qmult_assoc (-1)).
    apply (Qmult_comp (-1)). reflexivity.
    rewrite (Qmult_comm (1 # (1 + 2 * p))).
    do 5 rewrite <- (Qmult_assoc ((-1)^p)).
    apply (Qmult_comp ((-1)^p)). reflexivity.
    (* Get rid of a *)
    setoid_replace (a ^ (1 + 2 * (1 + p))) with (a ^ (1 + 2 * p) * (a * a)).
    do 4 rewrite <- (Qmult_assoc (a ^ (1 + 2 * p))).
    apply Qmult_comp. reflexivity.
    rewrite <- (Qmult_assoc _ a a).
    rewrite (Qmult_comm (1 # (1 + 2 * p))).
    rewrite <- (Qmult_assoc (a*a)).
    apply Qmult_comp. reflexivity.
    (* Finish equalities *)
    unfold Qeq, Qmult, Qnum, Qden.
    rewrite Z.mul_1_l, Z.mul_1_l.
    reflexivity.
    rewrite <- (Qpower_plus_positive a 1 1).
    rewrite <- (Qpower_plus_positive a (1+2*p)).
    apply Qpower_positive_comp. reflexivity.
    rewrite <- Pos.add_assoc.
    apply f_equal. rewrite (Pos.add_comm 1 p).
    reflexivity.
    intro abs. discriminate.
Qed.

Hypothesis Ha: (-1 <= a <= 1).

Lemma arctanStream_alt : Str_alt_decr _ arctanStream (1%positive,a).
Proof.
  split.
  - (* Replace a by Qabs a *)
    rewrite Str_pth_arctanStream, Str_pth_arctanStream.
    rewrite Qabs_Qmult, Qabs_Qmult, Qabs_Qmult, Qabs_Qmult.
    rewrite Qabs_Qpower, Qabs_Qpower.
    change (Qabs (-1)) with 1.
    rewrite Qpower_1, Qpower_1, Qmult_1_l, Qmult_1_l.
    rewrite (Qabs_Qpower a (1+2*Pos.succ p)), (Qabs_Qpower a (1+2*p)).
    (* Finish inequality *)
    setoid_replace (Qabs a ^ (1 + 2 * Pos.succ p)%positive)
      with (Qabs a * Qabs a * Qabs a ^ (1 + 2 * p)%positive).
    rewrite Qmult_assoc.
    apply Qmult_le_compat_r.
    2: rewrite <- Qabs_Qpower; apply Qabs_nonneg.
    + rewrite Qmult_comm.
      apply (Qabs_Qle_condition a 1) in Ha.
      apply (Qle_trans _ (1* (1 # (1 + 2 * (Pos.succ p))))).
      apply Qmult_le_compat_r. 2: discriminate.
      apply (Qle_trans _ (1*Qabs a)).
      apply Qmult_le_compat_r. exact Ha.
      apply Qabs_nonneg. rewrite Qmult_1_l. exact Ha.
      rewrite Qmult_1_l. unfold Qabs, Z.abs.
      unfold Qle, Qnum, Qden.
      rewrite Z.mul_1_l, Z.mul_1_l. 
      change (p <= Pos.succ p)%positive.
      apply Pos.lt_le_incl, Pos.lt_succ_r, Pos.le_refl.
    + replace (1 + 2 * Pos.succ p)%positive with (2 + (1 + 2 * p))%positive.
      generalize (1 + 2 * p)%positive. clear p. intro p.
      unfold Qpower.
      rewrite Qpower_plus_positive. reflexivity.
      rewrite Pos.add_comm, <- Pos.add_assoc. apply f_equal.
      rewrite <- Pos.add_1_l. 
      rewrite Pos.mul_add_distr_l, Pos.mul_1_r.
      apply Pos.add_comm.
  - rewrite Str_pth_arctanStream, Str_pth_arctanStream.
    rewrite Qmult_comm, <- Qmult_assoc. apply Qmult_pos_neg.
    discriminate. rewrite Qmult_comm, <- Qmult_assoc.
    apply Qmult_pos_neg. discriminate.
    rewrite <- Pos.add_1_l.
    change ((-1) ^ (1 + p)%positive) with (Qpower_positive (-1) (1 + p)).
    rewrite Qpower_plus_positive. simpl (Qpower_positive (-1) 1).
    rewrite <- Qmult_assoc, <- Qmult_assoc.
    apply (Qopp_le_compat 0). 
    rewrite (Qmult_comm (a ^ (1 + 2 * (1 + p)%positive))).
    rewrite Qmult_assoc, Qmult_assoc.
    rewrite <- Qmult_assoc.
    apply Qmult_le_0_compat.
    simpl.
    destruct (Qpower_positive (-1) p), Qnum; discriminate.
    setoid_replace (a ^ (1 + 2 * (1 + p))) with (a ^ (1 + 2 * p) * (a * a)).
    rewrite Qmult_assoc.
    apply Qmult_le_0_compat.
    destruct (a ^ (1 + 2 * p)), Qnum; discriminate.
    destruct a, Qnum; discriminate.
    change (a*a) with (Qpower_positive a 2).
    rewrite <- (Qpower_plus_positive a (1+2*p)).
    change (a ^ (1 + 2 * (1 + p))) with (Qpower_positive a (1 + 2 * (1 + p))).
    replace (1 + 2 * (1 + p))%positive with (1 + 2 * p + 2)%positive.
    reflexivity.
    rewrite <- Pos.add_assoc. apply f_equal.
    rewrite Pos.mul_add_distr_l, Pos.mul_1_r.
    apply Pos.add_comm. 
Qed.

Lemma arctanStream_zl
  : Limit_zero _ arctanStream (xH,a)
               (fun e:Qpos => Z.to_pos (Qceiling (/ (proj1_sig e)))).
Proof.
  intros [e epos]. rewrite Str_pth_arctanStream, Qabs_Qmult, Qabs_Qmult.
  rewrite Qabs_Qpower. change (Qabs (-1)) with 1.
  rewrite Qpower_1, Qmult_1_l.
  rewrite Qmult_comm.
  apply (Qle_trans _ (1 * Qabs (1 # 1 + 2 * Z.to_pos (Qceiling (/ ` (e ↾ epos)))))).
  apply Qmult_le_compat_r. 2: apply Qabs_nonneg.
  - rewrite (Qabs_Qpower a (1 + 2 * Z.to_pos (Qceiling (/ ` (e ↾ epos))))).
    apply Qpower_le_1. split.
    apply Qabs_nonneg.
    apply Qabs_Qle_condition, Ha.
  - clear Ha a.
    rewrite Qmult_1_l. unfold Qabs, Z.abs, proj1_sig.
    rewrite <- (Qinv_involutive e) at 2.
    assert (0 < /e) as H.
    { apply Qinv_lt_0_compat, epos. }
    apply (@Qinv_le_compat (/e) (Zpos (1 + 2 * Z.to_pos (Qceiling (/ e))) # 1)).
    exact H.
    apply (Qle_trans _ _ _ (Qle_ceiling (/e))).
    generalize (Qceiling (/ e)).
    clear H epos e. intros [|p|p].
    discriminate. 2: discriminate.
    pose proof (Zle_Qle p (Z.pos (1 + 2 * Z.to_pos p))).
    unfold inject_Z.
    unfold inject_Z in H.
    rewrite <- H. clear H.
    change (p <= 1 + 2*p)%positive.
    rewrite <- Pplus_one_succ_l.
    apply Pos.lt_le_incl, Pos.lt_succ_r.
    apply (Pos.mul_le_mono_r p 1 2). discriminate.
Qed.

End ArcTanSeries.

Definition rational_arctan_small (a:Q) (p: -1 <= a <= 1) : CR :=
  (inject_Q_CR a + AltSeries _ (arctanStream a) (xH,a) _
                             (arctanStream_alt p) (arctanStream_zl p))%CR.

Lemma rational_arctan_small_wd : forall (a1 a2 : Q) (p1 : -1 <= a1 <= 1) (p2 : -1 <= a2 <= 1),
    a1 = a2 → rational_arctan_small p1 = rational_arctan_small p2.
Proof.
  intros. unfold rational_arctan_small.
  apply ucFun2_wd. rewrite H. reflexivity.
  apply AltSeries_wd.
  2: reflexivity. intro p.
  rewrite Str_pth_arctanStream, Str_pth_arctanStream, H. reflexivity.
Qed.

Lemma widen_interval : forall a:Q, -1 < a < 1 -> -1 <= a <= 1.
Proof.
  intros a [H H0]. split; apply Qlt_le_weak; assumption.
Qed.

Lemma rational_arctan_small_correct : forall (a:Q) (Ha : -1 < a < 1),
    (@rational_arctan_small a (widen_interval Ha) == IRasCR (ArcTan (inj_Q IR a)))%CR.
Proof.
  intros a Ha.
  unfold rational_arctan_small.
  rewrite <- (IR_inj_Q_as_CR a).
  rewrite
    (AltSeries_correct
       _ _ _ _ (arctanStream_alt (widen_interval Ha))
       (arctanStream_zl (widen_interval Ha))
       _ (AltSeries_convergent_0 _ _ _ _ (inj_Q IR a)
                                 (arctanStream_alt (widen_interval Ha)) (arctanStream_zl (widen_interval Ha)))).
  - apply IRasCR_wd.
    assert (olor ([--][1]) [1] (inj_Q IR a)) as X.
    { split.
      stepl (inj_Q IR (-1)). apply inj_Q_less, Ha. 
      rewrite (inj_Q_inv IR 1), inj_Q_One. reflexivity.
      stepr (inj_Q IR 1); [| now apply inj_Q_One].
      apply inj_Q_less, Ha. }
    eapply eq_transitive_unfolded;
      [|apply (arctan_series (inj_Q IR a) (arctan_series_convergent_IR) X)].
    apply series_sum_wd.
    intros n.
    transitivity (inj_Q IR (((-1)^n)%Q *(a^(1+2*Z.of_nat n) * (1#(Pos.of_nat (1+2*n)))))).
    + destruct n. apply inj_Q_wd. simpl.
      rewrite Qmult_1_l, Qmult_1_r. reflexivity.
      apply inj_Q_wd.
      rewrite Str_pth_arctanStream.
      rewrite (Qmult_assoc ((-1)^S n)).
      rewrite (Qmult_comm ((-1) ^ S n * a ^ (1 + 2 * S n))). apply Qmult_comp.
      unfold Qeq, Qnum, Qden. 
      rewrite Z.mul_1_l, Z.mul_1_l.
      change 2%positive with (Pos.of_nat 2).
      rewrite <- (Nat2Pos.inj_mul 2 (S n)).
      2: discriminate. 2: discriminate.
      rewrite <- (Nat2Pos.inj_add 1). reflexivity.
      discriminate. discriminate.
      apply Qmult_comp.
      rewrite <- Pos.of_nat_succ, POS_anti_convert.
      reflexivity.
      replace (1 + 2 * Z.pos (Pos.of_nat (S n)))%Z with (1 + 2 * S n)%Z.
      reflexivity.
      rewrite <- Pos.of_nat_succ, POS_anti_convert.
      reflexivity.
    + transitivity (([--][1][^]n[/]nring (R:=IR) (S (2 * n))[//]nringS_ap_zero IR (2 * n))[*]
     (inj_Q IR a)[^](2 * n + 1)).
      2: reflexivity.
      rstepr (([--][1][^]n)[*]((inj_Q IR a)[^](2*n+1)[/]nring (R:=IR) (S (2 * n))[//]nringS_ap_zero IR (2 * n))).
      rewrite inj_Q_mult.
      apply mult_wd.
      rewrite inj_Q_power.
      apply nexp_wd.
      rewrite (inj_Q_inv IR 1), inj_Q_One. 
      reflexivity.
      apply mult_cancel_lft with (nring (R:=IR) (S (2 * n))).
      apply nringS_ap_zero.
      rstepr (inj_Q IR a[^](2 * n + 1)).
      stepr (inj_Q IR (a^(2*n+1)%nat)); [| now apply inj_Q_power].
      stepl ((inj_Q IR (nring (S (2*n))))[*]inj_Q IR (a ^ (1 + 2 * n) * (1 # Pos.of_nat (1 + 2 * n))));
        [| now apply mult_wdl; apply inj_Q_nring].
      rewrite <- inj_Q_mult.
      apply inj_Q_wd.
      setoid_rewrite (nring_Q (S (2*n))).
      change (S (2 * n) * (a ^ (1 + 2 * n) * (1 # Pos.of_nat (1 + 2 * n)))
              == a ^ (2 * n + 1)%nat)%Q.
      rewrite Qmult_comm.
      rewrite <- Qmult_assoc.
      setoid_replace ((1 # Pos.of_nat (1 + 2 * n)) * S (2 * n)) with 1%Q.
      rewrite Qmult_1_r, Nat.add_comm.
      rewrite Nat2Z.inj_add, Nat2Z.inj_mul. reflexivity.
      unfold Qeq, inject_Z, Qmult, Qnum, Qden.
      rewrite Z.mul_1_l, Z.mul_1_l, Z.mul_1_r, Pos.mul_1_r.
      unfold Z.of_nat.
      rewrite Pos.of_nat_succ. reflexivity.
  - intro p. destruct (Pos.to_nat p) eqn:des.
    exfalso. pose proof (Pos2Nat.is_pos p). rewrite des in H.
    inversion H.
    apply inj_Q_wd.
    rewrite <- des, Pos2Nat.id. reflexivity.
Qed.
