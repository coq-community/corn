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
Require Import CoRN.reals.fast.CRAlternatingSum_alg.
Require Import CoRN.reals.fast.CRstreams.
Require Import CoRN.reals.fast.CRexp.
Require Import CoRN.reals.fast.CRpi.
Require Export CoRN.reals.fast.CRArith.
Require Import CoRN.reals.fast.CRIR.
Require Import Coq.QArith.Qpower Coq.QArith.Qabs.
Require Import CoRN.model.ordfields.Qordfield.
Require Import Coq.QArith.Qround.
Require Import CoRN.transc.Pi.
Require Import CoRN.reals.fast.ModulusDerivative.
Require Import CoRN.reals.fast.ContinuousCorrect.
Require Import CoRN.model.metric2.Qmetric.
Require Import CoRN.transc.PowerSeries.
Require Import CoRN.transc.SinCos.
Require Import CoRN.reals.fast.Compress.
Require Import CoRN.reals.fast.PowerBound.
Require Import CoRN.tactics.CornTac.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import CoRN.util.Qdlog.
From Coq Require Import Lia.

(* Backwards compatibility for Hint Rewrite locality attributes *)
Set Warnings "-unsupported-attributes".

Set Implicit Arguments.

Local Open Scope Q_scope.
Local Open Scope uc_scope.

Opaque inj_Q CR Qmin Qmax.

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

Lemma fact_inc : forall n:nat, (fact n <= fact (S n))%nat.
Proof.
  intro n. 
  rewrite <- (Nat.mul_1_l (fact n)).
  change (fact (S n)) with ((1+n)*fact n)%nat.
  apply Nat.mul_le_mono_nonneg_r.
  apply (Nat.le_trans _ 1).
  auto. exact (lt_O_fact n).
  apply le_n_S, Nat.le_0_l.
Qed.

Lemma fact_inc_recurse : forall p n:nat, (n <= p)%nat -> (fact n <= fact p)%nat.
Proof.
  induction p.
  - intros. inversion H. apply Nat.le_refl.
  - intros. apply Nat.le_succ_r in H. destruct H.
    apply (Nat.le_trans (fact n) (fact p)).
    apply IHp, H. apply fact_inc.
    subst n. apply Nat.le_refl.
Qed.

(**
** Sine
Sine is defined in terms of its alternating Taylor's series.
*)
Section SinSeries.
Variable a:Q.

(* (1,a) -> (3, -a^3/3!) -> ... *)
Definition sinStream (px : positive*Q) : positive*Q
  := let d := Pos.succ (fst px) in
     (Pos.add 2 (fst px), - snd px * a * a * (1#(d*Pos.succ d))).

Lemma sinStream_fst : forall p,
    fst (iterate _ sinStream p (1%positive, a)) ≡ Pos.succ (2*p).
Proof.
  apply Pos.peano_ind.
  - reflexivity.
  - intros p H. rewrite iterate_succ. 
    destruct (iterate (positive and Q) sinStream p (1%positive, a)).
    simpl in H. subst p0.
    transitivity (Pos.add 2 (p~1)). reflexivity.
    clear q a. rewrite Pos.mul_succ_r.
    rewrite <- Pos.add_1_l, (Pos.add_comm 1).
    rewrite <- Pos.add_assoc. apply f_equal. reflexivity.
Qed.

(* The closed formula for the sine stream. *)
Lemma Str_pth_sinStream : forall (p:positive),
    Str_pth _ sinStream p (xH,a)
    == (1#Pos.of_nat (fact (1+2*Pos.to_nat p))) * ((-1)^p*a^(1+2*p))%Q.
Proof.
  apply Pos.peano_ind.
  - unfold sinStream, Str_pth; simpl.
    rewrite Qmult_comm. apply Qmult_comp. reflexivity.
    rewrite Qmult_assoc, Qmult_assoc.
    reflexivity.
  - intros p pInd. unfold Str_pth.
    rewrite iterate_succ. unfold Str_pth in pInd.
    pose proof (sinStream_fst p) as H0.
    destruct (iterate (positive and Q) sinStream p (1%positive, a)) as [p0 q].
    simpl in H0. subst p0. unfold snd in pInd. 
    unfold sinStream, snd, fst.
    rewrite pInd. clear pInd q.
    (* Get rid of (-1)^p *)
    rewrite <- (Qmult_comm ((-1) ^ Pos.succ p * a ^ (1 + 2 * Pos.succ p))).
    rewrite <- (Pos.add_1_l p).
    rewrite Pos2Z.inj_add, (Qpower_plus (-1)%Q).
    simpl ((-1)^1).
    rewrite Qmult_opp_1.
    do 5 rewrite <- (Qmult_assoc (-1)).
    apply (Qmult_comp (-1)). reflexivity.
    rewrite (Qmult_comm (1 # Pos.of_nat (fact (1 + 2 * Pos.to_nat p)))).
    do 5 rewrite <- (Qmult_assoc ((-1)^p)).
    apply Qmult_comp. reflexivity.
    (* Get rid of a *)
    setoid_replace (a ^ (1 + 2 * (1 + p))) with (a ^ (1 + 2 * p) * (a * a)).
    do 4 rewrite <- (Qmult_assoc (a ^ (1 + 2 * p))).
    apply Qmult_comp. reflexivity.
    rewrite <- (Qmult_assoc _ a a).
    rewrite (Qmult_comm (1 # Pos.of_nat (fact (1 + 2 * Pos.to_nat p)))).
    rewrite <- (Qmult_assoc (a*a)).
    apply Qmult_comp. reflexivity.
    (* Get rid of fact *)
    unfold Qeq, Qmult, Qnum, Qden.
    rewrite Z.mul_1_l, Z.mul_1_l.
    rewrite <- (Pos2Nat.id (Pos.succ p~1 * Pos.succ (Pos.succ p~1))).
    rewrite <- Nat2Pos.inj_mul.
    2: apply fact_neq_0.
    replace (fact (1 + 2 * Pos.to_nat (1 + p)))%nat
      with (fact (1 + 2 * Pos.to_nat p) *
            Pos.to_nat (Pos.succ p~1 * Pos.succ (Pos.succ p~1)))%nat.
    reflexivity.
    rewrite Nat.mul_comm.
    replace (1 + 2 * Pos.to_nat (1 + p))%nat with (3 + 2 * Pos.to_nat p)%nat.
    change (fact (3 + 2 * Pos.to_nat p))%nat
      with ((3 + 2 * Pos.to_nat p)
            * ((2 + 2 * Pos.to_nat p) * fact (1 + 2 * Pos.to_nat p)))%nat.
    replace (Pos.to_nat (Pos.succ p~1 * Pos.succ (Pos.succ p~1)))%nat
      with ((3 + 2 * Pos.to_nat p) * ((2 + 2 * Pos.to_nat p)))%nat.
    rewrite Nat.mul_assoc.
    reflexivity.
    (* Finish equalities *)
    rewrite Pos2Nat.inj_mul.
    rewrite Nat.mul_comm. apply f_equal2.
    rewrite Pos2Nat.inj_succ.
    apply (f_equal S).
    rewrite Pos2Nat.inj_xI. reflexivity.
    rewrite Pos2Nat.inj_succ. apply (f_equal S).
    rewrite Pos2Nat.inj_succ. apply (f_equal S).
    rewrite Pos2Nat.inj_xI. reflexivity.
    rewrite Pos2Nat.inj_add. simpl.
    rewrite Nat.add_0_r, Nat.add_succ_r. reflexivity.
    intro abs.
    pose proof (Pos2Nat.is_pos (Pos.succ p~1 * Pos.succ (Pos.succ p~1))).
    rewrite abs in H. inversion H.
    rewrite <- (Qpower_plus_positive a 1 1).
    rewrite <- (Qpower_plus_positive a (1+2*p)).
    apply Qpower_positive_comp. reflexivity.
    rewrite <- Pos.add_assoc.
    apply f_equal. rewrite (Pos.add_comm 1 p).
    reflexivity.
    intro abs. discriminate.
Qed.

(** Sine is first defined on [[-1,1]] by an alternating series. *)
Lemma sinStream_alt : -1 <= a <= 1 -> Str_alt_decr _ sinStream (1%positive,a).
Proof.
  intro Ha. split.
  - (* Replace a by Qabs a *)
    rewrite Str_pth_sinStream, Str_pth_sinStream.
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
      apply (Qle_trans _ (1* (1 # Pos.of_nat (fact (1 + 2 * Pos.to_nat (Pos.succ p)))))).
      apply Qmult_le_compat_r. 2: discriminate.
      apply (Qle_trans _ (1*Qabs a)).
      apply Qmult_le_compat_r. exact Ha.
      apply Qabs_nonneg. rewrite Qmult_1_l. exact Ha.
      rewrite Qmult_1_l. unfold Qabs, Z.abs.
      unfold Qle, Qnum, Qden.
      rewrite Z.mul_1_l, Z.mul_1_l. 
      apply Pos2Nat.inj_le.
      rewrite Nat2Pos.id, Nat2Pos.id.
      2: apply fact_neq_0. 2: apply fact_neq_0.
      replace (1 + 2 * Pos.to_nat (Pos.succ p))%nat
        with (2 + (1 + 2 * Pos.to_nat p))%nat
        by (rewrite Pos2Nat.inj_succ; ring).
      apply (Nat.le_trans _ _ _ (fact_inc _)).
      apply fact_inc.
    + replace (1 + 2 * Pos.succ p)%positive with (2 + (1 + 2 * p))%positive.
      generalize (1 + 2 * p)%positive. clear p. intro p.
      unfold Qpower.
      rewrite Qpower_plus_positive. reflexivity.
      rewrite Pos.add_comm, <- Pos.add_assoc. apply f_equal.
      rewrite <- Pos.add_1_l. 
      rewrite Pos.mul_add_distr_l, Pos.mul_1_r.
      apply Pos.add_comm.
  - rewrite Str_pth_sinStream, Str_pth_sinStream.
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

Lemma sinStream_zl
  : -1 <= a <= 1
    -> Limit_zero _ sinStream (xH,a)
                 (fun e:Qpos => Pos.succ (Z.to_pos (Z.log2_up (Qceiling (/ (proj1_sig e)))))).
Proof.
  intro Ha.
  intros [e epos]. rewrite Str_pth_sinStream, Qabs_Qmult, Qabs_Qmult.
  rewrite Qabs_Qpower. change (Qabs (-1)) with 1.
  rewrite Qpower_1, Qmult_1_l.
  rewrite Qmult_comm.
  apply (Qle_trans
           _ (1 * Qabs (1 # Pos.of_nat (fact (1+2*(Pos.to_nat (Pos.succ (Z.to_pos (Z.log2_up (Qceiling (/ e))))))))))).
  apply Qmult_le_compat_r. 2: apply Qabs_nonneg.
  - rewrite (Qabs_Qpower
               a (1 + 2 * Pos.succ (Z.to_pos (Z.log2_up (Qceiling (/ ` (e ↾ epos))))))).
    apply Qpower_le_1. split.
    apply Qabs_nonneg.
    apply Qabs_Qle_condition, Ha.
  - clear Ha a.
    rewrite Qmult_1_l. unfold Qabs, Z.abs, proj1_sig.
    rewrite <- (Qinv_involutive e) at 2.
    assert (0 < /e) as H.
    { apply Qinv_lt_0_compat, epos. }
    apply (@Qinv_le_compat
             (/e) ((Pos.of_nat (fact (1+2*(Pos.to_nat (Pos.succ (Z.to_pos (Z.log2_up (Qceiling (/ e))))))))) # 1)).
    exact H.
    apply (Qle_trans _ _ _ (Qceiling_fact_le H)).
    generalize (Pos.succ (Z.to_pos (Z.log2_up (Qceiling (/ e))))).
    clear H epos e. intro p.
    unfold Qle, Qnum, Qden.
    rewrite Z.mul_1_r, Z.mul_1_r.
    apply Pos2Nat.inj_le.
    rewrite Nat2Pos.id, Nat2Pos.id.
    2: apply fact_neq_0. 2: apply fact_neq_0.
    apply fact_inc_recurse. 
    apply (Nat.le_trans (Pos.to_nat p) (1 + Pos.to_nat p)).
    apply le_S, Nat.le_refl.
    apply le_n_S.
    rewrite <- (Nat.mul_1_l (Pos.to_nat p)) at 1.
    apply Nat.mul_le_mono_nonneg_r.
    apply Nat.le_0_l. apply le_S, Nat.le_refl.
Qed.

End SinSeries.

Definition rational_sin_small (a:Q) (p: -1 <= a <= 1) : CR :=
  (inject_Q_CR a + AltSeries _ (sinStream a) (xH,a) _
                             (sinStream_alt p) (sinStream_zl p))%CR.

Lemma rational_sin_small_correct : forall (a:Q) (Ha : -1 <= a <= 1),
    (@rational_sin_small a Ha == IRasCR (Sin (inj_Q IR a)))%CR.
Proof.
  intros a Ha.
  unfold rational_sin_small.
  simpl.
  generalize (fun_series_conv_imp_conv (inj_Q IR a) (inj_Q IR a)
   (leEq_reflexive IR (inj_Q IR a)) sin_ps
     (sin_conv (inj_Q IR a) (inj_Q IR a) (leEq_reflexive IR (inj_Q IR a))
       (compact_single_iprop realline (inj_Q IR a) I)) (inj_Q IR a)
         (compact_single_prop (inj_Q IR a))
           (fun_series_inc_IR realline sin_ps sin_conv (inj_Q IR a) I)).
  intros H.
  (* Replace AltSeries by IRasCR (series_sum ...) *)
  rewrite <- (IR_inj_Q_as_CR a).
  rewrite
       (AltSeries_correct
          _ _ _ _ (sinStream_alt Ha) (sinStream_zl Ha)
          _ (AltSeries_convergent_0 _ _ _ _ (inj_Q IR a)
                                    (sinStream_alt Ha) (sinStream_zl Ha))).
  apply IRasCR_wd.
 - (* Prove the 2 series are equal in IR.
    We need to sum twice as many terms in sin_seq, to get rid of
    the zeros at even indexes. *) 
   unfold series_sum.
   apply Lim_seq_eq_Lim_subseq with (fun n => 2*n)%nat.
   intros; lia.
  intros n; exists (S n); lia.
  (* Prove that the partial sums until n are equal. *)
 intros n.
 induction n.
  apply eq_reflexive.
 replace (2*(S n))%nat with (S (S (2*n)))%nat by lia.
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
 rewrite <- cm_lft_unit.
 unfold sin_seq.
 apply bin_op_wd_unfolded.
   + destruct (even_or_odd_plus n') as [m [Hm|Hm]]; simpl.
     rational.
     elim (Nat.Even_Odd_False n');
     [ exists n; subst n'; ring |
       now exists m; rewrite Hm, Nat.add_1_r; simpl; rewrite Nat.add_0_r].
   + destruct (even_or_odd_plus (S n')) as [m [Hm|Hm]]; simpl.
  elim (Nat.Even_Odd_False (S n')).
   rewrite Hm.
   replace (m + m)%nat with (2*m)%nat by lia; now exists m.
   subst n'; exists n; ring.
 inversion Hm.
 unfold n' in H1.
 replace m with n by lia.
 clear Hm H1.
 (* Unfold sinStream *)
 transitivity (inj_Q IR ((1#Pos.of_nat (fact (1+2*n))) * ((-1)^n*a^(1+2*n))%Q)).
 clear IHn H. destruct n. simpl.
 apply inj_Q_wd. rewrite Qmult_1_l, Qmult_1_l. reflexivity.
 apply inj_Q_wd. rewrite Str_pth_sinStream.
 rewrite Nat2Pos.id. 2: discriminate. 
 replace (Z.pos (Pos.of_nat (S n))) with (Z.of_nat (S n)).
 reflexivity.
 simpl. destruct n. reflexivity.
 rewrite <- Pos.succ_of_nat. reflexivity. discriminate.
 (* Get rid of (-1)^n *)
 transitivity (inj_Q IR ((-(1))^n) [*] (inj_Q IR (a ^ (1 + 2 * n)) [*] inj_Q IR (1 # Pos.of_nat (fact (1 + 2 * n))))).
 rewrite <- inj_Q_mult, <- inj_Q_mult.
 apply inj_Q_wd. rewrite Qmult_comm. rewrite Qmult_assoc. reflexivity.
 change (inj_Q IR ((- (1)) ^ n) [*] (inj_Q IR (a ^ (1 + 2 * n))
  [*] inj_Q IR (1 # Pos.of_nat (fact (1 + 2 * n))))
               [=]
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
 rewrite <- inj_Q_mult.
  apply inj_Q_wd.
  rewrite Qmult_comm.
  apply Qmult_comp.
  replace (1 + 2 * Z.of_nat n)%Z with (Z.of_nat (1 + 2 * n)).
  reflexivity. rewrite <- (Nat2Z.inj_mul 2), <- (Nat2Z.inj_add 1).
  reflexivity. pose proof (fact_neq_0 (1+2*n)).
  destruct (fact (1+2*n)). exfalso; apply H0; reflexivity.
  simpl. destruct n0. reflexivity.
  rewrite <- Pos2SuccNat.id_succ, Nat2Pos.id.
  reflexivity. discriminate.
  (* Finish equality *)
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
   exfalso; auto with *.
  simpl; reflexivity.
 stepr ((inj_Q IR a)[^](S n')).
  apply inj_Q_power.
 change (inj_Q IR a[^]S n'[=](inj_Q IR a[-][0])[^]S n').
 apply nexp_wd.
 rational.
- intro p.
  pose proof (Pos2Nat.is_pos p). destruct (Pos.to_nat p) eqn:des.
  exfalso; inversion H0.
  rewrite <- des. rewrite Pos2Nat.id. reflexivity. 
Qed.

(** Sine's range can then be extended to [[-3^n,3^n]] by [n] applications
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

Lemma DthreeXMinusFourX3 : Derivative (clcr (inj_Q IR (-(1))) (inj_Q IR (1:Q)))
                   (inj_Q_less _ (-1) 1 eq_refl)
                   ((Three:IR){**}FId{-}(Four:IR){**}FId{^}3)
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
  apply (fun a => is_UniformlyContinuousD_Q
                 (Some (-(1))%Q) (Some (1:Q)) eq_refl _ _ DthreeXMinusFourX3 sin_poly_fun a (9#1)).
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
  lia.
 rstepr (Twelve[*]x[^]2).
 apply mult_resp_nonneg.
  apply (nring_leEq  IR 0 12).
  lia.
 apply sqr_nonneg.
Qed.

Definition sin_poly_uc : Q_as_MetricSpace --> Q_as_MetricSpace :=
Build_UniformlyContinuousFunction sin_poly_prf.

Definition sin_poly : CR --> CR
  := uc_compose compress (Cmap QPrelengthSpace sin_poly_uc).

Lemma sin_poly_correct : forall x,
    AbsSmall (inj_Q IR (1)) x
    -> (IRasCR (Three[*]x[-]Four[*]x[^]3)==sin_poly (IRasCR x))%CR.
Proof.
 intros x Hx.
 assert (Y:Continuous (clcr (inj_Q IR (-(1))) (inj_Q IR (1:Q))) ((Three:IR){**}FId{-}(Four:IR){**}FId{^}3)).
  eapply Derivative_imp_Continuous.
  apply DthreeXMinusFourX3.
  apply: (ContinuousCorrect
            (I:=(clcr (inj_Q IR (-(1))) (inj_Q IR (1:Q))))
            (inj_Q_less _ (-1) 1 eq_refl) Y);
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

Lemma shrink_by_three : forall n a,
    -(3^(S n))%Z <= a <= (3^(S n))%Z -> -(3^n)%Z <= a/3 <= (3^n)%Z.
Proof.
  intros n a H0.
  apply AbsSmall_Qabs. apply AbsSmall_Qabs in H0.
  apply Qmult_lt_0_le_reg_r with (Qabs 3).
  reflexivity. rewrite <- Qabs_Qmult.
  unfold Qdiv. rewrite <- Qmult_assoc.
  setoid_replace (/ 3 * 3) with 1 by reflexivity.
  rewrite Qmult_1_r.
  apply (Qle_trans _ _ _ H0). clear H0.
  change (Qabs 3) with (inject_Z 3).
  rewrite <- (inject_Z_mult (3^n) 3).
  rewrite <- Zle_Qle.
  change (S n) with (1+n)%nat.
  rewrite (Nat2Z.inj_add 1 n).
  rewrite ZBinary.Z.pow_add_r, Z.mul_comm.
  apply Z.le_refl.
  discriminate.
  apply (Nat2Z.inj_le 0), Nat.le_0_l.
Qed.

Fixpoint rational_sin_bounded (n:nat) (a:Q) : -(3^n)%Z <= a <= (3^n)%Z -> CR :=
match n return -(3^n)%Z <= a <= (3^n)%Z -> CR with
| O => @rational_sin_small a
| S n' => fun H => sin_poly (rational_sin_bounded n' (shrink_by_three n' H))
end.

Lemma rational_sin_bounded_correct_aux a :
  (sin_poly (IRasCR (Sin (inj_Q IR (a / 3)))) == IRasCR (Sin (inj_Q IR a)))%CR. 
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

Lemma rational_sin_bounded_correct :
  forall (n:nat) (a:Q) (Ha : -(3^n #1) <= a <= (3^n #1)),
    (@rational_sin_bounded n a Ha == IRasCR (Sin (inj_Q IR a)))%CR.
Proof.
 induction n.
  apply rational_sin_small_correct.
 intros a Ha.
 unfold rational_sin_bounded; fold rational_sin_bounded.
 rewrite -> IHn.
 apply rational_sin_bounded_correct_aux.
Qed.
End Sin_Poly.

Definition sin_bound (q:Q) : nat := Z.abs_nat (1 + Qdlog 3 (Qabs q)).

Lemma sin_bound_correct : forall q, -(3 ^ sin_bound q #1) ≤ q ≤ (3 ^ sin_bound q #1).
Proof.
  intro q.
  apply AbsSmall_Qabs.
  unfold sin_bound.
  destruct (Qlt_le_dec (Qabs q) 1).
  - apply (Qle_trans _ 1).
    apply Qlt_le_weak, q0.
    rewrite Qdlog2_le1; simpl; try easy.
    apply Qlt_le_weak, q0.
  - assert (2 ≤ 3%Z) as H by discriminate. 
    pose proof (Qdlog_spec 3 (Qabs q) H q0) as [_ H0]. clear H.
    unfold additional_operations.pow, stdlib_rationals.Q_pow in H0.
    assert (0 <= 1 + Qdlog 3 (Qabs q))%Z.
    { apply semirings.nonneg_plus_compat; [easy | now apply Qdlog_bounded_nonneg]. }
    rewrite inj_Zabs_nat, Z.abs_eq.
    apply Qlt_le_weak.
    rewrite <- Zpower_Qpower in H0. apply H0.
    exact H. exact H.
Qed. 

(** Therefore sin works on all real numbers. *)
Definition rational_sin (a:Q) : CR :=
  rational_sin_bounded (sin_bound a) (sin_bound_correct a).

Lemma rational_sin_correct : forall (a:Q),
    (rational_sin a == IRasCR (Sin (inj_Q IR a)))%CR.
Proof.
 intros; apply rational_sin_bounded_correct.
Qed.

#[global]
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
 apply rational_sin_bounded_correct_aux.
Qed.

Lemma rational_sin_correct_aux (a : Q) :
  (- IRasCR (Sin (inj_Q IR (- a)%Q)) == IRasCR (Sin (inj_Q IR a)))%CR.
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
#[global]
Hint Rewrite sin_correct : IRtoCR.
(* end hide *)
