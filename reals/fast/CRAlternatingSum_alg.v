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
Require Import CoRN.reals.iso_CReals.
Require Import CoRN.reals.Q_in_CReals.
Require Import Coq.setoid_ring.ArithRing.
Require Export CoRN.reals.fast.CRArith.
Require Import CoRN.reals.fast.CRIR.
Require Import Coq.Bool.Bool.
Require Import CoRN.algebra.COrdAbs.
Require Import CoRN.model.ordfields.Qordfield.
Require Export CoRN.model.metric2.Qmetric.
Require Import CoRN.reals.fast.LazyNat.
Require Export CoRN.metric2.Limit.
Require Import CoRN.model.totalorder.QposMinMax.
Require Import Coq.QArith.Qpower.
Require Export MathClasses.theory.CoqStreams.
Require Import CoRN.transc.PowerSeries.
Require Import CoRN.tactics.CornTac.
Require Import CoRN.classes.Qclasses.
Require Import MathClasses.interfaces.abstract_algebra MathClasses.interfaces.orders MathClasses.theory.series MathClasses.theory.streams.
Require Import CoRN.reals.fast.CRAlternatingSum.

Opaque CR.

Local Open Scope Q_scope.

(** [InfiniteAlternatingSum] is correct. *)
Lemma dnn_zl_convergent (seq : Stream Q) {dnn:DecreasingNonNegative seq}
      {zl: @Limit Q_as_MetricSpace seq 0} :
 convergent (fun n => inj_Q IR ((-(1))^n*Str_nth n seq))%Q.
Proof.
 cut (convergent (fun n : nat => [--][1][^]n[*]inj_Q IR (Str_nth n seq))).
 - apply convergent_wd.
  intros n.
  stepr ((inj_Q IR ((-(1))^n))[*](inj_Q IR (Str_nth n seq)))%Q; [| now (apply eq_symmetric; apply inj_Q_mult)].
  apply mult_wdl.
  stepr ((inj_Q IR (-(1)))[^]n); [| now (apply eq_symmetric; apply inj_Q_power)].
  apply nexp_wd.
  stepr ([--](inj_Q IR 1)); [| now (apply eq_symmetric; apply inj_Q_inv)].
  apply un_op_wd_unfolded.
  rstepl ((nring 1):IR).
  apply eq_symmetric; apply (inj_Q_nring IR 1).
 - apply alternate_series_conv.
   + intros n.
   unfold Str_nth.
   change ([0]:IR) with (nring 0:IR).
   stepl (inj_Q IR (nring 0)); [| now apply inj_Q_nring].
   apply inj_Q_leEq.
   simpl. 
   pose proof (_ : DecreasingNonNegative (Str_nth_tl n seq)) as dnn_tl.
   apply (dnn_hd_nonneg (dnn_tl)).
  + intros e He.
  destruct (Q_dense_in_CReals IR e He) as [c Hc].
  cut {N : nat | forall m : nat, (N <= m)%nat -> AbsSmall c ((Str_nth m seq))}.
   * intros [N HN].
   exists N.
   intros m Hm.
   eapply AbsSmall_trans with (inj_Q IR c).
    assumption.
   rstepr (inj_Q IR (Str_nth m seq)).
   apply inj_Q_AbsSmall.
   apply HN.
   assumption.
   * clear e He c0.
  assert (Hc':(0<c)%Q).
   apply less_inj_Q with IR.
   change (0#1)%Q with (nring O:Q).
   stepl (nring O:IR).
    exact Hc.
   apply eq_symmetric; apply (inj_Q_nring _ O).
   pose proof (Limit_near_zero (zl (Qpos2QposInf (exist _ _ Hc'))))
     as L.
  exists (takeUntil _ L (fun _ => S) O).
  generalize dnn; clear dnn.
  set (Q:= (fun seq b => DecreasingNonNegative seq -> forall m : nat, (b <= m)%nat ->
    AbsSmall (R:=Q_as_COrdField) c (Str_nth m seq))).
  change (Q seq (takeUntil (fun s : Stream Q_as_MetricSpace =>
    Qball_ex_bool (Qpos2QposInf (exist _ _ Hc')) (hd s) 0) L (fun _ : Q_as_MetricSpace => S) 0%nat)).
  apply takeUntil_elim; unfold Q; clear seq zl L Q.
   intros seq H dnn m _.
   unfold Str_nth.
   unfold Qball_ex_bool in H.
   destruct (ball_ex_dec Q_as_MetricSpace Qmetric_dec (Qpos2QposInf (exist _ _ Hc')) (hd seq) 0) as [b|b]; try contradiction.
   simpl in b.
   apply leEq_imp_AbsSmall.
    pose proof (_ : DecreasingNonNegative (Str_nth_tl m seq)) as dnn_tl.
    apply (dnn_hd_nonneg dnn_tl).
   apply dnn_alt in dnn. 
   destruct dnn as [X _].
   destruct (ForAll_Str_nth_tl m X) as [[_ Y] _]. 
   simpl.
   apply (Qle_trans _ _ _ Y).
   destruct b as [_ b].
   unfold Qminus in b.
   rewrite Qplus_0_r in b.
   exact b.
  intros x b IH H dnn [|m] Hm.
   elimtype False; auto with *.
  apply IH; auto with *.
 + intros n.
 apply inj_Q_leEq.
 destruct (ForAll_Str_nth_tl n dnn) as [[_ X] _].
 rewrite tl_nth_tl in X.
 assumption.
Qed.

Lemma InfiniteAlternatingSum_correct (seq:Stream Q) (x:nat -> IR)
 (Hx : forall n:nat, inj_Q IR (((-(1))^n)*Str_nth n seq)%Q[=]x n)
 {dnn : DecreasingNonNegative seq} {zl : @Limit Q_as_MetricSpace seq 0} H :
 (InfiniteAlternatingSum seq ==IRasCR (series_sum x H))%CR.
Proof.
 unfold series_sum.
 rewrite -> IR_Lim_as_CR.
 apply (SeqLimit_unique CRasCReals).
 intros e He.
 generalize (IR_Cauchy_prop_as_CR (Build_CauchySeq IR (seq_part_sum x) H)).
 intros C.
 destruct (C _ (pos_div_two CRasCOrdField _ He)) as [n Hn].
 exists n.
 intros m Hm.
 unfold CS_seq in *.
 clear C.
 unfold seq_part_sum in *.
 setoid_replace (@cg_minus CRasCGroup (IRasCR (Sum0 m x)) (InfiniteAlternatingSum seq))%CR
   with (((IRasCR (Sum0 (G:=IR) m x) - (IRasCR (Sum0 (G:=IR) n x))) + 
          ((IRasCR (Sum0 (G:=IR) n x) - InfiniteAlternatingSum seq))))%CR
   by (unfold cg_minus; simpl; ring).
 apply (AbsSmall_eps_div_two CRasCOrdField e
                             (IRasCR (Sum0 m x) - IRasCR (Sum0 n x))
                             (IRasCR (Sum0 n x) - InfiniteAlternatingSum seq))%CR.
 exact (Hn m Hm).
 assert (X:AbsSmall (@cf_div CRasCOrdField e _ (two_ap_zero CRasCOrdField)) (('(((-(1))^n)*(Str_nth n seq))%Q)%CR)).
 { stepr (IRasCR (x n)).
   setoid_replace (IRasCR (x n)) with (@Sum CRasCAbGroup n n (fun n => IRasCR (x n))).
   2: rewrite Sum_one; reflexivity.
   unfold Sum, Sum1.
   rewrite <- IR_Sum0_as_CR, <- IR_Sum0_as_CR.
   apply Hn.
   auto.
  simpl.
  symmetry.
  rewrite <- IR_inj_Q_as_CR.
  apply IRasCR_wd.
  apply Hx. }
 stepr (('(Sum0 n (fun n => ((-(1))^n)*(Str_nth n seq))%Q))%CR - InfiniteAlternatingSum seq)%CR.
  clear - X.
  generalize seq dnn zl X.
  clear seq dnn zl X.
  change (@AbsSmall (crl_crr CRasCReals) (e [/]TwoNZ))
    with (@AbsSmall CRasCOrdField (@cf_div CRasCOrdField e _ (two_ap_zero CRasCOrdField))).
  generalize (@cf_div CRasCOrdField e _ (two_ap_zero CRasCOrdField)). clear e.
  induction n; intros e seq dnn zl X.
 - simpl in *.
   apply (AbsSmall_minus CRasCOrdField e (InfiniteAlternatingSum seq) 0%CR).
   stepr (InfiniteAlternatingSum seq).
   2: (unfold cg_minus;simpl;unfold msp_Equiv;ring).
   apply leEq_imp_AbsSmall;[apply InfiniteAlternatingSum_nonneg|].
   eapply leEq_transitive;simpl.
    apply InfiniteAlternatingSum_bound.
   assert ((hd seq)%CR == (1*hd seq)%Q). ring. rewrite -> H. clear H.
   destruct X; assumption.
 - pose proof (AbsSmall_minus CRasCOrdField e (InfiniteAlternatingSum seq)
         (' Sum0 (S n) (λ n0 : nat, ((- (1)) ^ n0 * Str_nth n0 seq)%Q))).
   apply H. clear H.
  stepr (('(((Sum0 (G:=Q_as_CAbGroup) n (fun n0 : nat =>  ((- (1)) ^ n0 * Str_nth n0 (tl seq))%Q)))%CR) - 
    InfiniteAlternatingSum (tl seq)))%CR; [apply IHn|].
  pose proof (CRopp_opp ('(((- (1)) ^ n * Str_nth n (tl seq))%Q))).
  rewrite <- H. clear H.
   apply inv_resp_AbsSmall.
   rewrite inj_S in X.
   stepr (' ((- (1)) ^ Z.succ n * Str_nth (S n) seq)%Q)%CR;[assumption|].
   simpl.
   change ((' ( (- (1)) ^ (n+1) * Str_nth n (tl seq))%Q == - ' ((- (1)) ^ n * Str_nth n (tl seq))%Q)%CR).
   rewrite -> Qpower_plus;[|discriminate]. 
   simpl. ring.
  stepl (InfiniteAlternatingSum seq - (('(((- (1)) ^ 0 * Str_nth 0 seq) + 
    ((Sum0 (G:=Q_as_CAbGroup) n
           (fun n0 : nat => ((- (1)) ^ (S n0) * Str_nth n0 (tl seq))%Q))))%Q)))%CR.
  apply CRplus_eq_r.
  apply uc_wd, inject_Q_CR_wd.
  apply Sum0_shift; intros i; simpl; reflexivity.
  unfold cg_minus; simpl.
  rewrite -> InfiniteAlternatingSum_step.
  generalize (@InfiniteAlternatingSum (tl seq) _).
  intros x.
  change (Str_nth 0 seq) with (hd seq).
  setoid_replace ((Sum0 (G:=Q_as_CAbGroup) n
    (fun n0 : nat => Qpower_positive (- (1)) (P_of_succ_nat n0)  * Str_nth n0 (tl seq)))%Q:Q)
      with (-(Sum0 (G:=Q_as_CAbGroup) n
        (fun n0 : nat => ((- (1)) ^ n0 * Str_nth n0 (tl seq)))))%Q.
   simpl. unfold msp_Equiv. ring.
  eapply eq_transitive;[|apply (inv_Sum0 Q_as_CAbGroup)].
  apply: Sum0_wd.
  intros i; simpl.
  change (Qpower_positive (- (1)) (P_of_succ_nat i)) with ((-(1))^ S i).
  rewrite inj_S.
  unfold Z.succ.
  rewrite -> Qpower_plus;[|discriminate].
  ring.
 - apply CRplus_eq_l.
   rewrite -> IR_Sum0_as_CR.
 clear - Hx.
 induction n.
  reflexivity.
 change ((' (Sum0 (G:=Q_as_CAbGroup) n (fun n0 : nat => ((- (1)) ^ n0 * Str_nth n0 seq)) +
   (- (1)) ^ n * Str_nth n seq)%Q ==
     (Sum0 (G:=CRasCAbGroup) n (fun n0 : nat => IRasCR (x n0)):CR) + IRasCR (x n))%CR).
 rewrite <- CRplus_Qplus.
 apply ucFun2_wd;[apply IHn|].
 transitivity (IRasCR (inj_Q IR ((- (1)) ^ n * Str_nth n seq)%Q)); [symmetry;apply IR_inj_Q_as_CR|].
 apply IRasCR_wd.
 apply Hx.
Qed.

Lemma InfiniteAlternatingSum_correct' (seq:Stream Q)
 {dnn:DecreasingNonNegative seq} {zl : @Limit Q_as_MetricSpace seq 0} :
 (InfiniteAlternatingSum seq == IRasCR (series_sum _ (dnn_zl_convergent seq)))%CR.
Proof.
 apply InfiniteAlternatingSum_correct.
 intros; apply eq_reflexive.
Qed.

