Require Import
        MathClasses.interfaces.abstract_algebra 
        MathClasses.theory.nat_pow
        MathClasses.theory.int_pow
        CoRN.algebra.RSetoid
        CoRN.stdlib_omissions.Q
        CoRN.metric2.Metric
        CoRN.metric2.UniformContinuity
        CoRN.reals.fast.CRarctan_small
        CoRN.reals.fast.CRarctan
        CoRN.reals.fast.CRstreams
        CoRN.reals.fast.CRAlternatingSum
        CoRN.reals.faster.ARAlternatingSum
        CoRN.reals.faster.ARsin.
Require Export
  CoRN.reals.faster.ARArith.

Section ARarctan_small.
Context `{AppRationals AQ}
        {num den : AQ} (Pnd : -den < num < den) (dpos : 0 < den).

(*
Split the stream 
  (-1)^i a^(2i+1) / (2i+1)
up into the streams
  (-1)^i a^(2i+1)    and    (2i+1)
because we do not have exact division
*)
Definition ARarctanStream (px : positive*(AQ*AQ)) : AQ*AQ
  := (- fst (snd px) * num * num * ZtoAQ (Zpos (Pos.pred (fst px)~0)),
      snd (snd px) * den * den * ZtoAQ (Zpos (fst px)~1)).

Lemma arctanStream_pos : ∀ x : positive * (AQ * AQ),
    0 < snd (snd x) → 0 < snd (ARarctanStream x).
Proof.
  assert (0 = ZtoAQ 0) as zero_int.
  { destruct H4. destruct aq_ints_mor, semiringmor_plus_mor.
    rewrite preserves_mon_unit. reflexivity. }
  intros. destruct x; simpl.
  simpl in H5.
  apply AQmult_lt_0_compat.
  apply AQmult_lt_0_compat.
  apply AQmult_lt_0_compat.
  exact H5. exact dpos. exact dpos.
  rewrite zero_int.
  apply (strictly_order_preserving (cast Z AQ)).
  reflexivity.
Qed.

Lemma arctanStream_correct : ∀ p : positive,
    Str_pth _ (arctanStream (AQtoQ num / AQtoQ den))
            p (1%positive, AQtoQ num / AQtoQ den)
    == let (_, r) := iterate _ (fS ARarctanStream) p (1%positive, (num, den)) in
       AQtoQ (fst r) / AQtoQ (snd r).
Proof.
  assert (forall n:Z, AQtoQ (ZtoAQ n) == (n#1)).
  { intro n. destruct n as [|n|n].
    pose proof (rings.preserves_0 (f:=cast Z AQ)). rewrite H5. clear H5.
    rewrite rings.preserves_0. reflexivity.
    apply ZtoQ. change (Z.neg n) with (-Z.pos n)%Z.
    pose proof (rings.preserves_negate (f:=cast Z AQ)).
    rewrite H5. clear H5. rewrite rings.preserves_negate.
    rewrite ZtoQ. reflexivity. } 
  apply Pos.peano_ind.
  - unfold Str_pth, iterate, arctanStream, snd.
    rewrite Qred_correct. simpl.
    do 6 rewrite rings.preserves_mult.
    rewrite rings.preserves_negate.
    rewrite H5, H5.
    unfold dec_recip, stdlib_rationals.Q_recip.
    unfold mult, stdlib_rationals.Q_mult.
    unfold negate, stdlib_rationals.Q_opp.
    rewrite Qmult_1_r.
    change (1#3) with (/3)%Q.
    unfold Qdiv.
    do 3 rewrite Qinv_mult_distr.
    do 3 rewrite Qmult_assoc.
    apply Qmult_comp. 2: reflexivity.
    do 2 rewrite Qmult_assoc.
    apply Qmult_comp. 2: reflexivity.
    ring.
  - intros p IHp. unfold Str_pth. unfold Str_pth in IHp.
    rewrite iterate_succ, iterate_succ.
    pose proof (arctanStream_fst (AQtoQ num / AQtoQ den) p) as H7.
    unfold dec_recip, stdlib_rationals.Q_recip.
    unfold dec_recip, stdlib_rationals.Q_recip in IHp.
    unfold mult, stdlib_rationals.Q_mult.
    unfold mult, stdlib_rationals.Q_mult in IHp.
    unfold Qdiv in H7. unfold Qdiv.
    unfold Qdiv in IHp.
    unfold Q_as_MetricSpace, msp_car.
    unfold Q_as_MetricSpace, msp_car in IHp.
    destruct (iterate _ (arctanStream (AQtoQ num * / AQtoQ den)%Q) p
            (1%positive, (AQtoQ num * / AQtoQ den)%Q)).
    simpl in H7. simpl in IHp. subst p0.
    unfold arctanStream, snd, fst. rewrite Qred_correct.
    rewrite IHp. clear IHp.
    pose proof (fS_fst ARarctanStream p (num, den)) as H6.
    destruct (iterate _ (fS ARarctanStream) p (1%positive, (num, den))) as [p0 p1].
    simpl in H6. subst p0. unfold ARarctanStream, fS.
    simpl (fst (Pos.succ p, p1)).
    simpl (snd (Pos.succ p, p1)).
    replace (Pos.pred (Pos.succ p)~0) with (p~1)%positive.
    do 6 rewrite rings.preserves_mult.
    rewrite rings.preserves_negate.
    unfold mult, stdlib_rationals.Q_mult.
    unfold negate, stdlib_rationals.Q_opp.
    rewrite ZtoQ, ZtoQ.
    do 3 rewrite Qinv_mult_distr.
    setoid_replace (Z.pos p~1 # 2 + p~1)%Q
      with ((Z.pos p~1 # 1) * / (Z.pos (Pos.succ p)~1 # 1))%Q.
    ring.
    unfold Qinv, Qeq, Qmult, Qnum, Qden.
    rewrite Pos.mul_1_l, Z.mul_1_r.
    replace (2 + p~1)%positive with ((Pos.succ p)~1)%positive.
    reflexivity.
    change (p~1)%positive with (2*p+1)%positive.
    change ((Pos.succ p)~1)%positive with (2*Pos.succ p+1)%positive.
    rewrite Pplus_one_succ_l.
    rewrite Pos.mul_add_distr_l. reflexivity.
    rewrite Pplus_one_succ_l.
    change (p~1)%positive with (2*p+1)%positive.
    change ((1+p)~0)%positive with (2*(1+p))%positive.
    rewrite Pos.mul_add_distr_l.
    rewrite Pos.pred_sub.
    rewrite (Pos.add_comm (2*1)).
    rewrite <- Pos.add_sub_assoc. reflexivity. reflexivity.
Qed.

Lemma AQarctan_small_Qprf : -1 < AQtoQ num / AQtoQ den < 1.
Proof.
  split.
  - apply Qlt_shift_div_l.
    pose proof (rings.preserves_0 (f:=cast AQ Q)).
    rewrite <- H5.
    apply (strictly_order_preserving (cast AQ Q)), dpos.
    setoid_replace (-1 * AQtoQ den) with (-AQtoQ den) by reflexivity.
    rewrite <- rings.preserves_negate.
    apply (strictly_order_preserving (cast AQ Q)), Pnd.
  - apply Qlt_shift_div_r.
    pose proof (rings.preserves_0 (f:=cast AQ Q)).
    rewrite <- H5.
    apply (strictly_order_preserving (cast AQ Q)), dpos.
    rewrite Qmult_1_l.
    apply (strictly_order_preserving (cast AQ Q)), Pnd.
Qed.

Definition AQarctan_small : msp_car AR
  := CRtoAR (inject_Q_CR (AQtoQ num / AQtoQ den))
     + AltSeries ARarctanStream arctanStream_pos
                 positive (arctanStream (AQtoQ num / AQtoQ den))
                 (num,den) (xH,AQtoQ num / AQtoQ den) arctanStream_correct _
                 (arctanStream_alt (widen_interval AQarctan_small_Qprf))
                 dpos (arctanStream_zl (widen_interval AQarctan_small_Qprf)).

Lemma AQarctan_small_correct : 
  'AQarctan_small = rational_arctan_small (widen_interval AQarctan_small_Qprf).
Proof.
  unfold AQarctan_small, rational_arctan_small.
  rewrite ARtoCR_preserves_plus.
  apply ucFun2_wd.
  pose proof CRAR_id.
  unfold cast. unfold cast in H5.
  rewrite H5. reflexivity.
  apply AltSeries_correct.
Qed.

End ARarctan_small.
