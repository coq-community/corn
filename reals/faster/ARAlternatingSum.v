From Coq Require Import Qabs.
Require Import CoRN.util.Qdlog
        CoRN.algebra.RSetoid
        CoRN.model.totalorder.QposMinMax
        CoRN.model.metric2.Qmetric
        CoRN.model.reals.CRreal
        CoRN.metric2.Metric
        CoRN.metric2.UniformContinuity
        CoRN.reals.fast.CRAlternatingSum
        CoRN.reals.fast.CRstreams
        CoRN.reals.faster.ApproximateRationals
        CoRN.reals.faster.ARArith.


(**
The goal of this section is to compute the infinite alternating sum. Since 
we do not have a precise division operation, we want to postpone divisions as 
long as possible. Hence we parametrize our infinite sum by a stream [sN] 
of numerators and a stream [sD] of denominators.

To compute an infinite series at precision epsilon, the finite number n of
terms to sum can be computed exactly, because sN n / sD n < epsilon/2 is
equivalent to sN n < (sD n) * epsilon/2, which does not involve the approximate
division. In the other epsilon/2, we can approximate the n divisions at
precision 2^k such as n*2^k < epsilon/2.
*)

Section RationalStreamSum.

  Context `{AppRationals AQ}.

  (* For exponential, f p n d := (n*a, d*p).
     We might need to generalize positive to a more complicated
     state type later. *)
  Variable f : positive*(AQ*AQ) -> AQ*AQ.
  Definition fS x : positive*(AQ*AQ) := (Pos.succ (fst x), f x).
  Definition fSsum (k:Z) (x : positive*(AQ*AQ)*AQ) : positive*(AQ*AQ)*AQ
    := let (y,s) := x in
       let (a,b) := fS y in
       (a, b, s + app_div (fst b) (snd b) k).

  Hypothesis denomPos : forall x, 0 < snd (snd x) -> 0 < snd (f x).

  Lemma denomPos_iter : forall p x,
      0 < snd (snd x) -> 
      0 < snd (snd (CRstreams.iterate _ fS p x)).
  Proof.
    apply (Pos.peano_ind (fun p => forall x,
      0 < snd (snd x) -> 
      0 < snd (snd (CRstreams.iterate _ fS p x)))).
    - intros. simpl. apply denomPos, H5.
    - intros. rewrite iterate_succ, iterate_shift.
      apply H5. simpl. 
      apply denomPos, H6.
  Qed. 

  (* Find first index where num/denom <= e. *)
  Definition IsStopIndex x (e : AQ) (candidate : positive) : Prop
    := let (_,v) := CRstreams.iterate _ fS candidate (xH,x) in
       le (abs (fst v)) (snd v * e).
  Definition StopIndex x (e : AQ) (candidate : positive) : positive
    := Pos.pred (fst (iterate_stop
              _ fS (fun y : positive*(AQ*AQ)
                    => bool_decide_rel le (abs (fst (snd y))) ((snd (snd y))*e))
              candidate (xH, x))).

  Lemma fS_fst : forall (p:positive) x,
      fst (CRstreams.iterate (positive and AQ and AQ) fS p (1%positive, x))
          ≡ Pos.succ p.
  Proof.
    apply (Pos.peano_ind (fun p => forall (x : AQ and AQ),
    fst (CRstreams.iterate (positive and AQ and AQ) fS p (1%positive, x)) ≡ Pos.succ p)).
    - reflexivity.
    - intros. rewrite iterate_succ. simpl.
      apply f_equal, H5.
  Qed. 

  Lemma StopIndex_correct : forall x (e:AQ) (p r : positive),
      IsStopIndex x e p
      -> (forall q:positive, Pos.lt q p -> ~IsStopIndex x e q)
      -> Pos.le p r
      -> StopIndex x e r ≡ p.
  Proof.
    unfold IsStopIndex. intros.
    unfold StopIndex.
    destruct (iterate_stop_correct
                  _ fS (fun y : positive and AQ and AQ =>
                              bool_decide_rel
                                le (abs (fst (snd y))) (snd (snd y) * e0))
               r (xH,x)) as [s [req [H8 H9]]].
    rewrite req, fS_fst, Pos.pred_succ. clear req.
    destruct H9.
    - subst r. apply Pos.le_lteq in H7.
      destruct H7. 2: symmetry; exact H7.
      exfalso. specialize (H8 p H7).
      apply bool_decide_rel_false in H8.
      contradict H8. 
      destruct (CRstreams.iterate _ fS p (1%positive, x)).
      exact H5.
    - destruct H9.
      apply bool_decide_rel_true in H10.
      clear H7 H9 r.
      destruct (Pos.lt_total s p).
      + exfalso. specialize (H6 s H7).
        contradict H6.
        destruct (CRstreams.iterate _ fS s (1%positive, x)).
        exact H10.
      + destruct H7. exact H7. exfalso.
        specialize (H8 p H7).
        apply bool_decide_rel_false in H8.
        contradict H8.
      destruct (CRstreams.iterate _ fS p (1%positive, x)).
      exact H5.
  Qed.

  Lemma StopIndex_stop_fuel : forall x (e:AQ) (candidate : positive),
      (forall p:positive, Pos.lt p candidate -> ~IsStopIndex x e p)
      -> StopIndex x e candidate ≡ candidate.
  Proof.
    intros. unfold StopIndex.
    destruct (iterate_stop_correct
                  _ fS (fun y : positive and AQ and AQ =>
                              bool_decide_rel
                                le (abs (fst (snd y))) (snd (snd y) * e0))
               candidate (xH,x)) as [r [req [H6 H7]]].
    rewrite req, fS_fst, Pos.pred_succ. clear req.
    destruct H7. symmetry. exact H7.
    destruct H7. exfalso. clear H6.
    specialize (H5 r H7).
    apply bool_decide_rel_true in H8.
    contradict H5.
    unfold IsStopIndex.
    destruct (CRstreams.iterate _ fS r (1%positive, x)).
    exact H8.
  Qed. 

  (* Approximate the infinite series at precision e.
     The precision i:Z in fSum satisfies n*2^i <= e/2. *)
  Definition app_inverse_below (q : Qpos) : AQ
    := AppInverse0 ((3#4)*proj1_sig q) ((1#4)*q)%Qpos.

  Lemma app_inverse_below_pos : forall q:Qpos, 0 < app_inverse_below q.
  Proof.
    intros. unfold app_inverse_below.
    destruct aq_dense_embedding.
    specialize (dense_inverse ((3 # 4) * ` q)%Q ((1#4)*q)%Qpos).
    apply AbsSmall_Qabs, Qabs_Qle_condition in dense_inverse.
    destruct dense_inverse as [H5 _].
    simpl in H5.
    apply (Qplus_le_r _ _ ((3 # 4) * ` q)) in H5.
    ring_simplify in H5.
    destruct aq_strict_order_embed.
    apply strict_order_embedding_reflecting.
    refine (Qlt_le_trans _ ((8 # 16) * ` q) _ _ H5).
    rewrite rings.preserves_0.
    apply (Qpos_ispos ((8#16)*q)).
  Qed.

  Lemma app_inverse_below_correct : forall q:Qpos,
      AQtoQ (app_inverse_below q) <= proj1_sig q.
  Proof.
    intros. unfold app_inverse_below.
    destruct aq_dense_embedding.
    specialize (dense_inverse ((3 # 4) * ` q)%Q ((1#4)*q)%Qpos).
    apply AbsSmall_Qabs, Qabs_Qle_condition in dense_inverse.
    destruct dense_inverse as [_ H5].
    simpl in H5.
    apply (Qplus_le_r _ _ ((3 # 4) * ` q)) in H5.
    ring_simplify in H5. exact H5.
  Qed.

  (* cvmod : AQ->positive would not improve this definition, because an
     AQtoQ would be almost inevitable to produce a boxed positive.
     Besides, Q will allow an easier interaction with fast reals streams. *)
  Definition AltSeries_raw (x : AQ*AQ) (cvmod : Qpos -> positive) (e:QposInf) : AQ
    := match e with 
       | Qpos2QposInf d
         => let ae := app_inverse_below (d*(1#2)) in
           let n := StopIndex x ae (cvmod (d * (1#2))%Qpos) in
           snd (CRstreams.iterate _ (fSsum (Qdlog2 (proj1_sig d * (1#2*n)))) n (xH,x,0))
       | QposInfinity => 0
       end.

  (* To prove the correctness of the limit, convert the stream f into
     a stream g of exact rationals. g could be defined as the zip of
     f with the exact divisions, but it's more flexible to take g from
     outside, so that in addition we prove the equality of series. *)
  Variable X : Type.
  Variable g : X*Q -> X*Q.
  Variable fInit : AQ*AQ.
  Variable gInit : X*Q.

  Hypothesis g_pth : forall p:positive,
      Str_pth _ g p gInit
      == let (y,r) := CRstreams.iterate _ fS p (xH, fInit) in
         AQtoQ (fst r) / AQtoQ (snd r).

  Lemma abs_div_aqtoq_shift : forall (q r s : AQ),
      0 < r ->
      (Qabs (AQtoQ q / AQtoQ r) <= AQtoQ s
       <-> le (abs q) (r * s)).
  Proof.
    assert (forall q:AQ, Qabs (AQtoQ q) == AQtoQ (abs q)) as preserves_abs.
    { intros. rewrite abs.preserves_abs. reflexivity. } 
    assert (forall q r:AQ, AQtoQ (q*r) == AQtoQ q*AQtoQ r) as preserves_mult.
    { intros. rewrite rings.preserves_mult. reflexivity. } 
    intros.
    assert (0 < AQtoQ r).
    { rewrite <- rings.preserves_0.
      destruct aq_strict_order_embed.
      apply strict_order_embedding_preserving. exact H5. } 
    split.
    - intros. unfold Qdiv in H7.
      rewrite Qabs_Qmult, Q.Qabs_Qinv in H7.
      rewrite (Qabs_pos (AQtoQ r)) in H7.
      rewrite preserves_abs, Qmult_comm in H7.
      apply (Qmult_le_l _ _ (AQtoQ r)) in H7.
      2: exact H6.
      rewrite Qmult_assoc, Qmult_inv_r, Qmult_1_l in H7.
      rewrite <- preserves_mult in H7.
      destruct aq_order_embed, order_embedding_reflecting.
      apply order_reflecting in H7.
      exact H7.
      intro abs. rewrite abs in H6. exact (Qlt_irrefl 0 H6).
      apply Qlt_le_weak, H6. 
    - intros. unfold Qdiv.
      rewrite Qabs_Qmult, Q.Qabs_Qinv.
      rewrite (Qabs_pos (AQtoQ r)).
      rewrite preserves_abs.
      rewrite Qmult_comm.
      apply (Qmult_le_l _ _ (AQtoQ r)).
      exact H6.
      rewrite Qmult_assoc, Qmult_inv_r, Qmult_1_l. 
      rewrite <- preserves_mult.
      destruct aq_order_embed.
      apply order_embedding_preserving.
      exact H7.
      intro abs. rewrite abs in H6. exact (Qlt_irrefl 0 H6).
      apply Qlt_le_weak, H6. 
  Qed.

  Lemma fSsum_fst : forall p k,
      fst (CRstreams.iterate _ (fSsum k) p (1%positive, fInit, 0))
          ≡ CRstreams.iterate _ fS p (xH,fInit).
  Proof.
    apply (Pos.peano_ind (fun p => forall k,
      fst (CRstreams.iterate _ (fSsum k) p (1%positive, fInit, 0))
          ≡ CRstreams.iterate _ fS p (xH,fInit))).
    - reflexivity.
    - intros. rewrite iterate_succ, iterate_succ.
      rewrite <- (H5 k). unfold fSsum at 1.
      destruct (CRstreams.iterate ((positive and AQ and AQ) and AQ) 
                                  (fSsum k) p (1%positive, fInit, 0)).
      reflexivity.
  Qed.

  (* Sum p terms, the error between each is below e. *)
  Lemma div_approx_error : ∀ (p:positive) (e:Qpos),
    Qball (` e * inject_Z (Zpos p))
      (AQtoQ (snd (CRstreams.iterate
                     _ (fSsum (Qdlog2 (` e))) p (1%positive, fInit, 0))))
      (snd (CRstreams.iterate
              _ (fun y : X*Q*Q =>
                       let (z, r) := g (fst y) in (z, r, Qred (r + snd y))) p
              (gInit, 0))).
  Proof.
    apply (Pos.peano_ind (fun p => forall (e:Qpos),
    Qball (` e * inject_Z (Zpos p))
      (AQtoQ (snd (CRstreams.iterate
                     _ (fSsum (Qdlog2 (` e))) p (1%positive, fInit, 0))))
      (snd (CRstreams.iterate
              _ (fun y : X*Q*Q =>
                       let (z, r) := g (fst y) in (z, r, Qred (r + snd y))) p
              (gInit, 0))))).
    - intros. rewrite iterate_one, iterate_one.
      rewrite Qmult_1_r.
      unfold fSsum, fS.
      unfold snd at 1. unfold fst at 2.
      pose proof (g_pth 1).
      unfold Str_pth in H5. simpl in H5.
      unfold snd at 3.
      replace (snd (let (z, r) := g gInit in (z, r, Qred (r + zero))))
        with (Qred (snd (g gInit) + 0))
        by (destruct (g gInit); reflexivity).
      rewrite Qred_correct, Qplus_0_r, H5.
      clear H5.
      destruct (f (1%positive, fInit)) as [u v].
      unfold snd, fst.
      rewrite rings.plus_0_l.
      apply ball_weak_le with (e:= (2 ^ Qdlog2 (` e0))%Q).
      apply Qdlog2_spec, Qpos_ispos.
      apply aq_div.
    - intros.
      rewrite iterate_succ.
      unfold fSsum at 1.
      specialize (H5 e0).
      pose proof (fSsum_fst p (Qdlog2 (` e0))).
      destruct (CRstreams.iterate _ (fSsum (Qdlog2 (` e0))) p (1%positive, fInit, 0))
        as [u approx_sum].
      unfold snd in H5 at 1.
      unfold fst in H6.
      change (snd
          (let (a, b) := fS u in (a, b, approx_sum + app_div (fst b) (snd b) (Qdlog2 (` e0)))))
        with (approx_sum + app_div (fst (snd (fS u))) (snd (snd (fS u))) (Qdlog2 (` e0))).
      rewrite iterate_succ, SumStream_fst_red.
      unfold fst at 2.
      rewrite <- iterate_succ.
      pose proof (g_pth (Pos.succ p)) as H7.
      unfold Str_pth in H7.
      destruct (CRstreams.iterate (X and Q) g (Pos.succ p) gInit).
      unfold snd at 4. unfold snd in H7 at 1.
      rewrite Qred_correct, H7. clear H7 q x.
      rewrite iterate_succ.
      rewrite <- H6. clear H6.
      destruct (fS u) as [v w].
      change (snd (v,w)) with w.
      clear v.
      destruct (CRstreams.iterate _
          (fun y : (X and Q) and Q =>
             let (z, r) := g (fst y) in (z, r, Qred (r + snd y))) p
          (gInit, 0))
        as [v exact_sum].
      unfold snd in H5.
      unfold snd at 3. clear v.
      destruct w as [v w].
      unfold fst, snd.
      rewrite rings.preserves_plus. 
      apply AbsSmall_Qabs.
      apply AbsSmall_Qabs in H5.
      setoid_replace ((AQtoQ approx_sum + AQtoQ (app_div v w (Qdlog2 (` e0)))) -
                      (AQtoQ v / AQtoQ w + exact_sum))%Q
        with (AQtoQ approx_sum - exact_sum
              + (AQtoQ (app_div v w (Qdlog2 (` e0))) - (AQtoQ v / AQtoQ w)))%Q
        by ring.
      apply (Qle_trans _ _ _ (Qabs_triangle _ _)).
      rewrite <- Pos.add_1_r, Pos2Z.inj_add, inject_Z_plus.
      rewrite Qmult_plus_distr_r, Qmult_1_r.
      apply Qplus_le_compat. exact H5.
      apply AbsSmall_Qabs.
      change (Qball (` e0) (AQtoQ (app_div v w (Qdlog2 (` e0)))) (AQtoQ v / AQtoQ w)).
      apply ball_weak_le with (e:= (2 ^ Qdlog2 (` e0))%Q).
      apply Qdlog2_spec, Qpos_ispos.
      apply aq_div.
  Qed.
   
  (* SumStream is the implementation of CRAlternatingSum.AltSeries_raw.
     Errors only come from approximate divisions here. *)
  Lemma AltSeries_raw_correct : forall (e:Qpos) (cvmod : Qpos -> positive),
      0 < snd fInit -> 
      Qball (` e * (1 # 2))
            (AQtoQ (AltSeries_raw fInit cvmod (Qpos2QposInf e)))
            (SumStream
               _ g gInit
               (cvmod (e * (1 # 2))%Qpos) (* fuel *)
               (AQposAsQpos (exist _ _ (app_inverse_below_pos (e * (1 # 2))%Qpos)))).
  Proof. 
    intros e0 cvmod xpos.
    unfold SumStream.
    change (` (AQposAsQpos
                 (app_inverse_below (e0 * (1 # 2))%Qpos
                            ↾ app_inverse_below_pos (e0 * (1 # 2))%Qpos)))
      with (AQtoQ (app_inverse_below (e0 * (1 # 2))%Qpos)).
    pose proof (iterate_stop_correct
                  _ (fun y : (X and Q) and Q =>
                           let (z, r) := g (fst y) in (z, r, Qred (r + snd y)))
                  (fun y : (X and Q) and Q =>
             Qle_bool (Qabs (snd (fst y)))
               (AQtoQ (app_inverse_below (e0 * (1 # 2) ↾ eq_refl))))
              (cvmod (e0 * (1 # 2))%Qpos) (gInit,0))
      as [p [qeq [H5 H6]]].
    rewrite qeq. clear qeq.
    unfold AltSeries_raw.
    replace (StopIndex fInit (app_inverse_below (e0 * (1 # 2) ↾ eq_refl))
                       (cvmod (e0 * (1 # 2))%Qpos))
      with p.
    setoid_replace (` e0 * (1 # 2))%Q
      with (` e0 * (1 # 2 * p) * inject_Z (Zpos p))%Q.
    apply (div_approx_error p (e0*(1#2*p))).
    rewrite <- Qmult_assoc. apply Qmult_comp. reflexivity.
    unfold Qmult, Qeq; simpl.
    rewrite Pos.mul_1_r, Pos.mul_comm. reflexivity.
    rewrite SumStream_fst_red in H6.
    destruct H6 as [fuel | predicate].
    - (* The sum consumes all the fuel. *)
      subst p.
      symmetry. apply StopIndex_stop_fuel.
      intros. specialize (H5 p H6).
      rewrite SumStream_fst_red in H5.
      unfold fst in H5.
      unfold IsStopIndex. intro abs.
      pose proof (g_pth p). unfold Str_pth in H7.
      rewrite H7 in H5. clear H7.
      pose proof (denomPos_iter p (xH,fInit) xpos).
      destruct (CRstreams.iterate _ fS p (1%positive, fInit))
        as [u v].
      apply abs_div_aqtoq_shift in abs.
      apply Qle_bool_iff in abs.
      rewrite abs in H5. discriminate.
      exact H7.
    - (* The sum stops before the fuel, because of the predicate. *)
      assert (IsStopIndex fInit (app_inverse_below (e0 * (1 # 2))%Qpos) p) as pstop.
      { destruct predicate as [_ predicate]. unfold IsStopIndex.
        apply Qle_bool_iff in predicate.
        simpl in predicate.
        pose proof (g_pth p).
        unfold Str_pth in H6. rewrite H6 in predicate. clear H6.
        pose proof (denomPos_iter p (xH,fInit) xpos). 
        destruct (CRstreams.iterate _ fS p (1%positive, fInit)).
        apply abs_div_aqtoq_shift. exact H6.
        exact predicate. } 
      symmetry. apply StopIndex_correct.
      exact pstop. intros.
      unfold IsStopIndex.
      specialize (H5 q H6).
      rewrite SumStream_fst_red in H5. unfold fst in H5.
      pose proof (g_pth q).
      unfold Str_pth in H7. rewrite H7 in H5. clear H7.
      pose proof (denomPos_iter q (xH,fInit) xpos).
      destruct (CRstreams.iterate _ fS q (1%positive, fInit)).
      intro abs.
      apply abs_div_aqtoq_shift in abs.
      apply Qle_bool_iff in abs.
      rewrite abs in H5. discriminate.
      exact H7. apply Pos.lt_le_incl, predicate.
  Qed.

  Lemma AltSeries_raw_prf : forall (cvmod : Qpos -> positive),
      Str_alt_decr _ g gInit
      -> 0 < snd fInit
      -> Limit_zero _ g gInit cvmod -> 
      is_RegularFunction (@ball AQ_as_MetricSpace) (AltSeries_raw fInit cvmod).
  Proof.
    intros cvmod g_decr xpos lz e1 e2.
    setoid_replace (`e1 + `e2)%Q
      with (`e1*(1#2) + (`e1*(1#2) + `e2*(1#2) + `e2*(1#2)))%Q by ring.
    apply (ball_triangle Q_as_MetricSpace _ _ _
      (SumStream
                   _ g gInit
                   (cvmod (e1 * (1 # 2))%Qpos)
                   (AQposAsQpos (exist _ _ (app_inverse_below_pos (e1 * (1 # 2))%Qpos))))).
    2: apply (ball_triangle Q_as_MetricSpace _ _ _
      (SumStream
                   _ g gInit
                   (cvmod (e2 * (1 # 2))%Qpos)
                   (AQposAsQpos (exist _ _ (app_inverse_below_pos (e2 * (1 # 2))%Qpos))))).
    - exact (AltSeries_raw_correct _ _ xpos).
    - apply (AltSeries_further
               _ g gInit _ _ _ _
               (e1 * (1 # 2))%Qpos (e2 * (1 # 2))%Qpos g_decr).
      apply lz. apply lz.
      apply app_inverse_below_correct.
      apply app_inverse_below_correct.
    - apply ball_sym, (AltSeries_raw_correct _ _ xpos).
  Qed.

  Definition AltSeries (cvmod : Qpos -> positive)
      (decr : Str_alt_decr _ g gInit)
      (xpos : 0 < snd fInit)
      (lz : Limit_zero _ g gInit cvmod) : msp_car AR
    := Build_RegularFunction (AltSeries_raw_prf cvmod decr xpos lz).

  Lemma AltSeries_correct : forall (cvmod : Qpos -> positive)
      (decr : Str_alt_decr _ g gInit)
      (xpos : 0 < snd fInit)
      (lz : Limit_zero _ g gInit cvmod),
      (ARtoCR (AltSeries cvmod decr xpos lz)
       == CRAlternatingSum.AltSeries _ g gInit cvmod decr lz)%CR.
  Proof.
    intros.
    apply regFunEq_equiv, regFunEq_e.
    intro d.
    setoid_replace (` d + ` d)%Q with (`d*(1#2) + (`d*(1#2)+` d))%Q by ring.
    apply (ball_triangle _ _ _ _ _ _ (AltSeries_raw_correct d cvmod xpos)).
    apply (AltSeries_further
             _ g gInit
             (cvmod (d * (1 # 2))%Qpos) (cvmod d)
             _ _ (d*(1#2))%Qpos d decr).
    apply lz. apply lz.
    apply app_inverse_below_correct.
    apply Qle_refl. 
  Qed.

End RationalStreamSum.
