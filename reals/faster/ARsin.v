Require Import
  Coq.QArith.Qround Coq.QArith.Qpower 
  MathClasses.interfaces.abstract_algebra 
  MathClasses.theory.nat_pow
  MathClasses.theory.int_pow
  CoRN.algebra.RSetoid
  CoRN.metric2.Metric
  CoRN.metric2.MetricMorphisms
  CoRN.metric2.UniformContinuity
  CoRN.model.totalorder.QMinMax
  CoRN.util.Qdlog
  CoRN.stdlib_omissions.Q 
  CoRN.reals.fast.CRsin
  CoRN.reals.fast.CRstreams
  CoRN.reals.fast.CRAlternatingSum
  CoRN.reals.fast.Compress
  CoRN.reals.faster.ARAlternatingSum.
Require Export
  CoRN.reals.faster.ARArith.

Local Open Scope mc_scope.

Section ARsin.
Context `{AppRationals AQ}.

Lemma AQmult_lt_0_compat : forall a b : AQ, 0 < a -> 0 < b -> 0 < a*b.
Proof.
  intros.
  apply (strictly_order_reflecting (cast AQ Q)).
  pose proof (rings.preserves_0 (f:=cast AQ Q)).
  rewrite H7.
  rewrite rings.preserves_mult.
  rewrite <- (Qmult_0_l ('b)).
  apply Qmult_lt_compat_r.
  rewrite <- H7.
  apply (strictly_order_preserving (cast AQ Q)), H6.
  rewrite <- H7.
  apply (strictly_order_preserving (cast AQ Q)), H5.
Qed.
 
Lemma ZtoQ : forall n:positive, AQtoQ (ZtoAQ (Zpos n)) == (Zpos n#1).
Proof.
  induction n.
  - change (Z.pos n~1) with (1+2*Z.pos n)%Z.
    pose proof (rings.preserves_plus (f:=cast Z AQ) 1 (2*Z.pos n)).
    rewrite H5. clear H5.
    rewrite rings.preserves_plus, rings.preserves_1.
    rewrite rings.preserves_1.
    pose proof (rings.preserves_mult (f:=cast Z AQ) 2 (Z.pos n)).
    rewrite H5. clear H5.
    rewrite rings.preserves_mult, IHn.
    rewrite rings.preserves_2, rings.preserves_2.
    unfold Qeq; simpl. rewrite Pos.mul_1_r. reflexivity.
  - change (Z.pos n~0) with (2*Z.pos n)%Z.
    pose proof (rings.preserves_mult (f:=cast Z AQ) 2 (Z.pos n)).
    rewrite H5.
    rewrite rings.preserves_mult, IHn.
    rewrite rings.preserves_2. 
    pose proof (rings.preserves_2 (f:=cast AQ Q)).
    rewrite H6. reflexivity.
  - pose proof (rings.preserves_1 (f:=cast Z AQ)).
    rewrite H5. rewrite rings.preserves_1. reflexivity.
Qed.

Local Open Scope uc_scope.


Section sin_small.
  (* First define (sin a) as a decreasing alternating series on the segment [-1,1].
     a = num/den and -1 <= a <= 1. *)

Context {num den : AQ} (Pnd : -den ≤ num ≤ den) (dpos : 0 < den).
  
(*
Split the stream 
  (-1)^i a^(2i+1) / (2i+1)! 
up into the streams
  (-1)^i a^(2i+1)    and    (2i+1)!
because we do not have exact division
*)
Definition ARsinStream (px : positive*(AQ*AQ)) : AQ*AQ
  := (- fst (snd px) * num * num,
      snd (snd px) * den * den * ZtoAQ (Zpos (fst px)~0) * ZtoAQ (Zpos (fst px)~1)).

Lemma sinStream_pos : ∀ x : positive * (AQ * AQ),
    0 < snd (snd x) → 0 < snd (ARsinStream x).
Proof.
  assert (0 = ZtoAQ 0) as zero_int.
  { destruct H4. destruct aq_ints_mor, semiringmor_plus_mor.
    rewrite preserves_mon_unit. reflexivity. }
  intros. destruct x; simpl.
  simpl in H5.
  apply AQmult_lt_0_compat.
  apply AQmult_lt_0_compat.
  apply AQmult_lt_0_compat.
  apply AQmult_lt_0_compat.
  exact H5. exact dpos. exact dpos.
  rewrite zero_int.
  apply (strictly_order_preserving (cast Z AQ)).
  reflexivity.
  rewrite zero_int.
  apply (strictly_order_preserving (cast Z AQ)).
  reflexivity.
Qed.

Lemma sinStream_correct : ∀ p : positive,
    Str_pth _ (sinStream (AQtoQ num / AQtoQ den))
            p (1%positive, AQtoQ num / AQtoQ den)
    == let (_, r) := iterate _ (fS ARsinStream) p (1%positive, (num, den)) in
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
  - unfold Str_pth. simpl.
    do 6 rewrite rings.preserves_mult.
    rewrite rings.preserves_negate.
    rewrite H5, H5.
    unfold dec_recip, stdlib_rationals.Q_recip.
    unfold mult, stdlib_rationals.Q_mult.
    unfold negate, stdlib_rationals.Q_opp.
    field. intro abs.
    apply (strictly_order_preserving (cast AQ Q)) in dpos.
    rewrite rings.preserves_0, abs in dpos.
    exact (Qlt_irrefl 0 dpos).
  - intros p IHp. unfold Str_pth. unfold Str_pth in IHp.
    rewrite iterate_succ, iterate_succ.
    pose proof (sinStream_fst (AQtoQ num / AQtoQ den) p) as H7.
    unfold dec_recip, stdlib_rationals.Q_recip.
    unfold dec_recip, stdlib_rationals.Q_recip in IHp.
    unfold mult, stdlib_rationals.Q_mult.
    unfold mult, stdlib_rationals.Q_mult in IHp.
    unfold Qdiv in H7. unfold Qdiv.
    unfold Qdiv in IHp.
    unfold Q_as_MetricSpace, msp_car.
    unfold Q_as_MetricSpace, msp_car in IHp.
    destruct (iterate _ (sinStream (AQtoQ num * / AQtoQ den)%Q) p
            (1%positive, (AQtoQ num * / AQtoQ den)%Q)).
    simpl in H7. simpl in IHp. subst p0.
    unfold sinStream, snd, fst. rewrite IHp. clear IHp.
    pose proof (fS_fst ARsinStream p (num, den)).
    destruct (iterate _ (fS ARsinStream) p (1%positive, (num, den))) as [p0 p1].
    simpl in H6. simpl. subst p0.
    do 6 rewrite rings.preserves_mult.
    rewrite rings.preserves_negate.
    unfold mult, stdlib_rationals.Q_mult.
    unfold negate, stdlib_rationals.Q_opp.
    rewrite ZtoQ, ZtoQ.
    rewrite <- (Qmult_assoc (AQtoQ (snd p1) * AQtoQ den * AQtoQ den)).
    rewrite Qinv_mult_distr.
    setoid_replace (/ ((Z.pos (Pos.succ p)~0 # 1) * (Z.pos (Pos.succ p)~1 # 1)))
      with (1 # (Pos.succ p * (Pos.succ p)~1)~0) by reflexivity.
    do 2 rewrite Qinv_mult_distr. ring.
Qed.

Lemma AQsin_small_Qprf : -1 ≤ AQtoQ num / AQtoQ den ≤ 1.
Proof.
  split.
  - apply Qle_shift_div_l.
    pose proof (rings.preserves_0 (f:=cast AQ Q)).
    rewrite <- H5.
    apply (strictly_order_preserving (cast AQ Q)), dpos.
    setoid_replace (-1 * AQtoQ den) with (-AQtoQ den) by reflexivity.
    rewrite <- rings.preserves_negate.
    apply (order_preserving (cast AQ Q)), Pnd.
  - apply Qle_shift_div_r.
    pose proof (rings.preserves_0 (f:=cast AQ Q)).
    rewrite <- H5.
    apply (strictly_order_preserving (cast AQ Q)), dpos.
    rewrite Qmult_1_l.
    apply (order_preserving (cast AQ Q)), Pnd.
Qed.

Definition AQsin_small : msp_car AR
  := CRtoAR (inject_Q_CR (AQtoQ num / AQtoQ den))
     + AltSeries ARsinStream sinStream_pos
                 positive (CRsin.sinStream (AQtoQ num / AQtoQ den))
                 (num,den) (xH,AQtoQ num / AQtoQ den) sinStream_correct _
                 (sinStream_alt AQsin_small_Qprf)
                 dpos (sinStream_zl AQsin_small_Qprf).

Lemma AQsin_small_correct : 'AQsin_small = rational_sin (AQtoQ num / AQtoQ den).
Proof.
  rewrite rational_sin_correct,
  <- (rational_sin_small_correct AQsin_small_Qprf).
  unfold AQsin_small, rational_sin_small.
  rewrite ARtoCR_preserves_plus.
  apply ucFun2_wd.
  pose proof CRAR_id. unfold cast in H5.
  unfold cast. rewrite H5.
  reflexivity.
  apply AltSeries_correct.
Qed.

End sin_small.

Lemma AQsin_small_pos_wd :
  forall (n1 n2 d1 d2 : AQ) (p1 : -d1 ≤ n1 ≤ d1) (p2 : -d2 ≤ n2 ≤ d2)
    (d1pos : 0 < d1) (d2pos : 0 < d2),
    n1 = n2
    -> d1 = d2
    -> AQsin_small p1 d1pos = AQsin_small p2 d2pos.
Proof.
  assert (forall x y, ARtoCR x = ARtoCR y -> x = y) as H5.
  { intros x y H5. exact H5. }
  intros. apply H5.
  rewrite (AQsin_small_correct p1 d1pos).
  rewrite (AQsin_small_correct p2 d2pos).
  rewrite H6, H7. reflexivity.
Qed.

(** Sine's range can then be extended to [[0,3^n]] by [n] applications
of the identity [sin(x) = 3*sin(x/3) - 4*(sin(x/3))^3]. *) 
Definition AQsin_poly_fun (x : AQ) : AQ := x * (3 - 4 * x ^ (2:N)).

Lemma AQsin_poly_fun_correct (q : AQ) :
  'AQsin_poly_fun q = sin_poly_fun ('q).
Proof.
  unfold AQsin_poly_fun, sin_poly_fun.
  rewrite nat_pow_2.
  rewrite rings.preserves_mult, rings.preserves_minus, ?rings.preserves_mult.
  rewrite rings.preserves_3, rings.preserves_4.
  now rewrite <-(associativity _ ('q) ('q : Q)).
Qed.

(* AQsin_poly_fun is not uniformly continuous because of x^3, but it will
   only be applied to sine values in [-1,1], a range on which it is
   uniformly continuous. *)
Lemma AQsin_poly_fun_bound_correct
  : forall q : AQ, msp_eq (' AQsin_poly_fun (ucFun (AQboundAbs_uc 1) q))
                     (sin_poly_fun (Qmax (- (1)) (Qmin 1 (' q)))).
Proof.
  intro q. apply Qball_0.
  rewrite AQsin_poly_fun_correct.
  f_equiv.
  unfold AQboundAbs_uc. simpl.
  change ('1) with (1:AQ).
  rewrite ?aq_preserves_max, ?aq_preserves_min.
  now rewrite ?rings.preserves_negate, ?rings.preserves_1.
Qed.

Definition AQsin_poly_uc : msp_car (AQ_as_MetricSpace --> AQ_as_MetricSpace)
  := unary_uc (cast AQ (msp_car Q_as_MetricSpace))
              (λ q : AQ, AQsin_poly_fun (ucFun (AQboundAbs_uc 1) q))
              sin_poly_uc AQsin_poly_fun_bound_correct.

Definition ARsin_poly : msp_car (AR --> AR)
  := uc_compose ARcompress (Cmap AQPrelengthSpace AQsin_poly_uc).

Lemma ARtoCR_preserves_sin_poly (x : msp_car AR)
  : 'ucFun ARsin_poly x = ucFun sin_poly ('x).
Proof.
  change ('ucFun ARcompress (ucFun (Cmap AQPrelengthSpace AQsin_poly_uc) x) 
    = ucFun compress (ucFun (Cmap QPrelengthSpace sin_poly_uc) ('x))).
  rewrite ARcompress_correct, compress_correct.
  now apply preserves_unary_fun.
Qed.

(* When x = sin y, this function computes sin (y*3^n). *)
Fixpoint ARsin_poly_iter (n : nat) (x : msp_car AR) : msp_car AR :=
  match n with
  | O => x
  | S n' => ucFun ARsin_poly (ARsin_poly_iter n' x)
  end.

Definition AQsin_bounded {n : nat} {num den : AQ}
           (Pnd : - (den * 3^n) ≤ num ≤ den * 3^n)
           (dpos : 0 < den * 3^n) : msp_car AR
  := ARsin_poly_iter n (AQsin_small Pnd dpos).

Lemma ARsin_poly_iter_wd : forall n x y,
    x = y -> ARsin_poly_iter n x = ARsin_poly_iter n y.
Proof.
  induction n.
  - intros. exact H5.
  - intros.
    change (ucFun ARsin_poly (ARsin_poly_iter n x)
            = ucFun ARsin_poly (ARsin_poly_iter n y)).
    rewrite (IHn x y H5).
    reflexivity.
Qed.

Lemma AQsin_bounded_correct {n : nat} {num den : AQ}
      (Pnd : -(den * 3^n) ≤ num ≤ den * 3^n) (dpos : 0 < den * 3^n) : 
  'AQsin_bounded Pnd dpos = rational_sin ('num / 'den).
Proof.
  revert num den dpos Pnd.
  induction n; intros.
  - unfold AQsin_bounded. simpl.
    rewrite AQsin_small_correct. 
    change (3^0%nat) with 1.
    rewrite rings.mult_1_r. reflexivity.
  - unfold AQsin_bounded.
    change (' ucFun ARsin_poly (ARsin_poly_iter n (AQsin_small Pnd dpos))
            = rational_sin (' num / ' den)).
    rewrite ARtoCR_preserves_sin_poly.
    unfold AQsin_bounded in IHn.
    assert (le (-(den * 3 * 3 ^ n)) num /\ num ≤ den * 3 * 3 ^ n) as H5.
    { rewrite <- (associativity den 3). exact Pnd. }
    assert (0 < den * 3 * 3 ^ n) as H6.
    { rewrite <- (associativity den 3). exact dpos. }
    setoid_replace (ARsin_poly_iter n (AQsin_small Pnd dpos))
      with (ARsin_poly_iter n (AQsin_small H5 H6)).
    rewrite IHn.
    change (Qdiv ('num) ('(den * 3))) with (('num : Q) / '(den * 3)).
    rewrite rings.preserves_mult, rings.preserves_3.
    rewrite dec_fields.dec_recip_distr, associativity.
    apply rational_sin_poly.
    apply ARsin_poly_iter_wd.
    apply AQsin_small_pos_wd. reflexivity.
    rewrite <- (associativity den 3). reflexivity.
Qed.

Definition AQsin_bound (a : AQ) : nat := CRsin.sin_bound ('a).

Lemma AQsin_bound_correct : forall (a:AQ),
    -(1 * 3 ^ AQsin_bound a) ≤ a ≤ 1 * 3 ^ AQsin_bound a.
Proof.
  intro a. unfold AQsin_bound.
  pose proof (CRsin.sin_bound_correct ('a)).
  split; apply (order_reflecting (cast AQ Q)).
  - rewrite rings.preserves_negate.
    destruct H4, aq_ring, ring_monoid.
    destruct commonoid_mon. rewrite monoid_left_id.
    rewrite preserves_nat_pow.
    rewrite rings.preserves_3.
    rewrite <-(int_pow_nat_pow (f:=cast nat Z)).
    rewrite <- (Zpower_Qpower 3).
    apply H5. apply (Nat2Z.inj_le 0), le_0_n.
  - destruct H4, aq_ring, ring_monoid.
    destruct commonoid_mon. rewrite monoid_left_id.
    rewrite preserves_nat_pow.
    rewrite rings.preserves_3.
    rewrite <-(int_pow_nat_pow (f:=cast nat Z)).
    rewrite <- (Zpower_Qpower 3).
    apply H5. apply (Nat2Z.inj_le 0), le_0_n.
Qed.

Lemma AQsin_bound_pos : forall a, 0 < 1 * 3 ^ AQsin_bound a.
Proof.
  intro a.
  destruct H4, aq_ring, ring_monoid.
  destruct commonoid_mon. rewrite monoid_left_id.
  apply (strictly_order_reflecting (cast AQ Q)).
  rewrite preserves_nat_pow.
  rewrite rings.preserves_3.
  rewrite <- (int_pow_nat_pow (f:=cast nat Z)).
  rewrite rings.preserves_0.
  apply (Qpower_0_lt 3 (Z.of_nat (AQsin_bound a))).
  reflexivity.
Qed.

Definition AQsin (a:AQ) : msp_car AR
  := AQsin_bounded (AQsin_bound_correct a) (AQsin_bound_pos a).

Lemma AQsin_correct : forall a, 'AQsin a = rational_sin ('a).
Proof.
  intro a.
  mc_setoid_replace ('a : Q) with ('a / '1 : Q).
   now apply AQsin_bounded_correct.
  rewrite rings.preserves_1, dec_fields.dec_recip_1. 
  rewrite Qmult_1_r. reflexivity.
Qed.

Lemma AQsin_prf {a : AQ} (pA : ¬0 ≤ a) : 0 ≤ -a.
Proof. apply rings.flip_nonpos_negate. now apply orders.le_flip. Qed.

Definition ARsin_uc : msp_car (AQ_as_MetricSpace --> AR)
  := unary_complete_uc 
       QPrelengthSpace (cast AQ (msp_car Q_as_MetricSpace)) AQsin sin_uc AQsin_correct.

Definition ARsin : msp_car (AR --> AR)
  := Cbind AQPrelengthSpace ARsin_uc.

Lemma ARtoCR_preserves_sin x : ' ucFun ARsin x = ucFun sin_slow ('x).
Proof. apply preserves_unary_complete_fun. Qed.

End ARsin.

