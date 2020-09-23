Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import
  MathClasses.misc.workaround_tactics
  CoRN.model.totalorder.QMinMax Coq.QArith.Qround CoRN.util.Qdlog CoRN.stdlib_omissions.Q 
  CoRN.reals.fast.CRsin CoRN.reals.fast.CRstreams CoRN.reals.fast.CRAlternatingSum CoRN.reals.fast.Compress
  CoRN.metric2.MetricMorphisms CoRN.reals.faster.ARAlternatingSum MathClasses.interfaces.abstract_algebra 
  MathClasses.orders.minmax MathClasses.theory.nat_pow MathClasses.theory.int_pow.
Require Export
  CoRN.reals.faster.ARArith.

Section ARsin.
Context `{AppRationals AQ}.

Local Open Scope uc_scope.

Add Field Q : (dec_fields.stdlib_field_theory Q).

(* First define sine as a decreasing alternating series on the segment [0,1]. *)
Section sin_small_pos.
Context {num den : AQ} (Pnd : 0 ≤ num ≤ den).

(* Prove that the division of the 2 AQ numerator and denominator streams
   are equal to fast reals' Q stream of sine. *)
Lemma ARsinSequence : DivisionStream 
  (sinSequence ('num / 'den)) 
  (powers_help (num ^ (2:N)) num)
  (mult_Streams (powers_help (den ^ (2:N)) den) (everyOther (tl factorials))).
Proof.
  apply DivisionStream_Str_nth.
  intros n.
  unfold sinSequence, mult_Streams.
  rewrite ?Str_nth_zipWith.
  rewrite commutativity. 
  rewrite rings.preserves_mult, dec_fields.dec_recip_distr.
  rewrite associativity.
  apply sg_op_proper.
  - rewrite 2!preserves_powers_help.
    rewrite 3!(Str_nth_powers_help_int_pow _ (cast nat Z)).
    rewrite 2!(preserves_nat_pow (f:=cast AQ Q)).
    rewrite <-2!(int_pow_nat_pow (f:=cast N Z)).
    change (Qpower ('num / 'den) 2) with (('num / 'den) ^ ('(2 : N)) : Q).
    rewrite 2!int_pow_mult. 
    rewrite 2!int_pow_recip.
    change (Qdiv ('num) ('den)) with ('num / 'den : Q).
    destruct (decide ('den = (0:Q))) as [Pden | Pden].
    + rewrite ?Pden, rings.mult_0_l, dec_recip_0.
      rewrite Qmult_0_r, Qmult_0_l.
      unfold dec_recip, stdlib_rationals.Q_recip.
      unfold Qinv. simpl. rewrite Qmult_0_r. reflexivity.
    + rewrite <- (Qmult_assoc ('num)).
      rewrite <- (Qmult_assoc ('num)).
      apply (Qmult_comp ('num)). reflexivity.
      rewrite Qmult_comm.
      rewrite <- Qmult_assoc.
      apply (Qmult_comp ((' num ^ ' 2) ^ ' n)).
      reflexivity.
      rewrite Qmult_comm.
      symmetry.
      apply Qinv_mult_distr.
  - rewrite 2!Str_nth_everyOther.
    change (@tl AQ) with (@Str_nth_tl AQ 1).
    change (@tl Q) with (@Str_nth_tl Q 1).
    rewrite ?Str_nth_plus.
    rewrite Str_nth_Qrecip_factorials'.
    now rewrite preserves_factorials.
Qed.

Lemma AQsin_small_pos_Qprf : 0 ≤ ('num / 'den : Q) ≤ 1.
Proof.
  split.
   apply nonneg_mult_compat.
    now apply semirings.preserves_nonneg.
   apply dec_fields.nonneg_dec_recip_compat.
   apply semirings.preserves_nonneg.
   red. now transitivity num.
  destruct (decide ('den = (0:Q))) as [Pden | Pden].
    rewrite ?Pden, dec_recip_0. now ring_simplify.
  rewrite <-(dec_recip_inverse ('den : Q)) by assumption.
  apply (maps.order_preserving_flip_nonneg (.*.) (/'den)).
   apply dec_fields.nonneg_dec_recip_compat.
   apply semirings.preserves_nonneg.
   red. now transitivity num.
  now apply (order_preserving _).
Qed.

Definition AQsin_small_pos : AR := ARInfAltSum ARsinSequence 
  (dnn:=sinSequence_dnn AQsin_small_pos_Qprf) (zl:=sinSequence_zl AQsin_small_pos_Qprf).

Lemma AQsin_small_pos_correct : 'AQsin_small_pos = rational_sin ('num / 'den).
Proof.
  rewrite rational_sin_correct.
  rewrite <-rational_sin_small_pos_correct.
  now apply ARInfAltSum_correct.
Qed.
End sin_small_pos.

Lemma AQsin_small_pos_wd :
  forall (n1 n2 d1 d2 : AQ) (p1 : 0 ≤ n1 ≤ d1) (p2 : 0 ≤ n2 ≤ d2),
    n1 = n2
    -> d1 = d2
    -> AQsin_small_pos p1 = AQsin_small_pos p2.
Proof.
  assert (forall x y, ARtoCR x = ARtoCR y -> x = y) as H5.
  { intros x y H5. exact H5. }
  intros. apply H5.
  rewrite (AQsin_small_pos_correct p1).
  rewrite (AQsin_small_pos_correct p2).
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
  : forall q : AQ, msp_eq (' AQsin_poly_fun (AQboundAbs_uc 1 q))
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

Definition AQsin_poly_uc : AQ_as_MetricSpace --> AQ_as_MetricSpace
  := unary_uc (cast AQ Q_as_MetricSpace)
              (λ q : AQ, AQsin_poly_fun (AQboundAbs_uc 1 q))
              sin_poly_uc AQsin_poly_fun_bound_correct.

Definition ARsin_poly : AR -> AR
  := uc_compose ARcompress (Cmap AQPrelengthSpace AQsin_poly_uc).

Lemma ARtoCR_preserves_sin_poly (x : AR) : 'ARsin_poly x = sin_poly ('x).
Proof.
  change ('ARcompress (Cmap AQPrelengthSpace AQsin_poly_uc x) 
    = compress (Cmap QPrelengthSpace sin_poly_uc ('x))).
  rewrite ARcompress_correct, compress_correct.
  now apply preserves_unary_fun.
Qed.

(* When x = sin y, this function computes sin (y*3^n). *)
Fixpoint ARsin_poly_iter (n : nat) (x : AR) : AR :=
  match n with
  | O => x
  | S n' => ARsin_poly (ARsin_poly_iter n' x)
  end.

Definition AQsin_pos_bounded {n : nat} {num den : AQ} (Pnd : 0 ≤ num ≤ den * 3^n) : AR
  := ARsin_poly_iter n (AQsin_small_pos Pnd).

Lemma ARsin_poly_iter_wd : forall n x y,
    x = y -> ARsin_poly_iter n x = ARsin_poly_iter n y.
Proof.
  induction n.
  - intros. exact H5.
  - intros. simpl. rewrite (IHn x y H5).
    reflexivity.
Qed.

Lemma AQsin_pos_bounded_correct {n : nat} {num den : AQ} (Pnd : 0 ≤ num ≤ den * 3^n) : 
  'AQsin_pos_bounded Pnd = rational_sin ('num / 'den).
Proof.
  revert num den Pnd.
  induction n; intros.
  - unfold AQsin_pos_bounded. simpl.
    rewrite AQsin_small_pos_correct. 
    change (3^0%nat) with 1.
    rewrite rings.mult_1_r. reflexivity.
  - unfold AQsin_pos_bounded.
    simpl.
    rewrite ARtoCR_preserves_sin_poly.
    unfold AQsin_pos_bounded in IHn.
    assert (num ≤ den * 3 * 3 ^ n).
    { destruct Pnd.
      rewrite <- (associativity den 3). exact H6. }
    setoid_replace (ARsin_poly_iter n (AQsin_small_pos Pnd))
      with (ARsin_poly_iter n (AQsin_small_pos (conj (proj1 Pnd) H5))).
    rewrite IHn.
    change (Qdiv ('num) ('(den * 3))) with (('num : Q) / '(den * 3)).
    rewrite rings.preserves_mult, rings.preserves_3.
    rewrite dec_fields.dec_recip_distr, associativity.
    apply rational_sin_poly.
    apply ARsin_poly_iter_wd.
    apply AQsin_small_pos_wd. reflexivity.
    rewrite <- (associativity den 3). reflexivity.
Qed.

Section sin_pos.
Context {a : AQ} (Pa : 0 ≤ a).

Definition AQsin_pos_bound : nat := Z.abs_nat (1 + Qdlog 3 ('a)).

Lemma AQsin_pos_bound_correct : 0 ≤ a ≤ 3 ^ AQsin_pos_bound.
Proof.
  split; [assumption |].
  unfold AQsin_pos_bound.
  apply (order_reflecting (cast AQ Q)).
  rewrite preserves_nat_pow.
  rewrite rings.preserves_3.
  rewrite <-(int_pow_nat_pow (f:=cast nat Z)).
  destruct (total (≤) ('a : Q) 1).
   rewrite Qdlog2_le1; simpl; try easy.
   now transitivity (1:Q).
  rewrite inj_Zabs_nat, Z.abs_eq.
   now apply orders.lt_le, Qdlog_spec.
  change (0 ≤ 1 + Qdlog 3 ('a)).
  apply semirings.nonneg_plus_compat; [easy | now apply Qdlog_bounded_nonneg].
Qed.

(* When we reach [0,1] we can continue dividing by 3 to compute a sine
   closer to 0. Doing this generally improves the performance because
   the sequence converges more quickly. *)
Lemma AQsin_pos_bound_weaken (n : nat) : 0 ≤ a ≤ 1 * 3 ^ (n + AQsin_pos_bound).
Proof.
  split; [assumption |].
  rewrite rings.mult_1_l.
  rewrite nat_pow_exp_plus.
  apply semirings.ge_1_mult_le_compat_l.
    apply nat_pow_ge_1. 
     now apply semirings.le_1_3.
   now apply nat_pow_nonneg; solve_propholds.
  now apply AQsin_pos_bound_correct.
Qed.

(* TODO remove AQsin_pos_bound_weaken, each time this polynomial
   is applied, the requested precision is multiplied by 9. *)
Definition AQsin_pos : AR := AQsin_pos_bounded (AQsin_pos_bound_weaken 0).

Lemma AQsin_pos_correct: 'AQsin_pos = rational_sin ('a).
Proof.
  mc_setoid_replace ('a : Q) with ('a / '1 : Q).
   now apply AQsin_pos_bounded_correct.
  rewrite rings.preserves_1, dec_fields.dec_recip_1. ring.
Qed.
End sin_pos.

Lemma AQsin_prf {a : AQ} (pA : ¬0 ≤ a) : 0 ≤ -a.
Proof. apply rings.flip_nonpos_negate. now apply orders.le_flip. Qed.

Definition AQsin (a : AQ) : AR := 
  match (decide_rel (≤) 0 a) with
  | left Pa => AQsin_pos Pa
  | right Pa => -AQsin_pos (AQsin_prf Pa)
  end.

Lemma AQsin_correct a : 'AQsin a = rational_sin ('a).
Proof.
  unfold AQsin.
  case (decide_rel _); intros.
   now apply AQsin_pos_correct.
  rewrite rings.preserves_negate, AQsin_pos_correct.
  rewrite rings.preserves_negate.
  now apply rational_sin_opp.
Qed.

Definition ARsin_uc : AQ_as_MetricSpace --> AR
  := unary_complete_uc 
       QPrelengthSpace (cast AQ Q_as_MetricSpace) AQsin sin_uc AQsin_correct.

Definition ARsin : AR --> AR := Cbind AQPrelengthSpace ARsin_uc.

Lemma ARtoCR_preserves_sin x : 'ARsin x = sin_slow ('x).
Proof. apply preserves_unary_complete_fun. Qed.

End ARsin.

