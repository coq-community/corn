Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import
  Coq.Program.Program MathClasses.misc.workaround_tactics
  CoRN.model.totalorder.QposMinMax 
  CoRN.model.totalorder.QMinMax Coq.QArith.Qround Coq.QArith.Qabs
  CoRN.util.Qdlog CoRN.stdlib_omissions.Q 
  CoRN.reals.fast.CRexp CoRN.reals.fast.CRstreams CoRN.reals.fast.CRAlternatingSum
  CoRN.reals.fast.Compress CoRN.reals.fast.CRpower
  CoRN.metric2.MetricMorphisms CoRN.reals.faster.ARAlternatingSum MathClasses.interfaces.abstract_algebra 
  MathClasses.orders.minmax MathClasses.theory.nat_pow MathClasses.theory.int_pow.
Require Export
  CoRN.reals.faster.ARArith.

Section ARexp.
Context `{AppRationals AQ}.

Section exp_small_neg.
Context {a : AQ} (Pa : -1 ≤ a ≤ 0).

(*
Split the stream 
  (-a)^i / i! 
up into the streams
  (-a)^i    and    i!
because we do not have exact division
*)
Definition ARexpStream (px : positive*(AQ*AQ)) : AQ*AQ
  := (fst (snd px) * a, snd (snd px) * ZtoAQ (Zpos (fst px))).

Lemma AQexp_small_neg_prf : -1 ≤ ('a : Q) ≤ 0.
Proof.
  split.
   now apply rings.preserves_ge_negate1.
  now apply semirings.preserves_nonpos.
Qed.

(*
The ARInfAltSum function computes the infinite alternating sum 
and takes care of:
- Computing the length of the partial sum
- Computing the precision of the approximate division
*)
Lemma expStream_pos : ∀ x : positive * (AQ * AQ),
    0 < snd (snd x) → 0 < snd (ARexpStream x).
Proof.
  intros. unfold ARexpStream. simpl.
  assert (AQtoQ 0 == 0).
  apply rings.preserves_0.
  destruct aq_strict_order_embed.
  apply strict_order_embedding_reflecting.
  rewrite rings.preserves_mult, rings.preserves_0.
  apply (Qle_lt_trans _ (AQtoQ (snd (snd x)) * 0)).
  rewrite Qmult_0_r. apply Qle_refl.
  apply Qmult_lt_l.
  rewrite <- H6. apply strict_order_embedding_preserving, H5.
  pose proof AQtoQ_ZtoAQ.
  unfold cast in H7. rewrite H7.
  reflexivity.
Qed.

Lemma AQ0_lt_1 : 0 < 1.
Proof.
  destruct aq_strict_order_embed.
  apply strict_order_embedding_reflecting.
  rewrite rings.preserves_0, rings.preserves_1.
  reflexivity.
Qed.

Lemma expStream_correct : ∀ p : positive,
    Str_pth _ (CRexp.expStream (AQtoQ a)) p (1%positive, 1%Q)
    == let (_, r) := iterate _ (fS ARexpStream) p (1%positive, (1, 1)) in
       AQtoQ (fst r) / AQtoQ (snd r).
Proof.
  apply Pos.peano_ind.
  - unfold Str_pth. simpl.
    rewrite Qmult_1_l, Qmult_1_r.
    rewrite rings.mult_1_l, rings.mult_1_l.
    pose proof (AQtoQ_ZtoAQ 1).
    unfold cast in H5. rewrite H5.
    unfold stdlib_rationals.inject_Z_Q, inject_Z.
    unfold Qdiv. rewrite Qmult_1_r. reflexivity.
  - intros. unfold Str_pth.
    rewrite iterate_succ, iterate_succ.
    unfold Str_pth in H5.
    pose proof (fS_fst ARexpStream p (1,1)).
    pose proof (expStream_fst (AQtoQ a) p).
    destruct (iterate _ (CRexp.expStream (AQtoQ a)) p (1%positive, 1%Q)) as [u v].
    destruct (iterate (positive * (AQ * AQ)) (fS ARexpStream) p (1%positive, (1, 1))).
    unfold snd in H5 at 1. simpl.
    unfold fst in H6. subst p0.
    rewrite H5. unfold fst in H7. clear H5 v.
    subst u.
    assert (forall i j : AQ, AQtoQ (i*j) == AQtoQ i * AQtoQ j).
    { intros. rewrite rings.preserves_mult. reflexivity. }
    rewrite H5, H5. unfold Qdiv.
    rewrite Qinv_mult_distr.
    pose proof (AQtoQ_ZtoAQ).
    unfold cast in H6. rewrite H6.
    unfold stdlib_rationals.inject_Z_Q, inject_Z.
    setoid_replace (/ (Z.pos (Pos.succ p) # 1))%Q with (1#Pos.succ p).
    ring. reflexivity.
Qed.

Definition AQexp_small_neg : AR
  := 1+ AltSeries ARexpStream expStream_pos
                  positive (CRexp.expStream (AQtoQ a))
                  (1,1) (xH,1) expStream_correct
                  (fun e:Qpos => Pos.succ (Pos.size (Qden (proj1_sig e))))
                  (expStream_alt AQexp_small_neg_prf)
                  AQ0_lt_1 (expStream_zl AQexp_small_neg_prf).
               
Lemma AQexp_small_neg_correct
  : 'AQexp_small_neg = rational_exp_small_neg AQexp_small_neg_prf.
Proof.
  unfold AQexp_small_neg, rational_exp_small_neg.
  rewrite ARtoCR_preserves_plus.
  rewrite ARtoCR_preserves_1.
  rewrite <- CRplus_translate. 
  apply ucFun2_wd. reflexivity.
  apply AltSeries_correct.
Qed.

End exp_small_neg.

(*
Implement the range reduction
  exp(x) = exp(x/2) ^ 2
*)
Fixpoint ARpower_2_iter (n : nat) (x : AR) : AR :=
  match n with
  | O => x
  | S p => ARpower_N_bounded 2 1 (ARcompress (ARpower_2_iter p x))
  end.

Lemma ARpower_2_iter_wd : forall (n : nat) (x y : AR),
    x = y -> ARpower_2_iter n x = ARpower_2_iter n y.
Proof.
  induction n.
  - intros. exact H5.
  - intros. simpl. apply Cmap_wd. reflexivity.
    pose proof ARcompress_correct.
    simpl in H6.
    rewrite H6, H6.
    apply IHn, H5. 
Qed.

Lemma AQexp_neg_bounded_correct : ∀ (n : nat) a (abound : -1 ≤ a * (1 ≪ (-1)) ^ n ≤ 0),
    a ≤ 0 ->
    ' ARpower_2_iter n (AQexp_small_neg abound) = rational_exp (' a).
Proof.
  induction n.
  - intros. simpl.
    rewrite AQexp_small_neg_correct.
    rewrite rational_exp_small_neg_correct.
    rewrite rational_exp_correct.
    apply CRIR.IRasCR_wd, Exponential.Exp_wd.
    apply Q_in_CReals.inj_Q_wd.
    rewrite rings.preserves_mult.
    unfold pow. simpl.
    rewrite rings.preserves_1, Qmult_1_r.
    reflexivity.
  - intros a abound aneg. 
    change (ARpower_2_iter (S n) (AQexp_small_neg abound))
      with (ARpower_N_bounded 2 1 (ARcompress (ARpower_2_iter n (AQexp_small_neg abound)))).
    rewrite ARcompress_correct.
    rewrite ARtoCR_preserves_power_N_bounded.
    assert (-1 ≤ a * (1 ≪ (-1)) * (1 ≪ (-1)) ^ n ≤ 0) as abound_shift.
    { setoid_replace (a * 1 ≪ (-1) * (1 ≪ (-1)) ^ n )
        with (a * (1 ≪ (-1)) ^ S n). exact abound.
      unfold pow at 2. simpl.
      rewrite (rings.mult_assoc a). reflexivity. }
    specialize (IHn _ abound_shift).
    setoid_replace (' ARpower_2_iter n (AQexp_small_neg abound))
      with (' ARpower_2_iter n (AQexp_small_neg abound_shift)).
    rewrite IHn. clear IHn.
    transitivity (CRpower_N_bounded 2 (1#1)%Qpos (rational_exp (' (a ≪ (-1))))).
    + apply Cmap_wd. 
      setoid_replace ('1 : Qpos) with (1#1)%Qpos.
      reflexivity.
      rewrite AQposAsQpos_preserves_1. reflexivity.
      setoid_replace (' (a * 1 ≪ (-1))) with (' (a ≪ (-1))).
      reflexivity. rewrite aq_shift_opp_1.
      rewrite rings.preserves_mult.
      rewrite aq_shift_opp_1.
      apply Qmult_comp. reflexivity.
      rewrite rings.preserves_1. reflexivity.
    + rewrite aq_shift_opp_1.
      apply rational_exp_square.
      now apply semirings.preserves_nonpos.
    + apply (order_reflecting (cast AQ Q)).
      rewrite rings.preserves_mult.
      rewrite rings.preserves_0.
      rewrite <- (Qmult_0_l (' (1 ≪ (-1)))).
      apply Qmult_le_compat_r.
      apply (order_preserving (cast AQ Q)) in aneg.
      rewrite rings.preserves_0 in aneg.
      exact aneg.
      rewrite aq_shift_opp_1.
      rewrite rings.preserves_1. discriminate.
    + apply ARpower_2_iter_wd.
      apply (injective (cast AR CR)).
      rewrite AQexp_small_neg_correct, AQexp_small_neg_correct.
      apply rational_exp_small_neg_wd.
      setoid_replace (' (a * (1 ≪ (-1)) ^ S n))
        with (' (a * 1 ≪ (-1) * (1 ≪ (-1)) ^ n)).
      reflexivity.
      unfold pow at 1. simpl.
      rewrite (rings.mult_assoc a). reflexivity.
Qed.

Section exp_neg.
Context {a : AQ} (Pa : a ≤ 0).

Lemma AQexp_neg_bound_correct : -2 ^ Z.to_nat (Z.log2_up (Qceiling(-'a))) ≤ a.
Proof.
  apply (order_reflecting (cast AQ Q)).
  rewrite rings.preserves_negate.
  rewrite preserves_nat_pow.
  rewrite rings.preserves_2.
  rewrite <-(int_pow_nat_pow (f:=Z_of_nat)).
  assert ('a <= 0)%Q as H5.
  { apply (order_preserving (cast AQ Q)) in Pa.
    rewrite rings.preserves_0 in Pa. exact Pa. }
  pose proof (rational_exp_bound_power_2 H5).
  rewrite Qpower.Zpower_Qpower in H6.
  apply H6.
  apply Nat2Z.is_nonneg.
Qed.

Lemma power_2_improve_bound_correct : forall (n:nat),
    -2 ^ n ≤ a ->
    -1 ≤ a*(1 ≪ (-1))^n ≤ 0.
Proof.
  intros.
  assert ('a <= 0)%Q as aneg.
  { apply (order_preserving (cast AQ Q)) in Pa.
    rewrite rings.preserves_0 in Pa. exact Pa. } 
  pose proof (CRexp.power_2_improve_bound_correct n aneg) as H6.
  assert ('(-1) <= '(a * (1 ≪ (-1)) ^ n) <= '0
          -> -1 ≤ a * (1 ≪ (-1)) ^ n ≤ 0).
  { intros. split; apply (order_reflecting (cast AQ Q)); apply H7. }
  apply H7. clear H7.
  rewrite rings.preserves_mult.
  rewrite rings.preserves_negate.
  rewrite rings.preserves_1.
  rewrite rings.preserves_0.
  rewrite preserves_nat_pow. 
  rewrite <-(int_pow_nat_pow (f:=Z_of_nat)).
  rewrite (aq_shift_correct 1 (-1)).
  rewrite rings.preserves_1.
  rewrite Qmult_1_l. apply H6. clear H6.
  apply (order_preserving (cast AQ Q)) in H5.
  refine (Qle_trans _ _ _ _ H5).
  rewrite rings.preserves_negate.
  rewrite preserves_nat_pow. 
  rewrite <-(int_pow_nat_pow (f:=Z_of_nat)).
  rewrite Qpower.Zpower_Qpower. 
  rewrite rings.preserves_2.
  apply Qle_refl. apply Nat2Z.is_nonneg.
Qed.

Definition AQexp_neg : AR
  := ARpower_2_iter
       (Z.to_nat (Z.log2_up (Qceiling(-'a))))
       (AQexp_small_neg
          (power_2_improve_bound_correct _ (AQexp_neg_bound_correct))).

Lemma AQexp_neg_correct: 'AQexp_neg = rational_exp ('a).
Proof.
  apply AQexp_neg_bounded_correct, Pa.
Qed.

(* We could use a number closer to 1/exp 1, for example 11 $ -5, but in practice this seems
    to make it slower. *)
Program Definition AQexp_inv_pos_bound : AQ₊ := ((1 ≪ (-2)) ^ Z.abs_N (Qfloor ('a)))↾_.
Next Obligation. solve_propholds. Qed.

Lemma AQexp_inv_pos_bound_correct :
  '(cast (AQ₊) Q AQexp_inv_pos_bound) ≤ rational_exp ('a). 
Proof.
  change (cast Q CR (cast AQ Q ((1 ≪ (-2)) ^ Z.abs_N (Qfloor ('a)))) ≤ rational_exp ('a)).
  rewrite preserves_nat_pow.
  rewrite aq_shift_opp_2.
  rewrite rings.preserves_1, rings.mult_1_l.
  rewrite <-(int_pow_nat_pow (f:=cast N Z)).
  rewrite Z_of_N_abs, Z.abs_neq.
   apply (rational_exp_lower_bound (1#4)).
    now apply semirings.preserves_nonpos.
   apply CRpos_nonNeg.
   now CRsign.CR_solve_pos (1#1)%Qpos.
  change (Qfloor ('a) ≤ 0).
  apply (order_reflecting (cast Z Q)).
  transitivity ('a : Q).
   now apply Qfloor_le.
  now apply semirings.preserves_nonpos.
Qed.
End exp_neg.

Lemma AQexp_prf1 {a : AQ} (pA : 0 ≤ a) : -a ≤ 0.
Proof. now apply rings.flip_nonneg_negate. Qed.

Lemma AQexp_prf2 {a : AQ} (pA : ¬0 ≤ a) : a ≤ 0.
Proof. now apply orders.le_flip. Qed.

(*
Extend it to the full domain.
*)
Definition AQexp (a : AQ) : AR := 
  match decide_rel (≤) 0 a with
  | left Pa => ARinv_pos (AQexp_inv_pos_bound (a:=-a)) (AQexp_neg (AQexp_prf1 Pa))
  | right Pa => AQexp_neg (AQexp_prf2 Pa)
  end.

Lemma AQexp_correct a : 'AQexp a = rational_exp ('a).
Proof.
  unfold AQexp.
  case (decide_rel _); intros.
   rewrite ARtoCR_preserves_inv_pos.
   rewrite AQexp_neg_correct.
   rewrite rings.preserves_negate.
   apply rational_exp_opp.
    now apply semirings.preserves_nonneg.
   posed_rewrite <-(rings.preserves_negate (f:=cast AQ Q)).
   apply (AQexp_inv_pos_bound_correct (a:=-a)).
   now apply rings.flip_nonneg_negate.
  apply AQexp_neg_correct.
Qed.

Local Obligation Tactic := idtac.
Program Definition ARexp_bounded_uc (z : Z) := unary_complete_uc 
  QPrelengthSpace (cast AQ Q_as_MetricSpace) (λ x, AQexp (('z) ⊓ x)) (exp_bound_uc z) _.
Next Obligation. 
  intros. 
  change ('AQexp ((' z) ⊓ x) = exp_bound_uc z (' x)).
  rewrite AQexp_correct, aq_preserves_min, AQtoQ_ZtoAQ.
  reflexivity.
Qed.

Definition ARexp_bounded (z : Z) := Cbind AQPrelengthSpace (ARexp_bounded_uc z).

Lemma ARtoCR_preserves_exp_bounded z x : 'ARexp_bounded z x = exp_bounded z ('x).
Proof. apply (preserves_unary_complete_fun QPrelengthSpace _ (λ x, AQexp (('z) ⊓ x))). Qed.

Definition ARexp (x : AR) : AR
  := ARexp_bounded (Qceiling ('approximate x (Qpos2QposInf (1#1)) + (1#1))) x.

Lemma ARtoCR_preserves_exp x : 'ARexp x = exp ('x).
Proof. unfold ARexp. apply ARtoCR_preserves_exp_bounded. Qed.
End ARexp.
