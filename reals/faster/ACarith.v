Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import
  Coq.QArith.Qabs
  CoRN.model.metric2.Qmetric
  CoRN.metric2.ProductMetric
  CoRN.model.totalorder.QposMinMax 
  CoRN.model.totalorder.QMinMax
  CoRN.reals.faster.ARabs 
  CoRN.reals.faster.ARroot
  CoRN.reals.faster.ARArith.

(** Basic definitions for the complex numbers. *)

Section ACcomplex.
Context `{AppRationals AQ}.

(* The instance of Setoid AR*AR is already in scope,
   with u = v iff (fst u = fst v /\ snd u = snd v). *)

Definition ACball (u v : AR*AR) (e : Q) : Prop
  := 0 <= e
     /\ ARle ((fst u - fst v)*(fst u - fst v) + (snd u - snd v)*(snd u - snd v))
            (inject_Q_AR (e*e)).

(* TODO the distance of ACball would be better. *)
Definition AC : MetricSpace := ProductMS AR AR.

Instance: Plus AC
  := fun xy uv => pair (fst xy + fst uv) (snd xy + snd uv).

Instance: Mult AC
  := fun xy uv => pair (fst xy*fst uv - snd xy*snd uv)
                    (fst xy*snd uv + snd xy*fst uv).

(* The square root of -1, imaginary number i. *)
Definition ACi : AC := pair 0 1.

Definition ACmodulus : AC -> AR
  := fun z => ARsqrt (fst z*fst z + snd z*snd z).

Lemma ACplus_comm : forall u v : AC, u + v = v + u.
Proof.
  intros u v. split; apply ARplus_comm.
Qed.

Lemma ACplus_assoc : forall u v w : AC,
    (u + v) + w = u + (v + w).
Proof.
  intros u v w. split; apply ARplus_assoc.
Qed.

Definition ACsqrt (z : AC) (yDec : {ARle 0 (snd z)} + {ARle (snd z) 0}) : AC
  := pair (ARsqrt ((ACmodulus z + fst z) * inject_Q_AR (1#2)))
          ((if yDec then 1 else -1)
           * (ARsqrt ((ACmodulus z - fst z) * inject_Q_AR (1#2)))).

Add Ring AR : (rings.stdlib_ring_theory AR).

Lemma ARdouble : forall x : AR, x + x = 2*x.
Proof.
  intro x. ring.
Qed.

Lemma ARmult_neg_one : forall x : AR, -1 * x = -x.
Proof.
  intros. ring.
Qed.

Lemma ACsqrt_correct : forall (z : AC) (yDec : {ARle 0 (snd z)} + {ARle (snd z) 0}),
    ACsqrt z yDec * ACsqrt z yDec = z.
Proof.
  intros [x y] yDec.
  assert (2 * inject_Q_AR (1 # 2) = 1) as twoHalf.
  { unfold one.
    pose proof inject_Q_AR_1.
    unfold one in H5.
    rewrite <- H5.
    rewrite <- inject_Q_AR_plus, <- inject_Q_AR_mult.
    apply inject_Q_AR_wd. reflexivity. }
  assert (ARle 0 (ACmodulus (x, y) - x)) as modMinus.
  { unfold ACmodulus, fst, snd.
    rewrite <- (ARplus_opp_r x).
    apply ARplus_le_compat_r.
    apply (ARle_trans _ (ARsqrt (x*x))).
    rewrite (ARsqrt_srq_abs x).
    apply ARle_abs.
    apply ARsqrt_inc.
    apply ARsquare_pos.
    rewrite <- (ARplus_0_r (x*x)) at 1.
    apply ARplus_le_compat_l.
    apply ARsquare_pos. }
  assert (ARle 0 (ACmodulus (x, y) + x)) as modPlus.
  { unfold ACmodulus, fst, snd.
    rewrite <- (ARplus_opp_r x).
    rewrite ARplus_comm.
    apply ARplus_le_compat_r.
    apply (ARle_trans _ (ARsqrt (x*x))).
    rewrite (ARsqrt_srq_abs x).
    rewrite <- ARabs_opp.
    apply ARle_abs.
    apply ARsqrt_inc.
    apply ARsquare_pos.
    rewrite <- (ARplus_0_r (x*x)) at 1.
    apply ARplus_le_compat_l.
    apply ARsquare_pos. }
  assert (ARle 0 (inject_Q_AR (1 # 2))) as halfPos.
  { rewrite <- inject_Q_AR_0.
    apply inject_Q_AR_le.
    discriminate. }
  split.
  - unfold mult, Mult_instance_0, ACsqrt, fst, snd.
    rewrite (ARsqrt_correct ((ACmodulus (x, y) + x) * inject_Q_AR (1 # 2))).
    rewrite (ARmult_comm (if yDec then 1 else -1)
                         (ARsqrt ((ACmodulus (x, y) - x) * inject_Q_AR (1 # 2)))).
    rewrite ARmult_assoc.
    rewrite <- (ARmult_comm (if yDec then 1 else -1)).
    rewrite <- (ARmult_assoc (if yDec then 1 else -1)).
    setoid_replace (ARmult (if yDec then 1 else -1) (if yDec then 1 else -1))
      with AR1.
    rewrite ARmult_1_l.
    rewrite (ARsqrt_correct ((ACmodulus (x, y) - x) * inject_Q_AR (1 # 2))).
    + setoid_replace ((ACmodulus (x, y) + x) * inject_Q_AR (1 # 2) -
                      (ACmodulus (x, y) - x) * inject_Q_AR (1 # 2))
        with (x*(2*inject_Q_AR (1#2))) by ring.
      rewrite twoHalf. 
      apply ARmult_1_r.
    + apply AR_mult_0_le_compat. exact modMinus.
      exact halfPos.
    + destruct yDec. exact (ARmult_1_l AR1).
      pose proof (ARmult_neg_one (-1)).
      simpl in H5. rewrite H5. clear H5.
      apply ARopp_involutive.
    + apply AR_mult_0_le_compat. exact modPlus.
      exact halfPos.
  - unfold mult, Mult_instance_0, ACsqrt, fst, snd.
    rewrite ARmult_comm, ARmult_assoc, ARdouble.
    rewrite ARsqrt_mult, ARsqrt_mult.
    assert (forall a b c : AR, a * c * (b * c) = c * c * (a * b)).
    { intros. ring. }
    rewrite H5. clear H5.
    pose proof (ARsqrt_correct (inject_Q_AR (1 # 2))).
    simpl in H5. rewrite H5. clear H5.
    rewrite <- (ARsqrt_mult (ACmodulus (x, y) - x)).
    setoid_replace ((ACmodulus (x, y) - x) * (ACmodulus (x, y) + x))
      with (ACmodulus (x, y) * ACmodulus (x, y) - x*x)
      by ring.
    unfold ACmodulus, fst, snd.
    rewrite (ARsqrt_correct (x*x+y*y)).
    setoid_replace (x * x + y * y - x * x)
      with (y*y) by ring.
    rewrite ARsqrt_srq_abs.
    setoid_replace (2 * ((if yDec then 1 else -1) * (inject_Q_AR (1 # 2) * ARabs y)))
      with (2 * inject_Q_AR (1 # 2) * ((if yDec then 1 else -1) * ARabs y))
      by ring.
    rewrite twoHalf, ARmult_1_l.
    simpl in yDec. destruct yDec.
    rewrite ARmult_1_l.
    rewrite ARabs_pos. reflexivity. exact a.
    rewrite ARabs_neg.
    rewrite ARmult_neg_one.
    apply ARopp_involutive.
    exact a.
    apply (ARle_trans _ (x*x + 0)).
    rewrite ARplus_0_r.
    apply ARsquare_pos.
    apply ARplus_le_compat_l, ARsquare_pos.
    exact modMinus.
    exact modPlus.
    exact halfPos.
    exact modPlus.
    exact halfPos.
    exact modMinus.
    exact halfPos.
Qed.

End ACcomplex.
