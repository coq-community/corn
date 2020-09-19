Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import
  Coq.QArith.Qabs Coq.QArith.Qround
  CoRN.model.metric2.Qmetric
  CoRN.metric2.ProductMetric
  CoRN.metric2.Prelength
  CoRN.metric2.Compact
  CoRN.model.totalorder.QposMinMax 
  CoRN.model.totalorder.QMinMax
  CoRN.reals.faster.ARArith
  CoRN.reals.fast.Interval.


(** Proof that intervals are compact. *)

Local Open Scope uc_scope.

Section ARintervalRational.
Context `{AppRationals AQ}.

(* The computations of the subdivisions are faster when the bounds are
   rational numbers, and this is what we'll use to plot graphs, by
   slightly extending the domains to get rational end points. *) 
Variable a b : Q.
Hypothesis leab : a <= b.

Lemma plFEQ : PrelengthSpace (FinEnum Q_as_MetricSpace).
Proof.
 apply FinEnum_prelength.
  apply locatedQ.
 apply QPrelengthSpace.
Qed.

(* TODO this has twice as many points as CompactIntervalQ,
   fine tune the subdivision. *)
Lemma Iab_reg_prf
  : is_RegularFunction
      (FinEnum_ball AQ_as_MetricSpace)
      (fun d0:QposInf
       => match d0 with
         | Qpos2QposInf d
           => map (λ x : Q, AppInverse0 x ((1 # 2) * d)%Qpos)
                 (UniformPartition
                    a b
                    (max 1 (Z.to_nat (Qround.Qceiling ((b - a) / (inject_Z 2 * ((1 # 2) * ` d)))))))
         | QposInfinity => nil
         end).
Proof.
  pose (CompactCompleteCompact
       _ (CompactImage (1#1)%Qpos plFEQ
                       (Build_UniformlyContinuousFunction inject_Q_AR_uc)
                       (CompactIntervalQ leab))) as K.
  apply (@is_RegularFunction_wd _ (approximate K)).
  2: apply (regFun_prf K). 
  intro d. simpl. unfold Cjoin_raw; simpl.
  unfold FinCompact_raw; simpl.
  rewrite map_map; simpl.
  unfold MetricMorphisms.app_inverse.
  unfold canonical_names.equiv.
  unfold FinEnum_eq. simpl.
  apply (@ball_refl (FinEnum AQ_as_MetricSpace) 0).
  discriminate.
Qed.
  
Definition IabCompact : Compact AQ_as_MetricSpace
  := Build_RegularFunction Iab_reg_prf.

End ARintervalRational.

