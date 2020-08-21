
Require Import CoRN.algebra.RSetoid.
Require Import CoRN.model.totalorder.QposMinMax.
Require Import CoRN.metric2.Metric.
Require Import CoRN.reals.fast.CRArith.

Local Open Scope CR.

Record is_DistanceMetricSpace (X : RSetoid) (distance: X -> X -> CR) : Prop
  := Build_is_DistanceMetricSpace
  { dmsp_refl: forall x y, st_eq x y <-> distance x y == 0
  ; dmsp_sym: forall x y, distance x y == distance y x
  ; dmsp_triangle: forall x y z, distance x z <= distance x y + distance y z
  ; dmsp_nonneg: forall x y, 0 <= distance x y
  }.

Record DistanceMetricSpace: Type := Build_alt_MetricSpace
  { dmsp_is_setoid:> RSetoid;
    distance: dmsp_is_setoid -> dmsp_is_setoid -> CR;
    distance_wd: Proper (@st_eq _ ==> @st_eq _ ==> @st_eq _) distance;
    dmsp : is_DistanceMetricSpace dmsp_is_setoid distance }.

Arguments distance [d].
Existing Instance distance_wd.

Section DistanceMetricSpace. (* Just mimicking Russell's code for MetricSpace here. *)

  Context {X: DistanceMetricSpace}.

  Lemma distance_refl (x y: X): st_eq x y <-> distance x y == 0.
  Proof. apply dmsp_refl, dmsp. Qed.

  Lemma distance_sym (x y: X): distance x y == distance y x.
  Proof. apply dmsp_sym, dmsp. Qed.

  Lemma distance_triangle (x y z: X):
    distance x z <= distance x y + distance y z.
  Proof. apply dmsp_triangle, dmsp. Qed.

End DistanceMetricSpace.

(* We show that a DistanceMetricSpace immediately yields a MetricSpace. *)

Section from_alt.

  Variable (X: DistanceMetricSpace).

  Definition ball (q: Q) (x y: X): Prop
    := (0 <= q)%Q /\ distance x y <= inject_Q_CR q.

  Instance ball_wd: Proper (Qeq ==> @st_eq X ==> @st_eq X ==> iff) ball.
  Proof.
   intros ?? E ?? F ?? G. unfold ball.
   split.
   - intros [qpos H]. assert (Qle 0 y). rewrite <- E. exact qpos.
     split. exact H0. rewrite <- F, <- G.
     rewrite <- E. exact H.
   - intros [qpos H]. assert (Qle 0 x). rewrite E. exact qpos.
     split. exact H0. rewrite F, G.
     rewrite E. exact H.
  Qed.

  Lemma ball_refl e: Qle 0 e -> Reflexive (ball e).
  Proof.
   unfold Reflexive, ball. intros. 
   split. exact H.
   rewrite (proj1 (distance_refl x x)).
   apply CRle_Qle. exact H.
   reflexivity.
  Qed.

  Lemma ball_sym e: Symmetric (ball e).
  Proof with auto.
   unfold Symmetric, ball. intros.
   destruct H as [qpos H]. 
   split. exact qpos.
   rewrite distance_sym...
  Qed.

  Lemma ball_closed (e:Q) x y: (forall d:Q, 0 < d -> ball (e+d) x y)%Q -> ball e x y.
  Proof.
   unfold ball. intro H.
   assert (Qle 0 e).
   { apply Qnot_lt_le. intro abs.
     destruct (H (-e*(1#2))%Q). rewrite <- (Qmult_0_l (1#2)).
     apply Qmult_lt_r. reflexivity.
     apply (Qplus_lt_l _ _ e). ring_simplify. exact abs.
     clear H1. ring_simplify in H0.
     rewrite <- (Qmult_0_r (1#2)) in H0.
     apply Qmult_le_l in H0. exact (Qlt_not_le _ _ abs H0). reflexivity. }
   split. exact H0.
   apply CRle_not_lt. intro abs.
   apply CRlt_Qmid in abs.
   destruct abs as [q [H1 H2]].
   specialize (H (q-e)%Q).
   revert H2.
   apply CRle_not_lt.
   setoid_replace q with (e+(q-e))%Q
     by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; ring).
   apply H.
   unfold Qminus. rewrite <- Qlt_minus_iff.
   apply Qlt_from_CRlt, H1.
  Qed.

  Lemma ball_triangle (e1 e2 : Q) a b c
    : ball e1 a b -> ball e2 b c -> ball (e1+e2) a c.
  Proof with auto.
   unfold ball.
   intros. destruct H, H0.
   assert (Qle 0 (e1+e2)).
   { apply (Qle_trans _ (e1+0)). rewrite Qplus_0_r.
     exact H. apply Qplus_le_r. exact H0. }
   split. exact H3.
   apply CRle_trans with (distance a b + distance b c).
   apply distance_triangle.
   rewrite <- CRplus_Qplus.
   apply CRplus_le_compat; assumption.
  Qed.

  Lemma ball_eq x y: (forall e, Qlt 0 e -> ball e x y) -> st_eq x y.
  Proof.
   unfold ball.
   intros.
   apply distance_refl.
   apply CRle_antisym. split.
   2: apply (dmsp_nonneg _ _ (dmsp X)).
   apply CRle_not_lt.
   intro abs.
   apply CRlt_Qmid in abs.
   destruct abs as [q [H1 H2]].
   apply Qlt_from_CRlt in H1.
   specialize (H q H1) as [_ H].
   revert H2.
   apply CRle_not_lt, H.
  Qed.

  Lemma is_MetricSpace: is_MetricSpace X ball.
  Proof with auto.
   constructor.
   - apply ball_refl.
   - apply ball_sym.
   - apply ball_triangle.
   - apply ball_closed.
   - apply ball_eq.
   - intros. destruct H. exact H.
   - unfold ball. split.
     destruct (Qlt_le_dec e 0).
     exfalso. contradict H; intros [H _].
     exact (Qlt_not_le _ _ q H). exact q.
     apply CRle_not_lt.
     intro abs.
     contradict H; intros [_ H].
     revert abs.
     apply CRle_not_lt, H. 
  Qed.

  Definition ballSpace: MetricSpace.
   apply (@Build_MetricSpace X ball).
    apply ball_wd.
   apply is_MetricSpace.
  Defined.

End from_alt.

(* Unfortunately, the other way around is not as direct,
   because the ball-based interface permits the distance
   between two points to be infinite, which CR does not support. *)
