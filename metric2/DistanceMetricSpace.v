
Require Import CoRN.algebra.RSetoid.
Require Import CoRN.model.totalorder.QposMinMax.
Require CoRN.model.structures.NNUpperR.
Import NNUpperR.notations.
Import QnonNeg.notations QnonNeg.coercions NNUpperR.coercions.

Require Import CoRN.metric2.Metric.

Open Scope NNUpperR_scope.

Record is_DistanceMetricSpace (X : RSetoid) (distance: X -> X -> NNUpperR) : Prop
  := Build_is_DistanceMetricSpace
  { dmsp_refl: forall x y, st_eq x y <-> distance x y == 0%Qnn
  ; dmsp_sym: forall x y, distance x y == distance y x
  ; dmsp_triangle: forall x y z, distance x z <= distance x y + distance y z
  }.

Record DistanceMetricSpace: Type := Build_alt_MetricSpace
  { dmsp_is_setoid:> RSetoid;
    distance: dmsp_is_setoid -> dmsp_is_setoid -> NNUpperR.T;
    distance_wd: Proper (@st_eq _ ==> @st_eq _ ==> NNUpperR.eq) distance;
    dmsp : is_DistanceMetricSpace dmsp_is_setoid distance }.

Arguments distance [d].
Existing Instance distance_wd.

Section DistanceMetricSpace. (* Just mimicking Russell's code for MetricSpace here. *)

  Context {X: DistanceMetricSpace}.

  Lemma distance_refl (x y: X): st_eq x y <-> distance x y == 0%Qnn.
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
    := exists qpos : Qle 0 q, distance x y <= inject_Qnn (exist _ _ qpos).

  Instance ball_wd: Proper (Qeq ==> @st_eq X ==> @st_eq X ==> iff) ball.
  Proof.
   intros ?? E ?? F ?? G. unfold ball.
   split.
   - intros [qpos H]. assert (Qle 0 y). rewrite <- E. exact qpos.
     exists H0. rewrite <- F, <- G.
     assert (QnonNeg.eq (exist (Qle 0) x qpos) (exist (Qle 0) y H0)).
     apply E. rewrite <- H1. exact H.
   - intros [qpos H]. assert (Qle 0 x). rewrite E. exact qpos.
     exists H0. rewrite F, G.
     assert (QnonNeg.eq (exist (Qle 0) x H0) (exist (Qle 0) y qpos)).
     apply E. rewrite H1. exact H.
  Qed.

  Lemma ball_refl e: Qle 0 e -> Reflexive (ball e).
  Proof.
   unfold Reflexive, ball. intros. exists H.
   rewrite (proj1 (distance_refl x x)).
    apply NNUpperR.le_0.
   reflexivity.
  Qed.

  Lemma ball_sym e: Symmetric (ball e).
  Proof with auto.
   unfold Symmetric, ball. intros.
   destruct H as [qpos H]. exists qpos.
   rewrite distance_sym...
  Qed.

  Lemma ball_closed (e:Q) x y: (forall d, 0 < d -> ball (e+d) x y) -> ball e x y.
  Proof with auto.
   unfold ball. intros.
   assert (Qle 0 e).
   { apply Qnot_lt_le. intro abs.
     destruct (H (-e*(1#2))%Q). rewrite <- (Qmult_0_l (1#2)).
     apply Qmult_lt_r. reflexivity.
     apply (Qplus_lt_l _ _ e). ring_simplify. exact abs.
     clear H0. ring_simplify in x0.
     rewrite <- (Qmult_0_r (1#2)) in x0.
     apply Qmult_le_l in x0. exact (Qlt_not_le _ _ abs x0). reflexivity. }
   exists H0.
   apply NNUpperR.le_closed. intros [d dpos].
   rewrite <- NNUpperR.plus_homo.
   specialize (H d dpos) as [qpos H].
   assert (QnonNeg.eq (exist (Qle 0) e H0 + from_Qpos (exist (Qlt 0) d dpos))%Qnn
                      (exist (Qle 0) (e + d)%Q qpos))
     by reflexivity.
   rewrite H1. exact H.
  Qed.

  Lemma ball_triangle (e1 e2 : Q) a b c
    : ball e1 a b -> ball e2 b c -> ball (e1+e2) a c.
  Proof with auto.
   unfold ball.
   intros. destruct H, H0.
   assert (Qle 0 (e1+e2)).
   { apply (Qle_trans _ (e1+0)). rewrite Qplus_0_r.
     exact x. apply Qplus_le_r. exact x0. }
   exists H1.
   apply NNUpperR.le_trans with (distance a b + distance b c).
    apply distance_triangle.
    assert (QnonNeg.eq (exist (Qle 0) (e1 + e2)%Q H1)
                       (exist (Qle 0) e1 x + exist (Qle 0) e2 x0)%Qnn)
      by reflexivity.
    rewrite H2.
    rewrite NNUpperR.plus_homo.
   apply NNUpperR.plus_le_compat...
  Qed.

  Lemma ball_eq x y: (forall e, Qlt 0 e -> ball e x y) -> st_eq x y.
  Proof with auto.
   unfold ball.
   intros.
   apply distance_refl.
   apply NNUpperR.le_0_eq.
   apply NNUpperR.le_closed.
   intros.
   rewrite NNUpperR.plus_0_l.
   destruct d as [d dpos].
   specialize (H d dpos) as [qpos H].
   assert (QnonNeg.eq (from_Qpos (exist (Qlt 0) d dpos))
                      (exist (Qle 0) d qpos)) by reflexivity.
   rewrite H0. exact H.
  Qed.

  Lemma is_MetricSpace: is_MetricSpace X ball.
  Proof with auto.
   constructor.
   - apply ball_refl.
   - apply ball_sym.
   - apply ball_triangle.
   - apply ball_closed.
   - apply ball_eq.
   - intros. destruct H. exact x.
  Qed.

  Definition ballSpace: MetricSpace.
   apply (@Build_MetricSpace X ball).
    apply ball_wd.
   apply is_MetricSpace.
  Defined.

End from_alt.

(* Unfortunately, the other way around is not as direct, because the ball-based interface
permits the distance between two points to be infinite, which NNUpperR does not support. *)
