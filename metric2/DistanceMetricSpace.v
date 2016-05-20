
Require CoRN.model.structures.NNUpperR.
Import NNUpperR.notations.
Import QnonNeg.notations.

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

Implicit Arguments distance [d].
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

  Definition ball (q: Qpos) (x y: X): Prop := distance x y <= q.

  Instance ball_wd: Proper (QposEq ==> @st_eq X ==> @st_eq X ==> iff) ball.
  Proof.
   intros ?? E ?? F ?? G. unfold ball.
   rewrite E, F, G. reflexivity.
  Qed.

  Lemma ball_refl e: Reflexive (ball e).
  Proof.
   unfold Reflexive, ball. intros.
   rewrite (proj1 (distance_refl x x)).
    apply NNUpperR.le_0.
   reflexivity.
  Qed.

  Lemma ball_sym e: Symmetric (ball e).
  Proof with auto.
   unfold Symmetric, ball. intros.
   rewrite distance_sym...
  Qed.

  Lemma ball_closed e x y: (forall d, ball (e + d) x y) -> ball e x y.
  Proof with auto.
   unfold ball. intros.
   apply NNUpperR.le_closed. intros.
   rewrite <- NNUpperR.plus_homo.
   rewrite <- QnonNeg.from_Qpos_plus_homo...
  Qed.

  Lemma ball_triangle e1 e2 a b c: ball e1 a b -> ball e2 b c -> ball (e1 + e2) a c.
  Proof with auto.
   unfold ball.
   intros.
   apply NNUpperR.le_trans with (distance a b + distance b c).
    apply distance_triangle.
   rewrite QnonNeg.from_Qpos_plus_homo.
   rewrite NNUpperR.plus_homo.
   apply NNUpperR.plus_le_compat...
  Qed.

  Lemma ball_eq x y: (forall e, ball e x y) -> st_eq x y.
  Proof with auto.
   unfold ball.
   intros.
   apply distance_refl.
   apply NNUpperR.le_0_eq.
   apply NNUpperR.le_closed.
   intros.
   rewrite NNUpperR.plus_0_l...
  Qed.

  Lemma is_MetricSpace: is_MetricSpace X ball.
  Proof with auto.
   constructor.
       apply ball_refl.
      apply ball_sym.
     apply ball_triangle.
    apply ball_closed.
   apply ball_eq.
  Qed.

  Definition ballSpace: MetricSpace.
   apply (@Build_MetricSpace X ball).
    apply ball_wd.
   apply is_MetricSpace.
  Defined.

End from_alt.

(* Unfortunately, the other way around is not as direct, because the ball-based interface
permits the distance between two points to be infinite, which NNUpperR does not support. *)
