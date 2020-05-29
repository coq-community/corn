(*
Copyright © 2006-2008 Russell O’Connor
Copyright © 2020 Vincent Semeria

Permission is hereby granted, free of charge, to any person obtaining a copy of
this proof and associated documentation files (the "Proof"), to deal in
the Proof without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Proof, and to permit persons to whom the Proof is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Proof.

THE PROOF IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE PROOF OR THE USE OR OTHER DEALINGS IN THE PROOF.
*)
Require Import CoRN.algebra.RSetoid.
Require Export CoRN.metric2.Metric.
Require Import CoRN.metric2.Prelength.
Require Import CoRN.metric2.Classification.
Require Import CoRN.model.totalorder.QMinMax.
Require Import Coq.QArith.Qabs.
Require Import CoRN.tactics.CornTac.
Require Import CoRN.metric2.UniformContinuity.
Require Import MathClasses.implementations.stdlib_rationals.

Set Implicit Arguments.
Set Automatic Introduction.

Local Open Scope Q_scope.

Opaque Qabs.

Definition QAbsSmall (e x : Q) : Prop := -e <= x /\ x <= e.

Lemma QAbsSmall_opp : forall x y : Q, QAbsSmall x y -> QAbsSmall x (-y).
Proof.
  intros x y H. split.
  apply Qopp_le_compat. apply H.
  rewrite <- (Qopp_involutive x).
  apply Qopp_le_compat. apply H.
Qed.

(**
** Example of a Metric: <Q, Qball>
*) 

Definition Qball (e : Qpos) (a b : Q) := QAbsSmall (e:Q) (a - b).

Lemma AbsSmall_Qabs : forall x y, (Qabs y <= x)%Q <-> QAbsSmall x y.
Proof.
 cut (forall x y, (0 <= y)%Q -> ((Qabs y <= x)%Q <-> QAbsSmall x y)).
  intros H x y.
  generalize (H x y) (H x (-y)%Q).
  clear H.
  rewrite -> Qabs_opp.
  apply Qabs_case; intros H H1 H2.
   auto.
  assert (X:QAbsSmall x y <-> QAbsSmall x (- y)%Q).
   split.
    apply QAbsSmall_opp.
    intros X. unfold QAbsSmall.
    rewrite <- (Qopp_involutive y).
   apply QAbsSmall_opp.
   assumption.
  rewrite -> X.
  apply H2.
  rewrite -> Qle_minus_iff in H.
  ring_simplify in H.
  ring_simplify.
  apply H.
 intros x y H.
 rewrite -> Qabs_pos;[|assumption].
 split.
  intros H0.
  split. 2 : exact H0.
  refine (Qle_trans _ 0 _ _ H).
  apply (Qopp_le_compat 0 x).
  exact (Qle_trans _ _ _ H H0).
 intros [_ H0].
 assumption.
Qed.

Lemma Qball_Qabs : forall e a b, Qball e a b <-> Qabs (a - b) <= e.
Proof. split; apply AbsSmall_Qabs. Qed.

Lemma Qle_closed : (forall e x, (forall d : Qpos, x <= e+d) -> x <= e).
Proof.
 intros. 
 apply Qnot_lt_le. intro abs.
 assert (0 < (x - e) * (1#2)) as H0.
 { apply (Qle_lt_trans _ (0*(1#2))). discriminate.
   apply Qmult_lt_r. reflexivity.
   rewrite <- (Qplus_opp_r e). apply Qplus_lt_l. exact abs. } 
 specialize (H (exist _ _ H0)). simpl in H.
 apply (Qplus_le_l _ _ (-x*(1#2))) in H.
 ring_simplify in H. apply Qmult_le_l in H.
 exact (Qle_not_lt _ _ H abs). reflexivity.
Qed.

Definition QS : RSetoid := Build_RSetoid Q_Setoid.
Canonical Structure QS.

Instance Qball_Reflexive e: Reflexive (Qball e).
Proof.
 intros x.
 unfold Qball. unfold QAbsSmall, Qminus.
 rewrite Qplus_opp_r. split.
 apply (Qopp_le_compat 0 e).
 destruct e. apply Qlt_le_weak, q.
 destruct e. apply Qlt_le_weak, q.
Qed.

Instance Qball_symmetric e: Symmetric (Qball e).
Proof.
 intros x y.
 unfold Qball.
 intros. apply QAbsSmall_opp in H.
 unfold QAbsSmall. destruct H. split.
 apply (Qle_trans _ _ _ H). ring_simplify. apply Qle_refl.
 refine (Qle_trans _ _ _ _ H0). ring_simplify. apply Qle_refl. 
Qed.

Lemma Q_is_MetricSpace : is_MetricSpace QS Qball.
Proof.
 split; auto with typeclass_instances.
 - (* triangle inequality *)
   intros [e1  He1] [e2 He2] a b c H1 H2.
   unfold Qball. unfold QAbsSmall. simpl.
   setoid_replace (a-c) with ((a-b)+(b-c)).
   2: ring. split. apply (Qle_trans _ (-e1 + -e2)).
   ring_simplify. apply Qle_refl.
   apply Qplus_le_compat. apply H1. apply H2.
   apply Qplus_le_compat. apply H1. apply H2.
 - (* distance closed *)
   intros e a b H. split.
   apply Qle_closed. intros. specialize (H d). destruct H.
   apply (Qplus_le_l _ _ (-d)). ring_simplify.
   simpl in H. ring_simplify in H. exact H.
   apply Qle_closed. intros. apply H.
 - intros. apply Qle_antisym. apply Qle_closed.
   intros. specialize (H d). destruct H.
   apply (Qplus_le_l _ _ b) in H0. ring_simplify in H0. exact H0.
   apply Qle_closed. intros. specialize (H d). destruct H.
   apply (Qplus_le_l _ _ (b+d)) in H. ring_simplify in H.
   rewrite Qplus_comm. exact H.
Qed.

(* begin hide *)
Add Morphism Qball with signature QposEq ==> Qeq ==> Qeq ==> iff as Qball_wd.
Proof.
 intros [x1 Hx1] [x2 Hx2] H x3 x4 H0 x5 x6 H1.
 unfold Qball.
 unfold QAbsSmall.
 simpl.
 rewrite -> H0.
 rewrite -> H1.
 unfold QposEq in H.
 simpl in H.
 rewrite -> H.
 tauto.
Qed.
(* end hide *)
Definition Q_as_MetricSpace : MetricSpace :=
@Build_MetricSpace QS _ Qball_wd Q_is_MetricSpace.

Canonical Structure Q_as_MetricSpace.

Lemma QPrelengthSpace_help
  : forall (e d1 d2:Qpos), e < d1+d2 -> forall (a b c:QS),
      ball e a b -> (c == (a*d2 + b*d1)/(d1+d2)%Qpos) -> ball d1 a c.
Proof with auto with *.
 intros e d1 d2 He a b c Hab Hc.
 simpl.
 unfold Qball.
 unfold QAbsSmall. rewrite Hc. clear Hc c.
 assert (0 < d1 + d2).
 { apply (Qlt_trans _ e). destruct e. exact q. exact He. }
 split.
 - apply (Qmult_le_r _ _ (d1+d2)). exact H. 
   simpl. field_simplify.
   2: apply (@Qpos_nonzero (d1+d2)%Qpos).
   apply (Qle_trans _ (d1 * (-(d1 + d2)))).
   field_simplify. apply Qle_refl.
   apply (Qle_trans _ (d1 * (a - b))).
   apply Qmult_le_l. destruct d1. exact q.
   destruct Hab. apply (Qle_trans _ (-e)).
   apply Qopp_le_compat, Qlt_le_weak, He. exact H0.
   field_simplify. apply Qle_refl.
 - apply (Qmult_le_r _ _ (d1+d2)). exact H.
   simpl. field_simplify.
   2: apply (@Qpos_nonzero (d1+d2)%Qpos).
   apply (Qle_trans _ (d1 * (a-b))).
   field_simplify. apply Qle_refl.
   apply (Qle_trans _ (d1 * (d1 + d2))).
   apply Qmult_le_l. destruct d1. exact q.
   destruct Hab. apply (Qle_trans _ e). exact H1.
   apply Qlt_le_weak, He.
   field_simplify. apply Qle_refl.
Qed.

(** Q is a prelength space *)
Lemma QPrelengthSpace : PrelengthSpace Q_as_MetricSpace.
Proof.
 intros a b e d1 d2 He Hab.
 pose (c:= (a * d2 + b * d1) / (d1 + d2)%Qpos).
 exists c.
  apply (@QPrelengthSpace_help e d1 d2 He a b c); try assumption.
  reflexivity.
 apply ball_sym.
 eapply QPrelengthSpace_help.
   rewrite -> Qplus_comm.
   apply He.
  apply ball_sym.
  apply Hab.
 unfold c.
 unfold Qdiv.
 apply Qmult_comp.
  ring.
 apply Qinv_comp.
 QposRing.
Qed.

(** Q is a decideable metric, and hence located and stable. *)
Lemma Qmetric_dec : decidableMetric Q_as_MetricSpace.
Proof.
 intros e a b.
 simpl.
 unfold Qball, QAbsSmall.
 simpl.
 set (c:=-e).
 set (d:=(a-b)).
 destruct (Qlt_le_dec_fast d c) as [Hdc|Hdc].
  right.
  abstract( intros [H1 H2]; apply (Qlt_not_le _ _ Hdc H1) ).
 destruct (Qlt_le_dec_fast e d) as [Hed|Hed].
  right.
  abstract( intros [H1 H2]; apply (Qlt_not_le _ _ Hed H2) ).
 left.
 abstract auto.
Defined.

Hint Resolve Qmetric_dec : metricQ.

Lemma locatedQ : locatedMetric Q_as_MetricSpace.
Proof.
 apply decidable_located.
 auto with *.
Defined.

Hint Resolve locatedQ : metricQ.

Lemma stableQ : stableMetric Q_as_MetricSpace.
Proof.
 apply located_stable.
 auto with *.
Qed.

Hint Resolve stableQ : metricQ.

Lemma in_Qball (r: Qpos) (x y: Q): (x - r <= y <= x + r) <-> Qball r x y.
Proof.
 now rewrite Qball_Qabs, Q.Qabs_diff_Qle.
Qed.

Lemma in_centered_Qball (w: Qpos) (m x: Q):
  m <= x <= m + w ->
  Qball ((1#2) * w) (m + (1#2) * w) x.
Proof.
 intros [??].
 apply in_Qball.
 split; simpl; ring_simplify; assumption.
Qed. 

Lemma nonneg_in_Qball_0 (x : Q) (Eq : 0 <= x) (ε : Qpos) : 
  x <= ε <-> ball ε x 0.
Proof.
  rewrite <-in_Qball.
  split.
   intros ?. split.
    apply (Q.Qplus_le_r ε). now ring_simplify.
   now apply Q.Qplus_nonneg; auto with *.
  intros [? ?].
  apply (Q.Qplus_le_r (-ε)). 
  rewrite Qplus_comm. now ring_simplify.
Qed.

Section Qball_Qmult.

  Variables (d : Qpos) (z x y: Q) (B: Qball (d / QabsQpos z) x y).

  Lemma Qball_Qmult_Q_r : Qball d (x * z) (y * z).
  Proof with auto.
   destruct (Qeq_dec z 0) as [E|E].
    rewrite E. do 2 rewrite Qmult_0_r. apply ball_refl.
   apply Qball_Qabs.
   apply Qball_Qabs in B.
   setoid_replace (x * z - y * z) with ((x - y) * z)%Q by (simpl; ring).
   rewrite Qabs_Qmult.
   setoid_replace (Qabs z) with (QabsQpos z).
    setoid_replace (QposAsQ d) with  (d * Qpos_inv (QabsQpos z) * QabsQpos z).
     apply Qmult_le_compat_r...
    simpl. field. apply Qpos_nonzero.
   symmetry. apply QabsQpos_correct...
  Qed.

  Lemma Qball_Qmult_Q_l : Qball d (z * x) (z * y).
  Proof.
   intros.
   do 2 rewrite (Qmult_comm z).
   apply Qball_Qmult_Q_r.
  Qed.

End Qball_Qmult.

Section more_Qball_Qmult.

  Variables (d z : Qpos) (x y: Q) (B: Qball (d / z) x y).

  Lemma Qball_Qmult_r: Qball d (x * z) (y * z).
  Proof with auto.
   apply Qball_Qmult_Q_r. rewrite QabsQpos_Qpos...
  Qed.

  Lemma Qball_Qmult_l: Qball d (z * x) (z * y).
  Proof with auto.
   apply Qball_Qmult_Q_l. rewrite QabsQpos_Qpos...
  Qed.

End more_Qball_Qmult.

Lemma Qball_plus (e d: Qpos) (x x' y y': Q):
 Qball e x x' -> Qball d y y' -> Qball (e + d) (x + y) (x' + y').
Proof with auto.
 intros.
 apply ball_triangle with (x' + y); apply Qball_Qabs.
  setoid_replace (x + y - (x' + y))%Q with (x - x') by (simpl; ring).
  apply Qball_Qabs...
 setoid_replace (x' + y - (x' + y')) with (y - y') by (simpl; ring).
 apply Qball_Qabs...
Qed.

Lemma Qball_plus_r (e: Qpos) (x y y': Q):
 Qball e y y' -> Qball e (x + y) (x + y').
Proof with auto.
 intros B.
 apply Qball_Qabs.
 apply Qball_Qabs in B.
 setoid_replace (x + y - (x + y')) with (y - y') by (simpl; ring)...
Qed.

Lemma Qball_0_r (e: Qpos) : Qball e e 0.
Proof with auto with qarith.
 apply Qball_Qabs. 
 setoid_replace (e - 0) with e by ring.
 rewrite Qabs_pos...
Qed.

Lemma Qball_0_l (e: Qpos) : Qball e 0 e.
Proof with auto with qarith.
 apply ball_sym. apply Qball_0_r.
Qed.

Lemma Qball_Qdiv_inv (d z: Qpos) (x y: Q):
  Qball (d / z) (x / z) (y / z) -> Qball d x y.
Proof with auto.
 intros.
 rewrite
   <- (Qmult_1_r x), <- (Qmult_1_r y),
   <- (Qmult_inv_r z), (Qmult_comm z),
   Qmult_assoc, Qmult_assoc...
 apply Qball_Qmult_r...
Qed.

Lemma Qball_opp (e : Qpos) (x x' : Q):
 Qball e x x' -> Qball e (-x) (-x').
Proof with auto.
 intros.
 apply Qball_Qabs.
 unfold Qminus.
 rewrite Qopp_involutive.
 rewrite Qplus_comm.
 apply Qball_Qabs. 
 apply ball_sym...
Qed.

Require Import Coq.QArith.Qround.

Lemma Qfloor_ball q:
  Qball (1#2) ((Qfloor q # 1) + (1#2)) q.
Proof with auto with *.
 intros.
 apply Qball_Qabs.
 simpl QposAsQ.
 apply Qabs_case; intros.
 apply Q.Qplus_le_l with ((-1#2)%Q + q).
 ring_simplify. apply Qfloor_le.
 pose proof (Qlt_floor q).
 apply (Qplus_le_l _ _ ((1#2) + (Qfloor q # 1))). ring_simplify.
 apply Qlt_le_weak. rewrite inject_Z_plus in H0. apply H0.
Qed.

(** A boolean version of Qball. *)
Definition Qball_ex_bool e a b : bool := 
 match ball_ex_dec _ Qmetric_dec e a b with left _ => true | right _ => false end.

Instance: Proper (QposInfEq ==> @st_eq _ ==> @st_eq _ ==> eq) Qball_ex_bool.
Proof.
  intros [ε1|] [ε2|] E1 x1 x2 E2 y1 y2 E3; try easy.
  unfold Qball_ex_bool.
  case (ball_ex_dec _ Qmetric_dec ε1 x1 y1); case (ball_ex_dec _ Qmetric_dec ε2 x2 y2); intros E4 E5; try easy.
   destruct E4. now eapply ball_wd; eauto; symmetry.
  destruct E5. now eapply ball_wd; eauto; symmetry.
Qed.

Lemma Qball_ex_bool_correct (ε : Qpos) x y : Is_true (Qball_ex_bool ε x y) <-> Qball ε x y.
Proof.
  split; intros E.
  apply Is_true_eq_true in E.
  unfold Qball_ex_bool in E.
  destruct (ball_ex_dec Q_as_MetricSpace Qmetric_dec ε x y).
  apply b. discriminate.
  apply Is_true_eq_left. unfold Qball_ex_bool.
  destruct (ball_ex_dec Q_as_MetricSpace Qmetric_dec ε x y).
  reflexivity. contradiction.
Qed.

Lemma gball_Qabs (e a b : Q) : gball e a b <-> (Qabs (a - b) <= e).
Proof.
unfold gball. destruct (Q_dec e) as [[e_neg | e_pos] | e_zero].
+ split; intros H; [easy |]. assert (H1 := Qle_lt_trans _ _ _ H e_neg).
  eapply Qle_not_lt; [apply Qabs_nonneg | apply H1].
+ apply Qball_Qabs.
+ split; intro H.
  - rewrite e_zero, H; setoid_replace (b - b) with 0 by ring; apply Qle_refl.
  - rewrite e_zero in H. apply Q.Qabs_nonpos in H; now apply Q.Qminus_eq.
Qed.

