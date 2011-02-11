(*
Copyright © 2006-2008 Russell O’Connor

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
Require Export Metric.
Require Import Prelength.
Require Import Classification.
Require Import QMinMax.
Require Import COrdAbs.
Require Import Qordfield.
Require Import Qabs.
Require Import CornTac.
Require Import UniformContinuity.

Set Implicit Arguments.
Set Automatic Introduction.

Open Local Scope Q_scope.

Opaque Qabs.

(**
** Example of a Metric: <Q, Qball>
*)

Definition Qball (e : Qpos) (a b : Q) := AbsSmall (e:Q) (a - b).

Lemma AbsSmall_Qabs : forall x y, (Qabs y <= x)%Q <-> AbsSmall x y.
Proof.
 cut (forall x y, (0 <= y)%Q -> ((Qabs y <= x)%Q <-> AbsSmall (R:=Q_as_COrdField) x y)).
  intros H x y.
  generalize (H x y) (H x (-y)%Q).
  clear H.
  rewrite -> Qabs_opp.
  apply Qabs_case; intros H H1 H2.
   auto.
  assert (X:AbsSmall (R:=Q_as_COrdField) x y <-> AbsSmall (R:=Q_as_COrdField) x (- y)%Q).
   split.
    apply inv_resp_AbsSmall.
   intros X.
   stepr (- - y)%Q; [| simpl; ring].
   apply inv_resp_AbsSmall.
   assumption.
  rewrite -> X.
  apply: H2.
  rewrite -> Qle_minus_iff in H.
  ring_simplify in H.
  ring_simplify.
  apply H.
 intros x y H.
 rewrite -> Qabs_pos;[|assumption].
 split.
  intros H0.
  apply leEq_imp_AbsSmall; assumption.
 intros [_ H0].
 assumption.
Qed.

Lemma Qball_Qabs : forall e a b, Qball e a b <-> Qabs (a - b) <= e.
Proof. split; apply AbsSmall_Qabs. Qed.

Lemma Qle_closed : (forall e x, (forall d : Qpos, x <= e+d) -> x <= e).
Proof.
 intros.
 apply: shift_zero_leEq_minus'.
 apply: inv_cancel_leEq.
 apply: approach_zero_weak;simpl.
 intros.
 replace LHS with (x[-](e:Q)).
  apply: shift_minus_leEq;simpl.
  stepr (e+e0); [| simpl; ring].
  rewrite <- (QposAsmkQpos H0).
  apply (H (mkQpos H0)).
 unfold cg_minus; simpl; ring.
Qed.

Notation QS  := Q_is_Setoid (only parsing).

Instance Qball_Reflexive e: Reflexive (Qball e).
Proof.
 intros x.
 unfold Qball.
 apply AbsSmall_wdr with 0.
  apply (zero_AbsSmall _ (e:Q)).
  apply less_leEq.
  apply Qpos_prf.
 simpl; ring.
Qed.

Instance Qball_symmetric e: Symmetric (Qball e).
Proof.
 intros x y.
 unfold Qball.
 apply AbsSmall_minus.
Qed. 

Lemma Q_is_MetricSpace : is_MetricSpace QS Qball.
Proof.
 split; auto with typeclass_instances.
   intros [e1  He1] [e2 He2] a b c H1 H2.
   unfold Qball.
   apply AbsSmall_wdr with ((a-b)+(b-c)).
    autorewrite with QposElim.
    apply AbsSmall_plus; assumption.
   simpl; ring.
  intros e a b H.
  unfold Qball.
  split.
   apply inv_cancel_leEq;simpl.
   stepr (e: Q); [| simpl; ring].
   apply Qle_closed.
   intros.
   destruct (H d).
   apply: inv_cancel_leEq;simpl.
   stepr (a-b); [| simpl; ring].
   destruct e; destruct d; apply H0.
  apply Qle_closed.
  intros d.
  destruct (H d).
  destruct e; destruct d; apply H1.
 intros.
 apply: cg_inv_unique_2.
 apply: AbsSmall_approach_zero;simpl.
 intros e H0.
 rewrite <- (QposAsmkQpos H0).
 apply (H (mkQpos H0)).
Qed.
(* begin hide *)
Add Morphism Qball with signature QposEq ==> Qeq ==> Qeq ==> iff as Qball_wd.
Proof.
 intros [x1 Hx1] [x2 Hx2] H x3 x4 H0 x5 x6 H1.
 unfold Qball.
 unfold AbsSmall.
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
(* begin hide *)
Canonical Structure Q_as_MetricSpace.
(* end hide *)
Lemma QPrelengthSpace_help : forall (e d1 d2:Qpos), e < d1+d2 -> forall (a b c:QS), ball e a b -> (c == (a*d2 + b*d1)/(d1+d2)%Qpos) -> ball d1 a c.
Proof with auto with *.
 intros e d1 d2 He a b c Hab Hc.
 simpl.
 unfold Qball.
 apply AbsSmall_wdr with ((d1/(d1+d2)%Qpos)*(a - b)).
  apply AbsSmall_wdl with ((d1/(d1+d2)%Qpos)*(d1+d2)%Qpos).
   apply mult_resp_AbsSmall.
   apply less_leEq.
   apply (div_resp_pos _  _ (d1:Q) (@Qpos_nonzero (d1+d2)%Qpos)); apply Qpos_prf.
   destruct d1; destruct d2; apply (AbsSmall_trans _ (e:Q)); assumption.
  simpl. field. intro.
  apply (Qlt_irrefl (d1 + d2)).
  apply Qlt_trans with e...
  rewrite H...
 simpl.
 rewrite -> Hc.
 pose (@Qpos_nonzero (d1 + d2)%Qpos).
 QposField.
 assumption.
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
 unfold Qball, AbsSmall.
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
Proof with auto.
 revert r x y.
 intros [r rp] x y.
 split; intro E.
  apply Qball_Qabs.
  simpl QposAsQ in *.
  apply Q.Qabs_diff_Qle...
 apply Qball_Qabs in E.
 simpl QposAsQ in *.
 apply Q.Qabs_diff_Qle...
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

Require Import Qround.

Lemma Qfloor_ball q:
  Qball (1#2) (Qfloor q + (1#2)) q.
Proof with auto with *.
 intros.
 apply Qball_Qabs.
 simpl QposAsQ.
 apply Qabs_case; intros.
  apply Q.Qplus_le_l with ((-1#2)%Q + q).
  ring_simplify...
 apply Q.Qplus_le_l with ((-1#2)%Q + Qfloor q + 1).
 ring_simplify.
 setoid_replace (Qfloor q + 1) with ((Qfloor q + 1)%Z:Q)...
 symmetry.
 rewrite injz_plus.
 reflexivity.
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

Lemma sumbool_eq_true P (dec: {P}+{~P}) : match dec with left _ => true | right _ => false end = true <-> P.
Proof.
 intros.
 destruct dec; simpl; split; auto.
 discriminate 1.
Qed.

Lemma Qball_ex_bool_correct (ε : Qpos) x y : Is_true (Qball_ex_bool ε x y) <-> Qball ε x y.
Proof.
  split; intros E.
   apply Is_true_eq_true in E.
   now apply sumbool_eq_true in E.
  apply Is_true_eq_left.
  now apply sumbool_eq_true.
Qed.
