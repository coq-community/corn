Require Import metric2.Complete metric2.Metric metric.

Require Import
  abstract_algebra stdlib_rationals
  orders.orders orders.semirings orders.rings theory.rings.

Import Qinf.notations.

Section QField.

Add Field Q : (dec_fields.stdlib_field_theory Q).

Section FromMetricSpace.

Variable X : MetricSpace.

Global Instance msp_mspc_ball : MetricSpaceBall X := λ (e : Qinf) (x y : X),
match e with
| Qinf.finite e' => gball e' x y
| Qinf.infinite => True
end.

Instance : Proper ((=) ==> (≡) ==> (≡) ==> iff) mspc_ball.
Proof.
intros e1 e2 E1 x1 x2 E2 y1 y2 E3.
destruct e1 as [e1 |]; destruct e2 as [e2 |];
try (unfold equiv, Qinf.eq in *; contradiction); try reflexivity.
unfold mspc_ball, msp_mspc_ball.
change (e1 = e2) in E1. now rewrite E1, E2, E3.
Qed.

Global Instance : ExtMetricSpaceClass X.
Proof.
constructor.
+ apply _.
+ intros; apply I.
+ intros; now apply gball_neg.
+ apply gball_refl.
+ intros [e |]; [apply gball_sym | easy].
+ apply gball_triangle.
+ apply gball_closed.
Qed.

Definition conv_reg (f : RegularFunction X) : Complete.RegularFunction X.
refine (@mkRegularFunction _ (f 0) (λ e : Qpos, let (e', _) := e in f e') _).
intros [e1 e1_pos] [e2 e2_pos]. now apply gball_pos, (rf_proof f).
Defined.

End FromMetricSpace.

Arguments conv_reg {X} _.

Set Printing Coercions.

Section FromCompleteMetricSpace.

Variable X : MetricSpace.

Global Instance limit_complete : Limit (Complete X) :=
  λ f : RegularFunction (Complete X), Cjoin_fun (conv_reg f).

Global Instance : CompleteMetricSpaceClass (Complete X).
Proof.
constructor; [| apply _].
apply ext_equiv_r; [intros x y E; apply E |].
intros f e1 e2 e1_pos e2_pos.
eapply gball_pos, (CunitCjoin (conv_reg f) (e1 ↾ e1_pos) (e2 ↾ e2_pos)).
Qed.

Lemma gball_complete (r : Q) (x y : Complete X) :
  gball r x y <->
  forall e1 e2 : Qpos, gball (QposAsQ e1 + r + QposAsQ e2)%mc (approximate x e1) (approximate y e2).
Proof.
destruct (Qsec.Qdec_sign r) as [[r_neg | r_pos] | r_zero].
+ split; intro H; [elim (gball_neg _ _ r_neg H) |].
  assert (H1 : 0 < -(r / 3)) by (apply Q.Qopp_Qlt_0_l, Q.Qmult_neg_pos; auto with qarith).
  specialize (H (exist _ _ H1) (exist _ _ H1)); simpl in H.
  mc_setoid_replace (- (r / 3) + r + - (r / 3)) with (r / 3) in H by (field; discriminate).
  exfalso; eapply gball_neg; [| apply H]; now eapply Q.Qopp_Qlt_0_l.
+ rewrite <- (gball_pos r_pos). simpl; unfold regFunBall. split; intros H e1 e2.
  - specialize (H e1 e2). apply gball_pos in H. apply H.
  - apply gball_pos, H.
+ rewrite r_zero. unfold gball at 1; simpl; unfold regFunEq. split; intros H e1 e2; specialize (H e1 e2).
  - apply gball_pos in H. now rewrite r_zero, Qplus_0_r.
  - apply gball_pos. now rewrite r_zero, Qplus_0_r in H.
Qed.

End FromCompleteMetricSpace.

Require Import CRmetric.

Section CompleteSegment.

Context {X : MetricSpace} (r : Q) (a : Complete X).

Global Program Instance : Limit (sig (mspc_ball r a)) :=
  λ f, exist _ (lim (Build_RegularFunction (@proj1_sig _ _ ∘ f) _)) _.
Next Obligation.
apply f.
Qed.
Next Obligation.
apply gball_complete; intros e1 e2.
unfold lim, limit_complete, Cjoin_fun, Cjoin_raw; simpl.
assert (H : mspc_ball r a ((@proj1_sig _ _ ∘ f) ((1 # 2) * QposAsQ e2)%Q)) by
  apply (proj2_sig (f ((1 # 2) * e2))).
unfold mspc_ball, msp_mspc_ball in H.
apply gball_weak_le with (q := QposAsQ e1 + r + (QposAsQ ((1 # 2) * e2)%Qpos)).
+ apply Qplus_le_r. apply Q.Qle_half; auto.
+ apply gball_complete, H.
Qed.

Global Instance : CompleteMetricSpaceClass (sig (mspc_ball r a)).
Proof.
constructor; [| apply _].
apply ext_equiv_r; [intros x y E; apply E |].
intros f e1 e2 e1_pos e2_pos; unfold Datatypes.id.
assert (C : CompleteMetricSpaceClass (Complete X)) by apply _.
destruct C as [C _].
assert (R : IsRegularFunction (@proj1_sig _ _ ∘ f)) by apply f.
specialize (C (Build_RegularFunction _ R) (Build_RegularFunction _ R)). now apply C.
Qed.

End CompleteSegment.

Require Import CRArith CRball CRabs.

Add Ring CR : (stdlib_ring_theory CR).

Close Scope CR_scope.
Unset Printing Coercions.

(* The following has to be generalized from CR to a metric space where
[ball r x y] is defined as [abs (x - y) ≤ r], probably a normed vector
space *)
Global Instance sum_lip `{MetricSpaceBall X}
  (f g : X -> CR) `{!IsLipschitz f Lf} `{!IsLipschitz g Lg} :
  IsLipschitz (f +1 g) (Lf + Lg).
Proof.
constructor.
+ pose proof (lip_nonneg f Lf); pose proof (lip_nonneg g Lg); change (0 ≤ Lf + Lg);
  solve_propholds.
+ intros x1 x2 e A. change (Lf + Lg)%Q with (Lf + Lg). rewrite plus_mult_distr_r.
  apply CRgball_plus; [now apply: (lip_prf f Lf) | now apply: (lip_prf g Lg)].
Qed.

End QField.

