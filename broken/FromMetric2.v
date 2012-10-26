Require Import metric2.Complete metric2.Metric metric.

Lemma Qle_half (x : Q) : 0 <= x -> (1 # 2) * x <= x.
Proof.
intro H. rewrite <- (Qmult_1_l x) at 2. apply Qmult_le_compat_r; auto with qarith.
Qed.

Lemma Qmult_neg_pos (x y : Q) : x < 0 -> 0 < y -> x * y < 0.
Proof.
intros H1 H2.
apply Q.Qopp_Qlt_0_l. setoid_replace (- (x * y)) with ((- x) * y) by ring.
apply Q.Qmult_lt_0_compat; trivial. now apply Q.Qopp_Qlt_0_l.
Qed.

Lemma Qmult_pos_neg (x y : Q) : 0 < x -> y < 0 -> x * y < 0.
Proof. intros H1 H2. rewrite Qmult_comm. now apply Qmult_neg_pos. Qed.

Lemma Qmult_pos_r : forall x y : Q, 0 <= x -> 0 < x * y -> 0 < y.
Proof.
intros x y H1 H2.
destruct (Qsec.Qdec_sign y) as [[? | ?] | H]; trivial.
+ exfalso. apply (Qlt_irrefl 0), Qlt_le_trans with (y := x * y); trivial.
  now apply Q.Qmult_nonneg_nonpos; [| apply Qlt_le_weak].
+ rewrite H, Qmult_0_r in H2. exfalso; now apply (Qlt_irrefl 0).
Qed.

Lemma Qmult_pos_l : forall x y : Q, 0 <= y -> 0 < x * y -> 0 < x.
Proof. intros x y H1 H2. rewrite Qmult_comm in H2. now apply (Qmult_pos_r y x). Qed.

Require Import
  abstract_algebra stdlib_rationals
  orders.orders orders.semirings orders.rings theory.rings.

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

Lemma gball_pos {e : Q} (e_pos : 0 < e) (x y : X) : ball (e ↾ e_pos) x y <-> gball e x y.
Proof.
unfold gball. destruct (Qsec.Qdec_sign e) as [[e_neg | e_pos'] | e_zero].
+ elim (Qlt_irrefl _ (Qlt_trans _ _ _ e_pos e_neg)).
+ mc_setoid_replace (e ↾ e_pos) with (e ↾ e_pos'); easy.
+ exfalso; rewrite e_zero in e_pos; apply (Qlt_irrefl _ e_pos).
Qed.

Lemma gball_neg (e : Q) (x y : X) : e < 0 -> ~ gball e x y.
Proof.
intro e_neg. unfold gball. destruct (Qsec.Qdec_sign e) as [[E | E] | E]; [easy | |].
+ intros _; apply (Qlt_irrefl _ (Qlt_trans _ _ _ e_neg E)).
+ rewrite E in e_neg. intros _; apply (Qlt_irrefl _ e_neg).
Qed.

Lemma gball_closed (e : Q) (x y : X) :
   (∀ d : Q, 0 < d → gball (e + d) x y) → gball e x y.
Proof.
intro C. (*change (gball e x y).*) unfold gball.
destruct (Qsec.Qdec_sign e) as [[e_neg | e_pos] | e_zero].
+ assert (e / 2 < 0) by now apply neg_pos_mult.
  apply (gball_neg (e/2) x y); [easy |].
  mc_setoid_replace (e / 2) with (e - e / 2) by (field; discriminate).
  apply C; now apply flip_neg_negate.
+ apply (msp_closed (msp X)). intros [d d_pos]. now apply gball_pos, C.
+ apply ball_eq. intros [d d_pos]. apply gball_pos.
  setoid_replace d with (e + d); [now apply C | rewrite e_zero; symmetry; apply plus_0_l].
Qed.

Lemma gball_closed_eq (x y : X) : (∀ d : Q, 0 < d -> gball d x y) -> x = y.
Proof.
intro C. change (gball 0 x y). apply gball_closed. intro d.
setoid_replace (0 + d)%Q with d by apply plus_0_l. apply C.
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
+ split; intro H; [elim (gball_neg _ _ _ _ r_neg H) |].
  assert (H1 : 0 < -(r / 3)) by (apply Q.Qopp_Qlt_0_l, Qmult_neg_pos; auto with qarith).
  specialize (H (exist _ _ H1) (exist _ _ H1)); simpl in H.
  mc_setoid_replace (- (r / 3) + r + - (r / 3)) with (r / 3) in H by (field; discriminate).
  exfalso; eapply gball_neg; [| apply H]; now eapply Q.Qopp_Qlt_0_l.
+ rewrite <- (gball_pos _ r_pos). simpl; unfold regFunBall. split; intros H e1 e2.
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
+ apply Qplus_le_r. apply Qle_half; auto.
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

End QField.
