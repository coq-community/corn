Require Import metric2.Complete metric2.Metric metric.
Require Import
  abstract_algebra stdlib_rationals
  orders.orders orders.semirings orders.rings theory.rings.

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

Lemma mspc_closed_help (e : Q) (x y : X) :
   (∀ d : Q, 0 < d → mspc_ball (e + d) x y) → mspc_ball e x y.
Proof.
intro C. change (gball e x y). unfold gball.
destruct (Qsec.Qdec_sign e) as [[e_neg | e_pos] | e_zero].
+ assert (e / 2 < 0) by now apply neg_pos_mult.
  apply (gball_neg (e/2) x y); [easy |].
  mc_setoid_replace (e / 2) with (e - e / 2) by (field; discriminate).
  now apply C, flip_neg_negate.
+ apply (msp_closed (msp X)). intros [d d_pos]. now apply gball_pos, C.
+ apply ball_eq. intros [d d_pos]. apply gball_pos.
  setoid_replace d with (e + d); [now apply C | rewrite e_zero; symmetry; apply plus_0_l].
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
+ apply mspc_closed_help.
Qed.

Definition conv_reg (f : RegularFunction X) : Complete.RegularFunction X.
refine (@mkRegularFunction _ (f 0) (λ e : Qpos, let (e', _) := e in f e') _).
intros [e1 e1_pos] [e2 e2_pos]. now apply gball_pos, (rf_proof f).
Defined.

End FromMetricSpace.

Arguments conv_reg {X} _.

Set Printing Coercions.

Definition ext_equiv' `{Equiv A} `{Equiv B} : Equiv (A → B) :=
  λ f g, ∀ x : A, f x = g x.

Infix "=1" := ext_equiv' (at level 70, no associativity) : type_scope.

Lemma ext_equiv_l `{Setoid A, Setoid B} (f g : A -> B) :
  Proper ((=) ==> (=)) f -> f =1 g -> f = g.
Proof. intros P eq1_f_g x y eq_x_y; rewrite eq_x_y; apply eq1_f_g. Qed.

Lemma ext_equiv_r `{Setoid A, Setoid B} (f g : A -> B) :
  Proper ((=) ==> (=)) g -> f =1 g -> f = g.
Proof. intros P eq1_f_g x y eq_x_y; rewrite <- eq_x_y; apply eq1_f_g. Qed.

Section FromCompleteMetricSpace.

Variable X : MetricSpace.

(*Definition conv_reg_help (f : Q -> X) : QposInf -> X := λ e,
match e with
| Qpos2QposInf (e' ↾ _) => f e'
| QposInfinity => f 0
end.

Lemma conv_reg_help_correct (f : Q -> X) :
  IsRegularFunction f -> is_RegularFunction (conv_reg_help f).
Proof. intros A [e1 e1_pos] [e2 e2_pos]; now apply gball_pos, A. Qed.*)

Global Instance limit_complete : Limit (Complete X) :=
  λ f : RegularFunction (Complete X), Cjoin_fun (conv_reg f).

Global Instance : CompleteMetricSpaceClass (Complete X).
Proof.
constructor.
+ apply ext_equiv_r; [intros x y E; apply E |].
  intros f e1 e2 e1_pos e2_pos.
  eapply gball_pos, (CunitCjoin (conv_reg f) (e1 ↾ e1_pos) (e2 ↾ e2_pos)).
+ constructor; [apply _ .. |].
  intros x y eq_x_y e1 e2 e1_pos e2_pos. apply mspc_eq; solve_propholds.
Qed.

End FromCompleteMetricSpace.



