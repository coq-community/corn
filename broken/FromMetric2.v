Require Import Complete metric.
Require Import
  abstract_algebra stdlib_rationals
  orders.orders orders.semirings orders.rings theory.rings.

Section FromMetricSpace.

Variable X : MetricSpace.

Instance msp_mspc_ball : MetricSpaceBall X := λ (e : Qinf) (x y : X),
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

Instance : ExtMetricSpaceClass X.
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

End FromMetricSpace.



