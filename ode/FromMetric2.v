Require Import CoRN.metric2.Complete CoRN.metric2.Metric CoRN.ode.metric.

Require Import
  MathClasses.interfaces.abstract_algebra MathClasses.implementations.stdlib_rationals
  MathClasses.orders.orders MathClasses.orders.semirings MathClasses.orders.rings MathClasses.theory.rings.

Import Qinf.notations Qinf.coercions.

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

Require Import CoRN.model.metric2.CRmetric.

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

Require Import CoRN.model.setoids.Qsetoid CoRN.model.metric2.Qmetric CoRN.reals.fast.CRArith CoRN.reals.fast.CRball CoRN.reals.fast.CRabs MathClasses.theory.abs MathClasses.orders.minmax.

Add Ring CR : (stdlib_ring_theory CR).

Close Scope CR_scope.
Unset Printing Coercions.

(* Uniformly continuous functions respect equality (see metric2.UniformContinuity.v) *)
Global Instance CRabs_proper : Proper (equiv ==> equiv) (abs (A := CR)).
Proof. change abs with (@ucFun CR CR CRabs); apply _. Qed.

Section CRQBallProperties.

Local Notation ball := mspc_ball.

(* The following has to be generalized from Q and CR to a metric space
where [ball r x y] is defined as [abs (x - y) ≤ r], probably a normed
vector space *)

Lemma mspc_ball_Qabs (r x y : Q) : ball r x y ↔ abs (x - y) ≤ r.
Proof. apply gball_Qabs. Qed.

Lemma mspc_ball_Qabs_flip (r x y : Q) : ball r x y ↔ abs (y - x) ≤ r.
Proof.
rewrite <- abs.abs_negate, <- rings.negate_swap_r. apply gball_Qabs.
Qed.

Lemma mspc_ball_CRabs (r : Q) (x y : CR) : ball r x y ↔ abs (x - y) ≤ 'r.
Proof. apply CRball.gball_CRabs. Qed.

(*Lemma mspc_ball_CRabs_flip (r : Q) (x y : CR) : ball r x y ↔ abs (y - x) ≤ 'r.
Proof.
rewrite <- abs.abs_negate, <- rings.negate_swap_r. apply gball_Qabs.
Qed.*)

Lemma mspc_ball_Qplus_l (e x y y' : Q) : ball e y y' -> ball e (x + y) (x + y').
Proof.
intro A. assert (A1 := radius_nonneg _ _ _ A).
destruct (orders.le_equiv_lt _ _ A1) as [e_zero | e_pos].
+ rewrite <- e_zero in A |- *. now rewrite A.
+ apply (gball_pos e_pos _ _) in A. now apply (gball_pos e_pos _ _), Qball_plus_r.
Qed.

(* This is a copy of [CRgball_plus] formulated in terms of [mspc_ball]
instead of [gball]. Applying [CRgball_plus] introduces [gball] into the
goal, and then applying some theorems about [mspc_ball] may not work. This
is because [mspc_ball] reduces to [gball] but not the other way around. *)
Lemma mspc_ball_CRplus (e1 e2 : Q) (x x' y y' : CR) :
  ball e1 x x' -> ball e2 y y' -> ball (e1 + e2) (x + y) (x' + y').
Proof. apply CRgball_plus. Qed.

Lemma mspc_ball_CRplus_l (e : Q) (x y y' : CR) : ball e y y' -> ball e (x + y) (x + y').
Proof.
intro A. rewrite <- (rings.plus_0_l e). apply mspc_ball_CRplus; [| easy].
now apply mspc_refl.
Qed.

Lemma mspc_ball_CRnegate (e : Q) (x y : CR) : mspc_ball e x y -> mspc_ball e (-x) (-y).
Proof.
intro A. apply mspc_ball_CRabs. mc_setoid_replace (-x - -y) with (y - x) by ring.
now apply mspc_ball_CRabs, mspc_symm.
Qed.

Lemma nested_balls (x1 x2 : Q) {y1 y2 : Q} {e : Qinf} :
  ball e x1 x2 -> x1 ≤ y1 -> y1 ≤ y2 -> y2 ≤ x2 -> ball e y1 y2.
Proof.
intros B A1 A2 A3. destruct e as [e |]; [| apply mspc_inf].
apply mspc_ball_Qabs_flip in B. apply mspc_ball_Qabs_flip.
assert (x1 ≤ x2) by (transitivity y1; [| transitivity y2]; trivial).
rewrite abs.abs_nonneg by now apply rings.flip_nonneg_minus.
rewrite abs.abs_nonneg in B by now apply rings.flip_nonneg_minus.
apply rings.flip_le_minus_l. apply rings.flip_le_minus_l in B.
transitivity x2; [easy |]. transitivity (e + x1); [easy |].
apply (orders.order_preserving (e +)); easy.
Qed. (* Too long? *)

End CRQBallProperties.

Global Instance sum_llip `{MetricSpaceBall X}
  (f g : X -> CR) `{!IsLocallyLipschitz f Lf} `{!IsLocallyLipschitz g Lg} :
  IsLocallyLipschitz (f + g) (λ x r, Lf x r + Lg x r).
Proof.
constructor.
+ pose proof (lip_nonneg (restrict f x r) (Lf x r)).
  pose proof (lip_nonneg (restrict g x r) (Lg x r)). solve_propholds.
+ intros x1 x2 e A. rewrite plus_mult_distr_r.
  apply CRgball_plus;
  [now apply: (lip_prf (restrict f x r) _) | now apply: (lip_prf (restrict g x r) _)].
Qed.

(*
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
*)

(* Needed to be able to state the property that the integral of the sum is
the sum of integrals *)
Global Instance sum_uc `{ExtMetricSpaceClass X}
  (f g : X -> CR) `{!IsUniformlyContinuous f mu_f} `{!IsUniformlyContinuous g mu_g} :
  IsUniformlyContinuous (f + g) (λ e, min (mu_f (e / 2)) (mu_g (e / 2))).
Proof.
constructor.
* intros e e_pos. apply lt_min; [apply (uc_pos f mu_f) | apply (uc_pos g mu_g)]; solve_propholds.
* intros e x1 x2 e_pos A. mc_setoid_replace e with (e / 2 + e / 2) by (field; discriminate).
  apply CRgball_plus.
  + apply: (uc_prf f mu_f); [solve_propholds |].
    apply (mspc_monotone' (min (mu_f (e / 2)) (mu_g (e / 2)))); [| assumption].
    change ((mu_f (e / 2)) ⊓ (mu_g (e / 2)) ≤ mu_f (e / 2)).
    apply orders.meet_lb_l. (* does not work without [change] *)
  + apply: (uc_prf g mu_g); [solve_propholds |].
    apply (mspc_monotone' (min (mu_f (e / 2)) (mu_g (e / 2)))); [| assumption].
    change ((mu_f (e / 2)) ⊓ (mu_g (e / 2)) ≤ mu_g (e / 2)).
    apply orders.meet_lb_r.
Qed.


Global Instance negate_uc `{MetricSpaceBall X} (f : X -> CR)
  `{!IsUniformlyContinuous f mu_f} : IsUniformlyContinuous (- f) mu_f.
Proof.
constructor.
* apply (uc_pos f _).
* intros e x1 x2 e_pos A. apply mspc_ball_CRnegate, (uc_prf f mu_f); easy.
Qed.

End QField.

