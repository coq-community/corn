Require Import
  QArith
  theory.setoids (* Equiv Prop *) theory.products
  stdlib_rationals Qinf Qpossec QposInf QnonNeg abstract_algebra QType_rationals additional_operations.
(*Import (*QnonNeg.notations*) QArith.*)
Require Import Qauto QOrderedType.
(*Require Import orders.*)
Require Import theory.rings theory.dec_fields orders.rings nat_pow.
Require Import interfaces.naturals interfaces.orders.

Add Field Q : (stdlib_field_theory Q).

Bind Scope mc_scope with Q.

(*Import Qinf.notations.*)
Notation Qinf := Qinf.T.
Import peano_naturals.

Notation "n .+1" := (S n) (at level 2, left associativity, format "n .+1") : nat_scope.

Local Notation Qnn := QnonNeg.T.

Instance Qnn_eq : Equiv Qnn := eq.
Instance Qnn_zero : Zero Qnn := QnonNeg.zero.
Instance Qnn_one : One Qnn := QnonNeg.one.
Instance Qnn_plus : Plus Qnn := QnonNeg.plus.
Instance Qnn_mult : Mult Qnn := QnonNeg.mult.
Instance Qnn_inv : DecRecip Qnn := QnonNeg.inv.

Instance Qpos_eq : Equiv Qpos := Qpossec.QposEq.
Instance Qpos_one : One Qpos := Qpossec.Qpos_one.
Instance Qpos_plus : Plus Qpos := Qpossec.Qpos_plus.
Instance Qpos_mult : Mult Qpos := Qpossec.Qpos_mult.
Instance Qpos_inv : DecRecip Qpos := Qpossec.Qpos_inv.

Instance Qinf_one : One Qinf := 1%Q.

Module Qinf.

Definition lt (x y : Qinf) : Prop :=
match x, y with
| Qinf.finite a, Qinf.finite b => Qlt a b
| Qinf.finite _, Qinf.infinite => True
| Qinf.infinite, _ => False
end.

Instance: Proper (=) lt.
Proof.
intros [x1 |] [x2 |] A1 [y1 |] [y2 |] A2; revert A1 A2;
unfold Qinf.eq, Q_eq, equiv; simpl; intros A1 A2;
try contradiction; try reflexivity.
rewrite A1, A2; reflexivity.
Qed.

End Qinf.

Instance Qinf_lt : Lt Qinf := Qinf.lt.

Ltac mc_simpl := unfold
  equiv, zero, one, plus, negate, mult, dec_recip, le, lt.

Ltac Qsimpl' := unfold
  Qnn_eq, Qnn_zero, Qnn_one, Qnn_plus, Qnn_mult, Qnn_inv,
  QnonNeg.eq, QnonNeg.zero, QnonNeg.one, QnonNeg.plus, QnonNeg.mult, QnonNeg.inv,
  Qpos_eq, Qpos_one, Qpos_plus, Qpos_mult, Qpos_inv,
  Qpossec.QposEq, Qpossec.Qpos_one, Qpossec.Qpos_plus, Qpossec.Qpos_mult, Qpossec.Qpos_inv,
  Qinf.eq, Qinf.lt, Qinf_lt, Qinf_one, Zero_instance_0 (* Zero Qinf *),
  Q_eq, Q_lt, Q_le, Q_0, Q_1, Q_opp, Q_plus, Q_mult, Q_recip;
  mc_simpl;
  unfold to_Q, QposAsQ;
  simpl.

Ltac nat_simpl := unfold
  nat_equiv, nat_0, nat_1, nat_plus, nat_plus, nat_mult, nat_le, nat_lt;
  mc_simpl;
  simpl.

Tactic Notation "Qsimpl" hyp_list(A) := revert A; Qsimpl'; intros A.

Lemma plus_comm `{SemiRing R} (x y : R) : x + y = y + x.
Proof. rapply commonoid_commutative; apply _. Qed.

Class MetricSpaceBall (X : Type) : Type := mspc_ball: Qinf → relation X.

Local Notation B := mspc_ball.

(* In the proof of Banach fixpoint theorem we have to use arithmetic
expressions such as q^n / (1 - q) when 0 <= q < 1 as the ball radius. If
the radius is in Qnn (ie., QnonNeg.T), then we have to prove that 1 - q :
Qnn. It seems more convenient to have the radius live in Q and have the
axiom that no points are separated by a negative distance. *)

Class ExtMetricSpace (X : Type) `{Equiv X} `{MetricSpaceBall X} : Prop :=
  { mspc_setoid :> Setoid X
  ; mspc_ball_proper:> Proper (=) B
  ; mspc_ball_inf: ∀ x y, B Qinf.infinite x y
  ; mspc_ball_negative: ∀ (e: Q), e < 0 → ∀ x y, ~ B e x y
  ; mspc_ball_zero: ∀ x y, B 0 x y ↔ x = y
  ; mspc_refl:> ∀ e : Q, 0 ≤ e → Reflexive (B e)
  ; mspc_sym:> ∀ e, Symmetric (B e)
  ; mspc_triangle: ∀ (e1 e2: Q) (a b c: X),
       B e1 a b → B e2 b c → B (e1 + e2) a c
  ; mspc_closed: ∀ (e: Q) (a b: X),
       (∀ d: Q, 0 < d -> B (e + d) a b) → B e a b }.

(*Class MetricSpaceBall (X : Type) : Type := mspc_ball: Q → relation X.

Local Notation B := mspc_ball.*)

Class MetricSpaceDistance (X : Type) := msd : X -> X -> Q.

Class MetricSpace (X : Type) `{ExtMetricSpace X} `{MetricSpaceDistance X} : Prop :=
  mspc_distance : forall x1 x2 : X, B (msd x1 x2) x1 x2.

(*Section Coercion.

Context `{MetricSpace X}.

Global Instance : ExtMetricSpaceBall X := λ e : Qinf,
match e with
| Qinf.infinite => λ _ _, True
| Qinf.finite e => B e
end.

Global Instance : ExtMetricSpace X.
Admitted.

End Coercion.*)

Section ExtMetricSpaceClass.

Context `{ExtMetricSpace X}.

(*Program Definition Qnn_minus `(A : q1 <= q2) : Qnn := (q2 - q1)%Q.
Next Obligation. lra. Qed.

Lemma mspc_zero : ∀ x y : X, (∀ q : Qpos, mspc_ball q x y) → mspc_ball 0 x y.
Proof.
intros x y A. apply mspc_closed; intro d. rewrite plus_0_l; trivial.
Qed.

Lemma mspc_eq' : ∀ x y : X, (∀ q : Qpos, mspc_ball q x y) → x = y.
Proof.
intros x y A; apply mspc_eq; intros [q A1].
destruct (Qle_lt_or_eq _ _ A1) as [A2 | A2].
setoid_replace (q ↾ A1) with (from_Qpos (q ↾ A2)) by reflexivity; apply A.
setoid_replace (q ↾ A1) with 0 by (symmetry in A2; apply A2).
apply mspc_zero, A.
Qed.*)

Lemma mspc_triangle' :
  ∀ (q1 q2 : Q) (x2 x1 x3 : X) (q : Q),
    q1 + q2 = q → B q1 x1 x2 → B q2 x2 x3 → B q x1 x3.
Proof.
intros q1 q2 x2 x1 x3 q A1 A2 A3. rewrite <- A1. eapply mspc_triangle; eauto.
Qed.

Lemma mspc_monotone :
  ∀ q1 q2 : Q, q1 ≤ q2 -> ∀ x y : X, B q1 x y → B q2 x y.
Admitted.
(*Proof.
intros q1 q2 A1 x y A2.
setoid_replace q2 with (q1 + (Qnn_minus A1)).
apply mspc_triangle with (b := y); [| apply mspc_refl]; trivial.
unfold Qnn_minus; Qsimpl; lra.
Qed.*)

(*Lemma mspc_zero_eq : ∀ x y : X, mspc_ball 0 x y ↔ x = y.
Proof.
intros x y; split; intro A1; [| rewrite A1; apply mspc_refl].
apply mspc_eq. intro q; apply (mspc_monotone 0); trivial. apply (proj2_sig q).
Qed.*)

End ExtMetricSpaceClass.

Section MetricSpaceClass.

Context `{MetricSpace X}.

Lemma msd_nonneg : forall x1 x2 : X, 0 ≤ msd x1 x2.
Proof.
intros x1 x2.
assert (A := mspc_distance x1 x2).
destruct (le_or_lt 0 (msd x1 x2)) as [A1 | A1]; trivial.
contradict A; now apply mspc_ball_negative.
Qed.

End MetricSpaceClass.

Section UniformContinuity.

Context `{ExtMetricSpace X, ExtMetricSpace Y}.

Class UniformlyContinuous (f : X -> Y) (mu : Q -> Qinf) := {
  uc_proper :> Proper (=) f;
  uc_pos : forall e : Q, 0 < e -> (0 < mu e);
  uc_prf : ∀ (e : Q) (x1 x2: X), 0 < e -> B (mu e) x1 x2 → B e (f x1) (f x2)
}.

Class Contraction (f : X -> Y) (q : Q) := {
  contr_proper :> Proper (=) f;
  contr_nonneg_mu : 0 ≤ q;
  contr_lt_mu_1 : q < 1;
  contr_prf : forall (x1 x2 : X) (e : Q), B e x1 x2 -> B (q * e) (f x1) (f x2)
}.

Global Arguments contr_nonneg_mu f q {_} _.
Global Arguments contr_lt_mu_1 f q {_}.
Global Arguments contr_prf f q {_} _ _ _ _.

Definition contr_modulus (q e : Q) : Qinf :=
  if (decide (q = 0)) then 1 else (e / q).

Close Scope Qinf_scope.

Instance contr_to_uc : forall `(Contraction f q), UniformlyContinuous f (contr_modulus q).
Proof.
intros f q fc. constructor.
apply fc.
intros e A. unfold contr_modulus. destruct (decide (q = 0)) as [A1 | A1].
Qsimpl; auto with qarith.
destruct fc as [_ A2 _ _]. apply Q.Qmult_lt_0_compat; [apply A | apply Qinv_lt_0_compat].
revert A1 A2; Qsimpl; q_order.
intros e x1 x2 A1 A2. unfold contr_modulus in A2. destruct (decide (q = 0)) as [A | A].
apply (contr_prf f q) in A2. rewrite A, Qmult_0_l in A2.
apply mspc_monotone with (q1 := 0); trivial. apply: Qlt_le_weak; trivial.
apply (contr_prf f q) in A2. mc_setoid_replace (q * (e / q)) with e in A2; trivial.
field; trivial.
Qed.

End UniformContinuity.

(*Section UCFMetricSpace.

Context `{MetricSpaceClass X, MetricSpaceClass Y}.

Instance UCFEquiv : Equiv (UniformlyContinuous X Y) := @equiv (X -> Y) _.

Lemma UCFSetoid : Setoid (UniformlyContinuous X Y).
Proof.
constructor.
intros f x y A; now rewrite A.
intros f g A1 x y A2; rewrite A2; symmetry; now apply A1.
intros f g h A1 A2 x y A3; rewrite A3; now transitivity (g y); [apply A1 | apply A2].
Qed.

Instance UCFSpaceBall : MetricSpaceBall (UniformlyContinuous X Y) :=
  fun q f g => forall x, mspc_ball q (f x) (g x).

Lemma UCFBallProper : Proper equiv mspc_ball.
Proof.
intros q1 q2 A1 f1 f2 A2 g1 g2 A3; split; intros A4 x.
+ rewrite <- A1. rewrite <- (A2 x x); [| reflexivity]. rewrite <- (A3 x x); [| reflexivity]. apply A4.
+ rewrite A1. rewrite (A2 x x); [| reflexivity]. rewrite (A3 x x); [| reflexivity]. apply A4.
Qed.

Global Instance : MetricSpaceClass (UniformlyContinuous X Y).
Proof.
constructor.
apply UCFSetoid.
apply UCFBallProper.
intros q f x; apply mspc_refl.
intros q f g A x; apply mspc_symm; trivial.
intros q1 q2 f g h A1 A2 x; apply mspc_triangle with (b := g x); trivial.
intros q f g A x; apply mspc_closed; intro d; apply A.
intros f g A1 x y A2. rewrite A2. eapply mspc_eq; trivial. intro q; apply A1.
Qed.

End UCFMetricSpace.
*)

Instance pos_ne_0 : forall `{StrictSetoidOrder A} `{Zero A} (x : A),
  PropHolds (0 < x) -> PropHolds (x ≠ 0).
Proof. intros; now apply lt_ne_flip. Qed.

(*
Section Isometry.

Context `{ExtMetricSpace X, ExtMetricSpace Y}.

Class Isometry (f : X -> Y) :=
  isometry : forall (e : Q) (x1 x2 : X), B e x1 x2 <-> B e (f x1) (f x2).

Global Instance isometry_injective `{Isometry f} : Injective f.
Proof.
constructor; [| constructor]; try apply _; intros x y; rewrite <- !mspc_ball_zero;
intros ?; [apply <- isometry | apply -> isometry]; trivial.
Qed.

Class IsometricIsomorphism (f : X -> Y) (g : Inverse f) := {
  isometric_isomorphism_isometry :> Isometry f;
  isometric_isomorphism_surjection :> Surjective f
}.

End Isometry.
*)

Definition seq A := nat -> A.

Section MetricSpaceLimits.

Context `{ExtMetricSpace X, ExtMetricSpace Y}.

(*Definition slim (x : seq X) (a : X) :=
  forall 

Theorem limit_unique : ∀ (x : seq X) (a b : X), limit x a → limit x b → a = b.
Proof.
intros x a b A1 A2; apply mspc_eq'; intro q.
specialize (A1 (q / 2)); specialize (A2 (q / 2)).
destruct A1 as [N1 A1]; destruct A2 as [N2 A2].
set (N := S (Peano.max N1 N2)). specialize (A1 N); specialize (A2 N).
apply (mspc_triangle' (q / 2) (q / 2) (x N));
[Qsimpl; field | apply mspc_symm |];
[apply A1 | apply A2]; subst N; lia.
Qed.

Theorem limit_cont : ∀ (f : UniformlyContinuous X Y) (x : seq X) (a : X),
  limit x a → limit (f ∘ x) (f a).
Proof.
intros f x a A1 q.
specialize (A1 (uc_mu f q)).
destruct A1 as [N A1]. exists N; intros n A2. now apply uc_prf, A1.
Qed.

Theorem limit_contr : ∀ (f : Contraction X Y) (x : seq X) (a : X),
  limit x a → limit (f ∘ x) (f a).
Proof. intro f; apply (limit_cont f). Qed.*)

End MetricSpaceLimits.

Section CompleteMetricSpace.

Context `{ExtMetricSpace X}.

Class IsRegularFunction (f : Q -> X) : Prop :=
  cauchy : forall e1 e2 : Q, 0 < e1 -> 0 < e2 -> B (e1 + e2) (f e1) (f e2).

Record RegularFunction := {
  rf_func :> Q -> X;
  rf_proof : IsRegularFunction rf_func
}.

Arguments Build_RegularFunction {_} _.

Global Existing Instance rf_proof.

Instance rf_eq : Equiv RegularFunction :=
  λ f1 f2, forall e1 e2 : Q, 0 < e1 -> 0 < e2 -> B (e1 + e2) (f1 e1) (f2 e2).

Instance rf_setoid : Setoid RegularFunction.
Proof.
constructor.
+ intros f e1 e2; apply cauchy.
+ intros f1 f2 A e1 e2 A1 A2. rewrite plus_comm. now apply mspc_sym, A.
+ intros f1 f2 f3 A1 A2 e1 e3 A3 A4. apply mspc_closed. intros d A5.
  mc_setoid_replace (e1 + e3 + d) with ((e1 + d / 2) + (e3 + d / 2))
  by (field; change ((2 : Q) ≠ 0); solve_propholds).
  apply mspc_triangle with (b := f2 (d / 2));
  [apply A1 | rewrite plus_comm; apply A2]; try solve_propholds.
Qed.

Instance rf_msb : MetricSpaceBall RegularFunction :=
  λ e f1 f2, forall e1 e2 : Q, 0 < e1 -> 0 < e2 -> B (e + e1 + e2) (f1 e1) (f2 e2).

Instance rf_mspc : ExtMetricSpace RegularFunction.
Proof.
constructor.
apply _.
Admitted.

Lemma unit_reg (x : X) : IsRegularFunction (λ _, x).
Proof. intros e1 e2 A1 A2; apply mspc_refl; solve_propholds. Qed.

Definition reg_unit (x : X) := Build_RegularFunction (unit_reg x).

Class Limit := lim : RegularFunction -> X.

Class CompleteMetricSpace `{Limit} := cmspc :> Surjective reg_unit (inv := lim).

Lemma limit_def `{CompleteMetricSpace} (f : RegularFunction) :
  forall e : Q, 0 < e -> B e (f e) (lim f).
Proof.
intros e2 A2. apply mspc_sym; apply mspc_closed.
(* [apply mspc_sym, mspc_closed.] does not work *)
intros e1 A1. change (lim f) with (reg_unit (lim f) e1). rewrite plus_comm.
rapply (surjective reg_unit (inv := lim)); trivial; reflexivity.
Qed.

End CompleteMetricSpace.

Section BanachFixpoint.

Context `{MetricSpace X} (f : X -> X) `{!Contraction f q} (x0 : X).

Let x n := nat_iter n f x0.

Arguments x n%mc.

Lemma x_Sn : forall n, x (1 + n) = f (x n).
Proof. reflexivity. Qed.

Let d := msd (x 0) (x 1).

Instance : PropHolds (0 ≤ d).
Proof. apply msd_nonneg. Qed.

Instance : PropHolds (0 ≤ q).
Proof. apply (contr_nonneg_mu f q). Qed.

Instance : PropHolds (0 < 1 - q).
Proof.
assert (A := contr_lt_mu_1 f q).
rewrite <- flip_lt_negate in A. apply (strictly_order_preserving (1 +)) in A.
now rewrite plus_negate_r in A.
Qed.

Lemma dist_xn_xSn : forall n : nat, B (d * q^n) (x n) (x (1 + n)).
Proof.
induction n using nat_induction.
+ rewrite nat_pow_0, right_identity; subst d; apply mspc_distance.
+ rewrite nat_pow_S. mc_setoid_replace (d * (q * q ^ n)) with (q * (d * q^n)) by ring.
  nat_simpl; rewrite 2!x_Sn; now apply contr_prf.
Qed.

(*Lemma nonzero_1_minus_q : 1 - q ≠ 0.
Proof. apply lt_ne_flip, pos_1_minus_q. Qed.*)

Lemma dist_xm_xn : forall m n : nat, B (d * q^m * (1 - q^n) / (1 - q)) (x m) (x (m + n)).
Proof.
intro m; induction n  as [| n IH] using nat_induction.
+ rewrite right_identity; apply mspc_refl.
  now rewrite nat_pow_0, plus_negate_r, right_absorb, left_absorb.
+ apply (mspc_triangle' (d * q^m * (1 - q^n) / (1 - q)) (d * q^(m + n)) (x (m + n))); trivial.
  - rewrite nat_pow_S, nat_pow_exp_plus. field; solve_propholds.
  - mc_setoid_replace (m + (1 + n)) with (1 + (m + n)) by ring. apply dist_xn_xSn.
Qed.

Lemma dist_xm_xn' : forall m n : nat, B (d * q^m / (1 - q)) (x m) (x (m + n)).
Proof.
intros m n. apply (mspc_monotone (d * q^m * (1 - q^n) / (1 - q))); [| apply dist_xm_xn].
apply (order_preserving (.* /(1 - q))). rewrite <- associativity.
apply (order_preserving (d *.)). rewrite <- (mult_1_r (q^m)) at 2.
apply (order_preserving (q^m *.)). rewrite <- (plus_0_r 1) at 2.
apply (order_preserving (1 +)). rewrite <- negate_0.
apply <- flip_le_negate. solve_propholds.
Qed.

End BanachFixpoint.
