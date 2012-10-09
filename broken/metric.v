Require Import
  QArith
  theory.setoids (* Equiv Prop *) theory.products
  stdlib_rationals Qinf Qpossec QposInf QnonNeg abstract_algebra QType_rationals additional_operations.
(*Import (*QnonNeg.notations*) QArith.*)
Require Import Qauto QOrderedType.
(*Require Import orders.*)
Require Import theory.rings theory.dec_fields orders.rings orders.dec_fields nat_pow.
Require Import interfaces.naturals interfaces.orders.
Import peano_naturals.

Require Import CRGeometricSum.
Import Qround Qpower.

Set Printing Coercions.

Lemma iff_not (P Q : Prop) : (P <-> Q) -> (not P <-> not Q).
Proof. tauto. Qed.

Notation "x ²" := (x * x) (at level 30) : mc_scope.

Lemma po_proper' `{PartialOrder A} {x1 x2 y1 y2 : A} :
  x1 ≤ y1 -> x1 = x2 -> y1 = y2 -> x2 ≤ y2.
Proof. intros A1 A2 A3; now apply (po_proper _ _ A2 _ _ A3). Qed.

Lemma le_not_eq `{FullPartialOrder A} (x y : A) : x ≤ y -> x ≶ y -> x < y.
Proof. intros ? ?; apply lt_iff_le_apart; now split. Qed.

(* Use orders.orders.le_equiv_lt instead *)
Lemma le_lt_eq `{@FullPartialOrder B Be Bap Ble Blt} `{@TrivialApart B Be Bap}
  `{forall x y : B, Decision (x = y)} (x y : B) : x ≤ y ↔ x < y ∨ x = y.
Proof.
assert (Setoid B) by apply po_setoid.
split; intro A.
+ destruct (decide (x = y)) as [A1 | A1]; [now right |].
  apply trivial_apart in A1. left; apply lt_iff_le_apart; now split.
+ destruct A as [A | A].
  - apply lt_iff_le_apart in A; now destruct A.
  - now rewrite A.
Qed.

Lemma Zto_nat_nonpos (z : Z) : (z <= 0)%Z -> Z.to_nat z ≡ 0.
Proof.
intro A; destruct z as [| p | p]; trivial.
unfold Z.le in A; now contradict A.
Qed.

Lemma le_Z_to_nat (n : nat) (z : Z) : (Z.to_nat z <= n)%nat <-> (z <= Z.of_nat n)%Z.
Proof.
pose proof (le_0_n n). pose proof (Zle_0_nat n).
destruct (Z.neg_nonneg_cases z).
+ rewrite Zto_nat_nonpos by now apply Z.lt_le_incl. split; auto with zarith.
+ split; intro A.
  - apply inj_le in A. rewrite Z2Nat.id in A; trivial.
  - apply Z2Nat.inj_le in A; trivial. rewrite Nat2Z.id in A; trivial.
Qed.

Lemma lt_Z_to_nat (n : nat) (z : Z) : (n < Z.to_nat z)%nat <-> (Z.of_nat n < z)%Z.
Proof.
assert (A : forall (m n : nat), not (m <= n)%nat <-> (n < m)%nat).
+ intros; split; [apply not_le | apply gt_not_le].
+ assert (A1 := le_Z_to_nat n z). apply iff_not in A1.
  now rewrite A, Z.nle_gt in A1.
Qed.

(* Qlt_Qceiling is not used below *)
Lemma Qlt_Qceiling (q : Q) : (Qceiling q < q + 1)%Q.
Proof.
apply Qplus_lt_l with (z := -1). setoid_replace (q + 1 + -1)%Q with q.
+ assert (A := Qceiling_lt q). unfold Z.sub in A.
  now rewrite inject_Z_plus, inject_Z_opp in A.
+ now rewrite <- Qplus_assoc, Qplus_opp_r, Qplus_0_r.
Qed.

Lemma Qle_Qceiling_Z (q : Q) (z : Z) : (Qceiling q <= z)%Z <-> (q <= z)%Q.
Proof.
split; intro A.
+ rewrite Zle_Qle in A. apply Qle_trans with (y := Qceiling q); [apply Qle_ceiling | trivial].
+ apply Z.lt_pred_le. rewrite Zlt_Qlt. now apply Qlt_le_trans with (y := q); [apply Qceiling_lt |].
Qed.

Lemma Qle_Qceiling_nat (q : Q) (n : nat) : (Z.to_nat (Qceiling q) <= n)%nat <-> (q <= n)%Q.
Proof. rewrite le_Z_to_nat; apply Qle_Qceiling_Z. Qed.

Lemma Qlt_Qceiling_Z (q : Q) (z : Z) : (z < q)%Q <-> (z < Qceiling q)%Z.
Proof.
assert (A : forall (x y : Q), not (x <= y)%Q <-> (y < x)%Q).
+ intros; split; [apply Qnot_le_lt | apply Qlt_not_le].
+ assert (A1 := Qle_Qceiling_Z q z). apply iff_not in A1.
  now rewrite A, Z.nle_gt in A1.
Qed.

Lemma Qlt_Qceiling_nat (q : Q) (n : nat) : (n < q)%Q <-> (n < Z.to_nat (Qceiling q))%nat.
Proof. rewrite (Qlt_Qceiling_Z q n); symmetry; apply lt_Z_to_nat. Qed.

Lemma neq_symm `{Ae : Equiv X} `{!Symmetric Ae} (x y : X) : x ≠ y -> y ≠ x.
Proof. intros A1 A2; apply A1; now symmetry. Qed.

Lemma plus_comm `{SemiRing R} : Commutative (+).
Proof. eapply commonoid_commutative; apply _. Qed.

Lemma plus_assoc `{SemiRing R} : forall x y z : R, x + (y + z) = (x + y) + z.
Proof. apply sg_ass, _. Qed.

Instance pos_ne_0 : forall `{StrictSetoidOrder A} `{Zero A} (x : A),
  PropHolds (0 < x) -> PropHolds (x ≠ 0).
Proof. intros; now apply lt_ne_flip. Qed.

(*Ltac MCQconst t :=
match t with
(*| @zero Q _ _ => constr:(Qmake Z0 xH)
| @one Q _ _ => constr:(Qmake (Zpos xH) xH)*)
| _ => Qcst t
end.

Add Field Q : (stdlib_field_theory Q)
  (decidable Qeq_bool_eq,
   completeness Qeq_eq_bool,
   constants [MCQconst]).

Goal forall x y : Q, (1#1)%Q * x = x.
intros x y. ring.*)

(*
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
*)

Notation Qinf := Qinf.T.

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

(*
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
*)

Section QField.

Add Field Q : (stdlib_field_theory Q).

Bind Scope mc_scope with Q.

Class MetricSpaceBall (X : Type) : Type := mspc_ball: Qinf → relation X.

Local Notation ball := mspc_ball.

(* In the proof of Banach fixpoint theorem we have to use arithmetic
expressions such as q^n / (1 - q) when 0 <= q < 1 as the ball radius. If
the radius is in Qnn (ie., QnonNeg.T), then we have to prove that 1 - q :
Qnn. It seems more convenient to have the radius live in Q and have the
axiom that no points are separated by a negative distance. *)

Class ExtMetricSpaceClass (X : Type) `{MetricSpaceBall X} : Prop := {
  mspc_radius_proper : Proper ((=) ==> (≡) ==> (≡) ==> iff) ball;
  mspc_inf: ∀ x y, ball Qinf.infinite x y;
  mspc_negative: ∀ (e: Q), e < 0 → ∀ x y, ~ ball e x y;
  mspc_refl:> ∀ e : Q, 0 ≤ e → Reflexive (ball e);
  mspc_symm:> ∀ e, Symmetric (ball e);
  mspc_triangle: ∀ (e1 e2: Q) (a b c: X),
     ball e1 a b → ball e2 b c → ball (e1 + e2) a c;
  mspc_closed: ∀ (e: Q) (a b: X),
     (∀ d: Q, 0 < d -> ball (e + d) a b) → ball e a b
}.

(*
This shows that if axioms of metric space are formulated with Qinf instead of Q,
the [apply] tactic won't be able to unify them with goals using Q

Goal (forall (e1 e2 : Qinf) (x1 x2 : X), ball (e1 + e2) x1 x2) ->
  (forall (e1 e2 : Q) (x1 x2 : X), ball (e1 + e2) x1 x2).
intros A e1 e2 x1 x2.
change (e1 + e2 : Qinf) with ((Qinf.finite e1) + (Qinf.finite e2)).
apply A.
*)

Class MetricSpaceDistance (X : Type) := msd : X -> X -> Q.

Class MetricSpaceClass (X : Type) `{ExtMetricSpaceClass X} `{MetricSpaceDistance X} : Prop :=
  mspc_distance : forall x1 x2 : X, ball (msd x1 x2) x1 x2.

Section ExtMetricSpace.

Context `{ExtMetricSpaceClass X}.

Global Instance mspc_equiv : Equiv X := λ x1 x2, ball 0%Q x1 x2.

Global Instance mspc_setoid : Setoid X.
Proof.
constructor.
+ now apply mspc_refl.
+ apply mspc_symm.
+ intros x1 x2 x3 eq12 eq23.
  unfold mspc_equiv, equiv; change 0%Q with (0%Q + 0%Q); now apply mspc_triangle with (b := x2).
Qed.

Global Instance mspc_proper : Proper ((=) ==> (=) ==> (=) ==> iff) ball.
Proof.
assert (A := @mspc_radius_proper X _ _).
intros e1 e2 Ee1e2 x1 x2 Ex1x2 y1 y2 Ey1y2;
destruct e1 as [e1 |]; destruct e2 as [e2 |]; split; intro B; try apply mspc_inf;
try (unfold Qinf.eq, equiv in *; contradiction).
+ mc_setoid_replace e2 with (0 + (e2 + 0)) by ring.
  apply mspc_triangle with (b := x1); [apply mspc_symm, Ex1x2 |].
  now apply mspc_triangle with (b := y1); [rewrite <- Ee1e2 |].
+ mc_setoid_replace e1 with (0 + (e1 + 0)) by ring.
  apply mspc_triangle with (b := x2); [apply Ex1x2 |].
  now apply mspc_triangle with (b := y2); [rewrite Ee1e2 | apply mspc_symm].
Qed.

Lemma mspc_triangle' :
  ∀ (q1 q2 : Q) (x2 x1 x3 : X) (q : Q),
    q1 + q2 = q → ball q1 x1 x2 → ball q2 x2 x3 → ball q x1 x3.
Proof.
intros q1 q2 x2 x1 x3 q A1 A2 A3. rewrite <- A1. eapply mspc_triangle; eauto.
Qed.

Lemma mspc_monotone :
  ∀ q1 q2 : Q, q1 ≤ q2 -> ∀ x y : X, ball q1 x y → ball q2 x y.
Proof.
intros q1 q2 A1 x y A2.
apply (mspc_triangle' q1 (q2 - q1) y); [ring | trivial |]. apply mspc_refl.
apply (order_preserving (+ (-q1))) in A1. now rewrite plus_negate_r in A1.
Qed.

Lemma mspc_eq : ∀ x y : X, (∀ e : Q, 0 < e -> ball e x y) ↔ x = y.
Proof.
intros x y; split; intro A.
+ apply mspc_closed; intro d. change 0%Q with (@zero Q _); rewrite plus_0_l; apply A.
+ intros e e_pos. apply (mspc_monotone 0); trivial; solve_propholds.
Qed.

End ExtMetricSpace.

Section MetricSpace.

Context `{MetricSpaceClass X}.

Lemma msd_nonneg : forall x1 x2 : X, 0 ≤ msd x1 x2.
Proof.
intros x1 x2.
assert (A := mspc_distance x1 x2).
destruct (le_or_lt 0 (msd x1 x2)) as [A1 | A1]; trivial.
contradict A; now apply mspc_negative.
Qed.

End MetricSpace.

Section UniformContinuity.

Context `{ExtMetricSpaceClass X, ExtMetricSpaceClass Y}.

Class IsUniformlyContinuous (f : X -> Y) (mu : Q -> Qinf) := {
  uc_pos : forall e : Q, 0 < e -> (0 < mu e);
  uc_prf : ∀ (e : Q) (x1 x2: X), 0 < e -> ball (mu e) x1 x2 → ball e (f x1) (f x2)
}.

Global Arguments uc_pos f mu {_} e _.
Global Arguments uc_prf f mu {_} e x1 x2 _ _.

Global Instance uc_proper `{IsUniformlyContinuous f mu} : Proper ((=) ==> (=)) f.
Proof.
intros x1 x2 A. apply -> mspc_eq. intros e e_pos. apply (uc_prf f mu); trivial.
pose proof (uc_pos f mu e e_pos) as ?.
destruct (mu e); [apply mspc_eq; trivial | apply mspc_inf].
Qed.

End UniformContinuity.

Section Contractions.

Context `{MetricSpaceClass X, ExtMetricSpaceClass Y}.

Class IsContraction (f : X -> Y) (q : Q) := {
  contr_nonneg_mu : 0 ≤ q;
  contr_lt_mu_1 : q < 1;
  contr_prf : forall (x1 x2 : X) (e : Q), ball e x1 x2 -> ball (q * e) (f x1) (f x2)
}.

Global Arguments contr_nonneg_mu f q {_} _.
Global Arguments contr_lt_mu_1 f q {_}.
Global Arguments contr_prf f q {_} _ _ _ _.

Definition contr_modulus (q e : Q) : Qinf :=
  if (decide (0 = q)) then Qinf.infinite else (e / q).

Global Instance contr_to_uc `(IsContraction f q) :
  IsUniformlyContinuous f (contr_modulus q).
Proof.
constructor.
+ intros e A. unfold contr_modulus. destruct (decide (0 = q)) as [A1 | A1]; [apply I |].
  change (0 < e / q). (* Changes from Qinf, which is not declared as ordered ring, to Q *)
  pose proof (contr_nonneg_mu f q) as A2. pose proof (le_not_eq _ _ A2 A1). solve_propholds.
+ intros e x1 x2 A1 A2. unfold contr_modulus in A2. destruct (decide (0 = q)) as [A | A].
  - assert (A3 := contr_prf f q x1 x2 (msd x1 x2) (mspc_distance x1 x2)).
    rewrite <- A, mult_0_l in A3; now apply mspc_eq.
  - mc_setoid_replace e with (q * (e / q)) by (field; now apply neq_symm).
    now apply contr_prf.
Qed.

End Contractions.

(*Section UCFMetricSpace.

Context `{MetricSpaceClass X, MetricSpaceClass Y}.

Instance UCFEquiv : Equiv (IsUniformlyContinuous X Y) := @equiv (X -> Y) _.

Lemma UCFSetoid : Setoid (IsUniformlyContinuous X Y).
Proof.
constructor.
intros f x y A; now rewrite A.
intros f g A1 x y A2; rewrite A2; symmetry; now apply A1.
intros f g h A1 A2 x y A3; rewrite A3; now transitivity (g y); [apply A1 | apply A2].
Qed.

Instance UCFSpaceBall : MetricSpaceBall (IsUniformlyContinuous X Y) :=
  fun q f g => forall x, ball q (f x) (g x).

Lemma UCFBallProper : Proper equiv ball.
Proof.
intros q1 q2 A1 f1 f2 A2 g1 g2 A3; split; intros A4 x.
+ rewrite <- A1. rewrite <- (A2 x x); [| reflexivity]. rewrite <- (A3 x x); [| reflexivity]. apply A4.
+ rewrite A1. rewrite (A2 x x); [| reflexivity]. rewrite (A3 x x); [| reflexivity]. apply A4.
Qed.

Global Instance : MetricSpaceClass (IsUniformlyContinuous X Y).
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

(*
Section Isometry.

Context `{ExtMetricSpaceClass X, ExtMetricSpaceClass Y}.

Class Isometry (f : X -> Y) :=
  isometry : forall (e : Q) (x1 x2 : X), ball e x1 x2 <-> ball e (f x1) (f x2).

Global Instance isometry_injective `{Isometry f} : Injective f.
Proof.
constructor; [| constructor]; try apply _; intros x y; rewrite <- !ball_zero;
intros ?; [apply <- isometry | apply -> isometry]; trivial.
Qed.

Class IsometricIsomorphism (f : X -> Y) (g : Inverse f) := {
  isometric_isomorphism_isometry :> Isometry f;
  isometric_isomorphism_surjection :> Surjective f
}.

End Isometry.
*)

Section CompleteMetricSpace.

Context `{ExtMetricSpaceClass X}.

Class IsRegularFunction (f : Q -> X) : Prop :=
  rf_prf : forall e1 e2 : Q, 0 < e1 -> 0 < e2 -> ball (e1 + e2) (f e1) (f e2).

Record RegularFunction := {
  rf_func :> Q -> X;
  rf_proof : IsRegularFunction rf_func
}.

Arguments Build_RegularFunction {_} _.

Global Existing Instance rf_proof.

Instance rf_eq : Equiv RegularFunction :=
  λ f1 f2, forall e1 e2 : Q, 0 < e1 -> 0 < e2 -> ball (e1 + e2) (f1 e1) (f2 e2).

Global Instance rf_setoid : Setoid RegularFunction.
Proof.
constructor.
+ intros f e1 e2; apply rf_prf.
+ intros f1 f2 A e1 e2 A1 A2. rewrite plus_comm. now apply mspc_symm, A.
+ intros f1 f2 f3 A1 A2 e1 e3 A3 A4. apply mspc_closed. intros d A5.
  mc_setoid_replace (e1 + e3 + d) with ((e1 + d / 2) + (e3 + d / 2))
  by (field; change ((2 : Q) ≠ 0); solve_propholds).
  apply mspc_triangle with (b := f2 (d / 2));
  [apply A1 | rewrite plus_comm; apply A2]; try solve_propholds.
Qed.

Instance rf_msb : MetricSpaceBall RegularFunction :=
  λ e f1 f2, forall e1 e2 : Q, 0 < e1 -> 0 < e2 -> ball (e + e1 + e2) (f1 e1) (f2 e2).

Lemma unit_reg (x : X) : IsRegularFunction (λ _, x).
Proof. intros e1 e2 A1 A2; apply mspc_refl; solve_propholds. Qed.

Definition reg_unit (x : X) := Build_RegularFunction (unit_reg x).

Class Limit := lim : RegularFunction -> X.

Class CompleteMetricSpaceClass `{Limit} := cmspc :> Surjective reg_unit (inv := lim).

Lemma limit_def `{CompleteMetricSpaceClass} (f : RegularFunction) :
  forall e : Q, 0 < e -> ball e (f e) (lim f).
Proof.
intros e2 A2. apply mspc_symm; apply mspc_closed.
(* [apply mspc_symm, mspc_closed.] does not work *)
intros e1 A1. change (lim f) with (reg_unit (lim f) e1). rewrite plus_comm.
rapply (surjective reg_unit (inv := lim)); trivial; reflexivity.
Qed.

End CompleteMetricSpace.

Global Arguments RegularFunction X {_}.
Global Arguments Limit X {_}.
Global Arguments CompleteMetricSpaceClass X {_ _ _}.

Definition seq A := nat -> A.

(*Hint Unfold seq : typeclass_instances.*)
(* This unfolds [seq X] as [nat -> X] and allows ext_equiv to find an
instance of [Equiv (seq X)] *)

Section SequenceLimits.

Context `{ExtMetricSpaceClass X}.

Definition seq_lim (x : seq X) (a : X) (N : Q -> nat) :=
  forall e : Q, 0 < e -> forall n : nat, N e ≤ n -> ball e (x n) a.

Global Instance : Proper (((=) ==> (=)) ==> (=) ==> ((=) ==> (=)) ==> iff) seq_lim.
Proof.
intros x1 x2 A1 a1 a2 A2 N1 N2 A3; split; intros A e e_pos n A4.
+ mc_setoid_replace (x2 n) with (x1 n) by (symmetry; now apply A1).
  rewrite <- A2. mc_setoid_replace (N2 e) with (N1 e) in A4 by (symmetry; now apply A3).
  now apply A.
+ mc_setoid_replace (x1 n) with (x2 n) by now apply A1.
  rewrite A2. mc_setoid_replace (N1 e) with (N2 e) in A4 by now apply A3.
  now apply A.
Qed.

Global Instance : Proper (((=) ==> (=)) ==> (=) ==> (≡) ==> iff) seq_lim.
Proof.
intros x1 x2 A1 a1 a2 A2 N1 N2 A3; split; intros A e e_pos n A4.
+ mc_setoid_replace (x2 n) with (x1 n) by (symmetry; now apply A1).
  rewrite <- A2. rewrite <- A3 in A4. now apply A.
+ mc_setoid_replace (x1 n) with (x2 n) by now apply A1.
  rewrite A2. rewrite A3 in A4. now apply A.
Qed.

Lemma seq_lim_unique : ∀ (x : seq X) (a1 a2 : X) N1 N2, seq_lim x a1 N1 → seq_lim x a2 N2 → a1 = a2.
Proof.
intros x a1 a2 N1 N2 A1 A2. apply -> mspc_eq; intros q A.
assert (A3 : 0 < q / 2) by solve_propholds.
specialize (A1 (q / 2) A3); specialize (A2 (q / 2) A3).
set (M := Peano.max (N1 (q / 2)) (N2 (q / 2))).
assert (A4 : N1 (q / 2) ≤ M) by apply le_max_l.
assert (A5 : N2 (q / 2) ≤ M) by apply le_max_r.
specialize (A1 M A4); specialize (A2 M A5).
apply mspc_symm in A1.
apply (mspc_triangle' (q / 2) (q / 2) (x M)); trivial.
field; change ((2 : Q) ≠ 0); solve_propholds.
Qed.

Lemma seq_lim_S (x : seq X) (a : X) N : seq_lim x a N -> seq_lim (x ∘ S) a N.
Proof. intros A e A1 n A2. apply A; trivial. apply le_S, A2. Qed.

Lemma seq_lim_S' (x : seq X) (a : X) N : seq_lim (x ∘ S) a N -> seq_lim x a (S ∘ N).
Proof.
intros A e A1 n A2.
destruct n as [| n].
+ contradict A2; apply le_Sn_0.
+ apply A; trivial. apply le_S_n, A2.
Qed.

End SequenceLimits.

Definition comp_inf {X Z : Type} (g : Q -> Z) (f : X -> Qinf) (inf : Z) (x : X) :=
match (f x) with
| Qinf.finite y => g y
| Qinf.infinite => inf
end.

Theorem seq_lim_cont
  `{ExtMetricSpaceClass X, ExtMetricSpaceClass Y} (f : X -> Y) `{!IsUniformlyContinuous f mu}
  (x : seq X) (a : X) (N : Q -> nat) :
  seq_lim x a N → seq_lim (f ∘ x) (f a) (comp_inf N mu 0).
Proof.
intros A e e_pos n A1. apply (uc_prf f mu); trivial.
unfold comp_inf in A1; assert (A2 := uc_pos f mu e e_pos).
now destruct (mu e); [apply A | apply mspc_inf].
Qed.

Theorem seq_lim_contr
  `{MetricSpaceClass X, ExtMetricSpaceClass Y} (f : X -> Y) `{!IsContraction f q}
  (x : seq X) (a : X) (N : Q -> nat) :
  seq_lim x a N → seq_lim (f ∘ x) (f a) (comp_inf N (contr_modulus q) 0).
Proof. intro A; apply seq_lim_cont; [apply _ | apply A]. Qed.

Lemma iter_fixpoint
  `{ExtMetricSpaceClass X, ExtMetricSpaceClass Y}
  (f : X -> X) `{!IsUniformlyContinuous f mu} (x : seq X) (a : X) (N : Q -> nat) :
  (forall n : nat, x (S n) = f (x n)) -> seq_lim x a N -> f a = a.
Proof.
intros A1 A2; generalize A2; intro A3. apply seq_lim_S in A2. apply (seq_lim_cont f) in A3.
mc_setoid_replace (x ∘ S) with (f ∘ x) in A2 by (intros ? ? eqmn; rewrite eqmn; apply A1).
eapply seq_lim_unique; eauto.
Qed.

Section CompleteSpaceSequenceLimits.

Context `{CompleteMetricSpaceClass X}.

Definition cauchy (x : seq X) (N : Q -> nat) :=
  forall e : Q, 0 < e -> forall m n : nat, N e ≤ m -> N e ≤ n -> ball e (x m) (x n).

Definition reg_fun (x : seq X) (N : Q -> nat) (A : cauchy x N) : RegularFunction X.
refine (Build_RegularFunction (x ∘ N) _).
(* without loss of generality, N e1 ≤ N e2 *)
assert (A3 : forall e1 e2, 0 < e1 -> 0 < e2 -> N e1 ≤ N e2 -> ball (e1 + e2) ((x ∘ N) e1) ((x ∘ N) e2)).
+ intros e1 e2 A1 A2 A3.
  apply (mspc_monotone e1).
  - apply (strictly_order_preserving (e1 +)) in A2; rewrite plus_0_r in A2; solve_propholds.
  - apply A; trivial; reflexivity.
+ intros e1 e2 A1 A2.
  assert (A4 : TotalRelation (A := nat) (≤)) by apply _; destruct (A4 (N e1) (N e2)).
  - now apply A3.
  - rewrite plus_comm; now apply mspc_symm, A3.
Defined.

Arguments reg_fun {_} {_} _.

Lemma seq_lim_lim (x : seq X) (N : Q -> nat) (A : cauchy x N) :
  seq_lim x (lim (reg_fun A)) (λ e, N (e / 2)).
Proof.
set (f := reg_fun A).
intros e A1 n A2. apply (mspc_triangle' (e / 2) (e / 2) (x (N (e / 2)))).
+ field; change ((2 : Q) ≠ 0); solve_propholds.
+ now apply mspc_symm, A; [solve_propholds | reflexivity |].
+ change (x (N (e / 2))) with (f (e / 2)).
  apply limit_def; solve_propholds.
Qed.

End CompleteSpaceSequenceLimits.

Section SubMetricSpace.

Context `{ExtMetricSpaceClass X} (P : X -> Prop).

Global Instance sig_mspc_ball : MetricSpaceBall (sig P) := λ e x y, ball e (` x) (` y).

Global Instance sig_mspc : ExtMetricSpaceClass (sig P).
Proof.
constructor.
+ repeat intro; rapply mspc_radius_proper; congruence.
+ repeat intro; rapply mspc_inf.
+ intros; now rapply mspc_negative.
+ repeat intro; now rapply mspc_refl.
+ repeat intro; now rapply mspc_symm.
+ repeat intro; rapply mspc_triangle; eauto.
+ repeat intro; now rapply mspc_closed.
Qed.

End SubMetricSpace.

Section LocalUniformContinuity.

Context `{ExtMetricSpaceClass X, ExtMetricSpaceClass Y}.

Definition restrict (f : X -> Y) (x : X) (r : Q) : sig (ball r x) -> Y :=
  f ∘ @proj1_sig _ _.

Class IsLocallyUniformlyContinuous (f : X -> Y) (lmu : X -> Q -> Q -> Qinf) :=
  luc_prf : forall (x : X) (r : Q), IsUniformlyContinuous (restrict f x r) (lmu x r).

(*Global Arguments luc_pos f mu {_} e _.
Global Arguments luc_prf f mu {_} e x1 x2 _ _.*)

Global Instance uc_ulc (f : X -> Y) `{!IsUniformlyContinuous f mu} :
  IsLocallyUniformlyContinuous f (λ _ _, mu).
Proof.
intros x r. constructor; [now apply (uc_pos f) |].
intros e [x1 A1] [x2 A2] e_pos A. now apply (uc_prf f mu).
Qed.

End LocalUniformContinuity.


(*Section ClosedSegmentComplete.

Context `{CompleteMetricSpaceClass X, Le X, @PartialOrder X _ _}.

Variables a b : X.

Definition segment := sig (λ x, a ≤ x ≤ b).

Typeclasses Transparent segment.

(*Program Instance segment_limit : Limit segment :=
  λ f, lim (Build_RegularFunction (λ e, proj1_sig (f e)) _).
generates an infinite number of obligation [MetricSpaceBall segment] *)

(* In the context (f : RegularFunction segment), (proj1_sig ∘ f) does not typecheck,
but (λ e, proj1_sig (f e)) does *)

Lemma lim_inside_r (f : RegularFunction X) :
  (forall e, f e ≤ b) -> lim f ≤ b.
Proof.
intro A.


Global Instance segment_limit : Limit segment.
intro f.
(* Check (λ (e : Q), `(f e)) : Q -> X. does not work *)
(* refine (lim (Build_RegularFunction (λ e, proj1_sig (f e)) _) ↾ _).
This generates one goal and one existential variable instead of two goals *)
refine (lim (Build_RegularFunction (λ e, proj1_sig (f e)) (rf_proof f)) ↾ _).
*)

End QField.

