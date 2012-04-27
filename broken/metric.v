(*Add Rec LoadPath "/home/emakarov/work/formath/corn" as CoRN.
Add Rec LoadPath "/home/emakarov/work/formath/corn/math-classes/src" as MathClasses.*)

Require Import
  Psatz QArith
  theory.setoids (* Equiv Prop *) theory.products
  Qinf Qpossec QposInf QnonNeg abstract_algebra QType_rationals additional_operations.
(*Import (*QnonNeg.notations*) QArith.*)
Import Qinf.notations.

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

Ltac Qsimpl := unfold
  equiv, zero, one, plus, mult, dec_recip,
  Qnn_eq, Qnn_zero, Qnn_one, Qnn_plus, Qnn_mult, Qnn_inv,
  QnonNeg.eq, QnonNeg.zero, QnonNeg.one, QnonNeg.plus, QnonNeg.mult, QnonNeg.inv,
  Qpos_eq, Qpos_one, Qpos_plus, Qpos_mult, Qpos_inv,
  Qpossec.QposEq, Qpossec.Qpos_one, Qpossec.Qpos_plus, Qpossec.Qpos_mult, Qpossec.Qpos_inv,
  to_Q, QposAsQ;
  simpl.

(*Open Scope Q_scope.*)

Class ExtMetricSpaceBall (X : Type) : Type := ext_mspc_ball: Qinf → relation X.

Local Notation B' := ext_mspc_ball.

(* In the proof of Banach fixpoint theorem we have to use arithmetic
expressions such as q^n / (1 - q) when 0 <= q < 1 as the ball radius. If
the radius is in Qnn (ie., QnonNeg.T), then we have to prove that 1 - q :
Qnn. It seems more convenient to have the radius live in Q and have the
axiom that no points are separated by a negative distance. *)

Class ExtMetricSpace (X : Type) `{Equiv X} `{ExtMetricSpaceBall X} : Prop :=
  { ext_mspc_setoid : Setoid X
  ; ext_mspc_ball_proper:> Proper (=) B'
  ; ext_mspc_ball_inf: ∀ x y, B' Qinf.infinite x y
  ; ext_mspc_ball_negative: ∀ (e: Q), (e < 0)%Q → ∀ x y, ~ B' e x y
  ; ext_mspc_ball_zero: ∀ x y, B' 0 x y ↔ x = y
  ; ext_mspc_refl:> ∀ e, (0 <= e)%Qinf → Reflexive (B' e)
  ; ext_mspc_sym:> ∀ e, Symmetric (B' e)
  ; ext_mspc_triangle: ∀ (e1 e2: Qinf) (a b c: X),
       B' e1 a b → B' e2 b c → B' (e1 + e2) a c
  ; ext_mspc_closed: ∀ (e: Qinf) (a b: X),
       (∀ d: Qpos, B' (e + d) a b) → B' e a b }.

Class MetricSpaceBall (X : Type) : Type := mspc_ball: Q → relation X.

Local Notation B := mspc_ball.

Class MetricSpace (X : Type) `{Equiv X} `{MetricSpaceBall X} : Prop :=
  { mspc_setoid : Setoid X
  ; mspc_ball_proper:> Proper (=) B
  ; mspc_ball_negative: ∀ (e: Q), (e < 0)%Q → ∀ x y, ~ B e x y
  ; mspc_ball_zero: ∀ x y, B 0 x y ↔ x = y
  ; mspc_refl:> ∀ e, (0 <= e)%Q → Reflexive (B e)
  ; mspc_sym:> ∀ e, Symmetric (B e)
  ; mspc_triangle: ∀ (e1 e2: Q) (a b c: X), B e1 a b → B e2 b c → B (e1 + e2) a c
  ; mspc_closed: ∀ (e: Q) (a b: X), (∀ d: Qpos, B (e + d) a b) → B e a b
  ; mspc_finite: forall x1 x2 : X, exists e : Q, mspc_ball e x1 x2 }.

Section Coercion.

Context `{MetricSpace X}.

Global Instance : ExtMetricSpaceBall X := λ e : Qinf,
match e with
| Qinf.infinite => λ _ _, True
| Qinf.finite e => B e
end.

Global Instance : ExtMetricSpace X.
Admitted.

End Coercion.


(*Section MetricSpaceClass.

Context `{MetricSpaceClass X}.

Program Definition Qnn_minus `(A : q1 <= q2) : Qnn := (q2 - q1)%Q.
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
Qed.

Lemma mspc_triangle' :
  ∀ (q1 q2 : Qnn) (b a c : X) (q : Qnn),
    q1 + q2 = q → mspc_ball q1 a b → mspc_ball q2 b c → mspc_ball q a c.
Proof.
intros q1 q2 b a c q A1 A2 A3. rewrite <- A1. eapply mspc_triangle; eauto.
Qed.

Lemma mspc_monotone :
  ∀ q1 q2 : Qnn, (q1 <= q2)%Q -> ∀ x y : X, mspc_ball q1 x y → mspc_ball q2 x y.
Proof.
intros q1 q2 A1 x y A2.
setoid_replace q2 with (q1 + (Qnn_minus A1)).
apply mspc_triangle with (b := y); [| apply mspc_refl]; trivial.
unfold Qnn_minus; Qsimpl; lra.
Qed.

Lemma mspc_zero_eq : ∀ x y : X, mspc_ball 0 x y ↔ x = y.
Proof.
intros x y; split; intro A1; [| rewrite A1; apply mspc_refl].
apply mspc_eq. intro q; apply (mspc_monotone 0); trivial. apply (proj2_sig q).
Qed.

End MetricSpaceClass.
*)

Record UniformlyContinuous
  (X Y : Type) `{Equiv X, Equiv Y, ExtMetricSpaceBall X, ExtMetricSpaceBall Y} := mkUniformlyContinuous {
  uc_fun :> X → Y;
  uc_mu : Qpos -> QposInf;
  uc_proper : Proper (=) uc_fun;
  uc_prf : ∀ (q: Qpos) (a b: X), B' (uc_mu q) a b → B' q (uc_fun a) (uc_fun b)
}.

Arguments uc_fun {X} {Y} {_} {_} {_} {_} _ _.
Arguments uc_mu {X} {Y} {_} {_} {_} {_} _ _.
Arguments uc_prf {X} {Y} {_} {_} {_} {_} _ _ _ _ _.

Global Existing Instance uc_proper.

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

Definition sequence (X : Type) := nat -> X.

Section MetricSpaceDefs.

Context `{ExtMetricSpace X}.

Definition cauchy (x : sequence X) :=
  ∀ q : Qpos, ∃ N : nat, ∀ m n : nat, (N < m)%nat -> (N < n)%nat -> B' q (x m) (x n).

Definition limit (x : sequence X) (a : X) :=
  ∀ q : Qpos, ∃ N : nat, ∀ n : nat, (N < n)%nat -> B' q (x n) a.

Definition complete := ∀ x : sequence X, cauchy x → ∃ a : X, limit x a.

End MetricSpaceDefs.

Arguments complete X {_} : clear implicits.

(*Program Definition contr_modulus (q : Qnn) :=
match q with

Record Contraction
  (X Y : Type) `{Equiv X, Equiv Y, ExtMetricSpaceBall X, ExtMetricSpaceBall Y} := mkContraction {
  contr_fun :> X → Y;
  contr_mu : Qnn;
  contr_mu1 : (contr_mu < 1)%Q;
  contr_proper : Proper (=) contr_fun;
  contr_prf : ∀ (e : Qpos) (x1 x2 : X),
    mspc_ball (e / contr_mu) x1 x2 → mspc_ball e (contr_fun x1) (contr_fun x2)
}.

Arguments contr_fun {X} {Y} {_} {_} {_} {_} _ _.
Arguments contr_mu {X} {Y} {_} {_} {_} {_} _.
Arguments contr_prf {X} {Y} {_} {_} {_} {_} _ _ _ _ _.

Global Existing Instance contr_proper.
*)

(*Section Contractions.*)

(*Context (X Y : Type) `{Equiv X, Equiv Y, MetricSpaceBall X, MetricSpaceBall Y}.*)

(*
Definition contr_to_cont
  (X Y : Type) `{Equiv X, Equiv Y, MetricSpaceBall X, MetricSpaceBall Y} (f : Contraction X Y) : UniformlyContinuous X Y.
split with (uc_fun := f) (uc_mu := fun e => e / contr_mu f).
(* uc_proper *)
apply f.
(* uc_prf *)
apply contr_prf.
Defined.

(*End Contractions.*)

Coercion contr_to_cont : Contraction >-> UniformlyContinuous.

Section MetricSpaceLimits.

Context `{MetricSpaceClass X, MetricSpaceClass Y}.

Theorem limit_unique : ∀ (x : sequence X) (a b : X), limit x a → limit x b → a = b.
Proof.
intros x a b A1 A2; apply mspc_eq'; intro q.
specialize (A1 (q / 2)); specialize (A2 (q / 2)).
destruct A1 as [N1 A1]; destruct A2 as [N2 A2].
set (N := S (Peano.max N1 N2)). specialize (A1 N); specialize (A2 N).
apply (mspc_triangle' (q / 2) (q / 2) (x N));
[Qsimpl; field | apply mspc_symm |];
[apply A1 | apply A2]; subst N; lia.
Qed.

Theorem limit_cont : ∀ (f : UniformlyContinuous X Y) (x : sequence X) (a : X),
  limit x a → limit (f ∘ x) (f a).
Proof.
intros f x a A1 q.
specialize (A1 (uc_mu f q)).
destruct A1 as [N A1]. exists N; intros n A2. now apply uc_prf, A1.
Qed.

Theorem limit_contr : ∀ (f : Contraction X Y) (x : sequence X) (a : X),
  limit x a → limit (f ∘ x) (f a).
Proof. intro f; apply (limit_cont f). Qed.

End MetricSpaceLimits.
*)

Section BanachFixpoint.

Context `{MetricSpace X} (f : (*Contraction*) X -> X) (x0 : X).

(*Let q : Q := f.(contr_mu).*)
Let x n := nat_iter n f x0.

Variable d : Q.

Hypothesis dist_x0_x1 : B d (x 0) (x 1).

Open Scope Qinf_scope.
Variables (a b : Q) (n : nat). Check (a^n).
Check _ : Pow Q nat.
SearchAbout (Pow Q nat).

Lemma dist_xn_xn' : forall n : nat, ball (d * q^n) (x n) (x n.+1).


SearchAbout "iter".

SearchAbout "power".
Lemma distance_n : ∀ n, mspc_ball 



