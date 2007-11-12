Require Export QArith.
Require Import Qordfield.
Require Import COrdFields.
Require Import Qauto.
Require Import CornTac.

Set Implicit Arguments.
Record OpenUnit:={OpenUnitasQ:> Q;
OpenUnitprf:0<OpenUnitasQ/\OpenUnitasQ<1}.

Delimit Scope ou_scope with ou.
Bind Scope ou_scope with OpenUnit.

Notation "'ou' x":=(@Build_OpenUnit x (conj (refl_equal Lt) (refl_equal Lt))) (at level 60, no associativity) : ou_scope.

Lemma OpenUnit_0_lt : forall (a:OpenUnit), 0 < a.
intros [a [H0 H1]]; assumption.
Qed.

Lemma OpenUnit_lt_1 : forall (a:OpenUnit), a < 1.
intros [a [H0 H1]]; assumption.
Qed.

Lemma OpenUnit_0_lt_Dual : forall (a:OpenUnit), 0 < 1-a.
intros [a [H0 H1]].
simpl.
rewrite Qlt_minus_iff in H1.
assumption.
Qed.

Lemma OpenUnit_Dual_lt_1 : forall (a:OpenUnit), 1-a < 1.
intros [a [H0 H1]].
simpl.
rewrite Qlt_minus_iff.
replace RHS with a by ring.
assumption.
Qed.

Hint Resolve OpenUnit_0_lt OpenUnit_lt_1 OpenUnit_0_lt_Dual OpenUnit_Dual_lt_1 : ouarith.

Definition OpenUnitMult (a b:OpenUnit):OpenUnit.
intros a b.
exists (a * b).
abstract(destruct a as [a [Ha0 Ha1]]; destruct b as [b [Hb0 Hb1]];
split; simpl;
 [rsapply mult_resp_pos; assumption
 |change (1:Q) with (1*1);
 rsapply mult_resp_less_both;auto with *]).
Defined.

Notation "x * y":=(OpenUnitMult x y) : ou_scope.

Definition OpenUnitDiv (a b:OpenUnit):(a<b)->OpenUnit.
intros a b p.
exists (a/b).
abstract (destruct a as [a [Ha0 Ha1]]; destruct b as [b [Hb0 Hb1]];
split; simpl;[
 apply Qlt_shift_div_l; auto; ring_simplify;  auto|
 apply Qlt_shift_div_r; auto; ring_simplify;  auto]).
Defined.

Definition OpenUnitDual (a:OpenUnit):OpenUnit.
intros a.
exists (1-a).
abstract (destruct a as [a [Ha0 Ha1]];
simpl; split; rewrite  Qlt_minus_iff in *;[
(replace RHS with (1+-a) by ring); auto|
(replace RHS with (a+-0) by ring); auto]).
Defined.

(* 1 - (1-a)*(1-b) or a + b - a*b *)
Definition OpenUnitDualMult (a b:OpenUnit):OpenUnit.
intros a b.
exists (a + b - a * b).
abstract (
split;
[(replace RHS with (OpenUnitDual ((OpenUnitDual a)*(OpenUnitDual b)):Q) by simpl; ring);
 auto with *
|(replace LHS with (OpenUnitDual ((OpenUnitDual a)*(OpenUnitDual b)):Q) by simpl; ring);
 auto with *]).
Defined.

(* 1 - (1-b)/(1-a) or (b-a)/(1-a) *)
Definition OpenUnitDualDiv (b a:OpenUnit):(a<b)->OpenUnit.
intros b a p.
exists ((b-a)/(1-a)).
abstract (
assert (X:OpenUnitDual b < OpenUnitDual a);
[rewrite Qlt_minus_iff in *;
 simpl;
 (replace RHS with (b + - a) by ring);
 assumption
|split;
 [(replace RHS with (OpenUnitDual (OpenUnitDiv _ _ X):Q) by simpl; field; auto with *);
  auto with *
 |(replace LHS with (OpenUnitDual (OpenUnitDiv _ _ X):Q) by simpl; field; auto with *);
  auto with *]]).
Defined.