(*
Copyright © 2007-2008 Russell O’Connor

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
Require Export Coq.QArith.QArith.
Require Import CoRN.model.ordfields.Qordfield.
Require Import CoRN.algebra.COrdFields.
Require Import CoRN.tactics.Qauto.
Require Import CoRN.tactics.CornTac.

Set Implicit Arguments.

Local Open Scope Q_scope.

(**
* [OpenUnit]
Open unit represents rational number in (0,1).
*)

Record OpenUnit:={OpenUnitasQ:> Q;
OpenUnitprf:0<OpenUnitasQ/\OpenUnitasQ<1}.

Delimit Scope ou_scope with ou.
Bind Scope ou_scope with OpenUnit.

(** This notation allows one to easily write closed expressions for
[OpenUnit] (e.g. [ou (1#2)]).  The typechecker verifies that the close
term is inside (0,1) by computation. *)
Notation "'ou' x":=(@Build_OpenUnit x (conj (refl_equal Lt) (refl_equal Lt))) (at level 60, no associativity) : ou_scope.

(** Basic propertirs about [a:OpenUnit] and its dual value [1-a]. *)
Lemma OpenUnit_0_lt : forall (a:OpenUnit), 0 < a.
Proof.
 intros [a [H0 H1]]; assumption.
Qed.

Lemma OpenUnit_lt_1 : forall (a:OpenUnit), a < 1.
Proof.
 intros [a [H0 H1]]; assumption.
Qed.

Lemma OpenUnit_0_lt_Dual : forall (a:OpenUnit), 0 < 1-a.
Proof.
 intros [a [H0 H1]].
 simpl.
 rewrite -> Qlt_minus_iff in H1;assumption.
Qed.

Lemma OpenUnit_Dual_lt_1 : forall (a:OpenUnit), 1-a < 1.
Proof.
 intros [a [H0 H1]].
 simpl.
 rewrite -> Qlt_minus_iff.
 replace RHS with a by simpl; ring.
 assumption.
Qed.
(* begin hide *)
Hint Resolve OpenUnit_0_lt OpenUnit_lt_1 OpenUnit_0_lt_Dual OpenUnit_Dual_lt_1 : ouarith.
(* end hide *)
(** Multiplication *)
Definition OpenUnitMult (a b:OpenUnit):OpenUnit.
Proof.
 exists (a * b).
 abstract(destruct a as [a [Ha0 Ha1]]; destruct b as [b [Hb0 Hb1]]; split; simpl;
   [apply: mult_resp_pos; assumption |change (1:Q) with (1*1);
     apply: mult_resp_less_both;auto with *]).
Defined.

Notation "x * y":=(OpenUnitMult x y) : ou_scope.

(** Division *)
Definition OpenUnitDiv (a b:OpenUnit):(a<b)->OpenUnit.
Proof.
 intros p.
 exists (a/b).
 abstract (destruct a as [a [Ha0 Ha1]]; destruct b as [b [Hb0 Hb1]]; split; simpl;[
   apply Qlt_shift_div_l; auto; ring_simplify;  auto|
     apply Qlt_shift_div_r; auto; ring_simplify;  auto]).
Defined.

(** The dual of a is 1-a *)
Definition OpenUnitDual (a:OpenUnit):OpenUnit.
Proof.
 exists (1-a).
 abstract (destruct a as [a [Ha0 Ha1]]; simpl; split; rewrite  -> Qlt_minus_iff in *;[
   (replace RHS with (1+-a) by simpl; ring); auto| (replace RHS with (a+-0) by simpl; ring); auto]).
Defined.

(** The dual of multipliation: 1 - (1-a)*(1-b) or a + b - a*b *)
Definition OpenUnitDualMult (a b:OpenUnit):OpenUnit.
Proof.
 exists (a + b - a * b).
 abstract ( split;
   [(replace RHS with (OpenUnitDual ((OpenUnitDual a)*(OpenUnitDual b)):Q) by simpl; ring);
     auto with *
       |(replace LHS with (OpenUnitDual ((OpenUnitDual a)*(OpenUnitDual b)):Q) by simpl; ring);
         auto with *]).
Defined.

(** The dual of division: 1 - (1-b)/(1-a) or (b-a)/(1-a) *)
Definition OpenUnitDualDiv (b a:OpenUnit):(a<b)->OpenUnit.
Proof.
 intros p.
 exists ((b-a)/(1-a)).
 abstract ( assert (X:OpenUnitDual b < OpenUnitDual a); [rewrite -> Qlt_minus_iff in *; simpl;
   (replace RHS with (b + - a) by simpl; ring); assumption |split;
     [(replace RHS with (OpenUnitDual (OpenUnitDiv _ _ X):Q) by simpl; field; auto with * );
       auto with *
         |(replace LHS with (OpenUnitDual (OpenUnitDiv _ _ X):Q) by simpl; field; auto with * );
           auto with *]]).
Defined.

(**
*** Equality
*)
Definition ou_eq (x y:OpenUnit) := Qeq x y.
Lemma ou_eq_refl : forall x, ou_eq x x.
Proof.
 intros; apply Qeq_refl.
Qed.

Lemma ou_eq_sym : forall x y, ou_eq x y -> ou_eq y x.
Proof.
 intros; apply Qeq_sym; auto.
Qed.

Lemma ou_eq_trans : forall x y z, ou_eq x y -> ou_eq y z -> ou_eq x z.
Proof.
 intros; apply (Qeq_trans x y); auto.
Qed.

Add Relation OpenUnit ou_eq
 reflexivity proved by ou_eq_refl
 symmetry proved by ou_eq_sym
 transitivity proved by ou_eq_trans
 as ou_st.

(** One cheif use of OpenUnit is to make strict affine combinations. *)
Definition affineCombo (o:OpenUnit) (a b:Q) := o*a + (1-o)*b.

Add Morphism affineCombo with signature ou_eq ==> Qeq ==> Qeq ==> Qeq as affineCombo_wd.
Proof.
 intros x1 x2 Hx y1 y2 Hy z1 z2 Hz.
 unfold affineCombo.
 unfold ou_eq in Hx.
 rewrite -> Hx, Hy, Hz; reflexivity.
Qed.

(** Properties of an affine combination. *)
Lemma affineCombo_gt : forall o a b (H:a < b), a < affineCombo o a b.
Proof.
 intros o a b H.
 unfold affineCombo.
 rewrite -> Qlt_minus_iff in *.
 replace RHS with ((1-o)*(b-a)) by simpl; ring.
 apply: mult_resp_pos; simpl; auto with *.
Qed.

Lemma affineCombo_lt : forall o a b (H:a < b), affineCombo o a b < b.
Proof.
 intros o a b H.
 unfold affineCombo.
 rewrite -> Qlt_minus_iff in *.
 replace RHS with (o*(b-a)) by simpl; ring.
 apply: mult_resp_pos; simpl; auto with *.
Qed.
(* begin hide *)
Hint Resolve affineCombo_lt affineCombo_gt : ouarith.
(* end hide *)

Lemma affineAffine_l : forall a b o1 o2,
(affineCombo o1 a (affineCombo o2 a b)==affineCombo (OpenUnitDualMult o1 o2) a b)%Q.
Proof.
 intros a b o1 o2.
 unfold affineCombo.
 simpl.
 ring.
Qed.

Lemma affineAffine_r : forall a b o1 o2,
(affineCombo o1 (affineCombo o2 a b) b==affineCombo (o1*o2) a b)%Q.
Proof.
 intros a b o1 o2.
 unfold affineCombo.
 simpl.
 ring.
Qed.
