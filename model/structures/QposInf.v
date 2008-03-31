(*
Copyright © 2006-2008 Russell O’Connor

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

Require Export Qpossec.
Require Import QposMinMax.

(** printing QposInf $\mathbb{Q}^{+}_{\infty}$ #Q<SUP>+</SUP><SUB>&infin;</SUB># *)
(** printing QposInfinity $\infty$ #&infin;# *)

Set Implicit Arguments.

Open Local Scope Q_scope.
Open Local Scope Qpos_scope.

(**
* [Qpos]
We choose to define [QposInf] as the disjoint union of [Qpos] and an
Infinity token.
*)

Inductive QposInf : Set :=
| Qpos2QposInf : Qpos -> QposInf
| QposInfinity : QposInf.

Bind Scope QposInf_scope with QposInf.
Delimit Scope QposInf_scope with QposInf.

(** Qpos2QposInf is an injection from [Qpos] to [QposInf] that we
declare as a coercion.
*)
Coercion Qpos2QposInf : Qpos >-> QposInf.

(** This bind operation is useful for lifting operations to work
on [QposInf].  It will map [QposInfinity] to [QposInfinity]. *)
Definition QposInf_bind (f : Qpos -> QposInf) (x:QposInf) :=
 match x with
 | Qpos2QposInf x' => f x'
 | QposInfinity => QposInfinity
 end.

Lemma QposInf_bind_id : forall x, QposInf_bind (fun e => e) x = x.
intros [x|]; reflexivity.
Qed.

(** Addditon *)
Definition QposInf_plus (x y : QposInf) : QposInf := 
QposInf_bind (fun x' => QposInf_bind (fun y' => x'+y') y) x.

(** Multiplication *)
Definition QposInf_mult (x y : QposInf) : QposInf := 
QposInf_bind (fun x' => QposInf_bind (fun y' => x'*y') y) x.

(** Order *)
Definition QposInf_le (x y: QposInf) : Prop :=
match y with
| QposInfinity => True
| Qpos2QposInf y' =>
 match x with 
 | QposInfinity => False
 | Qpos2QposInf x' => x' <= y'
 end
end.

(** Minimum *)
Definition QposInf_min (x y : QposInf) : QposInf :=
match x with
| QposInfinity => y
| Qpos2QposInf x' => 
 match y with
 | QposInfinity => x'
 | Qpos2QposInf y' => Qpos2QposInf (Qpos_min x' y')
 end
end.

Lemma QposInf_min_lb_l : forall x y, QposInf_le (QposInf_min x y) x.
Proof.
intros [x|] [y|]; simpl; try auto.
apply Qpos_min_lb_l.
apply Qle_refl.
Qed.

Lemma QposInf_min_lb_r : forall x y, QposInf_le (QposInf_min x y) y.
Proof.
intros [x|] [y|]; simpl; try auto.
apply Qpos_min_lb_r.
apply Qle_refl.
Qed.

Infix "+" := QposInf_plus : QposInf_scope.
Infix "*" := QposInf_mult : QposInf_scope.
