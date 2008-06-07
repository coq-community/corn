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

Set Implicit Arguments.

Require Export Setoid.
Require Import CornTac.

(**
* Classic Setoids
*)
Record Setoid: Type :=
{ st_car:>Type;
  st_eq:st_car-> st_car ->Prop;
  st_isSetoid: Setoid_Theory _ st_eq
}.

Add Parametric Relation s : (st_car s) (st_eq s)
 reflexivity proved by (@Equivalence_Reflexive _ _ (st_isSetoid s))
 symmetry proved by (@Equivalence_Symmetric _ _ (st_isSetoid s))
 transitivity proved by (@Equivalence_Transitive _ _ (st_isSetoid s))
 as genericSetoid.

(** Propositions form a setoid under iff *)
Definition iffSetoid : Setoid.
exists Prop iff.
firstorder.
Defined.

(**
** Morhpisms between Setoids
*)
Record Morphism (X Y:Setoid) :=
{evalMorphism :> X -> Y
;Morphism_prf : forall x1 x2, (st_eq X x1 x2) -> (st_eq Y (evalMorphism x1) (evalMorphism x2))
}.

Definition extEq (X:Type) (Y:Setoid) (f g:X -> Y) := forall x, st_eq Y (f x) (g x).
Definition extSetoid (X Y:Setoid) : Setoid.
intros X Y.
exists (Morphism X Y) (extEq Y).
split.
  intros x y; reflexivity.
 intros x y H a; symmetry; auto.
intros x y z Hxy Hyz a; transitivity (y a); auto.
Defined.

Notation "x --> y" := (extSetoid x y) (at level 55, right associativity) : setoid_scope.

Open Local Scope setoid_scope.
(**
** Basic Combinators for Setoids 
*)

Definition id (X:Setoid) : X-->X.
intros X.
exists (fun x => x).
abstract (auto).
Defined.
(* begin hide *)
Implicit Arguments id [X].
(* end hide *)
Definition compose0 X Y Z (x : Y ->Z) (y:X -> Y) z := x (y z).

Definition compose1 (X Y Z:Setoid) : (Y-->Z) -> (X --> Y) -> X --> Z.
intros X Y Z f0 f1.
exists (compose0 f0 f1).
abstract (
destruct f0 as [f0 Hf0];
destruct f1 as [f1 Hf1];
intros x1 x2 Hx;
rapply Hf0;
rapply Hf1;
assumption).
Defined.

Definition compose2 (X Y Z:Setoid) : (Y-->Z) -> (X --> Y) --> X --> Z.
intros X Y Z f0.
exists (compose1 f0).
abstract (
destruct f0 as [f0 Hf0];
intros x1 x2 H y;
rapply Hf0;
rapply H).
Defined.

Definition compose (X Y Z:Setoid) : (Y-->Z) --> (X --> Y) --> X --> Z.
intros X Y Z.
exists (@compose2 X Y Z).
abstract (
intros x1 x2 H y z;
rapply H).
Defined.
(* begin hide *)
Implicit Arguments compose [X Y Z].
(* end hide *)
Definition const0 (X Y:Setoid) : X->Y-->X.
intros X Y x.
exists (fun y => x).
abstract (
intros x1 x2 Hx;
reflexivity).
Defined.

Definition const (X Y:Setoid) : X-->Y-->X.
intros X Y.
exists (@const0 X Y).
abstract (
intros x1 x2 Hx y;
assumption).
Defined.
(* begin hide *)
Implicit Arguments const [X Y].
(* end hide *)
Definition flip0 (X Y Z:Setoid) : (X-->Y-->Z)->Y->X-->Z.
intros X Y Z f y.
exists (fun x => f x y).
abstract (
destruct f as [f Hf];
intros x1 x2 H;
apply Hf;
auto).
Defined.

Definition flip1 (X Y Z:Setoid) : (X-->Y-->Z)->Y-->X-->Z.
intros X Y Z f.
exists (flip0 f).
abstract (
destruct f as [f Hf];
intros x1 x2 H y;
simpl;
destruct (f y) as [g Hg];
rapply Hg;
auto).
Defined.

Definition flip (X Y Z:Setoid) : (X-->Y-->Z)-->Y-->X-->Z.
intros X Y Z.
exists (@flip1 X Y Z).
abstract (
intros x1 x2 H y z;
rapply H).
Defined.
(* begin hide *)
Implicit Arguments flip [X Y Z].
(* end hide *)
Definition join0 (X Y:Setoid) : (X-->X-->Y)->X-->Y.
intros X Y f.
exists (fun y => f y y).
abstract (
destruct f as [f Hf];
intros x1 x2 H;
simpl;
transitivity (f x1 x2);
[destruct (f x1) as [g Hg];
 rapply Hg; auto
|apply Hf; auto]).
Defined.

Definition join (X Y:Setoid) : (X-->X-->Y)-->X-->Y.
intros X Y.
exists (@join0 X Y).
abstract (
intros x1 x2 H y;
rapply H).
Defined.
(* begin hide *)
Implicit Arguments join [X Y].
(* end hide *)
Definition ap (X Y Z:Setoid) : (X --> Y --> Z) --> (X --> Y) --> (X --> Z)
:= compose (compose (compose (@join _ _)) (@flip _ _ _)) (compose (@compose _ _ _)).
(* begin hide *)
Implicit Arguments ap [X Y Z].
(* end hide *)