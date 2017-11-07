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

Require Export Coq.Setoids.Setoid.
Require Import CoRN.logic.CornBasics.
Require Import MathClasses.interfaces.abstract_algebra.

(* Require Import CornTac.*)

(**
* Classic Setoids presented in a bundled way. 
*
* THIS NOTION IS OBSOLETE AND SHOULD NOT BE USED ANYMORE
* Use [abstract_algebra.Setoid] instead
*)

Structure RSetoid: Type :=
{ st_car :> Type;
  st_eq : Equiv st_car ;
  st_isSetoid : Setoid st_car
}.

Typeclasses Transparent Equiv.
Hint Extern 10 (Equiv _) => apply @st_eq : typeclass_instances.
Hint Extern 10 (Setoid _) => apply @st_isSetoid  : typeclass_instances.

Implicit Arguments st_eq [r].

Definition mcSetoid_as_RSetoid X {e : Equiv X} {setoid : Setoid X} : RSetoid := Build_RSetoid setoid.
Implicit Arguments mcSetoid_as_RSetoid [[e] [setoid]].

(* Canonical Structure mcSetoid_as_RSetoid. *)
(* If we make this a canonical structure StepQsec will break: investigate *)

(** Propositions form a setoid under iff *)
Definition iffSetoid : RSetoid.
Proof.
 eexists Prop iff.
 firstorder.
Defined.

(**
** Morhpisms between Setoids
*)
Record Morphism (X Y : RSetoid) :=
{evalMorphism :> X -> Y
;Morphism_prf : forall x1 x2, (st_eq x1 x2) -> (st_eq (evalMorphism x1) (evalMorphism x2))
}.

Definition extEq (X:Type) (Y : RSetoid) (f g:X -> Y) := forall x, st_eq (f x) (g x).
Definition extSetoid (X Y : RSetoid) : RSetoid.
Proof.
 eexists (Morphism X Y) (extEq Y).
 split.
   intros x y; reflexivity.
  intros x y H a; symmetry; auto.
 intros x y z Hxy Hyz a; transitivity (y a); auto.
Defined.

Notation "x --> y" := (extSetoid x y) (at level 55, right associativity) : setoid_scope.

Local Open Scope setoid_scope.
(**
** Basic Combinators for Setoids
*)

Definition id (X : RSetoid) : X-->X.
Proof.
 eexists (fun x => x).
 abstract (auto).
Defined.
(* begin hide *)
Implicit Arguments id [X].
(* end hide *)
Definition compose0 X Y Z (x : Y ->Z) (y:X -> Y) z := x (y z).

Definition compose1 (X Y Z : RSetoid) : (Y-->Z) -> (X --> Y) -> X --> Z.
Proof.
 intros f0 f1.
 exists (compose0 f0 f1).
 abstract ( destruct f0 as [f0 Hf0]; destruct f1 as [f1 Hf1]; intros x1 x2 Hx; apply Hf0; apply Hf1;
   assumption).
Defined.

Definition compose2 (X Y Z : RSetoid) : (Y-->Z) -> (X --> Y) --> X --> Z.
Proof.
 intros f0.
 eexists (compose1 f0).
 abstract ( destruct f0 as [f0 Hf0]; intros x1 x2 H y; apply: Hf0; apply H).
Defined.

Definition compose (X Y Z : RSetoid) : (Y-->Z) --> (X --> Y) --> X --> Z.
Proof.
 exists (@compose2 X Y Z).
 abstract ( intros x1 x2 H y z; apply: H).
Defined.
(* begin hide *)
Implicit Arguments compose [X Y Z].
(* end hide *)
Definition const0 (X Y : RSetoid) : X->Y-->X.
Proof.
 intros x.
 eexists (fun y => x).
 abstract reflexivity.
Defined.

Definition const (X Y : RSetoid) : X-->Y-->X.
Proof.
 exists (@const0 X Y).
 abstract ( intros x1 x2 Hx y; assumption).
Defined.
(* begin hide *)
Implicit Arguments const [X Y].
(* end hide *)
Definition flip0 (X Y Z : RSetoid) : (X-->Y-->Z)->Y->X-->Z.
Proof.
 intros f y.
 exists (fun x => f x y).
 abstract ( destruct f as [f Hf]; intros x1 x2 H; apply Hf; auto).
Defined.

Definition flip1 (X Y Z : RSetoid) : (X-->Y-->Z)->Y-->X-->Z.
Proof.
 intros f.
 exists (flip0 f).
 abstract ( destruct f as [f Hf]; intros x1 x2 H y; simpl; destruct (f y) as [g Hg]; apply Hg; auto).
Defined.

Definition flip (X Y Z : RSetoid) : (X-->Y-->Z)-->Y-->X-->Z.
Proof.
 exists (@flip1 X Y Z).
 abstract ( intros x1 x2 H y z; apply: H).
Defined.
(* begin hide *)
Implicit Arguments flip [X Y Z].
(* end hide *)
Definition join0 (X Y : RSetoid) : (X-->X-->Y)->X-->Y.
Proof.
 intros f.
 exists (fun y => f y y).
 abstract ( destruct f as [f Hf]; intros x1 x2 H; simpl; transitivity (f x1 x2);
   [destruct (f x1) as [g Hg]; apply Hg; auto |apply Hf; auto]).
Defined.

Definition join (X Y : RSetoid) : (X-->X-->Y)-->X-->Y.
Proof.
 exists (@join0 X Y).
 abstract ( intros x1 x2 H y; apply: H).
Defined.
(* begin hide *)
Implicit Arguments join [X Y].
(* end hide *)
Definition ap (X Y Z : RSetoid) : (X --> Y --> Z) --> (X --> Y) --> (X --> Z)
:= compose (compose (compose (@join _ _)) (@flip _ _ _)) (compose (@compose _ _ _)).
(* begin hide *)
Implicit Arguments ap [X Y Z].
(* end hide *)

Definition bind (X Y Z : RSetoid) : (X--> Y) --> (Y --> X--> Z) --> (X--> Z):=
(compose (compose (@join _ _)) (flip (@compose X Y (X-->Z)))).

Definition bind_compose (X Y Z W : RSetoid) :
 (W--> X--> Y) --> (Y --> X--> Z) --> (W--> X--> Z):=
 (flip (compose (@compose W _ _) ((flip (@bind X Y Z))))).
(* begin hide *)
Implicit Arguments bind [X Y Z].
Implicit Arguments bind_compose [X Y Z W].
(* end hide *)
