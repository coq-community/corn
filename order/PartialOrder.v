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
Set Firstorder Depth 5.

Require Export RSetoid.

Set Implicit Arguments.

(**
* Partial Order
A partial order is a relfexive, transitive, antisymetric ordering relation.
*)

(* Perhaps adding monotone and antitone to the signature is going too far *)
Record is_PartialOrder
 (car : Type)
 (eq : car -> car -> Prop)
 (le : car -> car -> Prop)
 (monotone : (car -> car) -> Prop)
 (antitone : (car -> car) -> Prop) : Prop :=
{ po_equiv_le_def : forall x y, eq x y <-> (le x y /\ le y x)
; po_le_refl : forall x, le x x
; po_le_trans : forall x y z, le x y -> le y z -> le x z
; po_monotone_def : forall f, monotone f <-> (forall x y, le x y -> le (f x) (f y))
; po_antitone_def : forall f, antitone f <-> (forall x y, le x y -> le (f y) (f x))
}.

(* This ought to decend from RSetoid *)
Record PartialOrder : Type :=
{ po_car :> RSetoid
; le : po_car -> po_car -> Prop
; monotone : (po_car -> po_car) -> Prop
; antitone : (po_car -> po_car) -> Prop
; po_proof : is_PartialOrder (@st_eq po_car) le monotone antitone
}.

Notation "x == y" := (st_eq x y) (at level 70, no associativity) : po_scope.
Notation "x <= y" := (le _ x y) : po_scope.

Open Local Scope po_scope.

Lemma po_st : forall X eq le mnt ant, @is_PartialOrder X eq le mnt ant -> Setoid_Theory X eq.
Proof with trivial.
 intros X eq le0 mnt ant H.
 split.
   firstorder.
  intros x y E. apply (po_equiv_le_def H), and_comm, (po_equiv_le_def H)...
 intros x y z.
 repeat rewrite ->(po_equiv_le_def H).
 firstorder.
Qed.

(* begin hide *)
Add Parametric Morphism (p:PartialOrder) : (le p) with signature (@st_eq p) ==> (@st_eq p) ==> iff as le_compat.
Proof.
 assert (forall x1 x2 : p, x1 == x2 -> forall x3 x4 : p, x3 == x4 -> (x1 <= x3 -> x2 <= x4)).
  intros.
  rewrite -> (po_equiv_le_def (po_proof p)) in *|-.
  destruct (po_proof p).
  clear - H H0 H1 po_le_trans0.
  firstorder.
 intros x y Hxy x0 y0 Hx0y0.
 assert (y==x).
  symmetry; assumption.
 assert (y0==x0).
  symmetry; assumption.
 firstorder.
Qed.
(* end hide *)
Section PartialOrder.

Variable X : PartialOrder.

Definition makePartialOrder car eq le monotone antitone p1 p2 p3 p4 p5 :=
let p := (@Build_is_PartialOrder car eq le monotone antitone p1 p2 p3 p4 p5) in
 @Build_PartialOrder (Build_RSetoid (po_st p)) le monotone antitone p.

(** The axioms and basic properties of a partial order *)
Lemma equiv_le_def : forall x y:X, x == y <-> (x <= y /\ y <= x).
Proof (po_equiv_le_def (po_proof X)).

Lemma le_refl : forall x:X, x <= x.
Proof (po_le_refl (po_proof X)).

Lemma le_trans : forall x y z : X, x <= y -> y <= z -> x <= z.
Proof (po_le_trans (po_proof X)).

Lemma monotone_def : forall f, monotone X f <-> (forall x y, x <= y -> (f x) <= (f y)).
Proof (po_monotone_def (po_proof X)).

Lemma antitone_def : forall f, antitone X f <-> (forall x y, x <= y -> (f y) <= (f x)).
Proof (po_antitone_def (po_proof X)).

Lemma le_equiv_refl : forall x y:X, x == y -> x <= y.
Proof.
 firstorder using equiv_le_def.
Qed.

Lemma le_antisym : forall x y:X, x <= y -> y <= x -> x == y.
Proof.
 firstorder using equiv_le_def.
Qed.

(**
** Dual Order
The dual of a partial order is made by fliping the order relation.
*)
Definition Dual : PartialOrder.
Proof.
 eapply makePartialOrder with (eq := @st_eq X) (le:= (fun x y => le X y x)) (monotone := @monotone X)
   (antitone := @antitone X).
     firstorder using equiv_le_def.
    firstorder using le_refl.
   firstorder using le_trans.
  firstorder using monotone_def. (* Notice the use of <-> in monotone_def here *)
 firstorder using antitone_def.
Defined.

End PartialOrder.

Module Default.
(**
** Default Monotone and Antitone
These provide default implemenations of Monotone and Antitone.
*)
Section MonotoneAntitone.

Variable A : Type.
Variable le : A -> A -> Prop.

Definition monotone (f: A -> A) := forall x y, le x y -> le (f x) (f y).

Lemma monotone_def : forall f, monotone f <-> (forall x y, le x y -> le (f x) (f y)).
Proof.
 firstorder.
Qed.

Definition antitone (f: A -> A) := forall x y, le x y -> le (f y) (f x).

Lemma antitone_def : forall f, antitone f <-> (forall x y, le x y -> le (f y) (f x)).
Proof.
 firstorder.
Qed.

End MonotoneAntitone.

End Default.
