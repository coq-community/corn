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

Require Export RSetoid.
Require Import Relation_Definitions.
Require Export Qpossec.
Require Import COrdFields2.
Require Import Qordfield.
Require Import QMinMax.
Require Import List.
Require Import CornTac.

Set Implicit Arguments.
(**
* Metric Space
In this version, a metric space over a setoid X is characterized by a
ball relation B where B e x y is intended to mean that the two points
x and y are within e of each other ( d(x,y)<=e ).  This is characterized
by the axioms given in the record structure below.
*)

Record is_MetricSpace (X:Setoid) (B: Qpos -> relation X) : Prop :=
{ msp_refl: forall e, reflexive _ (B e)
; msp_sym: forall e, symmetric _ (B e)
; msp_triangle: forall e1 e2 a b c, B e1 a b -> B e2 b c -> B (e1 + e2)%Qpos a c
; msp_closed: forall e a b, (forall d, B (e+d)%Qpos a b) -> B e a b
; msp_eq: forall a b, (forall e, B e a b) -> st_eq a b
}.

Record MetricSpace : Type :=
{ msp_is_setoid :> Setoid
; ball : Qpos -> msp_is_setoid -> msp_is_setoid -> Prop
; ball_wd : forall (e1 e2:Qpos), (QposEq e1 e2) -> 
            forall x1 x2, (st_eq x1 x2) -> 
            forall y1 y2, (st_eq y1 y2) -> 
            (ball e1 x1 y1 <-> ball e2 x2 y2)
; msp : is_MetricSpace msp_is_setoid ball
}.

(* begin hide *)
Implicit Arguments ball [m].

(*This is intended to be used as a ``type cast'' that Coq won't randomly make disappear.
  It is useful when defining setoid rewrite lemmas for st_eq.*)
Definition ms_id (m:MetricSpace) (x:m) : m := x.
Implicit Arguments ms_id [m].

Add Parametric Morphism (m:MetricSpace) : (@ball m) with signature QposEq ==> (@st_eq m) ==> (@st_eq m) ==> iff as ball_compat.
exact (@ball_wd m).
Qed.
(* end hide *)

Section Metric_Space.

(*
** Ball lemmas
*)

Variable X : MetricSpace.

(** These lemmas give direct access to the ball axioms of a metric space 
*)

Lemma ball_refl : forall e (a:X), ball e a a.
Proof.
apply (msp_refl (msp X)).
Qed.

Lemma ball_sym : forall e (a b:X), ball e a b -> ball e b a.
Proof.
apply (msp_sym (msp X)).
Qed.

Lemma ball_triangle : forall e1 e2 (a b c:X), ball e1 a b -> ball e2 b c -> ball (e1+e2) a c.
Proof.
apply (msp_triangle (msp X)).
Qed.

Lemma ball_closed :  forall e (a b:X), (forall d, ball (e+d) a b) -> ball e a b.
Proof.
apply (msp_closed (msp X)).
Qed.

Lemma ball_eq : forall (a b:X), (forall e, ball e a b) -> st_eq a b.
Proof.
apply (msp_eq (msp X)).
Qed.

Lemma ball_eq_iff : forall (a b:X), (forall e, ball e a b) <-> st_eq a b.
Proof.
split.
apply ball_eq.
intros H e.
rewrite H.
apply ball_refl.
Qed.

(** The ball constraint on a and b can always be weakened.  Here are
two forms of the weakening lemma.
*)

Lemma ball_weak : forall e d (a b:X), ball e a b -> ball (e+d) a b.
Proof.
intros e d a b B1.
eapply ball_triangle.
apply B1.
apply ball_refl.
Qed.

Hint Resolve ball_refl ball_triangle ball_weak : metric.

Lemma ball_weak_le : forall (e d:Qpos) (a b:X), e<=d ->  ball e a b -> ball d a b.
Proof.
intros e d a b Hed B1.
destruct (Qle_lt_or_eq _ _ Hed).
destruct (Qpos_lt_plus H) as [c Hc].
rewrite <- Q_Qpos_plus in Hc.
change (QposEq d (e+c)) in Hc.
rewrite Hc; clear - B1.
auto with *.
change (QposEq e d) in H.
rewrite <- H.
assumption.
Qed.

End Metric_Space.
(* begin hide *)
Hint Resolve ball_refl ball_sym ball_triangle ball_weak : metric.
(* end hide *)