(*
Copyright © 2006 Russell O’Connor

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

Require Import QArith.
Require Export Complete.
Require Export Streams.

Set Implicit Arguments.

Inductive LazyExists A (P:Stream A -> Prop) (x: Stream A) : Prop :=
  | LazyHere : P x -> LazyExists P x
  | LazyFurther : (unit -> LazyExists P (tl x)) -> LazyExists P x.

Section Limit.

Variable X : MetricSpace.

Definition NearBy (l:X)(e:QposInf) := ForAll (fun (s:Stream X) => ball_ex e (hd s) l).

Lemma NearBy_comp: forall l1 l2, ms_eq l1 l2 -> forall (e1 e2:Qpos), QposEq e1 e2 -> forall s, (NearBy l1 e1 s <-> NearBy l2 e2 s).
Proof.
cut (forall l1 l2 : X,
ms_eq (m:=X) l1 l2 ->
forall e1 e2 : Qpos,
QposEq e1 e2 -> forall s : Stream X, NearBy l1 e1 s -> NearBy l2 e2 s).
intros.
split.
firstorder.
intros.
eapply H.
symmetry.
apply H0.
unfold QposEq; symmetry.
apply H1.
assumption.

unfold NearBy; simpl.
intros l1 l2 Hl e1 e2 He.
cofix.
intros s [H0 H].
constructor.
simpl.
rewrite <- Hl.
rewrite <- He.
assumption.
auto.
Qed.

Lemma NearBy_weak: forall l (e1 e2:Qpos), e1 <= e2 -> forall s, NearBy l e1 s -> NearBy l e2 s.
Proof.
unfold NearBy; simpl.
intros l e1 e2 He.
cofix.
intros s [H0 H].
constructor.
eapply ball_weak_le.
apply He.
assumption.
auto.
Qed.

Definition Limit (s:Stream X)(l:X) := forall e, LazyExists (NearBy l e) s.

Lemma Limit_tl : forall s l, Limit s l -> Limit (tl s) l.
Proof.
intros s l H e.
destruct (H e) as [[_ H']|H'].
left; auto.
apply H'.
constructor.
Defined.

Lemma Limit_Str_nth_tl : forall n s l, Limit s l -> Limit (Str_nth_tl n s) l.
Proof.
induction n.
 tauto.
intros.
simpl.
apply IHn.
apply Limit_tl.
assumption.
Defined.

End Limit.

Implicit Arguments NearBy [X].
Implicit Arguments Limit [X].
