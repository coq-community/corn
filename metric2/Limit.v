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

Require Import QArith.
Require Import Bool.
Require Export Complete.
Require Export Streams.

Set Implicit Arguments.
(**
** Limits
A predicate saying there exists a point in the stream where a predicate
is satsified.

We take the unusual step of puting this inductive type in Prop even
though it contains constructive information.  This is because we expect
this proof to only be used in proofs of termination. *)
Inductive LazyExists A (P:Stream A -> Prop) (x: Stream A) : Prop :=
  | LazyHere : P x -> LazyExists P x
  | LazyFurther : (unit -> LazyExists P (tl x)) -> LazyExists P x.

Section TakeUntil.
(* begin hide *)
Coercion Local Is_true : bool >-> Sortclass.
(* end hide *)
(** takeUntil creates a list of of elements upto a the point where the predicate
P is satisfied.  For efficency reasons it doesn't actually build a list, but
takes continuations for cons and nil instead.  To build an actual list pass in
the const and nil constructors. *)
Fixpoint takeUntil (A B:Type) (P : Stream A -> bool)(s:Stream A) (ex:LazyExists P s) (cons: A -> B -> B) (nil : B) {struct ex} : B :=
(if P s as b return ((P s -> b) -> B)
then fun _ => nil
else fun (n : P s -> False) => cons (hd s)
     (@takeUntil A B P (tl s)
      match ex with
      | LazyHere H => (False_ind _ (n H))
      | LazyFurther ex0 => ex0 tt
      end cons nil))
(fun x => x).

Lemma takeUntil_wd : forall (A B:Type) (P : Stream A -> bool)(s:Stream A)(ex1 ex2:LazyExists P s) (cons: A -> B -> B) (nil:B),
  takeUntil P ex1 cons nil = takeUntil P ex2 cons nil.
Proof.
intros A B P s ex1 ex2 cons nil.
assert (H:=ex1).
induction H;
case ex1; clear ex1; case ex2; clear ex2;
simpl;
destruct (P x); try contradiction; auto.
intros ex2 ex1.
rewrite (H0 tt (ex1 tt) (ex2 tt)).
reflexivity.
Qed.

Lemma takeUntil_end : forall (A B:Type) (P:Stream A -> bool) seq (ex:LazyExists P seq) (cons:A -> B -> B) (nil : B),
 P seq -> takeUntil P ex cons nil = nil.
Proof.
intros A B P seq ex cons nil H.
rewrite <- (takeUntil_wd (B:=B) P (LazyHere P _ H)).
unfold takeUntil.
destruct (P seq);[|contradiction].
reflexivity.
Qed.

Lemma takeUntil_step : forall (A B:Type) (P:Stream A -> bool) seq (ex:LazyExists P seq) (cons: A -> B -> B) (nil: B),
 ~P seq -> exists ex':(LazyExists P (tl seq)), takeUntil P ex cons nil = cons (hd seq) (takeUntil P ex' cons nil).
Proof.
intros A B P seq ex cons nil H.
assert (ex':=ex).
destruct ex' as [H0|ex'].
elim H; assumption.
exists (ex' tt).
rewrite <- (takeUntil_wd (B:=B) P (LazyFurther seq ex')).
simpl.
destruct (P seq).
elim H; constructor.
reflexivity.
Qed.

Lemma takeUntil_elim : forall (A B:Type) (P:Stream A -> bool) (cons: A -> B -> B) (nil: B)
 (Q: Stream A -> B -> Prop),
 (forall seq, P seq -> Q seq nil) ->
 (forall seq x, Q (tl seq) x -> ~P seq -> Q seq (cons (hd seq) x)) ->
 forall seq (ex:LazyExists P seq), Q seq (takeUntil P ex cons nil).
Proof.
intros A B P cons nil Q c1 c2 seq ex.
assert (ex':=ex).
induction ex'.
 rewrite takeUntil_end; try assumption.
 eapply c1.
 apply H.
assert (Z0:=takeUntil_end P ex cons nil).
assert (Z1:=takeUntil_step P ex cons nil).
assert (Z0':=c1 x).
assert (Z1':=c2 x).
destruct (P x).
 clear Z1.
 rewrite Z0; try constructor.
 apply Z0'.
 constructor.
clear Z0 Z0'.
destruct (Z1 (fun x => x)) as [ex' Z].
rewrite Z.
clear Z Z1.
eapply Z1'; auto.
apply H0.
constructor.
Qed.

End TakeUntil.

Section Limit.

Variable X : MetricSpace.

(** This proposition says that the entire stream is within e of l *)
Definition NearBy (l:X)(e:QposInf) := ForAll (fun (s:Stream X) => ball_ex e (hd s) l).

Lemma NearBy_comp: forall l1 l2, st_eq l1 l2 -> forall (e1 e2:Qpos), QposEq e1 e2 -> forall s, (NearBy l1 e1 s <-> NearBy l2 e2 s).
Proof.
cut (forall l1 l2 : X,
st_eq l1 l2 ->
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

(** l is the limit if for every e there exists a point where the stream is
always within e of l. *)
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
(* begin hide *)
Implicit Arguments NearBy [X].
Implicit Arguments Limit [X].
(* end hide *)