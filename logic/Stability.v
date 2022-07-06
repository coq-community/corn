
Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import CoRN.model.totalorder.QposMinMax.
Require Import Coq.Classes.Morphisms.

(* Doubly-negated types as a monad: *)

Definition DN (T: Type): Prop := (T -> False) -> False.

#[global]
Hint Unfold DN.

#[global]
Instance DN_Proper: Proper (iff ==> iff) DN.
Proof. firstorder. Qed.

Definition DN_return {T: Type}: T -> DN T :=
  fun x f => f x.

#[global]
Hint Resolve @DN_return.

Definition DN_bind {A: Type}: DN A -> forall B, (A -> DN B) -> DN B :=
  fun X Y Z P => X (fun a => Z a P).

Definition ext_eq: Prop := forall (A B: Type) (f g: A -> B), (forall x, f x = g x) -> f = g.

Lemma DN_runit: ext_eq -> forall A (x: DN A),
  DN_bind x _ DN_return = x.
Proof.
  intros.
  cut (forall y y', y = y' -> x y = x y'). firstorder.
  congruence.
Qed.

Lemma DN_lunit: ext_eq -> forall A B (a: A) (f: A -> DN B),
  DN_bind (DN_return a) _ f = f a.
Proof. firstorder. Qed.

Lemma DN_assoc A B C (a: DN A) (f: A -> DN B) (g: B -> DN C):
  DN_bind (DN_bind a _ f) _ g = DN_bind a _ (fun x => DN_bind (f x) _ g).
Proof. reflexivity. Qed.

Lemma DN_fmap {A: Type}: DN A -> forall B, (A -> B) -> DN B.
Proof. firstorder. Qed.

Lemma DN_liftM2 {A B C: Type} (f: A -> B -> C): DN A -> DN B -> DN C.
Proof. firstorder. Qed.
  (* todo: this is a specialization for DN. make a normal monadic version *)

Lemma DN_exists {T: Type} {P: T -> Prop} {x: T}: DN (P x) -> DN (ex P).
Proof. firstorder. Qed.

Class Stable P := from_DN: (DN P -> P).
  (* Using an Inductive gets us universe polymorphism, which the following
   simpler alternative does not provide: *)

(* Definition Stable P := DN P -> P. *)

Lemma DN_apply {T: Type}: DN T -> forall P, Stable P -> (T -> P) -> P.
Proof. firstorder. Qed.

Lemma DN_free P: Stable P -> DN P -> P.
Proof. firstorder. Qed.

Lemma Stable_neg (P: Prop): Stable (~P).
Proof. firstorder. Qed.

#[global]
Instance Stable_False: Stable False.
Proof. firstorder. Qed.

#[global]
Instance Stable_True: Stable True.
Proof. firstorder. Qed.

#[global]
Hint Immediate Stable_False Stable_True.

#[global]
Instance stable_conjunction (A B: Prop): Stable A -> Stable B -> Stable (A /\ B).
Proof. firstorder. Qed.

#[global]
Hint Resolve stable_conjunction.

#[global]
Instance forall_stable (T: Type) (P: T -> Type): (forall x, Stable (P x)) -> Stable (forall x, P x).
Proof. firstorder. Qed.

#[global]
Instance stable_iff (P Q: Prop): Stable P -> Stable Q -> Stable (P <-> Q).
Proof. firstorder. Qed.

#[global]
Hint Resolve forall_stable.

(*Require Import util.*)

Class decision (P: Prop): Set := decide: { P } + { ~ P }.

Lemma decision_stable P: decision P -> Stable P.
Proof. firstorder. Qed.

Require Import CoRN.reals.fast.CRGroupOps CoRN.logic.Classic.

Lemma Qle_dec x y: decision (Qle x y).
  intros.
  destruct (Qlt_le_dec y x); [right | left]; [apply Qlt_not_le |]; assumption.
Defined.
  (* Todo: Don't I have this elsewhere? *)

(* Everything is decidable in DN: *)

Lemma DN_decision (P: Prop): DN (decision P).
Proof. firstorder. Qed.

Lemma DN_decisionT (P: Type): DN (P + (P->False)).
Proof. firstorder. Qed.

#[global]
Instance CRnonNeg_stable x: Stable (CRnonNeg x).
Proof with auto.
  unfold CRnonNeg.
  intros.
  intro.
  intros.
  destruct (Qle_dec (-proj1_sig e) (approximate x (Qpos2QposInf e))).
  exact q.
  elimtype False...
Qed.

#[global]
Hint Resolve CRnonNeg_stable.

#[global]
Instance CReq_stable (x y: msp_car CR): Stable (x == y)%CR.
Proof.
  simpl.
  unfold regFunEq, ball. simpl.
  apply forall_stable. intros. 
  apply forall_stable. intros. 
  unfold Qmetric.Qball, Qmetric.QAbsSmall.
  simpl. apply stable_conjunction.
  apply decision_stable. apply Qle_dec.
  apply decision_stable. apply Qle_dec.
Qed.

Local Open Scope CR_scope.

Lemma DN_or P Q: (((P -> False) /\ (Q -> False)) -> False) -> DN (P + Q).
Proof. firstorder. Qed.

Definition not_forall_exists_not_DN (T: Type) (P: T -> Prop) (Pd: forall x, P x \/ ~ P x):
  (~ forall x, P x) -> DN (exists x, ~ P x).
Proof. firstorder. Qed.
