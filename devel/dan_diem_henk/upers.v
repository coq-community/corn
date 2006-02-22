Require Export pers. (* for def of transitive etc. *)

(********************** Universe ********************)

Inductive unv : Type :=
  InU : forall A : Set, forall a: A, unv.

Definition URel := relation unv.

Definition UTrans (R : URel) :=
  transitive R.

Definition USym (R : URel) :=
  symmetric R.

Record Uper : Type:=
  {urel :> URel;
   utrans : UTrans urel;
   usym : USym urel
  }.

Notation "a '<~' A" := (urel A a a) (at level 70).

Definition Ucompatible (A : Uper)(P : unv->Prop) :=
  forall a, a <~ A -> P a.

Definition uRestr (A : Uper)(P : unv -> Prop) :=
  fun a b => urel A a b /\ P a /\ P b.

Lemma uRestr_trans : 
  forall (A : Uper)(P : unv -> Prop), 
  UTrans (uRestr A P).
Proof.
intros A P a b c [Aab [pa pb]] [Abc [_ pc]].
split.
apply utrans with (1:=Aab) (2:=Abc).
spl.
Qed.

Lemma uRestr_symm : 
  forall  (A : Uper)(P : unv -> Prop),
  USym (uRestr A P).
Proof.
intros A P a b [Aab [pa pb]].
split.
apply usym with (1:=Aab).
spl.
Qed.

Definition urestr (A : Uper) (P : unv -> Prop) :=
  Build_Uper (uRestr A P) (uRestr_trans A P) (uRestr_symm A P).

Infix "@" := urestr (at level 69).

Lemma L31 : 
  forall (C : Uper) (a : unv) (P : unv -> Prop),
  a <~ C@P <-> a <~ C /\ P a.
Proof.
intros C a P.
split; intros [H H0].
exact (conj H (proj1 H0)).
exact (conj H (conj H0 H0)).
Qed.
