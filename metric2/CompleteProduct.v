(*
Copyright © 2008 Russell O’Connor

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
Require Export ProductMetric.
Require Export Complete.
Require Import Qauto.

Set Implicit Arguments.

Section CompleteProduct.
(**
*** Completion of product spaces.
This section develops the strong monad properties of the Completion
operation with respect to the product operation.
*)
Variable X Y:MetricSpace.
Let XY := ProductMS X Y.

(** The projection operations are uniformly continuous *)
Lemma fst_uc : is_UniformlyContinuousFunction (fun p:XY => fst p) Qpos2QposInf.
Proof.
 intros e a b [H _].
 assumption.
Qed.

Open Local Scope uc_scope.

Definition pi1 : XY --> X :=
Build_UniformlyContinuousFunction fst_uc.

Lemma snd_uc : is_UniformlyContinuousFunction (fun p:XY => snd p) Qpos2QposInf.
Proof.
 intros e a b [_ H].
 assumption.
Qed.

Definition pi2 : XY --> Y :=
Build_UniformlyContinuousFunction snd_uc.

Definition Cfst_raw (p:Complete XY) (e:QposInf) : X :=
(fst (approximate p e)).

Definition Csnd_raw (p:Complete XY) (e:QposInf) : Y :=
(snd (approximate p e)).

Lemma Cfst_prf : forall p, is_RegularFunction (Cfst_raw p).
Proof.
 intros p e1 e2.
 destruct (regFun_prf p e1 e2).
 auto.
Qed.

Lemma Csnd_prf : forall p, is_RegularFunction (Csnd_raw p).
Proof.
 intros p e1 e2.
 destruct (regFun_prf p e1 e2).
 auto.
Qed.

Definition Cfst_fun (p:Complete XY) : Complete X :=
Build_RegularFunction (Cfst_prf p).

Definition Csnd_fun (p:Complete XY) : Complete Y :=
Build_RegularFunction (Csnd_prf p).

Lemma Cfst_uc : is_UniformlyContinuousFunction Cfst_fun Qpos2QposInf.
Proof.
 intros e a b H e1 e2.
 destruct (H e1 e2).
 auto.
Qed.

Lemma Csnd_uc : is_UniformlyContinuousFunction Csnd_fun Qpos2QposInf.
Proof.
 intros e a b H e1 e2.
 destruct (H e1 e2).
 auto.
Qed.

Definition Cfst : Complete XY --> Complete X :=
Build_UniformlyContinuousFunction Cfst_uc.

Definition Csnd : Complete XY --> Complete Y :=
Build_UniformlyContinuousFunction Csnd_uc.

(** The pairing function is uniformly continuous *)
Lemma pair_uc_l : forall y:Y, @is_UniformlyContinuousFunction X XY (fun x => (x,y)) Qpos2QposInf.
Proof.
 intros y e a b H.
 split; auto.
 apply ball_refl.
Qed.

Lemma pair_uc_r : forall x:X, @is_UniformlyContinuousFunction Y XY (fun y => (x,y)) Qpos2QposInf.
Proof.
 intros x e a b H.
 split; auto.
 apply ball_refl.
Qed.

(** C(X*Y) is isomorphic to (C X)*(C Y) *)
Definition Couple_raw (p: ProductMS (Complete X) (Complete Y)) (e:QposInf): XY :=
(approximate (fst p) e,approximate (snd p) e).

Lemma Couple_prf : forall p, is_RegularFunction (Couple_raw p).
Proof.
 intros [p1 p2] e1 e2.
 split; simpl; apply regFun_prf.
Qed.

Definition Couple_fun (p: ProductMS (Complete X) (Complete Y)) : Complete XY :=
Build_RegularFunction (Couple_prf p).

Lemma Couple_uc : is_UniformlyContinuousFunction Couple_fun Qpos2QposInf.
Proof.
 intros e a b [Hl Hr] e1 e2.
 split; simpl; auto.
Qed.

Definition Couple : (ProductMS (Complete X) (Complete Y)) --> (Complete (ProductMS X Y)) :=
Build_UniformlyContinuousFunction Couple_uc.

Lemma CoupleCorrect1 : forall p,
st_eq (Couple ((Cfst p), (Csnd p))) p.
Proof.
 intros p e1 e2.
 destruct (regFun_prf p e1 e2).
 split; simpl; auto.
Qed.

Lemma CoupleCorrect2 : forall p q,
st_eq (Cfst (Couple (p,q))) p.
Proof.
 intros p q e1 e2.
 apply (regFun_prf p e1 e2).
Qed.

Lemma CoupleCorrect3 : forall p q,
st_eq (Csnd (Couple (p,q))) q.
Proof.
 intros p q e1 e2.
 apply (regFun_prf q e1 e2).
Qed.

End CompleteProduct.

(* begin hide *)
Implicit Arguments Couple [X Y].
Implicit Arguments Cfst [X Y].
Implicit Arguments Csnd [X Y].
(* end hide *)
