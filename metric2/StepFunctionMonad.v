(*
Copyright © 2007-2008 
 Russell O’Connor
 Bas Spitters

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
Require Export StepFunctionSetoid.
Require Import OpenUnit.
Require Import CornTac.

Set Implicit Arguments.
Definition StepFS (X:Setoid):Setoid.
intro X. exists (StepF X) (@StepF_eq X).
split;auto with *. rapply StepF_eq_trans.
Defined.

Open Scope setoid_scope.
Open Local Scope sfstscope.

Definition StFReturn (X:Setoid) : X-->(StepFS X).
intros.
exists (@constStepF X).
auto with *.
Defined.

(*
Definition StepFfoldS (X Y:Setoid): (X --> Y) -> (OpenUnit -> Y --> Y --> Y) 
     -> (StepFS X)--> Y.
intros X Y f g.
exists (@StepFfold X Y f (fun o y=>g o y)).
intros. revert H.
induction x1 using StepF_ind.
 induction x2 using StepF_ind.
  simpl. intro. apply f. assumption.
 simpl. intro.
 assert (t:(glue o (constStepF x) (constStepF x)) ==  glue o x2_1 x2_2).
 rewrite <-H. apply glue_StepF_eq; auto with *.
 clear H.
 pose (IHx2_2 (glue_injr _ _ _ _  _ t)). pose (IHx2_1 (glue_injl _ _ _ _  _ t)).
 set (SF:=(@StepFfold X Y f (fun o y=>g o y))).
How to continue??*)


Definition StFJoin0 (X:Setoid):(StepFS (StepFS X)) -> (StepFS X).
intros X m.
apply (@StepFfold (StepFS X)).
exact (@id (StepFS X)).
exact (@glue X).
exact m.
Defined.


Axiom StFJoin_wd: forall X:Setoid, forall m m1:(StepFS (StepFS X)), m==m1 -> 
  (StFJoin0 m)==(StFJoin0 m1).


Definition StFJoin (X:Setoid):(StepFS (StepFS X)) --> (StepFS X).
intros X.
exists (@StFJoin0 X).
intros. apply (StFJoin_wd x1 x2). assumption.
Defined.

Definition StFBind (X Y:Setoid)(m:StepFS X)(f:X-->StepFS Y):(StepFS Y):=
StFJoin0 (f^@>m).

(** Monad laws *)
Variable X Y:Setoid.

Lemma ReturnBind(x:X)(f:X-->StepFS Y): (StFBind (StFReturn X x) f)== (f x).
simpl; auto with *.
Qed.

Definition Bind_compose(Z:Setoid)(f:X-->StepFS Y)(g:Y-->StepFS Z):X-->StepFS Z.
intros.
exists (fun x => (StFBind (f x) g)).
abstract (intros; simpl; unfold StFBind;
apply (StFJoin_wd );
apply Map_resp_StepF_eq;[
intros; apply g; assumption|
apply f; assumption]).
Defined.

Lemma BindBind(Z:Setoid)(f:X-->StepFS Y)(g:Y-->StepFS Z)(m:StepF X): 
(StFBind (StFBind m f) g) == (StFBind m (Bind_compose f g)).
intros.
unfold Bind_compose.
unfold StFBind.
unfold StFJoin0.
induction m. simpl; auto with *.
simpl.
rewrite IHm1. rewrite IHm2.
auto with *.
Qed.

Lemma BindReturn(m:StepF X): (StFBind m (StFReturn X)) == m.
intro m.
unfold StFBind.
induction m. simpl; auto with *.
simpl.
change (StFJoin0 (StFReturn X ^@> glue o m1 m2) ==
glue o m1 m2).
rewrite MapGlue.
unfold StFJoin0.
simpl.
apply glue_resp_StepF_eq.
apply IHm1. apply IHm2.
Qed.