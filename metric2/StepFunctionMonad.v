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

(* Problem: what is the right encoding*)
Definition StFJoin0 (X:Setoid):(StepFS (StepFS X)) -> (StepFS X).
intros X m.
apply (@StepFfold (StepFS X)).
exact (@id (StepFS X)).
exact (fun o l r => @glue X o (SplitL l o) (SplitR r o)).
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
(* Map should have type --> *)

(* 
Definition Map' (X Y : Setoid):
       (X --> Y) -> StepFS X --> StepFS Y.
intros X Y f.
pose (Map (compose (@StFReturn Y) f  )).
assert (mapcompose:(StepFS X)--> (StepFS (StepFS Y))).
exists s.
intros.
unfold s.
Problem: Map has the wrong type *)

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

(*
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
*)

Definition SSplitL(S:StepFS X):(StepFS (StepFS X)).
intro f.
apply (@StepFfold X (StepFS (StepFS X))).
3:exact f. clear f.
intro x.
exact (StFReturn (StepFS X) (StFReturn X x)).
intros o g h.
exact (Map (fun x=> SplitL x o) g).
Defined.

Definition SSplitR(S:StepFS X):(StepFS (StepFS X)).
intro f.
apply (@StepFfold X (StepFS (StepFS X))).
3:exact f. clear f.
intro x.
exact (StFReturn (StepFS X) (StFReturn X x)).
intros o g h.
exact (Map (fun x=> SplitR x o) h).
Defined.

Definition Diag(S:StepFS (StepFS X)):(StepFS (StepFS X)).
fix 1.
intro m.
case m.
exact (StFReturn (StepFS X)).
intros o f g.
pose (Map (fun x=> SplitL x o) f).
pose (Map (fun x=> SplitR x o) g).
apply (Map2 (glue o) s s0).
Defined.

Print Diag.

Lemma JoinDiag:forall m, (StFJoin X m)==(StFJoin X (Diag m)).
intros.
induction m.
reflexivity.
pose (s := Map (fun x : StepF X => SplitL x o) m1).
pose (s0 := Map (fun x : StepF X => SplitR x o) m2). 
change ((@glue X o (SplitL (StFJoin X m1) o) (SplitR (StFJoin X m2) o))
== StFJoin X (Diag (StepFunction.glue o m1 m2))).
change (glue o (SplitL (StFJoin X m1) o) (SplitR (StFJoin X m2) o) 
== StFJoin X (Map2 (glue o) s s0)).
simpl.
rewrite IHm1. rewrite IHm2.
clear IHm1 IHm2.





StFJoin0
  (Map2 (glue o) (Map (fun x : StepF X => SplitL x o) m1)
     (Map (fun x : StepF X => SplitR x o) m2))).


unfold StFJoin0.
simpl.






Lemma BindReturn(m:StepF X): (StFBind m (StFReturn X)) == m.
intro m.
unfold StFBind.
assert ((StFReturn X ^@> m) == (SSplitL m)).
induction m using StepF_ind.
unfold SSplitL. simpl. auto with *.
rewrite MapGlue.
unfold SSplitL. simpl.
rewrite IHm1. rewrite IHm2.



induction m using StepF_ind. simpl;auto with *.

rewrite MapGlue.
assert ((StFReturn X ^@> m) == 
unfold StFJoin0.
simpl.
apply glue_resp_StepF_eq. 
 clear IHm2 m2. rewrite  IHm1.
(* SplitL m1 o == m1 ??*)
rewrite GlueSplit.
apply IHm1. apply IHm2.
Qed.