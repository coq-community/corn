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
fix 2. intros X m. case m.
exact (fun x=> x). 
intros o m1 m2.
exact (glue o (StFJoin0 X (Map (fun m => (@SplitL X m o)) m1))
                      (StFJoin0 X (Map (fun m => (@SplitR X m o)) m2))).
Defined.


Lemma StFJoin_wd: forall X:Setoid, forall m m1:(StepFS (StepFS X)), m==m1 -> 
  (StFJoin0 m)==(StFJoin0 m1).
intros X m. 
induction m.
intros. unfold StFJoin0. simpl.
induction m1 using StepF_ind.
  assumption.
 revert IHm1_1. revert IHm1_2. unfold StFJoin0. simpl. intros.
 assert (H1:(constStepF (X:=StepFS X) x == m1_1)).
  pose (s:=SplitL_resp_Xeq (constStepF (X:=StepFS X) x) 
   (glue o m1_1 m1_2) o H). rewrite SplitLGlue  in s. rewrite s. auto with *.
 assert (H2:(constStepF (X:=StepFS X) x == m1_2)).
  pose (s1:=SplitR_resp_Xeq (constStepF (X:=StepFS X) x) 
   (glue o m1_1 m1_2) o H). rewrite SplitRGlue  in s1. rewrite s1. auto with *.
 symmetry. apply glue_StepF_eq.
 rewrite (IHm1_1 H1). reflexivity.
 rewrite (IHm1_2 H2). reflexivity.
intros.
 pose (s:=SplitL_resp_Xeq 
   (glue o m1 m2) m0 o H). rewrite SplitLGlue in s.
 unfold StFJoin0. simpl.
 change (glue o
  (SplitL
     (StFJoin0 m1) o)
  (SplitR
     (StFJoin0 m2) o) ==
   (StFJoin0 m0)).
rewrite (IHm1 _ s).
 pose (t:=SplitR_resp_Xeq 
   (glue o m1 m2) m0 o H). rewrite SplitRGlue in t.
rewrite (IHm2 _ t). 
clear s t.
clear H IHm1 IHm2.
clear m1 m2.
revert o.
assert (forall m:StepFS (StepFS X), forall o : OpenUnit,
glue o (SplitL (StFJoin0 (SplitL m o)) o)
  (SplitR (StFJoin0 (SplitR m o)) o) == StFJoin0 m).



induction m0.
unfold StFJoin0. simpl.
apply glueSplit.
clear o.
unfold StFJoin0. simpl.







 m1.
induction m using StepF_ind. induction m1 using StepF_ind.
  intros. assumption.
 intro. revert IHm1_1. revert IHm1_2. unfold StFJoin0. simpl. intros.
 assert (H1:(constStepF (X:=StepFS X) x == m1_1)).
  pose (s:=SplitL_resp_Xeq (constStepF (X:=StepFS X) x) 
   (glue o m1_1 m1_2) o H). rewrite SplitLGlue  in s. rewrite s. auto with *.
 assert (H2:(constStepF (X:=StepFS X) x == m1_2)).
  pose (s1:=SplitR_resp_Xeq (constStepF (X:=StepFS X) x) 
   (glue o m1_1 m1_2) o H). rewrite SplitRGlue  in s1. rewrite s1. auto with *.
 symmetry. apply glue_StepF_eq.
 rewrite (IHm1_1 H1). reflexivity.
 rewrite (IHm1_2 H2). reflexivity.
intro.
unfold StFJoin0.
simpl. change (glue o
  (SplitL
     (StFJoin0 m2) o)
  (SplitR
     (StFJoin0 m3) o) ==
   (StFJoin0 m1)).
Admitted.


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

(*
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
*)





Lemma BindReturn(m:StepF X): (StFBind m (StFReturn X)) == m.
intro m.
unfold StFBind.
induction m using StepF_ind.
unfold SSplitL. simpl. auto with *.
rewrite MapGlue.
unfold SSplitL. simpl.
rewrite IHm1. rewrite IHm2.


map ret (glue o (const x1) (const x2)) is

glue o (const (ret x1)) (const (ret x2))

now if we apply gjoin to it we get.

glue o (const x1) (const x2)

which is what we started with.


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