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

(* Use:    destruct H as [Hl Hr] using (glue_eq_ind x2_1). *)
Lemma ConstGlue(X:Setoid):forall m n x o, ((constStepF x)==(@glue X o m n)) ->
((constStepF x)==m)/\((constStepF x)==n).
intros. split.  
 pose (s:=SplitL_resp_Xeq _ _ o H). rewrite SplitLGlue in s. auto with *.
 pose (s:=SplitR_resp_Xeq _ _ o H). rewrite SplitRGlue in s. auto with *.
Qed.

(*
Lemma Ext(X Y:Setoid):forall f:(StepFS X)->Y, 
 (forall x y:X, (st_eq X x y)-> (st_eq _ (f (constStepF x)) (f (constStepF y))))->
(*  (forall m n o, (st_eq _ (f (glue o m n))
                 (glue o (f m)) (f n))) -> *)
 (forall m o, (st_eq _ (f (glue o (SplitL m o) (SplitR m o) )) (f m)))
 -> (forall m n, m==n -> (st_eq _ (f m)(f n))).
Admitted.*)
(*
intros X Y f H H0 H1.
induction m using StepF_ind.
 induction n using StepF_ind. intro. assert (st_eq _ x x0); auto with *.
 intro H2. destruct (ConstGlue H2) as [left right].
 rewrite H1. 
 pose (L:=(IHn1 left)). pose (R:=(IHn2 right)).
 rewrite <- L. rewrite <- R. apply H0.
intros n H2. clear H H0.
rewrite H1. 
assert (H3:(SplitL (glue o m1 m2) o) == (SplitL n o)). apply (SplitL_wd _ _ H2); auto with *.
  rewrite SplitLGlue in H3.
assert ((SplitR (glue o m1 m2) o) == (SplitR n o)). apply (SplitR_wd _ _ H2); auto with *.
  rewrite SplitRGlue in H4.
 pose (L:=(IHm1 _ H3)). pose (R:=(IHm2 _ H4)).
change (f (glue o m1 m2) == f n).
clear H H0.
rewrite  H1.
*)



Definition StFReturn (X:Setoid) : X-->(StepFS X).
intros.
exists (@constStepF X).
auto with *.
Defined.

Definition SplitLS0(X:Setoid):OpenUnit->(StepFS X)->(StepFS X):=
(fun o x => SplitL x o).

Definition SplitLS(X:Setoid):OpenUnit->(StepFS X)-->(StepFS X).
intros X o.
exists (fun x => (SplitLS0 o x)).
intros. rapply SplitL_wd;auto with *.
Defined.

Definition SplitRS0(X:Setoid):OpenUnit->(StepFS X)->(StepFS X):=
(fun o x => SplitR x o).

Definition SplitRS(X:Setoid):OpenUnit->(StepFS X)-->(StepFS X).
intros X o.
exists (fun x => (SplitRS0 o x)).
intros. rapply SplitR_wd;auto with *.
Defined.

Definition StFBind00(X Y:Setoid) : 
  (StepFS X) -> (X --> (StepFS Y)) -> (StepFS Y).
intros X Y .
fix 1. intro m. case m.
intros x f.
exact (f x).
intros o m1 m2 f.
exact (glue o (StFBind00 m1 (compose (SplitLS Y o) f))
                     (StFBind00 m2 (compose (SplitRS Y o) f))).
Defined.

Axiom cheat:False.
Definition StFBind1(X Y:Setoid) : 
  (StepFS X) -> (X --> (StepFS Y)) --> (StepFS Y).
intros X Y m.
exists (fun f=> (@StFBind00 X Y m f)).
induction m.
 intros. simpl; auto with *. apply H.
intros. simpl. apply glue_resp_StepF_eq.
 apply IHm1. intro. simpl. unfold compose0. 
 apply SplitL_wd; auto with *. apply H.
apply IHm2. intro. simpl. unfold compose0. 
apply SplitR_wd; auto with *. apply H.
Defined.

Definition StFBind(X Y:Setoid) : 
  (StepFS X) --> (X --> (StepFS Y)) --> (StepFS Y).
intros X Y.
exists (fun m => (@StFBind1 X Y m)).
induction x1 using StepF_ind. intro y. 
 induction y using StepF_ind. simpl. intro H.
  intro f. apply f. auto with *. 
 simpl. intro H. symmetry in H. destruct H as [Hl Hr] using (glue_eq_ind y1).
 symmetry in Hl. pose (s1:=IHy1 Hl). 
 symmetry in Hr. pose (s2:=IHy2 Hr).
 intro f. 
 rewrite <- (s1 (compose1 (SplitLS Y o) f)). simpl. unfold compose0. clear s1 IHy1. 
 rewrite <- (s2 (compose1 (SplitRS Y o) f)). simpl. unfold compose0. unfold SplitLS0, SplitRS0. symmetry. apply glueSplit.
intro y.
intro H.
pose (s:=SplitL_resp_Xeq _ _ o H). rewrite SplitLGlue in s.
pose (t:=SplitR_resp_Xeq _ _ o H). rewrite SplitRGlue in t.
intro f. simpl.
pose (IHx1_1 _ s (compose1 (SplitLS Y o) f)).
rewrite s0. clear s0.
pose (IHx1_2 _ t (compose1 (SplitRS Y o) f)).
rewrite s0. clear s0 IHx1_1 IHx1_2. 
change ((StFBind1 _ (glue o (SplitL y o) (SplitR y o)) f)  == StFBind00 y f).
clear H s t x1_1 x1_2.
simpl.
(* *)
rewrite <- (glueSplit (StFBind00 y f) o).
apply glue_wd; auto with *. revert f o.
 induction y using StepF_ind. reflexivity.
 intros f p. apply SplitL_glue_ind. intro. simpl.
 assert ((SplitL
  (glue o (StFBind00 y1 (compose1 (SplitLS Y o) f))
     (StFBind00 y2 (compose1 (SplitRS Y o) f))) p)
 ==
(SplitL (StFBind00 y1 (compose1 (SplitLS Y o) f)) p)).
elim cheat.
rewrite H0. clear H0. clear IHy2 y2.
rewrite <- IHy1.
assert (StFBind00 (SplitL y1 (OpenUnitDiv p o H)) (compose1 (SplitLS Y p) f) ==
StFBind00 (SplitL y1 p) ((compose1 (SplitLS Y (OpenUnitDualDiv o p H)) f))).
clear IHy1.


elim (cheat).
elim (cheat).
Defined.

Definition StFJoin0 (X:Setoid):(StepFS (StepFS X))->(StepFS X):=
(fun m => (StFBind1 _ m id)).

(* Check laws for Join return
What about join glue.
*)

Definition StFJoin (X:Setoid):(StepFS (StepFS X))-->(StepFS X).
intros.
exists (@StFJoin0 X).
intros m. induction m using StepF_ind.
intro n.
induction n using StepF_ind.
Focus 3.
intros n H.
assert (st_eq (StepFS X) (StFJoin0 (glue o (SplitL n o) (SplitR n o))) (StFJoin0 n)).
simpl.
unfold StFJoin0.
simpl.
assert  ((glue o (StFBind00 (SplitL n o) (SplitLS X o) )
  (StFBind00 (SplitR n o) (SplitRS X o)) == StFBind00 n id)).








abstract (elim cheat).
Defined.



(*
Lemma StFJoin_wd: forall X:Setoid, forall m m1:(StepFS (StepFS X)), m==m1 -> 
  (StFJoin0 m)==(StFJoin0 m1).

(*
Definition StFJoin (X:Setoid):(StepFS (StepFS X)) --> (StepFS X).
intros X.
exists (@StFJoin0 X).
intros. apply (StFJoin_wd x1 x2). assumption.
Defined.
*)

(*
Definition StFBind (X Y:Setoid)(m:StepFS X)(f:X-->StepFS Y):(StepFS Y):=
StFJoin0 (f^@>m).
(* Map should have type --> *)
*)

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

Lemma ReturnBind(x:X)(f:X-->StepFS Y): (StFBind X Y (StFReturn X x) f)== (f x).
simpl; auto with *.
Qed.

Definition Bind_compose(Z:Setoid)(f:X-->StepFS Y)(g:Y-->StepFS Z):=
(compose ((flip (StFBind Y Z)) g) f).

Lemma BindBind(Z:Setoid)(m:StepF X)(f:X-->StepFS Y)(g:Y-->StepFS Z):
(StFBind Y Z (StFBind X Y m f) g) == (StFBind X Z m (Bind_compose f g)).
intros Z m.
induction m. simpl. unfold compose0. simpl; auto with *.
simpl.
intros. apply glue_resp_StepF_eq.
 clear IHm2 m2. simpl in IHm1.
 rewrite (IHm1 (compose1 (SplitLS Y o) f) (compose1 (SplitLS Z o) g)).
 clear IHm1. assert (extEq (StepFS Z)
 (Bind_compose (compose1 (SplitLS Y o) f) (compose1 (SplitLS Z o) g)) 
(compose1 (SplitLS Z o) (Bind_compose f g))).
  intro. simpl. unfold compose0. pose (glueSplit (f x) o).
  change (StFBind Y Z (SplitLS Y o (f x)) (compose (SplitLS Z o) g) ==
  SplitLS Z o (StFBind Y Z (f x) g)).
  assert (extEq (StepFS Z) (StFBind Y Z (f x))
  (StFBind Y Z (glue o (SplitL (f x) o) (SplitR (f x) o)))).
     symmetry in s. apply (Morphism_prf (StFBind Y Z) _ _ s).
  clear s. 
   (* SplitLS Z o should be a morphism
     so that we can rewrite (H g) *)
  rewrite (Morphism_prf (SplitLS Z o) _ _ (H g)).
  simpl. unfold SplitLS0. rewrite SplitLGlue; auto with *.
 apply (Morphism_prf (StFBind X Z m1) _ _ H).

 clear IHm1 m1. simpl in IHm2.
 rewrite (IHm2 (compose1 (SplitRS Y o) f) (compose1 (SplitRS Z o) g)).
 clear IHm2. assert (extEq (StepFS Z)
 (Bind_compose (compose1 (SplitRS Y o) f) (compose1 (SplitRS Z o) g)) 
(compose1 (SplitRS Z o) (Bind_compose f g))).
  intro. simpl. unfold compose0. pose (s:=glueSplit (f x) o).
  change (StFBind Y Z (SplitRS Y o (f x)) (compose (SplitRS Z o) g) ==
  SplitRS Z o (StFBind Y Z (f x) g)).
  assert (H:extEq (StepFS Z) (StFBind Y Z (f x))
  (StFBind Y Z (glue o (SplitL (f x) o) (SplitR (f x) o)))).
     symmetry in s. apply (Morphism_prf (StFBind Y Z) _ _ s). clear s.
  rewrite (Morphism_prf (SplitRS Z o) _ _ (H g)).
  simpl. unfold SplitRS0. rewrite SplitRGlue; auto with *.
 apply (Morphism_prf (StFBind X Z m2) _ _ H).
Qed.

Lemma BindReturn(m:StepF X): (StFBind X X m (StFReturn X)) == m.
intro m.
unfold StFBind.
induction m using StepF_ind.
 simpl. auto with *.
simpl. 
unfold StFBind00.
simpl. apply glue_resp_StepF_eq.
 clear IHm2 m2. simpl in IHm1. 
 assert (extEq (StepFS X) (StFReturn X) 
 (compose1 (SplitLS X o) (StFReturn X))).
  intro. simpl. auto with *.
 pose (s:=Morphism_prf (StFBind1 X m1) (StFReturn X)
  (compose1 (SplitLS X o) (StFReturn X)) H).
 rewrite s in IHm1. clear s H.
 assumption.

clear IHm1 m1. simpl in IHm2. 
assert (extEq (StepFS X) (StFReturn X) 
(compose1 (SplitRS X o) (StFReturn X))).
intro; simpl; auto with *.
pose (s:=Morphism_prf (StFBind1 X m2) (StFReturn X)
(compose1 (SplitRS X o) (StFReturn X)) H).
rewrite s in IHm2. clear s H.
assumption.
Qed.