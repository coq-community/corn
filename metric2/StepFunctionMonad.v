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
apply StepF_Sth.
Defined.

Open Scope setoid_scope.
Open Local Scope sfstscope.

Definition StFReturn (X:Setoid) : X-->(StepFS X).
intros.
exists (@constStepF X).
abstract (auto with *).
Defined.

Definition SplitLS0(X:Setoid):OpenUnit->(StepFS X)->(StepFS X):=
(fun o x => SplitL x o).

Definition SplitLS(X:Setoid):OpenUnit->(StepFS X)-->(StepFS X).
intros X o.
exists (fun x => (SplitLS0 o x)).
abstract (intros; rapply SplitL_wd;auto with *).
Defined.

Definition SplitRS0(X:Setoid):OpenUnit->(StepFS X)->(StepFS X):=
(fun o x => SplitR x o).

Definition SplitRS(X:Setoid):OpenUnit->(StepFS X)-->(StepFS X).
intros X o.
exists (fun x => (SplitRS0 o x)).
abstract (intros; rapply SplitR_wd;auto with *).
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

Lemma StFBind_wd1(X Y:Setoid):forall m, forall x1 x2 : X --> StepFS Y,
st_eq (X --> StepFS Y) x1 x2 ->
st_eq (StepFS Y) (StFBind00 m x1) (StFBind00 m x2).
induction m.
 intros x1 x2 H.
 simpl; auto with *. apply H.
intros x1 x2 H. simpl. apply glue_resp_StepF_eq.
 apply IHm1. intro. simpl. unfold compose0. 
 apply SplitL_wd; auto with *. apply H.
apply IHm2. intro. simpl. unfold compose0. 
apply SplitR_wd; auto with *. apply H.
Qed.

Definition StFBind1(X Y:Setoid) : 
  (StepFS X) -> (X --> (StepFS Y)) --> (StepFS Y).
intros X Y m.
exists (fun f=> (@StFBind00 X Y m f)).
apply StFBind_wd1.
Defined.


Definition MirrorS(X:Setoid):(StepFS X)-->(StepFS X).
intro X.
exists (@Mirror X).
abstract (intros; change (Mirror x1 == Mirror x2); rewrite Mirror_eq_Mirror; assumption).
Defined.

Lemma MirrorBind(X Y:Setoid):forall (x:StepF X) (f:X --> (StepFS Y)), 
Mirror (StFBind00 x f)==(StFBind00 (Mirror x) (compose (MirrorS Y) f)).
induction x using StepF_ind.
 reflexivity.
intros. simpl. rewrite MirrorGlue. apply glue_wd; auto with *.
 rewrite IHx2. simpl. change 
 (StFBind00 (Mirror x2) (compose1 (MirrorS Y) (compose1 (SplitRS Y o) f)) ==
 StFBind00 (Mirror x2) (compose1 (SplitLS Y (OpenUnitDual o)) (compose1 (MirrorS Y) f))).
 apply StFBind_wd1. intro. simpl. unfold compose0. unfold SplitRS0, SplitLS0.
 apply MirrorSplitR; auto with *.
rewrite IHx1. simpl. change (StFBind00 (Mirror x1) (compose1 (MirrorS Y) (compose1 (SplitLS Y o) f)) ==
StFBind00 (Mirror x1) (compose1 (SplitRS Y (OpenUnitDual o)) (compose1 (MirrorS Y) f))).
apply StFBind_wd1. intro. simpl. unfold compose0. unfold SplitRS0, SplitLS0.
apply MirrorSplitL; auto with *.
Qed.

Lemma SplitLBind (X Y:Setoid) : forall (y:(StepF X)) (o:OpenUnit) (f: (X-->(StepFS Y))),
 SplitL (StFBind00 y f) o == StFBind00 (SplitL y o) (compose1 (SplitLS Y o) f).
induction y using StepF_ind. reflexivity.
intros p f. simpl.  apply SplitL_glue_ind; apply SplitL_glue_ind; intros H H0;
  try solve [ elim (Qlt_not_le o p); auto with *
            | elim (Qlt_not_le _ _  H0) || elim (Qlt_not_le _ _  H); rewrite H || rewrite H0; auto with *].
  setoid_replace (OpenUnitDiv p o H0) with (OpenUnitDiv p o H) by (unfold ou_eq; reflexivity).
  rewrite IHy1.
  apply StFBind_wd1.
  intros x. simpl. unfold compose0. apply StepF_Qeq_eq.
  rapply (SplitLSplitL (f x) o (OpenUnitDiv p o H) p). simpl. field. auto with *.
 (* o<p*)
 simpl. apply glue_wd.
   unfold ou_eq; reflexivity.
  apply StFBind_wd1.
  intro x. simpl. unfold compose0, SplitLS0. symmetry. apply StepF_Qeq_eq. rapply (SplitLSplitL (f x)).
  simpl. field. auto with *.
 setoid_replace (OpenUnitDualDiv _ _ H0) with (OpenUnitDualDiv _ _ H) by (unfold ou_eq; reflexivity).
 rewrite IHy2.
 apply StFBind_wd1. intro. simpl. unfold compose0, SplitLS0, SplitRS0.
 apply StepF_Qeq_eq. rapply ((SplitLSplitR (f x) o) (OpenUnitDualDiv p o H));
  simpl; field; auto with *.
(* p==o *)
apply StFBind_wd1. intro. simpl. unfold compose0, SplitLS0, SplitRS0.
apply SplitL_wd;auto with *.
Qed.

Lemma SplitRBind (X Y:Setoid) : forall (y:(StepF X)) (o:OpenUnit) (f: (X-->(StepFS Y))),
 SplitR (StFBind00 y f) o == StFBind00 (SplitR y o) (compose1 (SplitRS Y o) f).
Proof.
induction y using StepF_ind. reflexivity.
intros p f. simpl.  apply SplitR_glue_ind; apply SplitR_glue_ind; intros H H0;
  try solve [ elim (Qlt_not_le o p); auto with *
            | elim (Qlt_not_le _ _  H0) || elim (Qlt_not_le _ _  H); rewrite H || rewrite H0; auto with *].
  simpl. apply glue_wd.
    unfold ou_eq; reflexivity.
   setoid_replace (OpenUnitDiv _ _ H0) with (OpenUnitDiv _ _ H) by (unfold ou_eq; reflexivity).
   rewrite IHy1.
   apply StFBind_wd1. intro. simpl. unfold compose0, SplitLS0, SplitRS0.
   symmetry. apply StepF_Qeq_eq. rapply ((SplitLSplitR (f x) p) (OpenUnitDualDiv _ _ H));
    simpl; field; auto with *.
  apply StFBind_wd1.
  intro x. simpl. unfold compose0, SplitLS0. symmetry. apply StepF_Qeq_eq. rapply (SplitRSplitR (f x)).
  simpl. field. auto with *.
 (* o<p*)
 setoid_replace (OpenUnitDualDiv p o H0) with (OpenUnitDualDiv p o H) by (unfold ou_eq; reflexivity).
 rewrite IHy2.
 apply StFBind_wd1.
 intros x. simpl. unfold compose0. apply StepF_Qeq_eq.
 rapply (SplitRSplitR (f x) o (OpenUnitDualDiv _ _ H) p). simpl. field. auto with *.
(* p==o *)
apply StFBind_wd1. intro. simpl. unfold compose0, SplitLS0, SplitRS0.
apply SplitR_wd;auto with *.
Qed.

Lemma StFBind_wd(X Y:Setoid): forall x1 x2 : StepFS X,
st_eq (StepFS X) x1 x2 ->
st_eq ((X --> StepFS Y) --> StepFS Y) (StFBind1 Y x1) (StFBind1 Y x2).
intros X Y.
induction x1 using StepF_ind. intro y. 
 induction y using StepF_ind. simpl. intro H.
  intro f. apply f. auto with *. 
 simpl. intro H. destruct H as [Hl Hr] using (eq_glue_ind y1).
 intro f.
 rewrite <- (IHy1 Hl (compose1 (SplitLS Y o) f)). simpl. unfold compose0. clear IHy1. 
 rewrite <- (IHy2 Hr (compose1 (SplitRS Y o) f)). simpl. unfold compose0. 
 unfold SplitLS0, SplitRS0. symmetry. apply glueSplit.
intros y H f.
simpl in H.
destruct H as [Hl Hr] using (glue_eq_ind x1_1).
simpl.
rewrite (IHx1_1 _ Hl (compose1 (SplitLS Y o) f)).
rewrite (IHx1_2 _ Hr (compose1 (SplitRS Y o) f)).
clear IHx1_1 IHx1_2. 
change ((StFBind1 _ (glue o (SplitL y o) (SplitR y o)) f)  == StFBind00 y f).
clear Hl Hr x1_1 x1_2.
simpl.
rewrite <- (glueSplit (StFBind00 y f) o).
rewrite SplitLBind.
rewrite SplitRBind.
reflexivity.
Qed.

Definition StFBind(X Y:Setoid) : 
  (StepFS X) --> (X --> (StepFS Y)) --> (StepFS Y).
intros X Y.
exists (fun m => (@StFBind1 X Y m)).
exact (@StFBind_wd X Y).
Defined.

Definition StFJoin (X:Setoid):(StepFS (StepFS X))-->(StepFS X):=
 (flip (@StFBind (StepFS X) X) (@id (StepFS X))).

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
 clear IHm1.
 apply StFBind_wd1.
 intro. simpl. unfold compose0.
 symmetry. rapply SplitLBind.
clear IHm1 m1. simpl in IHm2.
rewrite (IHm2 (compose1 (SplitRS Y o) f) (compose1 (SplitRS Z o) g)).
clear IHm2.
apply StFBind_wd1.
intro. simpl. unfold compose0.
symmetry. rapply SplitRBind.
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
Check Ap. 

(* (\f x -> f >>= (\g -> x >>= \a -> return (g a)))
f: S (X -->Y)
x: S X
a: X
g: X--> Y
\a -> return (g a) :X --> S Y   = (compose return g)
x >>= \a -> return (g a) : SY   
x >>= : (X --> S Y) --> SY     = (bind x)
\g -> ,...    : (X-->Y) -> SY

(compose return g)

*)



Lemma ApBind(X Y:Setoid): forall (f:StepFS (X-->Y)) (x:(StepFS X)), True.
intros. 
Check (@compose1 (X0 --> (StepFS Y0)) _ _ (@StFBind X0 Y0 x) (@StFReturn Y0)).
Check (@StFBind00 _ _ f (compose (StFBind _ _ x) (StFReturn _))).
(f<@>x== (@StFBind00 _ _ f (compose (StFBind _ _ x) (StFReturn _)))).