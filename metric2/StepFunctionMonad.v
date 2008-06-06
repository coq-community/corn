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
 intros. simpl; auto with *. apply H.
intros. simpl. apply glue_resp_StepF_eq.
 apply IHm1. intro. simpl. unfold compose0. 
 apply SplitL_wd; auto with *. apply H.
apply IHm2. intro. simpl. unfold compose0. 
apply SplitR_wd; auto with *. apply H.
Qed.

Definition StFBind1(X Y:Setoid) : 
  (StepFS X) -> (X --> (StepFS Y)) --> (StepFS Y).
intros X Y m.
exists (fun f=> (@StFBind00 X Y m f)).
abstract (apply StFBind_wd1).
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

Lemma StFBind_wd(X Y:Setoid): forall x1 x2 : StepFS X,
st_eq (StepFS X) x1 x2 ->
st_eq ((X --> StepFS Y) --> StepFS Y) (StFBind1 Y x1) (StFBind1 Y x2).
intros X Y.
assert (Bind_resp_Q:forall x1 x2 : StepFS X,
(StepF_Qeq  x1 x2) ->
st_eq ((X --> StepFS Y) --> StepFS Y) (StFBind1 Y x1) (StFBind1 Y x2)).
induction x1 using StepF_ind; induction x2 using StepF_ind;try contradiction.
 intro. intro. simpl. rewrite H. reflexivity.
 intro H. simpl in H. destruct H as [eq [L R]].
 intro f. simpl. apply glue_wd; try assumption.
clear IHx2_1 IHx2_2.
pose (IHx1_1 _ L).
assert (extEq _ (compose1 (SplitLS Y o) f) (compose1 (SplitLS Y o0) f)). 
intro. simpl. unfold compose0. unfold SplitLS0. 
apply SplitL_wd; auto with *. 
transitivity (StFBind00 x1_1 (compose1 (SplitLS Y o0) f)).
change (StFBind1 _ x1_1 (compose1 (SplitLS Y o) f) ==
StFBind1 _ x1_1 (compose1 (SplitLS Y o0) f)).
rapply (@StFBind_wd1 X Y x1_1). intro. apply H. clear H.
rapply s.
clear IHx2_1 IHx2_2.
pose (IHx1_2 _ R).
assert (extEq _
(compose1 (SplitRS Y o) f)
(compose1 (SplitRS Y o0) f)). intro. simpl. unfold compose0. unfold SplitRS0. 
apply SplitR_wd; auto with *. 
transitivity (StFBind00 x1_2 (compose1 (SplitRS Y o0) f)).
change (StFBind1 _ x1_2 (compose1 (SplitRS Y o) f) ==
StFBind1 _ x1_2 (compose1 (SplitRS Y o0) f)).
rapply (@StFBind_wd1 X Y x1_2). intro. apply H. clear H.
rapply s.
(* Bind_resp_Q*)
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
revert f o y.
assert (BindSplitL: forall (y:(StepF X)) (o:OpenUnit) (f: (X-->(StepFS Y))),
StFBind00 (SplitL y o) (compose1 (SplitLS Y o) f) == SplitL (StFBind00 y f) o).
 induction y using StepF_ind. reflexivity.
 intros p f. simpl.  apply SplitL_glue_ind; apply SplitL_glue_ind. intro. intro.
rewrite <- IHy1.
assert (rew:ou_eq (OpenUnitDiv p o H0) (OpenUnitDiv p o H)). unfold ou_eq; reflexivity.
pose (@Bind_resp_Q (SplitL y1 (OpenUnitDiv p o H0))  (SplitL y1 (OpenUnitDiv p o H))).
unfold StFBind1 in s. assert ((StepF_Qeq (SplitL y1 (OpenUnitDiv p o H0))
      (SplitL y1 (OpenUnitDiv p o H)))). apply SplitL_resp_Qeq; auto with *. reflexivity.
pose (s H1).
simpl in s0. 
transitivity (StFBind00 (SplitL y1 (OpenUnitDiv p o H)) (compose1 (SplitLS Y p) f)).
apply s0.
assert (extEq _ (compose1 (SplitLS Y p) f)  
 (compose1 (SplitLS Y (OpenUnitDiv p o H)) (compose1 (SplitLS Y o) f))).
intro. simpl. unfold compose0. symmetry. apply StepF_Qeq_eq.
rapply (SplitLSplitL (f x) o (OpenUnitDiv p o H) p). simpl. field. auto with *.
apply StFBind_wd1. auto with *.
intros. elim (Qlt_not_le o p); auto with *.
intros. elim (Qlt_not_le p o H0).  rewrite H. auto with *.
intros. elim (Qlt_not_le o p); auto with *.
(* o<p*)
intros. simpl. apply glue_wd. unfold ou_eq; reflexivity. apply StFBind_wd1.
intro. simpl. unfold compose0, SplitLS0. apply StepF_Qeq_eq. rapply (SplitLSplitL (f x)).
simpl. field. auto with *. rewrite <- IHy2.
transitivity (StFBind00 (SplitL y2 (OpenUnitDualDiv p o H))
  (compose1 (SplitRS Y (OpenUnitDiv o p H0)) (compose1 (SplitLS Y p) f))). rapply Bind_resp_Q.
apply SplitL_resp_Qeq; [unfold ou_eq|]; reflexivity. clear IHy1.
apply StFBind_wd1. intro. simpl. unfold compose0, SplitLS0, SplitRS0.
apply StepF_Qeq_eq. symmetry. rapply ((SplitLSplitR (f x) o) (OpenUnitDualDiv p o H)).
simpl. field. auto with *. simpl. field. auto with *.
(* *)
intros. elim (Qlt_not_le o p); auto with *.
intros. elim (Qlt_not_le p o H).  rewrite H0. auto with *.
intros. elim (Qlt_not_le o p); auto with *.
(* p==o *)
intros. apply StFBind_wd1. intro. simpl. unfold compose0, SplitLS0, SplitRS0.
apply SplitL_wd;auto with *.
intros.
apply glue_wd; auto with *.
(*
rewrite <- Mirror_eq_Mirror.
rewrite MirrorBind. rewrite (@MirrorSplitR _ (StFBind00 y f) o (OpenUnitDual o)); auto with *.
rewrite MirrorBind. rewrite <- BindSplitL. simpl.
*)
(*RIGHT*)
revert y f o.
 induction y using StepF_ind. reflexivity. intros f p. 
 simpl.  apply SplitR_glue_ind; apply SplitR_glue_ind. intro. intro.
simpl. apply glue_wd; auto with *. unfold ou_eq; reflexivity. rewrite <- IHy1.
transitivity (StFBind00 (SplitR y1 (OpenUnitDiv p o H))
  (compose1 (SplitLS Y (OpenUnitDualDiv o p H0)) (compose1 (SplitRS Y p) f))).
rapply Bind_resp_Q.
apply SplitR_resp_Qeq; [unfold ou_eq|]; reflexivity. clear IHy1.
apply StFBind_wd1. intro. simpl. unfold compose0, SplitLS0, SplitRS0.
apply StepF_Qeq_eq. rapply ((SplitLSplitR (f x) p) (OpenUnitDualDiv o p H0)).
simpl. field. auto with *. simpl. field. auto with *.
apply StFBind_wd1. intro x. simpl. unfold compose0, SplitLS0, SplitRS0.
apply StepF_Qeq_eq. rapply (SplitRSplitR (f x) p (OpenUnitDualDiv o p H0) o).
simpl. field. auto with *.
intros. elim (Qlt_not_le o p); auto with *.
intros. elim (Qlt_not_le p o H0).  rewrite H. auto with *.
intros. elim (Qlt_not_le o p); auto with *.
(* o<p*)
intros. simpl. rewrite <- IHy2.
transitivity (StFBind00 (SplitR y2 (OpenUnitDualDiv p o H)) (compose1 (SplitRS Y p) f)).
rapply Bind_resp_Q. apply SplitR_resp_Qeq; [unfold ou_eq|]; reflexivity. clear IHy1.
apply StFBind_wd1. intro. simpl. unfold compose0, SplitLS0, SplitRS0.
apply StepF_Qeq_eq. symmetry. rapply ((SplitRSplitR (f x) o (OpenUnitDualDiv p o H) p)).
simpl. field. auto with *. simpl. 
(* *)
intros. elim (Qlt_not_le o p); auto with *.
intros. elim (Qlt_not_le p o H).  rewrite H0. auto with *.
intros. elim (Qlt_not_le o p); auto with *.
(* p==o *)
intros. apply StFBind_wd1. intro. simpl. unfold compose0, SplitLS0, SplitRS0.
apply SplitR_wd;auto with *.
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