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
Require Import CoRN.algebra.RSetoid.
Require Export CoRN.metric2.StepFunctionSetoid.
Require Import CoRN.model.structures.OpenUnit.
Require Import CoRN.tactics.CornTac.
Require Import CoRN.logic.CornBasics.

(** ** Monad
Here we define bind and join for the step function monad, and prove that they
satify the monad laws.
*)

Set Implicit Arguments.

(** This version of [StepF] has type [Setoid] that carries its equivalence
relation with it. *)
Definition StepFS (X : RSetoid) : RSetoid.
Proof.
 exists (StepF X) (@StepF_eq X).
 apply StepF_Sth.
Defined.

Local Open Scope setoid_scope.
Local Open Scope sfstscope.

(** We redefine several functions to return a setoid type. *)

Definition StFReturn (X : RSetoid) : X-->(StepFS X).
Proof.
 intros.
 exists (@constStepF X).
 abstract (auto with *).
Defined.

Definition SplitLS0(X : RSetoid):OpenUnit->(StepFS X)->(StepFS X):=
(fun o x => SplitL x o).

Definition SplitLS(X : RSetoid):OpenUnit->(StepFS X)-->(StepFS X).
Proof.
 intros o.
 exists (fun x => (SplitLS0 o x)). 
 abstract (intros; apply: SplitL_wd;auto with *).
Defined.

Definition SplitRS0(X : RSetoid):OpenUnit->(StepFS X)->(StepFS X):=
(fun o x => SplitR x o).

Definition SplitRS(X : RSetoid):OpenUnit->(StepFS X)-->(StepFS X).
Proof.
 intros o.
 exists (fun x => (SplitRS0 o x)).
 abstract (intros; apply: SplitR_wd;auto with *).
Defined.

Definition MirrorS(X : RSetoid):(StepFS X)-->(StepFS X).
Proof.
 exists (@Mirror X).
 abstract (intros; change (Mirror x1 == Mirror x2); rewrite -> Mirror_eq_Mirror; assumption).
Defined.

(** Definition of bind. *)

Definition StFBind00(X Y : RSetoid) :
  (StepFS X) -> (X --> (StepFS Y)) -> (StepFS Y).
Proof.
 fix StFBind00 1. intro m. case m.
 intros x f.
  exact (f x).
 intros o m1 m2 f.
 exact (glue o (StFBind00 m1 (compose (SplitLS Y o) f)) (StFBind00 m2 (compose (SplitRS Y o) f))).
Defined.

Lemma StFBind_wd1(X Y : RSetoid):forall m, forall x1 x2 : X --> StepFS Y,
st_eq x1 x2 ->
st_eq (StFBind00 m x1) (StFBind00 m x2).
Proof.
 induction m.
  intros x1 x2 H.
  simpl; auto with *. apply H.
  intros x1 x2 H. simpl. apply glue_resp_StepF_eq.
 apply IHm1. intro. simpl. unfold compose0.
  apply SplitL_wd; auto with *. apply H.
  apply IHm2. intro. simpl. unfold compose0.
 apply SplitR_wd; auto with *. apply H.
Qed.

Definition StFBind1(X Y : RSetoid) :
  (StepFS X) -> (X --> (StepFS Y)) --> (StepFS Y).
Proof.
 intros m.
 exists (fun f=> (@StFBind00 X Y m f)).
 apply StFBind_wd1.
Defined.

Lemma MirrorBind(X Y : RSetoid):forall (x:StepF X) (f:X --> (StepFS Y)),
Mirror (StFBind00 x f)==(StFBind00 (Mirror x) (compose (MirrorS Y) f)).
Proof.
 induction x using StepF_ind.
  reflexivity.
 intros. simpl. rewrite MirrorGlue. apply glue_wd; auto with *.
  rewrite -> IHx2. simpl. change
    (StFBind00 (Mirror x2) (compose1 (MirrorS Y) (compose1 (SplitRS Y o) f)) ==
      StFBind00 (Mirror x2) (compose1 (SplitLS Y (OpenUnitDual o)) (compose1 (MirrorS Y) f))).
  apply StFBind_wd1. intro. simpl. unfold compose0. unfold SplitRS0, SplitLS0.
  apply MirrorSplitR; auto with *.
 rewrite -> IHx1. simpl. change (StFBind00 (Mirror x1) (compose1 (MirrorS Y) (compose1 (SplitLS Y o) f)) ==
   StFBind00 (Mirror x1) (compose1 (SplitRS Y (OpenUnitDual o)) (compose1 (MirrorS Y) f))).
 apply StFBind_wd1. intro. simpl. unfold compose0. unfold SplitRS0, SplitLS0.
 apply MirrorSplitL; auto with *.
Qed.

Lemma SplitLBind (X Y : RSetoid) : forall (y:(StepF X)) (o:OpenUnit) (f: (X-->(StepFS Y))),
 SplitL (StFBind00 y f) o == StFBind00 (SplitL y o) (compose1 (SplitLS Y o) f).
Proof.
 induction y using StepF_ind. reflexivity.
 intros p f. simpl.  apply SplitL_glue_ind; apply SplitL_glue_ind; intros H H0;
   try solve [ elim (Qlt_not_le o p); auto with *
     | elim (Qlt_not_le _ _  H0) || elim (Qlt_not_le _ _  H); rewrite -> H || rewrite -> H0; auto with *].
   setoid_replace (OpenUnitDiv p o H0) with (OpenUnitDiv p o H) by (unfold ou_eq; reflexivity).
   rewrite -> IHy1.
   apply StFBind_wd1.
   intros x. simpl. unfold compose0. apply StepF_Qeq_eq.
   apply (SplitLSplitL (f x) o (OpenUnitDiv p o H) p). simpl. simpl. field. auto with *.
   (* o<p*)
   simpl. apply glue_wd.
  unfold ou_eq; reflexivity.
   apply StFBind_wd1.
   intro x. simpl. unfold compose0, SplitLS0. symmetry. apply StepF_Qeq_eq. apply (SplitLSplitL (f x)).
   simpl. field. auto with *.
   setoid_replace (OpenUnitDualDiv _ _ H0) with (OpenUnitDualDiv _ _ H) by (unfold ou_eq; reflexivity).
  rewrite -> IHy2.
  apply StFBind_wd1. intro. simpl. unfold compose0, SplitLS0, SplitRS0.
  apply StepF_Qeq_eq. apply ((SplitLSplitR (f x) o) (OpenUnitDualDiv p o H));
    simpl; field; auto with *.
 (* p==o *)
 apply StFBind_wd1. intro. simpl. unfold compose0, SplitLS0, SplitRS0.
 apply SplitL_wd. auto with *.
  symmetry; auto with *.
Qed.

Lemma SplitRBind (X Y : RSetoid) : forall (y:(StepF X)) (o:OpenUnit) (f: (X-->(StepFS Y))),
 SplitR (StFBind00 y f) o == StFBind00 (SplitR y o) (compose1 (SplitRS Y o) f).
Proof.
 induction y using StepF_ind. reflexivity.
 intros p f. simpl.  apply SplitR_glue_ind; apply SplitR_glue_ind; intros H H0;
   try solve [ elim (Qlt_not_le o p); auto with *
     | elim (Qlt_not_le _ _  H0) || elim (Qlt_not_le _ _  H); rewrite -> H || rewrite -> H0; auto with *].
   simpl. apply glue_wd.
   unfold ou_eq; reflexivity.
    setoid_replace (OpenUnitDiv _ _ H0) with (OpenUnitDiv _ _ H) by (unfold ou_eq; reflexivity).
    rewrite -> IHy1.
    apply StFBind_wd1. intro. simpl. unfold compose0, SplitLS0, SplitRS0.
    symmetry. apply StepF_Qeq_eq. apply ((SplitLSplitR (f x) p) (OpenUnitDualDiv _ _ H));
      simpl; field; auto with *.
   apply StFBind_wd1.
   intro x. simpl. unfold compose0, SplitLS0. symmetry. apply: StepF_Qeq_eq. apply (SplitRSplitR (f x)).
   simpl. field. auto with *.
   (* o<p*)
   setoid_replace (OpenUnitDualDiv p o H0) with (OpenUnitDualDiv p o H) by (unfold ou_eq; reflexivity).
  rewrite -> IHy2.
  apply StFBind_wd1.
  intros x. simpl. unfold compose0. apply StepF_Qeq_eq.
  apply (SplitRSplitR (f x) o (OpenUnitDualDiv _ _ H) p). simpl. field. auto with *.
  (* p==o *)
  apply StFBind_wd1. intro. simpl. unfold compose0, SplitLS0, SplitRS0.
 apply SplitR_wd;auto with *.
 symmetry. auto with *.
Qed.

Lemma StFBind_wd(X Y : RSetoid): forall x1 x2 : StepFS X,
st_eq  x1 x2 ->
st_eq (StFBind1 Y x1) (StFBind1 Y x2).
Proof.
 induction x1 using StepF_ind. intro y.
  induction y using StepF_ind. simpl. intro H.
   intro f. apply f. auto with *.
   simpl. intro H. destruct H as [Hl Hr] using (eq_glue_ind y1).
  intro f.
  rewrite <- (IHy1 Hl (compose1 (SplitLS Y o) f)). simpl. unfold compose0. clear IHy1.
  rewrite <- (IHy2 Hr (compose1 (SplitRS Y o) f)). simpl. unfold compose0.
  unfold SplitLS0, SplitRS0. symmetry. apply: glueSplit.
  intros y H f.
 simpl in H.
 destruct H as [Hl Hr] using (glue_eq_ind x1_1).
 simpl.
 rewrite ->  (IHx1_1 _ Hl (compose1 (SplitLS Y o) f)).
 rewrite ->  (IHx1_2 _ Hr (compose1 (SplitRS Y o) f)).
 clear IHx1_1 IHx1_2.
 change ((StFBind1 _ (glue o (SplitL y o) (SplitR y o)) f)  == StFBind00 y f).
 clear Hl Hr x1_1 x1_2.
 simpl.
 rewrite <- (glueSplit (StFBind00 y f) o).
 rewrite -> SplitLBind.
 rewrite -> SplitRBind.
 reflexivity.
Qed.

Definition StFBind(X Y : RSetoid) :
  (StepFS X) --> (X --> (StepFS Y)) --> (StepFS Y).
Proof.
 exists (fun m => (@StFBind1 X Y m)).
 exact (@StFBind_wd X Y).
Defined.

Add Parametric Morphism X Y : (@StFBind00 X Y) with signature (@StepF_eq X ==> (@st_eq _) ==> @StepF_eq Y) as StFBind00_wd.
Proof.
 intros x y Hxy f g Hfg.
 transitivity (StFBind00 x g).
  apply StFBind_wd1; assumption.
 apply: StFBind_wd; assumption.
Qed.

(** Join is defined in terms of bind. *)

Definition StFJoin (X : RSetoid):(StepFS (StepFS X))-->(StepFS X):=
 (flip (@StFBind (StepFS X) X) (@id (StepFS X))).

Lemma JoinGlue(X : RSetoid): forall o a b,
(StFJoin X (glue o a b))==(glue o (StFBind (StepFS X) _ a (SplitLS X o)) (StFBind (StepFS X) _ b (SplitRS X o))).
Proof.
 intros. simpl.
 transitivity (glue o (StFBind00 (SplitL (glue o a b) o) (compose1 (SplitLS X o) id))
   (StFBind00 (SplitR (glue o a b) o) (compose1 (SplitRS X o) id))).
  apply glue_wd; auto with *. apply StFBind00_wd; try reflexivity. rewrite SplitLGlue. reflexivity.
   apply StFBind00_wd; try reflexivity. rewrite SplitRGlue. reflexivity.
  apply glue_wd; auto with *.
  rewrite <- SplitLBind. simpl. rewrite SplitLGlue. apply StFBind_wd1. intro x. reflexivity.
  rewrite <- SplitRBind. simpl. rewrite SplitRGlue. apply StFBind_wd1. intro x. reflexivity.
Qed.

Section Monad_Laws.
(** Here we prove the monad laws. *)
Variable X Y : RSetoid.

Lemma ReturnBind(x:X)(f:X-->StepFS Y): (StFBind X Y (StFReturn X x) f)==(f x).
Proof.
 simpl; auto with *.
Qed.

Let Bind_compose(Z : RSetoid)(f:X-->StepFS Y)(g:Y-->StepFS Z):=
(compose ((flip (StFBind Y Z)) g) f).

Lemma BindBind(Z : RSetoid)(m:StepF X)(f:X-->StepFS Y)(g:Y-->StepFS Z):
(StFBind Y Z (StFBind X Y m f) g) == (StFBind X Z m (Bind_compose f g)).
Proof.
 revert f g.
 induction m. simpl. unfold compose0. simpl; auto with *.
  simpl.
 intros. apply glue_resp_StepF_eq.
 clear IHm2 m2. simpl in IHm1.
  rewrite -> (IHm1 (compose1 (SplitLS Y o) f) (compose1 (SplitLS Z o) g)).
  clear IHm1.
  apply StFBind_wd1.
  intro. simpl. unfold compose0.
  symmetry. apply: SplitLBind.
  clear IHm1 m1. simpl in IHm2.
 rewrite -> (IHm2 (compose1 (SplitRS Y o) f) (compose1 (SplitRS Z o) g)).
 clear IHm2.
 apply StFBind_wd1.
 intro. simpl. unfold compose0.
 symmetry. apply: SplitRBind.
Qed.

Lemma BindReturn(m:StepF X): (StFBind X X m (StFReturn X)) == m.
Proof.
 unfold StFBind.
 induction m using StepF_ind.
  simpl. auto with *.
  simpl.
 unfold StFBind00.
 simpl. apply glue_resp_StepF_eq.
 clear IHm2 m2. simpl in IHm1.
  assert (extEq (StepFS X) (StFReturn X) (compose1 (SplitLS X o) (StFReturn X))).
   intro. simpl. auto with *.
   pose (s:=Morphism_prf (StFBind1 X m1) (StFReturn X) (compose1 (SplitLS X o) (StFReturn X)) H).
  rewrite -> s in IHm1. clear s H.
  assumption.
 clear IHm1 m1. simpl in IHm2.
 assert (extEq (StepFS X) (StFReturn X) (compose1 (SplitRS X o) (StFReturn X))).
  intro; simpl; auto with *.
 pose (s:=Morphism_prf (StFBind1 X m2) (StFReturn X) (compose1 (SplitRS X o) (StFReturn X)) H).
 rewrite ->  s in IHm2. clear s H.
 assumption.
Qed.

End Monad_Laws.

(* (\f x -> f >>= (\g -> x >>= \a -> return (g a)))
f: S (X -->Y)
x: S X
a: X
g: X--> Y
\a -> return (g a) :X --> S Y   = (compose return g)
x >>= \a -> return (g a) : SY
x >>= : (X --> S Y) --> SY     = (bind x)
\g -> ,...    : (X-->Y) -> SY

(StFBinf x (compose return g)) :SY

(compose return) : (X-->Y)-->(X-->SY)
(compose (StFBinf x) (compose return)) :(X-->Y)-->SY

*)

(** Lastly, we prove that the applicative functor is the canonical one
 for this monad. *)

Lemma ApBind(X Y : RSetoid): forall (x:(StepFS X)) (f:StepFS (X-->Y)) ,
(f<@>x==
(@StFBind _ _ f (compose (StFBind _ _ x)
(compose (StFReturn _))))).
Proof.
 apply: StepF_ind2.
   intros s s0 t t0 Hs Ht H.
   rewrite <- Hs, <- Ht at 1.
   rewrite -> H.
   unfold StFBind.
   simpl.
   transitivity (StFBind00 t0 (compose1 (StFBind1 Y s) (compose2 X (StFReturn Y)))).
    apply: StFBind_wd; auto.
   apply StFBind_wd1.
   intros a.
   apply: StFBind_wd; auto.
  reflexivity.
 intros o s s0 t t0 IHf1 IHf2.
 rewrite ApGlueGlue.
 rewrite -> IHf1, IHf2.
 simpl. apply glue_wd; try reflexivity; apply StFBind_wd1; intro x;
   unfold StFBind1, compose1, compose0; simpl.
  unfold SplitLS0. rewrite SplitLGlue.
  apply StFBind_wd1.
  intro y. reflexivity.
  unfold SplitRS0. rewrite SplitRGlue.
 apply StFBind_wd1.
 intro y. reflexivity.
Qed.
