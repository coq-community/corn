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
Require Import StepFunctionMonad.
Require Import UniformContinuity.
Require Import OpenUnit.
Require Import QArith.
Require Import QMinMax.
Require Import Qabs.
Require Import Qordfield.
Require Import Qmetric.
Require Import Prelength.
Require Import COrdFields2.
Require Import CornTac.

Set Implicit Arguments.

Open Local Scope sfstscope.
Open Local Scope setoid_scope.

(**
** Linf metric for Step Functions
The Linf metric for [StepF X] is obtained by lifting the ball predicate on X *)

Section StepFSupBall.
Set Implicit Arguments.

Variable X:MetricSpace.

(** A setoid verion of the ball predicate *)
Definition ballS0 (m : MetricSpace): Qpos ->  m  -> m --> iffSetoid.
intros m e x.
exists (ball e x).
intros. apply ball_wd;auto with *.
Defined.

Definition ballS (m : MetricSpace): Qpos ->  m --> m --> iffSetoid.
intros m e.
exists (ballS0  m e).
intros. simpl. split; rewrite H; auto with *.
Defined.

(** The definition of the usp metric *)
Definition StepFSupBall(e:Qpos)(f:StepF X)(g:StepF X):=
StepFfoldProp ((@ballS X e)^@> f <@> g).

Lemma StepFSupBallGlueGlue : forall e o fl fr gl gr, 
StepFSupBall e (glue o fl fr) (glue o gl gr) <->
StepFSupBall e fl gl /\ StepFSupBall e fr gr.
Proof.
intros e o fl fr gl gr.
unfold StepFSupBall at 1.
rewrite MapGlue.
rewrite ApGlueGlue.
reflexivity.
Qed.

End StepFSupBall.

Implicit Arguments StepFSupBall [X].

Add Parametric Morphism X : (@StepFSupBall X)
  with signature QposEq ==> (@StepF_eq _) ==> (@StepF_eq _) ==> iff
 as StepFSupBall_wd.
unfold StepFSupBall.
intros a1 a2 Ha x1 x2 Hx y1 y2 Hy.
apply StepFfoldProp_morphism.
rewrite Hx.
rewrite Hy.
setoid_replace (ballS X a1) with (ballS X a2).
reflexivity.
intros x y.
simpl.
rewrite Ha.
reflexivity.
Qed.

Section SupMetric.
(** The StepFSupBall satifies the requirements of a metric. *)
Variable X : MetricSpace.

Lemma StepFSupBall_refl : forall e (x:StepF X), (StepFSupBall e x x).
Proof.
intros e x.
unfold StepFSupBall.
set (b:=(@ballS X e)).
set (f:=(@join _ _) ^@> (constStepF b)).
cut (StepFfoldProp (f <@> x )).
 unfold f.
 evalStepF.
 auto.
rapply StepFfoldPropForall_Map.
simpl.
auto with *.
Qed.

Lemma StepFSupBall_sym : forall e (x y:StepF X), (StepFSupBall e x y) -> (StepFSupBall e y x).
Proof.
intros e x y.
unfold StepFSupBall.
set (b:=(@ballS X e)).
apply StepF_imp_imp.
unfold StepF_imp.
set (f:=ap
 (compose (@ap _ _ _) (compose (compose imp) b))
 (flip (b))).
cut (StepFfoldProp (f ^@> x <@> y)).
 unfold f; evalStepF; tauto.
apply StepFfoldPropForall_Map2.
intros a b0.
simpl. unfold compose0.
auto with *.
Qed.

Lemma StepFSupBall_triangle : forall e d (x y z:StepF X), 
 (StepFSupBall e x y) -> (StepFSupBall d y z) -> (StepFSupBall (e+d) x z).
Proof.
intros e d x y z.
unfold StepFSupBall.
set (be:=(@ballS X e)).
set (bd:=(@ballS X d)).
set (bed:=(@ballS X (e+d) )).
intro H. apply StepF_imp_imp. revert H.
apply StepF_imp_imp.
unfold StepF_imp.
pose (f:= ap
(compose (@ap _ _ _) (compose (compose (compose (@compose _ _ _) imp)) be))
(compose (flip (compose (@ap _ _ _) (compose (compose imp) bd))) bed)).
cut (StepFfoldProp (f ^@> x <@> y <@> z)).
 unfold f.
 evalStepF.
 tauto.
apply StepFfoldPropForall_Map3.
rapply (ball_triangle X e d).
Qed.

Lemma StepFSupBall_closed : forall e (x y:StepF X), (forall d, (StepFSupBall (e+d) x y)) -> (StepFSupBall e x y).
Proof.
intros e.
rapply (StepF_ind2).
  intros. rewrite H, H0 in H1. apply H1.
  intro. rewrite H, H0. apply H2.
 rapply ball_closed.
intros o s s0 t t0 IH0 IH1 H.
unfold StepFSupBall in *.
rewrite MapGlue. rewrite ApGlue. simpl.
split.
 rewrite SplitLGlue. apply IH0. clear IH0.
 intro d. pose (H2:=H d).
  rewrite MapGlue in H2. rewrite ApGlue in H2. rewrite SplitRGlue in H2. rewrite SplitLGlue in H2. 
 destruct H2. auto. 
rewrite SplitRGlue. apply IH1. clear IH1.
intro d. pose (H2:=H d).
rewrite MapGlue in H2. rewrite ApGlue in H2. rewrite SplitRGlue in H2. rewrite SplitLGlue in H2. 
destruct H2. auto.
Qed.

Lemma StepFSupBall_eq : forall (x y : StepF X),
(forall e : Qpos, StepFSupBall e x y) -> StepF_eq x y.
Proof.
rapply (StepF_ind2).
  intros s s0 t t0 H H0 H1 H2. rewrite H, H0 in H1. apply H1.
  intro. rewrite H, H0. apply H2.
 rapply ball_eq.
intros o s s0 t t0 H H0 H1.
unfold StepFSupBall in *. apply glue_resp_StepF_eq.
apply H. clear H.
 intro e. pose (H2:=H1 e). 
 rewrite MapGlue in H2. rewrite ApGlue in H2. rewrite SplitRGlue in H2. rewrite SplitLGlue in H2.
 destruct H2; auto.
apply H0. clear H0.
intro e. pose (H2:=H1 e).
rewrite MapGlue in H2. rewrite ApGlue in H2. rewrite SplitRGlue in H2. rewrite SplitLGlue in H2.
destruct H2; auto.
Qed.
(**
*** Example of a Metric Space <Step, StepFSupBall>
*)
Lemma StepFSupBall_is_MetricSpace : 
 (is_MetricSpace (@StepFS X) (@StepFSupBall X)).
split.
    rapply StepFSupBall_refl.
   rapply StepFSupBall_sym.
  rapply StepFSupBall_triangle.
 rapply StepFSupBall_closed.
rapply StepFSupBall_eq.
Qed.

Definition StepFSup : MetricSpace :=
@Build_MetricSpace (StepFS X) _ (@StepFSupBall_wd X) StepFSupBall_is_MetricSpace.

(** The StepFSup is is a prelength space. *)
Lemma StepFSupPrelengthSpace : PrelengthSpace X -> PrelengthSpace StepFSup.
Proof.
intros pl.
rapply StepF_ind2.
  intros s s0 t t0 Hs Ht H e d1 d2 He H0.
  rewrite <- Hs, <- Ht in H0.
  destruct (H _ _ _ He H0) as [c Hc0 Hc1].
  exists c.
   rewrite <- Hs; auto.
  rewrite <- Ht; auto.
 intros a b e d1 d2 He Hab.
 destruct (pl a b e d1 d2 He Hab) as [c Hc0 Hc1].
 exists (constStepF c); auto.
intros o s s0 t t0 IHl IHr e d1 d2 He H.
simpl in H.
rewrite StepFSupBallGlueGlue in H.
destruct H as [Hl Hr].
destruct (IHl _ _ _ He Hl) as [c Hc0 Hc1].
destruct (IHr _ _ _ He Hr) as [d Hd0 Hd1].
exists (glue o c d);
 simpl;
 rewrite StepFSupBallGlueGlue;
 auto.
Qed.

End SupMetric.

(* begin hide *)
Canonical Structure StepFSup.
(* end hide *)

Lemma StepFSupBallBind(X:MetricSpace): ((forall (e : Qpos) (a b : StepF (StepFS X)) ,
forall f:(StepFS X) -->(StepFS X), 
(forall c d, (StepFSupBall e c d) -> (StepFSupBall e (f c) (f d)))->
StepFSupBall (X:=StepFSup X) e a b ->
StepFSupBall (X:=X) e (StFBind00 a f) (StFBind00 b f))).
intros X e a. unfold ball_ex.
induction a using StepF_ind. simpl. induction b using StepF_ind.
  intros. simpl. apply H. assumption.
 intros f Hf H. simpl in H. unfold StepFSupBall in H. rewrite GlueAp in H. 
 rewrite StepFfoldPropglue_rew in H. destruct H as [H H1].
 simpl.
 unfold StepFSupBall. rewrite GlueAp.
 rewrite StepFfoldPropglue_rew. split.
 pose (HH:=IHb1  (compose1 (SplitLS X o) f)). simpl in HH.
 simpl in HH. unfold StepFSupBall in HH. unfold compose0 in HH.
  assert (rew:(ballS X e ^@> SplitLS0 o (f x)) ==
   (SplitL (ballS X e ^@> f x) o)). unfold SplitLS0. rewrite SplitLMap;reflexivity.
  rewrite <-rew. clear rew. apply HH; auto with *.
   intros. unfold SplitLS0. rewrite <- SplitLMap. rewrite <- SplitLAp.
   apply StepFfoldPropSplitL. apply (Hf c d H0).
 (* right *)
 pose (HH:=IHb2  (compose1 (SplitRS X o) f)). simpl in HH.
 unfold StepFSupBall in HH. unfold compose0 in HH.
  assert (rew:(ballS X e ^@> SplitRS0 o (f x)) ==
   (SplitR (ballS X e ^@> f x) o)). unfold SplitRS0. rewrite SplitRMap;reflexivity.
  rewrite <-rew. clear rew. apply HH; auto with *.
   intros. unfold SplitRS0. rewrite <- SplitRMap. rewrite <- SplitRAp.
   apply StepFfoldPropSplitR. apply (Hf c d H0).
intros b f Hf H.
simpl. 
unfold StepFSupBall. simpl. rewrite MapGlue. 
rewrite ApGlue. rewrite StepFfoldPropglue_rew. split.
 clear IHa2. pose (HH:=IHa1 (SplitL b o) (compose1 (SplitLS X o) f)). simpl in HH.
 unfold compose0 in HH. unfold StepFSupBall in HH. 
 rewrite SplitLBind. apply HH; clear HH.
  intros. unfold SplitLS0. rewrite <- SplitLMap. rewrite <- SplitLAp.
  apply StepFfoldPropSplitL. apply (Hf c d H0).
 pose (HH:=StepFfoldPropSplitL _ o H). rewrite SplitLAp in HH. rewrite SplitLMap in HH.
 setoid_replace a1 with (SplitL (glue o a1 a2) o ).
 assumption. rewrite SplitLGlue;reflexivity.

 clear IHa1. pose (HH:=IHa2 (SplitR b o) (compose1 (SplitRS X o) f)). simpl in HH.
 unfold compose0 in HH. unfold StepFSupBall in HH. 
 rewrite SplitRBind. apply HH; clear HH.
  intros. unfold SplitRS0. rewrite <- SplitRMap. rewrite <- SplitRAp.
  apply StepFfoldPropSplitR. apply (Hf c d H0).
 pose (HH:=StepFfoldPropSplitR _ o H). rewrite SplitRAp in HH. rewrite SplitRMap in HH.
 setoid_replace a2 with (SplitR (glue o a1 a2) o ).
 assumption. rewrite SplitRGlue;reflexivity.
Qed.

Open Local Scope uc_scope.

Section UniformlyContinuousFunctions.

Variable X Y : MetricSpace.

(** Various functions with step functions are uniformly continuous with this metric. *)
Definition StFJoinSup :(StepFSup (StepFSup X)) --> (StepFSup X).
simpl. rapply (@Build_UniformlyContinuousFunction
_ _ (@StFJoin X) (fun e:Qpos=>e)).
abstract (unfold is_UniformlyContinuousFunction; simpl; intros; apply
StepFSupBallBind; [auto with * | assumption]).
Defined.

Definition StFReturn_uc : X --> (StepFSup X).
simpl. exists (StFReturn X) (fun x:Qpos=> x:QposInf).
abstract (intros e a b H ; rapply H).
Defined.

Lemma uc_stdFun(X Y:MetricSpace):
(UniformlyContinuousFunction X Y) ->(extSetoid X Y).
intros X0 Y0 f. exists (ucFun f). abstract (intros; apply uc_wd; assumption).
Defined.

(* Why doesn't this work?
Coercion uc_stdFun: (UniformlyContinuousFunction X Y)>-> (extSetoid X Y).
*)

Definition Map_uc (f:X-->Y):(StepFSup X)-->(StepFSup Y).
intros.
exists (Map f) (mu f).
intros e a b.
simpl. unfold StepFSupBall.
case_eq (mu f e).
Focus 2. intros.
set (bal:=(ballS Y e)).
unfold ball_ex in H.
cut (StepFfoldProp 
((flip (compose (flip (compose bal (uc_stdFun f))) (uc_stdFun f))) ^@> a <@> b)).
evalStepF. auto with *.
apply StepFfoldPropForall_Map2. intros. simpl.
apply uc_prf.
rewrite H. simpl. auto.
intros q eq. rapply StepF_imp_imp.
unfold StepF_imp.
set (bal:=(ballS Y e)).
set (F:=(((flip (compose (flip (compose bal (uc_stdFun f))) (uc_stdFun f)))))).
set (IMP:=(ap
 (compose (@ap _ _ _) (compose (compose imp) (ballS X q)))
 F)).
cut (StepFfoldProp (IMP ^@> a <@> b)).
 unfold IMP, F; evalStepF. tauto.
apply StepFfoldPropForall_Map2.
intros a0 b0. simpl. unfold compose0.
intro. apply uc_prf. rewrite eq. rapply H.
Defined.

Definition glue_uc0 (o:OpenUnit): 
 StepFSup X -> StepFSup X --> StepFSup X.
intros o x.
exists (fun y=>(glue o x y)) (fun x:Qpos=> x).
abstract(
intros e a b;  simpl; rewrite StepFSupBallGlueGlue; intuition;
apply StepFSupBall_refl).
Defined.

Definition glue_uc (o:OpenUnit): 
 StepFSup X --> StepFSup X --> StepFSup X.
intros o.
exists (fun y=>(glue_uc0 o y)) (fun x:Qpos=> x).
abstract (intros e a b; simpl; unfold ucBall; simpl; intros; 
rewrite StepFSupBallGlueGlue; intuition;
apply StepFSupBall_refl).
Defined.

(** There is an injection from X to StepFSup X. *)
Lemma constStepF_uc_prf : is_UniformlyContinuousFunction
 (@constStepF X:X -> StepFSup X) Qpos2QposInf.
Proof.
intros e x y H.
simpl in *.
assumption.
Qed.

Definition constStepF_uc : X --> StepFSup X
:= Build_UniformlyContinuousFunction (constStepF_uc_prf).

End UniformlyContinuousFunctions.

Implicit Arguments constStepF_uc [X].