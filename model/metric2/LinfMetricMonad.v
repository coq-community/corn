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
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import CoRN.model.totalorder.QposMinMax.
Require Export CoRN.metric2.StepFunctionSetoid.
Require Import CoRN.metric2.StepFunctionMonad.
Require Import CoRN.metric2.UniformContinuity.
Require Import CoRN.model.structures.OpenUnit.
From Coq Require Import QArith.
Require Import CoRN.model.totalorder.QMinMax.
From Coq Require Import Qabs.
Require Import CoRN.model.ordfields.Qordfield.
Require Import CoRN.model.metric2.Qmetric.
Require Import CoRN.metric2.Prelength.
Require Import CoRN.algebra.COrdFields2.
Require Import CoRN.tactics.CornTac.

Set Implicit Arguments.

Local Open Scope sfstscope.
Local Open Scope setoid_scope.

(**
** Linf metric for Step Functions
The Linf metric for [StepF X] is obtained by lifting the ball predicate on X *)

Section StepFSupBall.
Set Implicit Arguments.

Variable X:MetricSpace.

(** A setoid verion of the ball predicate *)
Definition ballS0 (m : MetricSpace): Q -> (msp_as_RSetoid m) -> (msp_as_RSetoid m) --> iffSetoid
  := fun (e : Q) (x : m) =>
       Build_Morphism
         (msp_as_RSetoid m) iffSetoid (ball e x)
         (fun (x1 x2 : m) (H : msp_eq x1 x2) =>
            ball_wd m (reflexivity e) x x (reflexivity x) x1 x2 H).

Definition ballS (m : MetricSpace): Q -> (msp_as_RSetoid m) --> (msp_as_RSetoid m) --> iffSetoid.
Proof.
 intros e.
 exists (ballS0  m e).
 intros. simpl. split; rewrite -> H; auto with *.
Defined.

(** The definition of the usp metric *)
Definition StepFSupBall (e:Q) (f:StepF (msp_as_RSetoid X)) (g:StepF (msp_as_RSetoid X))
  := StepFfoldProp (((@ballS X e)^@> f) <@> g).

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

Arguments StepFSupBall [X].

Add Parametric Morphism X : (@StepFSupBall X)
  with signature Qeq ==> (@StepF_eq _) ==> (@StepF_eq _) ==> iff
 as StepFSupBall_wd.
Proof.
 unfold StepFSupBall.
 intros a1 a2 Ha x1 x2 Hx y1 y2 Hy.
 apply StepFfoldProp_morphism.
 rewrite -> Hx.
 rewrite -> Hy.
 setoid_replace (ballS X a1) with (ballS X a2).
  reflexivity.
 intros x y.
 simpl.
 rewrite -> Ha.
 reflexivity.
Qed.

Lemma StepFSupBall_e_wd : forall X (e1 e2:Q) x y,
    Qeq e1 e2 -> (StepFSupBall e1 x y <-> @StepFSupBall X e2 x y).
Proof.
  intros. rewrite H. reflexivity.
Qed. 

Section SupMetric.
(** The StepFSupBall satifies the requirements of a metric. *)
Variable X : MetricSpace.

Lemma StepFSupBall_refl : forall (e:Q) (x:StepF (msp_as_RSetoid X)),
    Qle (0#1) e -> StepFSupBall e x x.
Proof.
 intros e x epos.
 unfold StepFSupBall.
 set (b:=(@ballS X e)).
 set (f:=(@join _ _) ^@> (constStepF b)).
 cut (StepFfoldProp (f <@> x )).
  unfold f.
  evalStepF.
  auto.
 apply: StepFfoldPropForall_Map.
 simpl.
 auto with *.
Qed.

Lemma StepFSupBall_sym : forall e (x y:StepF (msp_as_RSetoid X)),
    (StepFSupBall e x y) -> (StepFSupBall e y x).
Proof.
 intros e x y.
 unfold StepFSupBall.
 set (b:=(@ballS X e)).
 apply StepF_imp_imp.
 unfold StepF_imp.
 set (f:=ap (compose (@ap _ _ _) (compose (compose imp) b)) (flip (b))).
 cut (StepFfoldProp (f ^@> x <@> y)).
  unfold f; evalStepF; tauto.
 apply StepFfoldPropForall_Map2.
 intros a b0.
 simpl. unfold compose0.
 auto with *.
Qed.

Lemma StepFSupBall_triangle : forall e d (x y z:StepF (msp_as_RSetoid X)),
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
 pose (f:= ap (compose (@ap _ _ _) (compose (compose (compose (@compose _ _ _) imp)) be))
   (compose (flip (compose (@ap _ _ _) (compose (compose imp) bd))) bed)).
 cut (StepFfoldProp (f ^@> x <@> y <@> z)).
  unfold f.
  evalStepF.
  tauto.
 apply StepFfoldPropForall_Map3.
 apply: (ball_triangle X e d).
Qed.

Lemma StepFSupBall_closed : forall e (x y:StepF (msp_as_RSetoid X)),
    (forall d, Qlt (0#1) d -> (StepFSupBall (e+d) x y)) -> (StepFSupBall e x y).
Proof.
 intros e.
 apply: (StepF_ind2).
 - intros. rewrite -> H, H0 in H1. apply H1.
   intro. rewrite -> H, H0. apply H2.
 - apply: ball_closed.
 - intros o s s0 t t0 IH0 IH1 H.
 unfold StepFSupBall in *.
 rewrite MapGlue. rewrite ApGlue. simpl.
 split.
  rewrite SplitLGlue. apply IH0. clear IH0.
  intros d dpos. pose (H2:=H d).
  rewrite -> MapGlue in H2. rewrite ApGlue in H2.
  rewrite SplitRGlue in H2. rewrite SplitLGlue in H2.
  destruct H2. exact dpos. auto.
  rewrite SplitRGlue. apply IH1. clear IH1.
 intros d dpos. pose (H2:=H d).
 rewrite -> MapGlue in H2. rewrite ApGlue in H2.
 rewrite SplitRGlue in H2. rewrite SplitLGlue in H2.
 destruct H2. exact dpos. auto.
Qed.

Lemma StepFSupBall_eq : forall (x y : StepF (msp_as_RSetoid X)),
(forall e : Qpos, StepFSupBall (proj1_sig e) x y) -> StepF_eq x y.
Proof.
 apply: (StepF_ind2).
 - intros s s0 t t0 H H0 H1 H2. rewrite -> H, H0 in H1. apply H1.
   intro. rewrite -> H, H0. apply H2.
 - intros. apply ball_eq. intros.
   specialize (H (exist _ _ H0)). exact H.
 - intros o s s0 t t0 H H0 H1.
 unfold StepFSupBall in *. apply glue_resp_StepF_eq.
 apply H. clear H.
  intro e. pose (H2:=H1 e).
  rewrite -> MapGlue in H2. rewrite ApGlue in H2. rewrite SplitRGlue in H2. rewrite SplitLGlue in H2.
  destruct H2; auto.
 apply H0. clear H0.
 intro e. pose (H2:=H1 e).
 rewrite -> MapGlue in H2. rewrite ApGlue in H2. rewrite SplitRGlue in H2. rewrite SplitLGlue in H2.
 destruct H2; auto.
Qed.

Lemma StepFSupBall_nonneg : forall (e : Q) (a b : StepFS (msp_as_RSetoid X)),
  StepFSupBall e a b -> Qle (0#1) e.
Proof.
  induction a.
  - (* a is the constant function x *)
    induction b. intro H0.
    unfold StepFSupBall, StepFfoldProp in H0. simpl in H0.
    exact (msp_nonneg (msp X) e x x0 H0).
    intros [H0 _]. exact (IHb1 H0).
  - intros b H.
    unfold StepFSupBall, StepFfoldProp in H. simpl in H.
    unfold Ap in H. simpl in H.
    destruct (@Split X b o). destruct H.
    apply (IHa1 _ H).
Qed.

Lemma StepFSupBall_stable : forall (e : Q) (a b : StepFS (msp_as_RSetoid X)),
  (~~StepFSupBall e a b) -> StepFSupBall e a b. 
Proof.
  induction a.
  - induction b.
    unfold StepFSupBall, StepFfoldProp.
    simpl. intros. apply (msp_stable (msp X)), H.
    intros. split.
    apply IHb1.
    intro abs. contradict H; intros [H _].
    contradiction.
    apply IHb2.
    intro abs. contradict H; intros [_ H].
    contradiction.
  - unfold StepFSupBall, StepFfoldProp, Ap.
    simpl. intros b H.
    destruct (@Split X b o). split.
    apply IHa1.
    intro abs. contradict H; intros [H _].
    contradiction.
    apply IHa2.
    intro abs. contradict H; intros [_ H].
    contradiction.
Qed.
  
(**
*** Example of a Metric Space <Step, StepFSupBall>
*)
Lemma StepFSupBall_is_MetricSpace : is_MetricSpace (@StepFSupBall X).
Proof.
 split.
 - intros. intro x. apply StepFSupBall_refl, H.
 - apply: StepFSupBall_sym.
 - apply: StepFSupBall_triangle.
 - apply: StepFSupBall_closed.
 - exact StepFSupBall_nonneg.
 - exact StepFSupBall_stable.
Qed.

Definition StepFSup : MetricSpace :=
  Build_MetricSpace (@StepFSupBall_e_wd X) StepFSupBall_is_MetricSpace.

Lemma StepF_eq_equiv : forall (x y : StepFSup),
    StepF_eq x y <-> msp_eq x y.
Proof.
  split.
  - intro H. simpl. rewrite H. apply (ball_refl StepFSup).
    discriminate.
  - intro H. apply StepFSupBall_eq.
    simpl in H.
    intro e. exact (ball_weak_le StepFSup x y (Qpos_nonneg e) H).
Qed.

(** The StepFSup is is a prelength space. *)
Lemma StepFSupPrelengthSpace : PrelengthSpace X -> PrelengthSpace StepFSup.
Proof.
 intros pl.
 apply: StepF_ind2.
   intros s s0 t t0 Hs Ht H e d1 d2 He H0.
   rewrite <- Hs, <- Ht in H0.
   destruct (H _ _ _ He H0) as [c Hc0 Hc1].
   exists c.
    rewrite <- Hs; auto.
   rewrite <- Ht; auto.
  intros a b e d1 d2 He Hab.
  destruct (pl a b e d1 d2 He Hab) as [c Hc0 Hc1].
  exists (@constStepF (msp_as_RSetoid X) c); auto.
 intros o s s0 t t0 IHl IHr e d1 d2 He H.
 simpl in H.
 rewrite -> StepFSupBallGlueGlue in H.
 destruct H as [Hl Hr].
 destruct (IHl _ _ _ He Hl) as [c Hc0 Hc1].
 destruct (IHr _ _ _ He Hr) as [d Hd0 Hd1].
 exists (glue o c d); simpl; rewrite -> StepFSupBallGlueGlue; auto.
Qed.

End SupMetric.

(* begin hide *)
Canonical Structure StepFSup.
(* end hide *)

Lemma StepFSupBallBind(X:MetricSpace): ((forall (e : Qpos) (a b : StepF (StepFS (msp_as_RSetoid X))) ,
forall f:(StepFS (msp_as_RSetoid X)) -->(StepFS (msp_as_RSetoid X)),
(forall c d, (StepFSupBall (proj1_sig e) c d) -> (StepFSupBall (proj1_sig e) (f c) (f d)))->
StepFSupBall (X:=StepFSup X) (proj1_sig e) a b ->
StepFSupBall (X:=X) (proj1_sig e) (StFBind00 a f) (StFBind00 b f))).
Proof.
 intros e a. unfold ball_ex.
 induction a. simpl.
 induction b.
  intros. simpl. apply H. assumption.
  intros f Hf H. simpl in H. unfold StepFSupBall in H.
  pose proof (GlueAp (constStepF (ballS (StepFSup X) (proj1_sig e)) <@^ x) o b1 b2).
  rewrite H0 in H. clear H0.
  rewrite -> StepFfoldPropglue_rew in H. destruct H as [H H1].
  simpl.
  unfold StepFSupBall. rewrite -> GlueAp.
  rewrite -> StepFfoldPropglue_rew. split.
  pose (HH:=IHb1  (compose1 (SplitLS (msp_as_RSetoid X) o) f)). simpl in HH.
   simpl in HH. unfold StepFSupBall in HH. unfold compose0 in HH.
   assert (rew:(ballS X (proj1_sig e) ^@> SplitLS0 o (f x)) ==
               (SplitL (ballS X (proj1_sig e) ^@> f x) o)).
   unfold SplitLS0. rewrite SplitLMap;reflexivity.
    rewrite <-rew. clear rew. apply HH; auto with *.
   intros. unfold SplitLS0. rewrite <- SplitLMap. rewrite <- SplitLAp.
   apply StepFfoldPropSplitL. apply (Hf c d H0).
   (* right *)
   pose (HH:=IHb2  (compose1 (SplitRS (msp_as_RSetoid X) o) f)). simpl in HH.
  unfold StepFSupBall in HH. unfold compose0 in HH.
  assert (rew:(ballS X (proj1_sig e) ^@> SplitRS0 o (f x)) ==
              (SplitR (ballS X (proj1_sig e) ^@> f x) o)).
  unfold SplitRS0. rewrite SplitRMap;reflexivity.
   rewrite <-rew. clear rew. apply HH; auto with *.
  intros. unfold SplitRS0. rewrite <- SplitRMap. rewrite <- SplitRAp.
  apply StepFfoldPropSplitR. apply (Hf c d H0).
  intros b f Hf H.
 simpl.
 unfold StepFSupBall. simpl. rewrite MapGlue.
 rewrite ApGlue. rewrite -> StepFfoldPropglue_rew. split.
 clear IHa2. pose (HH:=IHa1 (SplitL b o) (compose1 (SplitLS (msp_as_RSetoid X) o) f)).
 simpl in HH.
  unfold compose0 in HH. unfold StepFSupBall in HH.
  rewrite -> SplitLBind. apply HH; clear HH.
  intros. unfold SplitLS0. rewrite <- SplitLMap. rewrite <- SplitLAp.
   apply StepFfoldPropSplitL. apply (Hf c d H0).
   pose (HH:=StepFfoldPropSplitL _ o H).
   rewrite -> SplitLAp in HH. rewrite SplitLMap in HH.
   assert (StepF_eq (ballS (StepFSup X) (proj1_sig e) ^@> a1 <@> SplitL b o)
                    (ballS (StepFSup X) (proj1_sig e) ^@> SplitL (glue o a1 a2) o <@> SplitL b o)).
   { rewrite SplitLGlue. reflexivity. }
   rewrite (StepFfoldProp_mor _ _ H0).
   exact HH. 
  clear IHa1. pose (HH:=IHa2 (SplitR b o) (compose1 (SplitRS (msp_as_RSetoid X) o) f)). simpl in HH.
 unfold compose0 in HH. unfold StepFSupBall in HH.
 rewrite -> SplitRBind. apply HH; clear HH.
 intros. unfold SplitRS0. rewrite <- SplitRMap. rewrite <- SplitRAp.
  apply StepFfoldPropSplitR. apply (Hf c d H0).
  pose (HH:=StepFfoldPropSplitR _ o H). rewrite -> SplitRAp in HH.
  rewrite SplitRMap in HH.
   assert (StepF_eq (ballS (StepFSup X) (proj1_sig e) ^@> a2 <@> SplitR b o)
                    (ballS (StepFSup X) (proj1_sig e) ^@> SplitR (glue o a1 a2) o <@> SplitR b o)).
   { rewrite SplitRGlue. reflexivity. }
   rewrite H0. exact HH.
Qed.

Local Open Scope uc_scope.

Section UniformlyContinuousFunctions.

Variable X Y : MetricSpace.

(** Various functions with step functions are uniformly continuous with this metric. *)
Definition StFJoinSup :(StepFSup (StepFSup X)) --> (StepFSup X).
Proof.
  simpl.
  apply (@Build_UniformlyContinuousFunction
           (StepFSup (StepFSup X))
           _ (@StFJoin (msp_as_RSetoid X)) (fun e:Qpos=>e)).
 abstract (unfold is_UniformlyContinuousFunction; simpl; intros; apply
   StepFSupBallBind; [auto with * | assumption]).
Defined.

Definition StFReturn_uc : X --> (StepFSup X).
Proof.
 simpl. exists (StFReturn (msp_as_RSetoid X)) (fun x:Qpos=> x:QposInf).
 abstract (intros e a b H ; apply H).
Defined.

Lemma uc_stdFun(X0 Y0:MetricSpace):
  (UniformlyContinuousFunction X0 Y0) -> (extSetoid (msp_as_RSetoid X0) (msp_as_RSetoid Y0)).
Proof.
 intros f. exists (ucFun f). abstract (intros; apply uc_wd; assumption).
Defined.

(* Why doesn't this work?
Coercion uc_stdFun: (UniformlyContinuousFunction X Y)>-> (extSetoid X Y).
*)

Definition Map_uc (f:X-->Y):(StepFSup X)-->(StepFSup Y).
Proof.
 intros.
 exists (Map f) (mu f).
 intros e a b.
 simpl. unfold StepFSupBall.
 case_eq (mu f e).
  Focus 2. intros.
 set (bal:=(ballS Y (proj1_sig e))).
 unfold ball_ex in H.
 cut (StepFfoldProp ((flip (compose (flip (compose bal (uc_stdFun f))) (uc_stdFun f))) ^@> a <@> b)).
  evalStepF. auto with *.
  apply StepFfoldPropForall_Map2. intros. simpl.
 apply uc_prf.
 rewrite H. simpl. auto.
 intros q eq. apply: StepF_imp_imp.
 unfold StepF_imp.
 set (bal:=(ballS Y (proj1_sig e))).
 set (F:=(((flip (compose (flip (compose bal (uc_stdFun f))) (uc_stdFun f)))))).
 set (IMP:=(ap (compose (@ap _ _ _) (compose (compose imp) (ballS X (proj1_sig q)))) F)).
 cut (StepFfoldProp (IMP ^@> a <@> b)).
  unfold IMP, F; evalStepF. tauto.
  apply StepFfoldPropForall_Map2.
 intros a0 b0. simpl. unfold compose0.
 intro. apply uc_prf. rewrite eq. apply H.
Defined.

Definition glue_uc0 (o:OpenUnit):
 StepFSup X -> StepFSup X --> StepFSup X.
Proof.
 intros x.
 exists (fun y=>(glue o x y)) (fun x:Qpos=> x).
 abstract( intros e a b;  simpl; rewrite -> StepFSupBallGlueGlue; intuition; apply StepFSupBall_refl; apply Qpos_nonneg).
Defined.

Definition glue_uc (o:OpenUnit):
 StepFSup X --> StepFSup X --> StepFSup X.
Proof.
 exists (fun y=>(glue_uc0 o y)) (fun x:Qpos=> x).
 intros e a b H.
 split. apply Qpos_nonneg. 
 intros. simpl. rewrite -> StepFSupBallGlueGlue. intuition.
 apply StepFSupBall_refl. apply Qpos_nonneg.
Defined.

(** There is an injection from X to StepFSup X. *)
Lemma constStepF_uc_prf
  : is_UniformlyContinuousFunction
      (@constStepF (msp_as_RSetoid X):X -> StepFSup X) Qpos2QposInf.
Proof.
 intros e x y H.
 simpl in *.
 assumption.
Qed.

Definition constStepF_uc : X --> StepFSup X
:= Build_UniformlyContinuousFunction (constStepF_uc_prf).

End UniformlyContinuousFunctions.

Arguments constStepF_uc {X}.
