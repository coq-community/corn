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
Require Export CoRN.metric2.StepFunctionMonad.
Require Import CoRN.model.structures.OpenUnit.
Require Import CoRN.tactics.CornTac.
Require Import CoRN.metric2.Complete.
Require Export CoRN.model.metric2.LinfMetricMonad.
Require Export CoRN.metric2.StepFunctionSetoid.
Require Import CoRN.tactics.Qauto.

(** ** Completion distributes over Step Functions
We prove the that StepF distributes over Complete using the function
swap (which we call dist) as in Jones, Duponcheel - composing monads
*)
Set Implicit Arguments.

Local Open Scope Q_scope.
Local Open Scope sfstscope.

Section Dist.
(* M= Complete, N= StepF
dist = distribComplete*)
Local Open Scope sfstscope.
Variable X: MetricSpace.
(** The dist function exchanges StepF (under the infinity metric) and Complete monads *)

Definition dist_raw (x:StepFSup (Complete X)) (e:QposInf): (StepFSup X):=
(Map (fun z=> approximate z e) x).

Lemma dist_prf : forall (x:StepFSup (Complete X)),
 is_RegularFunction (dist_raw x).
Proof.
 unfold dist_raw.
 intros x a b.
 induction x using StepF_ind.
  apply: regFun_prf.
 simpl (ball (m:=StepFSup X)).
 set (f:=(fun z : RegularFunction X => approximate z a)) in *.
 set (g:=(fun z : RegularFunction X => approximate z b)) in *.
 simpl.
 fold (glue o (Map f x1) (Map f x2)).
 fold (glue o (Map g x1) (Map g x2)).
 setoid_rewrite (StepFSupBallGlueGlue).
 auto.
Qed.

Definition dist1 (x:StepFSup (Complete X)): (Complete (StepFSup X)).
Proof.
 exists (dist_raw x).
 abstract (apply (dist_prf x)).
Defined.

Add Morphism dist1 with signature (@st_eq _)
 ==> (@st_eq _) as dist1_wd.
Proof.
 induction x.
  induction y.
   intros H d1 d2.
   apply: H.
  intros H d1 d2.
  destruct H.
  split.
   apply IHy1; assumption.
  apply IHy2; assumption.
 intros y H d1 d2.
 simpl.
 unfold dist_raw.
 simpl.
 destruct H as [Hl Hr] using (glue_eq_ind x1 x2 y o).
 rewrite <- (glueSplit (Map (fun z : RegularFunction X => approximate z d2) y) o).
 unfold SplitL, SplitR.
 rewrite StepFunction.SplitLMap, StepFunction.SplitRMap.
 fold (glue o (Map (fun z : RegularFunction X => approximate z d1) x1)
   (Map (fun z : RegularFunction X => approximate z d1) x2)).
 rewrite -> StepFSupBallGlueGlue.
 split; revert d1 d2.
  apply: IHx1; assumption.
 apply: IHx2; assumption.
Qed.

Lemma dist1_uc : is_UniformlyContinuousFunction dist1 Qpos2QposInf.
Proof.
 intros e.
 apply: StepF_ind2.
   simpl (ball_ex).
   intros s s0 t t0 Hs Ht H.
   unfold ball_ex.
   rewrite <- Hs, <- Ht.
   assumption.
  intros.
  assumption.
 intros o s s0 t t0 Hl Hr H d1 d2.
 simpl.
 unfold dist_raw.
 simpl.
 fold (glue o (Map (fun z : RegularFunction X => approximate z (Qpos2QposInf d1)) s)
   (Map (fun z : RegularFunction X => approximate z (Qpos2QposInf d1)) s0)).
 fold (glue o (Map (fun z : RegularFunction X => approximate z (Qpos2QposInf d2)) t)
   (Map (fun z : RegularFunction X => approximate z (Qpos2QposInf d2)) t0)).
 simpl in *.
 rewrite -> StepFSupBallGlueGlue in H |- *.
 split; revert d1 d2; tauto.
Qed.

Local Open Scope uc_scope.
Local Open Scope sfstscope.
Local Open Scope sfscope.

Definition dist: (StepFSup (Complete X))-->(Complete (StepFSup X)).
Proof.
 apply (@Build_UniformlyContinuousFunction _ _ dist1 (fun e => e)).
 abstract (exact dist1_uc).
Defined.
End Dist.

Arguments dist {X}.

Definition distconst(X : MetricSpace):(Complete X)->Complete (StepFSup X).
Proof.
 intros x. exists (fun e => (constStepF (approximate x e ))).
 abstract (intros e1 e2; simpl; unfold StepFSupBall, StepFfoldProp; simpl; apply x).
Defined.

Lemma distConst(X : MetricSpace):forall (x:Complete X),
(st_eq (dist (constStepF x)) (distconst x)).
Proof.
 intros. intros e1 e2. simpl. unfold dist_raw. simpl.
 unfold StepFSupBall, StepFfoldProp;simpl; apply x.
Qed.

Lemma dist_glue(X:MetricSpace)(o:OpenUnit): forall (x y:(StepFSup (Complete X))),
(st_eq (dist (glue o x y))  (Cmap2_slow (glue_uc _ o) (dist x) (dist y))).
Proof.
  pose (exist (Qlt 0) (1#2) eq_refl) as half.
 intros. simpl. intros e e1. simpl.
 unfold dist_raw. simpl.
 unfold Cmap_slow_fun. simpl.
 unfold Cap_slow_raw. simpl.
 unfold dist_raw.
 fold (glue o (Map (fun z : RegularFunction X => approximate z e) x)
   (Map (fun z : RegularFunction X => approximate z e) y)).
 rewrite -> StepFSupBallGlueGlue.
 assert (forall w:StepF (Complete X), StepFSupBall (X:=X) (proj1_sig e + proj1_sig e1)
   (Map (fun z : RegularFunction X => approximate z e) w) (Map (fun z : RegularFunction X =>
     approximate z (half * (half * e1))%Qpos) w)).
  induction w using StepF_ind.
   unfold StepFSupBall. unfold StepFfoldProp. simpl.
   rewrite <- ball_Cunit.
   apply ball_triangle with x0.
    apply ball_approx_l.
   apply ball_weak_le  with (proj1_sig (half * (half * e1))%Qpos).
    rewrite -> Qle_minus_iff.
    simpl.
     replace RHS with ((3#4)*proj1_sig e1); [| simpl; ring].
     Qauto_nonneg.
   apply ball_approx_r.
  simpl.
  change (StepFSupBall (X:=X) (proj1_sig e + proj1_sig e1) (glue o0 (Map (fun z : RegularFunction X => approximate z e) w1)
    (Map (fun z : RegularFunction X => approximate z e) w2)) (glue o0 (Map
      (fun z : RegularFunction X => approximate z (half * (half * e1))%Qpos) w1) (Map
        (fun z : RegularFunction X => approximate z (half * (half * e1))%Qpos) w2))).
  rewrite -> StepFSupBallGlueGlue.
  intuition.
 split;auto.
Qed.

Section DistributionLaws.
(** Now we show the laws for dist are satified, except for the last one
which we have not completed yet. *)

(* M= Complete, N= StepF
dist = distribComplete*)
(*
prod≔mapM joinN . distN
mapM joinN: MNN-> MN
distN: NMN -> MNN *)
Let prod(X:MetricSpace):= (uc_compose (Cmap_slow (StFJoinSup X))
  (@dist (StepFSup X))).

(*
dorp ≔joinM . mapM dist
MNM -> MMN -> MN
*)
Let dorp(X:MetricSpace):= (uc_compose Cjoin
  (Cmap_slow (@dist X))).

(*
dist . mapN (mapM f)≍mapM (mapN f) . dist
NM->NM->MN    =    NM -> MN ->MN*)
 Lemma distmapmap: forall X Y (f : UniformlyContinuousSpace X Y), (ucEq
(uc_compose (dist) (Map_uc (@Cmap_slow _ _ f)))
(uc_compose (Cmap_slow (Map_uc f)) (dist))).
Proof.
  pose (exist (Qlt 0) (1#2) eq_refl) as half.
 intros.
 intro x.
 induction x using StepF_ind.
  intros e e1. simpl.
  unfold dist_raw. simpl.
  change (ballS Y (proj1_sig e + proj1_sig e1) (Cmap_slow_raw f x e) (f (approximate x
    (QposInf_bind (fun y' : Qpos => (half * y')%Qpos) (mu f e1))))).
  unfold Cmap_slow_raw. simpl.
  set (ee:=(QposInf_bind (fun y' : Qpos => (half * y')%Qpos) (mu f e))).
  set (ee1:=(QposInf_bind (fun y' : Qpos => (half * y')%Qpos) (mu f e1))).
  rewrite <-  ball_Cunit.
  assert (H:ball (m:=(Complete Y)) (proj1_sig e + proj1_sig e1)
    ((Cmap_slow f) (Cunit (approximate x ee))) ((Cmap_slow f) (Cunit (approximate x ee1)))).
   apply ball_triangle with (Cmap_slow f x);apply: (uc_prf (Cmap_slow f));[apply: ball_ex_approx_l|apply: ball_ex_approx_r].
  apply H.
 intros e1 e2. simpl. unfold dist_raw. simpl.
 (* Why do we need to fold glue??*)
 change (StepFSupBall (X:=Y) (proj1_sig e1 + proj1_sig e2) (glue o (Map (fun z : RegularFunction Y => approximate z e1)
   (Map (Cmap_slow_fun f) x1)) (Map (fun z : RegularFunction Y => approximate z e1)
     (Map (Cmap_slow_fun f) x2))) (glue o (Map f (Map (fun z : RegularFunction X => approximate z
       (QposInf_bind (fun y' : Qpos => (half * y')%Qpos) (mu f e2))) x1)) (Map f (Map
         (fun z : RegularFunction X => approximate z
           (QposInf_bind (fun y' : Qpos => (half * y')%Qpos) (mu f e2))) x2)))).
 rewrite -> (@StepFSupBallGlueGlue Y (proj1_sig e1+proj1_sig e2) o).
 split; [apply IHx1|apply IHx2].
Qed.

(* dist . returnM≍mapM returnN*)
Lemma distreturn: forall X,
(ucEq
(uc_compose dist (StFReturn_uc _))
(@Cmap_slow _ _ (StFReturn_uc X))).
Proof.
  pose (exist (Qlt 0) (1#2) eq_refl) as half.
 intros X x. simpl.
 unfold StFReturn_uc.
 intros e e1. simpl. unfold dist_raw. simpl.
 unfold StepFSupBall.
 (* From here onwards the proof is too difficult *)
 change (ballS X (proj1_sig e + proj1_sig e1) (approximate x e) (approximate x (half * e1)%Qpos)).
 simpl.
 apply ball_weak_le with (proj1_sig (Qpos_plus e (half * e1)%Qpos)).
  2: apply (regFun_prf_ex x e (half * e1)%Qpos).
 rewrite -> Qle_minus_iff. simpl.
  replace RHS with ((1#2)* proj1_sig e1); [| simpl; ring].
  Qauto_nonneg.
Qed.

(*dist . mapN returnM≍returnM*)
Lemma distmapret: forall X, (ucEq
(uc_compose dist
(@Map_uc _ _ (@Cunit X)))
(@Cunit (StepFSup X))).
Proof.
 intros X x e1 e2. simpl.
 unfold dist_raw.
 unfold StepFSupBall.
 setoid_replace ( Map (fun z : RegularFunction X => approximate z e1) (Map (Cunit_fun X) x))
   with (Map (fun z  => (approximate ((Cunit_fun X) z) e1)) x).
  simpl.
  setoid_replace (Map (fun z : X => z) x) with x.
   set (b:=(@ballS X (proj1_sig e1+proj1_sig e2))).
   set (f:=(@join _ _) ^@> (constStepF b)).
   cut (StepFfoldProp (f <@> x )).
    unfold f;  evalStepF; tauto.
   apply: StepFfoldPropForall_Map.
   simpl.
   auto with *.
  apply: Map_identity.
 (* Is there a general solution to avoid StepF_Qeq_eq??*)
 apply StepF_Qeq_eq; rewrite <- Map_compose_Map; reflexivity.
Qed.

(* We skip the proof of the following lemma since the obvious induction
proof does not work since glue does not work well with join
In our current setting it would be more natural to check the distributive laws
 using a (unit, bind) presentation. Unfortunately, we have been unable to find one
in the literature.
*)

(* prod . mapN dorp≍dorp . prod*)
(*
Lemma prodmadorp:(ucEq
(uc_compose (prod _)
(@Map_uc _ _ (dorp _)))
(uc_compose (dorp _) (@prod (Complete X)))
).
*)
End DistributionLaws.
