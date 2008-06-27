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
Require Export StepFunctionMonad.
Require Import OpenUnit.
Require Import CornTac.
Require Export Integration.
Require Export LinfMetricMonad.

(** We prove the that StepF distributes over Complete.
*)
Set Implicit Arguments.
Open Local Scope sfstscope.
Lemma JoinGlue(X:Setoid): forall o a b, 
(StFJoin X (glue o a b))==(glue o (StFBind (StepFS X) _ a (SplitLS X o)) (StFBind (StepFS X) _ b (SplitRS X o))).
intros. simpl. 
transitivity (glue o (StFBind00 (SplitL (glue o a b) o) (compose1 (SplitLS X o) id))
  (StFBind00 (SplitR (glue o a b) o) (compose1 (SplitRS X o) id))).
apply glue_wd; auto with *. apply StFBind00_wd; try reflexivity. rewrite SplitLGlue. reflexivity.
 apply StFBind00_wd; try reflexivity. rewrite SplitRGlue. reflexivity.
 apply glue_wd; auto with *.
 rewrite <- SplitLBind. simpl. rewrite SplitLGlue. apply StFBind_wd1. intro x. reflexivity.
 rewrite <- SplitRBind. simpl. rewrite SplitRGlue. apply StFBind_wd1. intro x. reflexivity.
Qed.

(* Should be moved*)
Axiom StepFfoldPropSplitR
     : forall (s : StepF iffSetoid) (a : OpenUnit),
       StepFfoldProp s -> StepFfoldProp (SplitR s a).

Section Swap.
(* M= Complete, N= StepF 
swap = distribComplete*)
Open Local Scope sfstscope.

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

Variable X Y:MetricSpace.
Definition StFJoinSup:(UniformlyContinuousSpace (StepFSup (StepFSup X)) (StepFSup X)).
simpl. rapply (@Build_UniformlyContinuousFunction
_ _ (@StFJoin X) (fun e:Qpos=>e)).
abstract (unfold is_UniformlyContinuousFunction; simpl; intros; apply
StepFSupBallBind; [auto with * | assumption]).
Defined.

Axiom cheat:False.
Open Scope uc_scope.
(*
Definition LeibnizSetoid(A:Type):Setoid.
intro A. exists A (@eq A).
split; auto with *.
Defined.

Definition typefun2extSetoid(A B:Type)(f:A->B):(extSetoid (LeibnizSetoid A)
(LeibnizSetoid B)).
intros A B f. exists f. simpl. intros.  rewrite H.
reflexivity.
Defined.
*)
(* RegularFunction should have been extensional *)
Definition swap_raw (x:StepFSup (Complete X)) (e:QposInf): (StepFSup X):=
(Map (fun z=> approximate z e) x).

Lemma swap_prf : forall (x:StepFSup (Complete X)),
 is_RegularFunction (swap_raw x).
Proof.
unfold swap_raw.
intros x a b.
induction x using StepF_ind.
rapply regFun_prf.
simpl (ball (m:=StepFSup X)).
set (f:=(fun z : RegularFunction X => approximate z a)) in *.
set (g:=(fun z : RegularFunction X => approximate z b)) in *.
simpl.
fold (glue o (Map f x1) (Map f x2)).
fold (glue o (Map g x1) (Map g x2)).
setoid_rewrite (StepFSupBallGlueGlue).
auto.
Qed.

Definition swap1 (x:StepFSup (Complete X)): (Complete (StepFSup X)).
intro x. exists (swap_raw x).
abstract (apply (swap_prf x)).
Defined.


Add Morphism swap1 with signature (@ms_eq _)
 ==> (@ms_eq _) as swap1_wd.
induction x.
 induction y.
  intros H d1 d2.
  rapply H.
 intros H d1 d2.
 destruct H.
 split.
  apply IHy1; assumption.
 apply IHy2; assumption.
intros y H d1 d2.
simpl.
unfold swap_raw.
simpl.
destruct H as [Hl Hr] using (glue_eq_ind x1 x2 y o).
rewrite <- (glueSplit (Map (fun z : RegularFunction X => approximate z d2) y) o).
unfold SplitL, SplitR.
 rewrite StepFunction.SplitLMap, StepFunction.SplitRMap.
fold (glue o (Map (fun z : RegularFunction X => approximate z d1) x1)
     (Map (fun z : RegularFunction X => approximate z d1) x2)).
rewrite StepFSupBallGlueGlue.
split; revert d1 d2.
 rapply IHx1.
 assumption.
rapply IHx2.
assumption.
Qed.

Lemma swap1_uc : is_UniformlyContinuousFunction swap1 Qpos2QposInf.
Proof.
intros e.
rapply StepF_ind2.
  simpl (ball_ex).
  intros s s0 t t0 Hs Ht H.
  rewrite <- Hs, <- Ht.
  assumption.
 intros.
 assumption.
intros o s s0 t t0 Hl Hr H d1 d2.
simpl.
unfold swap_raw.
simpl.
fold (glue o (Map (fun z : RegularFunction X => approximate z d1) s)
     (Map (fun z : RegularFunction X => approximate z d1) s0)).
fold (glue o
     (Map (fun z : RegularFunction X => approximate z d2) t)
     (Map (fun z : RegularFunction X => approximate z d2) t0)).
simpl in *.
rewrite StepFSupBallGlueGlue in H |- *.
split; revert d1 d2; tauto.
Qed.

Require Export StepFunctionSetoid.
Lemma uc_stdFun(X Y:MetricSpace):
(UniformlyContinuousFunction X Y) ->(extSetoid X Y).
intros X0 Y0 f. exists (ucFun f). abstract (intros; apply uc_wd; assumption).
Defined.

(* Why doesn't this work?
Coercion uc_stdFun: (UniformlyContinuousFunction X Y)>-> (extSetoid X Y).

*)
(* Should be moved. 
 Better: how can we use Map_compose_Map for rewriting?*)
Lemma Map_compose_Map_eq: forall (X Y:Type) (Z : Setoid) (f : Y -> Z) (g : X -> Y)
         (a : StepFunction.StepF X),
       (Map (fun a0 : X => f (g a0)) a) == (Map f (Map g a)).
intros. apply StepF_Qeq_eq. apply Map_compose_Map.
Qed.

Open Scope sfstscope.
Print Scopes.
Open Scope sfscope.
Definition swap: (StepFSup (Complete X))-->(Complete (StepFSup X)).
rapply (@Build_UniformlyContinuousFunction _ _ swap1 (fun e => e)).
abstract (exact swap1_uc).
Defined.
End Swap.

Variable X:MetricSpace.
(* M= Complete, N= StepF 
swap = distribComplete*)
(* 
prod≔mapM joinN . swapN
mapM joinN: MNN-> MN
swapN: NMN -> MNN *)
Definition prod(X:MetricSpace):= (uc_compose (Cmap_slow (StFJoinSup X))
  (@swap (StepFSup X))).

(*
dorp ≔joinM . mapM swap
MNM -> MMN -> MN
*)
Definition dorp(X:MetricSpace):= (uc_compose Cjoin
  (Cmap_slow (@swap X))).

Definition StFReturn_uc(X:MetricSpace):
(UniformlyContinuousSpace X (StepFSup X)).
intro X0. simpl. exists (StFReturn X0) (fun x:Qpos=> x:QposInf).
abstract (intros e a b H ; rapply H).
Defined.

Open Scope uc_scope.

Definition Map_uc(X Y:MetricSpace)(f:X-->Y):(StepFSup X)-->(StepFSup Y).
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
 (compose (@ap _ _ _) (compose (compose imp) (ballS X0 q)))
 F)).
cut (StepFfoldProp (IMP ^@> a <@> b)).
 unfold IMP, F; evalStepF. tauto.
apply StepFfoldPropForall_Map2.
intros a0 b0. simpl. unfold compose0.
intro. apply uc_prf. rewrite eq. rapply H.
Defined.



(*
swap . mapN (mapM f)≍mapM (mapN f) . swap
NM->NM->MN    =    NM -> MN ->MN*)
 Lemma swapmapmap: forall f, (ucEq
(uc_compose (swap X) (Map_uc (@Cmap_slow _ _ f)))
(uc_compose (Cmap_slow (Map_uc f)) (swap X))).
intros.
intro x.
induction x using StepF_ind.
 intros e e1. simpl.
 unfold swap_raw. simpl.
 change (ballS X (e + e1) (Cmap_slow_raw f x e) 
  (f (approximate x 
   (QposInf_bind (fun y' : Qpos => ((1 # 2) * y')%Qpos) (mu f e1))))). 
 unfold Cmap_slow_raw. simpl.
 set (ee:=(QposInf_bind (fun y' : Qpos => ((1 # 2) * y')%Qpos) (mu f e))).
 set (ee1:=(QposInf_bind (fun y' : Qpos => ((1 # 2) * y')%Qpos) (mu f e1))).
 rewrite <-  ball_Cunit.
 assert (H:ball (m:=(Complete X)) (e + e1) 
  ((Cmap_slow f) (Cunit (approximate x ee))) ((Cmap_slow f) (Cunit (approximate x ee1)))).
   apply ball_triangle with (Cmap_slow f x);rapply (uc_prf (Cmap_slow f));[rapply ball_ex_approx_l|rapply ball_ex_approx_r].
 apply H.
intros e1 e2. simpl. unfold swap_raw. simpl.
(* Why do we need to fold glue??*)
change 
(StepFSupBall (X:=X) (e1 + e2)
  (glue o
     (Map (fun z : RegularFunction X => approximate z e1)
        (Map (Cmap_slow_fun f) x1))
     (Map (fun z : RegularFunction X => approximate z e1)
        (Map (Cmap_slow_fun f) x2)))
  (glue o
     (Map f
        (Map
           (fun z : RegularFunction X =>
            approximate z
              (QposInf_bind (fun y' : Qpos => ((1 # 2) * y')%Qpos) (mu f e2)))
           x1))
     (Map f
        (Map
           (fun z : RegularFunction X =>
            approximate z
              (QposInf_bind (fun y' : Qpos => ((1 # 2) * y')%Qpos) (mu f e2)))
           x2)))).
rewrite (@StepFSupBallGlueGlue X (e1+e2) o).
split; [rapply IHx1|rapply IHx2].
Qed.

Require Import Qauto.
(* swap . returnM≍mapM returnN*)
Lemma swapreturn:
(ucEq
(uc_compose (swap _)(StFReturn_uc _))
(@Cmap_slow _ _ (StFReturn_uc X))).
Proof.
intro x. simpl.
unfold StFReturn_uc. 
intros e e1. simpl. unfold swap_raw. simpl.
unfold StepFSupBall.
(* From here onwards the proof is too difficult *) 
change (ballS X (e + e1) (approximate x e) 
(approximate x ((1 # 2) * e1)%Qpos)).
simpl.
apply ball_weak_le with (Qpos_plus e ((1 # 2) * e1)%Qpos).
2: rapply (regFun_prf_ex x e ((1 # 2) * e1)%Qpos).
rewrite Qle_minus_iff.
replace RHS with (e1 - (1#2)*e1).
replace RHS with ((1#2)*e1) by ring.
Qauto_nonneg. replace LHS with ((e + e1)+ - (e + (1 # 2) * e1)).
ring. reflexivity. Qed.

Open Scope setoid_scope.
(* Should be moved to RSetoid*)
Definition bind (X Y Z:Setoid) : (X--> Y) --> (Y --> X--> Z) --> (X--> Z):=
(compose (compose (@join _ _)) (flip (@compose X Y (X-->Z)))).

Definition bind_compose (X Y Z W:Setoid) : 
 (W--> X--> Y) --> (Y --> X--> Z) --> (W--> X--> Z):=
 (flip (compose (@compose W _ _) ((flip (@bind X Y Z))))).

Implicit Arguments bind [X Y Z].
Implicit Arguments bind_compose [X Y Z W].
(* <-- Should be moved to RSetoid*)

Open Scope sfstscope.
(* Do we need this???*)
Lemma Map_functor(X Y Z:Setoid)(f:X-->Y)(g:Y-->Z):forall x, 
g^@>(f^@>x)==(compose g f)^@>x.
Admitted.

Open Scope uc_scope.

(*swap . mapN returnM≍returnM*)
Lemma swapmapret:(ucEq
(uc_compose (swap _)
(@Map_uc _ _ (@Cunit X))) 
(@Cunit (StepFSup X))).
intros x e1 e2. simpl. 
unfold swap_raw.
unfold StepFSupBall.
setoid_replace (
Map (fun z : RegularFunction X => approximate z e1)
         (Map (Cunit_fun X) x))
with (Map (fun z  => (approximate ((Cunit_fun X) z) e1)) x).
simpl.
setoid_replace (Map (fun z : X => z) x) with x.
set (b:=(@ballS X (e1+e2))).
set (f:=(@join _ _) ^@> (constStepF b)).
cut (StepFfoldProp (f <@> x )).
 unfold f;  evalStepF; tauto.
rapply StepFfoldPropForall_Map.
simpl.
auto with *.
rapply Map_identity.
(* Is there a general solution to avoid StepF_Qeq_eq??*)
apply StepF_Qeq_eq; rewrite <- Map_compose_Map; reflexivity.
Qed.

Lemma is_RegularFunction_wd(X:MetricSpace):(forall x:(Complete X), 
forall approx:QposInf->X, (extEq _ approx (approximate x)) ->is_RegularFunction approx).
intros. unfold is_RegularFunction. intros. rewrite (H e1). rewrite (H e2). apply x.
Qed.

Definition swapconst(X : MetricSpace):(Complete X)->Complete (StepFSup X).
intros X0 x. exists (fun e => (constStepF (approximate x e ))).
abstract (intros e1 e2; simpl; unfold StepFSupBall, StepFfoldProp;
simpl; apply x).
Defined.

Lemma swapConst(X : MetricSpace):forall x,
(ms_eq (swap  X (constStepF x)) (swapconst x)).
intros. intros e1 e2. simpl. unfold swap_raw. simpl.
unfold StepFSupBall, StepFfoldProp;simpl; apply x.
Qed.

(* prod . mapN dorp≍dorp . prod*)
Lemma prodmadorp:(ucEq
(uc_compose (prod _)
(@Map_uc _ _ (dorp _)))
(uc_compose (dorp _) (@prod (Complete X)))
).
intro x. 
induction x using StepF_ind.
simpl. intros e e1.
simpl.
unfold Cjoin_raw. simpl. unfold swap_raw.
set (f1:=(fun z : RegularFunction X =>
      approximate z ((1 # 2) * ((1 # 2) * e))%Qpos)).
set (f2:=(fun z : RegularFunction X => approximate z ((1 # 2) * e1)%Qpos)).

(* FIXME *)
Admitted.



====

(*
unfold is_UniformlyContinuousFunction.
intros. simpl in H. simpl. unfold swap1, regFunBall. simpl. unfold swap_raw.
intros.
(* We first need to compare the distances in Complete X*) 
assert (StepFSupBall (Qpos_plus (Qpos_plus d1 e) d2)
  (Map (uc_stdFun (@Cunit X)) (Map (fun z : RegularFunction X => approximate z d1) a))
  ((uc_stdFun (@Cunit X)) ^@>  (Map (fun z : RegularFunction X => approximate z d2) b))).

setoid_replace (Map (uc_stdFun Cunit)
     (Map (fun z : RegularFunction X => approximate z d1) a))
with
(Map (fun z : RegularFunction X => ((uc_stdFun Cunit) (approximate z d1))) a).
2: symmetry; rapply Map_compose_Map_eq.
set (f:=  (fun z : RegularFunction X => uc_stdFun Cunit (approximate z d1))).
simpl. 
setoid_replace 
(Cunit_fun X ^@> 
((fun z : RegularFunction X => approximate z d2) ^@> b))
with
( ((fun z : RegularFunction X => Cunit (approximate z d2)) ^@> b))
by (symmetry; rapply Map_compose_Map_eq).
simpl.
set (g:=  (fun z : RegularFunction X => Cunit_fun X (approximate z d2))).
simpl in f.
revert H.
set (bb:=(fun x =>((@ballS (Complete X) (d1+e+d2)) (f x) (g x)))).
rapply StepF_imp_imp.
unfold StepF_imp.
Open Scope sfstscope.
(*
set (F:=(((flip (compose (flip (compose bb (uc_stdFun f))) (uc_stdFun f)))))).
*)
(*
set (IMP:=(ap
 (compose (@ap _ _ _) 
  (compose (compose imp) (ballS (Complete X) e)))
 bb)).
cut (StepFfoldProp (IMP ^@> a <@> b)).
 unfold IMP, F; evalStepF. tauto.
apply StepFfoldPropForall_Map2.
intros a0 b0. simpl. unfold compose0.
intro. apply uc_prf. rewrite eq. rapply H.

set (F:=(((flip (compose (flip (compose bb f)) g))))).

rapply ball_ex_approx_l.
*)
(* FIX ME *)
abstract (elim cheat).
abstract (elim cheat).
Defined.

===

(* Should have a variant of  Map_compose_Map *)
setoid_replace (
Map (fun z : RegularFunction X => approximate z e)
         (Map (Cmap_slow f) x))
with (Map (fun z  => (approximate ((Cmap_slow f) z) e)) x).
2: (apply StepF_Qeq_eq; rewrite <- Map_compose_Map; reflexivity).
set (qbind:= (QposInf_bind (fun y' : Qpos => ((1 # 2) * y')%Qpos) (mu f e1))).
setoid_replace (Map f
     (Map
        (fun z : RegularFunction X =>
         approximate z
           qbind) x))
with (Map
        (fun z : RegularFunction X =>
         ((ucFun f) (approximate z
           qbind))) x).
2: (apply StepF_Qeq_eq; rewrite <- Map_compose_Map; reflexivity).
set (bal:=(ballS X (e+e1))).
set (f1:=(fun z : Complete X => approximate (Cmap_slow f z) e)).
set (f2:=(fun z : RegularFunction X => f (approximate z qbind))).
simpl in f1.

setoid_rewrite <- (@Map_compose_Map_eq _ _ _ bal f1 x).

(* approximate, Cmap_slow_raw should be a setoid function on RegularFunction *)
(* set (F:=(((flip (compose (flip (compose bal f1))) f2)))).*)
