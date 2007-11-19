Require Export StepFunctionSetoid.
Require Export Metric.
Require Import OpenUnit.
Require Import QArith.
Require Import QMinMax.
Require Import Qabs.
Require Import CornTac.

Set Implicit Arguments.

Open Local Scope sfscope.

Lemma QS:(Setoid).
exists Q Qeq.
split; eauto with qarith.
Defined.

Definition test1:=(leaf (1:QS)).
Definition test2:=(glue (ou 1/2) (leaf (0:QS)) (leaf (1:QS))).

Open Local Scope sfstscope.

Definition Supnorm:(StepF QS)->Q:=(StepFfold (Qabs:QS->QS) (fun _=> Qmax)).
Eval compute in (Supnorm test2):Q.
Definition IntegralQ:(StepF QS)->Q:=(StepFfold (fun x => x) (fun b (x y:QS) => (b*x+(1-b)*y:QS))).
Eval compute in (IntegralQ test2):Q.
Definition QabsS : QS-->QS.
exists Qabs.
abstract(
simpl; intros x1 x2 Hx;
rewrite Hx;
reflexivity).
Defined.
Definition L1Norm(f:StepF QS):Q:=(IntegralQ (Map (QabsS) f)).
Eval compute in (L1Norm test2):Q.
Definition Qminus0 : QS -> QS --> QS.
intros q.
exists (Qminus q).
abstract (
simpl; intros x1 x2 Hx;
rewrite Hx;
reflexivity).
Defined.
Definition QminusS : QS --> QS --> QS.
exists (Qminus0).
abstract (
intros x1 x2 Hx y; simpl in *;
rewrite Hx;
reflexivity).
Defined.
Definition Distance(f g:StepF QS):Q:=(L1Norm (QminusS ^@> f <@> g)).
Eval compute in (Distance test1 test2):Q.
Eval compute in (Distance test2 test1):Q.
Definition L1Ball (e:Qpos)(f g:StepF QS):Prop:=(Distance f g)<=e.
Eval compute in (L1Ball (1#1)%Qpos test2 test1).
Definition Mesh (X:Setoid):(StepF X)->Q:=(StepFfold (fun x => 1)(fun b x y => (Qmax (b*x) ((1-b)*y)))).
Eval compute in (Mesh test2).

Section Equivalence1.
Variable X Y:Setoid.

End Equivalence1.

Section L1metric.

Definition StepQ := (StepF QS).

Lemma Qball_dec : forall e a b, {L1Ball e a b}+{~L1Ball e a b}.
intros e a b.
unfold L1Ball.
set (d:=Distance a b).
destruct (Qlt_le_dec_fast e d) as [Hdc|Hdc].
right. abstract auto with *.
left. exact Hdc.
Defined.
Require Import QArith_base.

Lemma IntegralSplit : forall (o:OpenUnit) x, 
 IntegralQ x ==
 o * IntegralQ (SplitL x o) + (1 - o) * IntegralQ (SplitR x o).
Proof.
intros o x.
revert o.
induction x using StepF_ind.
unfold IntegralQ. simpl. intros. simpl in x; ring.
intros p.
apply SplitLR_glue_ind; intros H.
  simpl.   (*This should be improved*) unfold IntegralQ; simpl; fold IntegralQ.
  rewrite (IHx1 (OpenUnitDiv p o H)).
  unfold IntegralQ; simpl; fold IntegralQ. field; auto with *. (*why does this not work*)
 simpl. unfold IntegralQ; simpl; fold IntegralQ. 
 rewrite (IHx2 (OpenUnitDualDiv p o H)).
 unfold IntegralQ; simpl; fold IntegralQ. field; auto with *.
rewrite H.
reflexivity.
Qed.

Hint Resolve IntegralSplit.

Add Morphism IntegralQ 
  with signature  StepF_eq ==>  Qeq
 as IntegralQ_mor.
unfold IntegralQ.
induction x1 using StepF_ind.
intros x2 H. simpl. induction x2 using StepF_ind.
  simpl.  auto with *.
 simpl.
 destruct H as [H0 H1] using (eq_glue_ind x2_1).
 rewrite <- IHx2_1; auto with *.
 rewrite <- IHx2_2; auto with *.
 simpl in x; ring.
intros x2 H.
destruct H as [H0 H1] using (glue_eq_ind x1_1).
simpl.
rewrite (IHx1_1 _ H0).
rewrite (IHx1_2 _ H1).
auto with *.
Qed.

(* 
Add Morphism Map
  with signature   (StepF_eq Qeq) ==>  Qeq
 as Map_mor.
Need to define equality on functions for this.

*)

Lemma Integral_glue : forall o s t, IntegralQ (glue o s t) = o*(IntegralQ s) + (1-o)*(IntegralQ t).
Proof.
reflexivity.
Qed.
Definition Qplus0 : QS -> QS --> QS.
intros q.
exists (Qplus q).
abstract (
simpl; intros x1 x2 Hx;
rewrite Hx;
reflexivity).
Defined.
Definition QplusS : QS --> QS --> QS.
exists (Qplus0).
abstract (
intros x1 x2 Hx y; simpl in *;
rewrite Hx;
reflexivity).
Defined.

Lemma Integral_linear:forall s t,
  (IntegralQ s)+(IntegralQ t)==(IntegralQ ((QplusS:QS-->QS-->QS) ^@> s <@> t)).
Proof.
induction s using StepF_ind.
 induction t using StepF_ind.
  reflexivity.
 rewrite Integral_glue.
 change ((QplusS:QS-->QS-->QS) ^@> leaf (X:=QS) x <@> glue o t1 t2)
  with ((QplusS x:QS-->QS) ^@> glue o t1 t2).
 rewrite MapGlue.
 change ((QplusS x:QS-->QS) ^@> t1)
  with ((QplusS:QS-->QS-->QS) ^@> leaf (X:=QS) x <@> t1).
 change ((QplusS x:QS-->QS) ^@> t2)
  with ((QplusS:QS-->QS-->QS) ^@> leaf (X:=QS) x <@> t2).
 rewrite Integral_glue.
 rewrite <- IHt1.
 rewrite <- IHt2.
 ring.
intros t.
rewrite MapGlue.
rewrite ApGlue.
do 2 rewrite Integral_glue.
rewrite <- IHs1.
rewrite <- IHs2.
rewrite (IntegralSplit o t).
ring.
Qed.

Require Import QMinMax.
Require Import COrdAbs.
Require Import Qordfield.
Require Import CornTac.
Require Import Qauto.

Definition Qle0 : QS -> QS --> iffSetoid.
intros q.
exists (Qle q).
abstract (
simpl; intros x1 x2 Hx;
rewrite Hx;
reflexivity).
Defined.
Definition QleS : QS --> QS --> iffSetoid.
exists (Qle0).
abstract (
intros x1 x2 Hx y; simpl in *;
rewrite Hx;
reflexivity).
Defined.

Definition StepF_le x y := (StepFfoldProp (QleS ^@> x <@> y)).

Lemma StepF_le_refl:forall x, (StepF_le x x).
unfold StepF_le.
pose (forall x, join QleS x).
(*TODO using combinators*)



 induction x using StepF_ind.
 change (Qle x x); auto with *.
rewrite MapGlue.
rewrite ApGlueGlue.split; auto with *.
Qed.

Lemma StepFfoldPropglue_rew:(forall o x y, (StepFfoldProp (glue o x y))<->((StepFfoldProp x)/\StepFfoldProp y)).
auto with *.
Qed.

Lemma StepFfoldPropMap: (forall b x, 
      (StepFfoldProp x /\ b)
   <->(StepFfoldProp (Map ((fun a  => a /\ b ):iffSetoid-->iffSetoid) x))).
induction x using StepF_ind.
 split.
  intro H. simpl. auto with *.
 simpl. auto with *.
rewrite MapGlue.
do 2 rewrite StepFfoldPropglue_rew. intuition.
Qed. 

Lemma StepFfoldPropMap': (forall a x, 
      (a /\ StepFfoldProp x)
   <->(StepFfoldProp (Map ((fun b  => a /\ b):iffSetoid-->iffSetoid) x))).
induction x using StepF_ind.
 split.
  intro H. simpl. auto with *.
 simpl. auto with *.
rewrite MapGlue. do 2 rewrite StepFfoldPropglue_rew. intuition.
Qed.

Lemma StepFfoldPropMap2: (forall x y, 
      (StepFfoldProp x /\ StepFfoldProp y)
   <->(StepFfoldProp (((fun a b => a /\ b) : iffSetoid-->iffSetoid-->iffSetoid ) ^@> x <@> y))).
unfold Map2.
induction x using StepF_ind. rapply StepFfoldPropMap'. 
intro y. set (H0:=IHx1 (SplitL y o)). set (H1:=IHx2 (SplitR y o)).
rewrite MapGlue.
rewrite <- (StepFfoldPropglue y o).
 do 2 rewrite StepFfoldPropglue_rew. revert H0 H1. 
do 2 intro. rewrite ApGlue. rewrite StepFfoldPropglue_rew. intuition.
Qed.

Lemma StepF_le_pos:forall x y, (StepF_le x y) <-> (StepFfoldProp (Map ((fun (q:QS)=>(0>=q)):QS-->iffSetoid) ((Qminus:QS-->QS-->QS) ^@> x <@> y))).
intros. unfold StepF_le. apply StepFfoldProp_morphism.
apply (Map_morphism); auto with *.
clear A x y.
intros w w' x x' H HH. rewrite H. rewrite HH. clear H HH. auto with *.
split. intro. rewrite Qle_minus_iff in *.
replace RHS with (x0+-w) by ring. assumption.
intro H. rewrite Qle_minus_iff in *. 
replace RHS with (0+ - (w -x0)) by ring. assumption.
Qed.

Lemma StepF_le_ge:forall x y, (StepF_le x y) <-> (StepFfoldProp (Map2 Qge y x)).
intros. unfold StepF_le, Map2. 
apply StepFfoldProp_morphism.
apply (@Map2switch Prop iff Qle).
Qed.

Definition Map3 X Y Z W (f:X -> Y -> Z -> W) a b c := f ^@> a <@> b <@> c.

Definition Map4 X Y Z W V (f:X -> Y -> Z -> W -> V) a b c d := f ^@> a <@> b <@> c <@> d.

Lemma Map4Map2Map2Map2(X Y Z W V U UU:Type):
forall  (f:X->Y->U)(g:Z->W->V)(h:U->V->UU) 
(x:StepF X) (y:StepF Y) (z:StepF Z) (w:StepF W),
(Map2 h (Map2 f x y) (Map2 g z w))=
(Map4 (fun x y z w => (h (f x y) (g z w))) x y z w).
intros.
unfold Map4.
simpl.
Admitted.

Lemma Map4Map32(X Y Z W:Type):forall (f:X->Y->Y->Z->W) 
(x:StepF X) (y:StepF Y) (z:StepF Z) ,
(Map4 f x y y z)=(Map3 (fun x y z=> (f x y y z)) x y z).
Admitted.

Lemma StepF_le_trans:forall x y z, (StepF_le x y)-> (StepF_le y z) ->(StepF_le x z).
intros x y z. unfold StepF_le.
intros H H0.
assert (StepFfoldProp (Map2 (fun a b : Prop => a /\ b) 
        (Map2 Qle x y) (Map2 Qle y z))).
rewrite <- StepFfoldPropMap2;intuition.
clear H0 H.
assert (H:StepFfoldProp
       (Map2 (fun a b : Prop => a /\ b) (Map2 Qle x y) (Map2 Qle y z))
    <-> StepFfoldProp (Map2 Qle x z)). 
apply (StepFfoldProp_morphism).
Focus 2. rewrite <- H. auto with *.
clear H1.
assert (StepF_eq iff
    (Map2 (fun a b : Prop => a /\ b) (Map2 Qle x y) (Map2 Qle y z))
    (App (Map (fun a => (fun b=>a /\ b)) (Map2 Qle x y)) (Map2 Qle y z))).
apply (Map2Map iff iff iff (fun a b : Prop => a /\ b) (fun a b : Prop => a /\ b)).
intuition.
rewrite Map4Map2Map2Map2.
rewrite Map4Map32.
assert (StepF_eq iff (Map3 (fun x0 z0 : Q => x0 <= y0 <= z0) x y z) (Map2 Qle x z)).
unfold Map3.




unfold Map3.

(*
rewrite H. rewrite MapMap2.
transitivity ((Map4 (fun x y z w=>(x<=y)/\(z<=w))) x y y z).

unfold Map4.


Check Map2Map.
Check (Map2Map Qeq Qeq iff Qle Qle).
assert  (StepF_eq iff (Map2 Qle y z) (App (Map (fun x  => Qle x) y) z)).
apply (Map2Map Qeq Qeq iff Qle Qle). 
  do 4 intro. intros H0 H1. rewrite H0. rewrite H1. auto with *.
transitivity (App (Map2 (fun (x0 y0 : Q) (b : Prop) => x0 <= y0 /\ b) x y)
     (App (Map (fun x : Q => Qle x) y) z)).
apply App_mor2. assumption.



set (Map2Map (fun a b : Prop => a /\ b) (fun a b : Prop => a /\ b)).
set (s Prop iff).
Check (Map2 (fun (x0 y0 : Q) (b : Prop) => x0 <= y0 /\ b) x y).
Check (Map (fun x0 : Q => Qle x0) y).




apply (AppMapMap iff).







intros x y z. do 3 rewrite StepF_le_pos.
do 3 rewrite MapMap2.
intros H H0.
set (HH:=StepFfoldPropMap2 
         (Map2 (fun x y : Q => x - y <= 0) x y)
         (Map2 (fun x y : Q => x - y <= 0) y z)).
assert  (H1:StepFfoldProp
       (Map2 (fun a b : Prop => a /\ b)
          (Map2 (fun x y : Q => x - y <= 0) x y)
          (Map2 (fun x y : Q => x - y <= 0) y z))).
rewrite <-HH; auto with *. clear HH H H0.
cut ((StepFfoldProp
       (Map2 (fun a b : Prop => a /\ b)
          (Map2 (fun x y : Q => x - y <= 0) x y)
          (Map2 (fun x y : Q => x - y <= 0) y z)))
         <->
          (StepFfoldProp (Map2 (fun x0 y0 : Q => x0 - y0 <= 0) x z))).
intro H. rewrite <- H. auto with *.
apply (StepFfoldProp_morphism).
clear H1.
assert (StepF_eq iff
  (Map2 (fun a b : Prop => a /\ b) 
     (Map2 (fun x0 y0 : Q => x0 - y0 <= 0) x y)
     (Map2 (fun x0 y0 : Q => x0 - y0 <= 0) y z))
  (Map2 (fun x0 y0 : Q => x0 - y0 <= 0) x z)).

rewrite Map2Map2Map2.

 (Map2 (fun x0 y0 : Q => x0 - y0 <= 0) x y))). (Map2 Qle y z)) (Map2 Qle x z)); auto with *.


 (Map2 f (Map2 g x y) (Map2 h x y))
  = (Map2 (fun x y => (f (g x y) (h x y))) x y).
 *)

Lemma L1ball_refl : forall e x, (L1Ball e x x).
Proof.
intros e x.
unfold L1Ball, Distance.
assert ((Map2 Qminus x x)===(leaf 0)).
 induction x.
  change (x - x==0).
  ring.
 rewrite Map2GlueGlue.
 rapply glue_StepF_eq; auto with *.
unfold L1Norm.
setoid_replace (Map Qabs (Map2 Qminus x x):StepQ) with (Map Qabs (leaf 0)).
 auto with *.
rapply (Map_morphism Q_Setoid); auto with *.
intros a b Hab.
rewrite Hab.
reflexivity.
Qed.

Lemma L1ball_sym : forall e x y, (L1Ball e x y) -> (L1Ball e y x).
Proof.
intros e x y Hxy.
unfold L1Ball, Distance, L1Norm in *.
rewrite MapMap2 in *.
setoid_replace (Map2 (fun x0 y0 : Q => Qabs (x0 - y0)) y x:StepQ)
 with (Map2 (fun x0 y0 : Q => Qabs (x0 - y0)) x y:StepQ).
 apply Hxy.
rewrite Map2switch. 
rapply (Map2_morphism Q_Setoid Q_Setoid Q_Setoid); auto with *.
  intros a b c d Hab Hcd.
  rewrite Hab, Hcd.
  reflexivity.
intros a b.
rewrite <- Qabs_opp.
apply Qabs_wd.
ring.
Qed.

Lemma L1_is_MetricSpace : (is_MetricSpace (StepF_eq Qeq)  L1Ball).
split.
     apply (StepF_Sth Q_Setoid).
    rapply L1ball_refl.
   rapply L1ball_sym.
  (* Trans*)
  do 5 intro. unfold L1Ball, Distance, L1Norm. intros.
  assert (IntegralQ (Map Qabs (Map2 Qminus a b))+
         IntegralQ (Map Qabs (Map2 Qminus b c)) >=
         IntegralQ (Map Qabs (Map2 Qminus a c))).
   clear -c. rewrite Integral_linear.  do 2 rewrite MapMap2.
   cut (forall x y z o, x<=y->x<=z->x<=(o*y+(1-o)*z)).
   intro HH.
   assert (intpos:forall x y:(StepF Q), 
         (StepF_lt x y)->(IntegralQ x <= IntegralQ y)).
    induction x.
     unfold StepF_lt, IntegralQ. simpl. 
      induction y. simpl. auto with *.
      simpl. intros [H H1]. apply HH; auto with *.
     intro y. unfold StepF_lt, IntegralQ. simpl. fold IntegralQ.
      assert (rew:IntegralQ y==IntegralQ (glue o (fst (Split y o)) (snd (Split y o)))). apply IntegralQ_mor. 
      (* This is broken rewrite glueSplit should work*) 
      change (y === glue o (SplitL y o) (SplitR y o)).
      rewrite (glueSplit Q_Setoid); auto with *.
      rewrite rew. clear rew.
      destruct (Split y o) as [L R]. intros [H1 H2].
      set (ineq1:=IHx1 L H1). set (ineq2:=IHx2 R H2). simpl.
      unfold IntegralQ. simpl. fold IntegralQ.
      rewrite Qle_minus_iff. rewrite Qle_minus_iff in ineq1, ineq2.
      replace RHS with (o* (IntegralQ L+-IntegralQ x1)+(1-o)*(IntegralQ R + - IntegralQ x2)) by ring.
      (* This is too difficult. Extend Qauto_nonneg?*)
      (set (q:=(OpenUnit_0_lt_Dual o))). revert q. set (d:=1-o). intro. assert (0<=d). auto with *. clear q.
      Qauto_nonneg.
    apply intpos.
(* 
 First show that 
    Show that StepF_lt is a reflexive, transitive relation
    Show that if f<=g, then (StepF_lt (Map2 f) (Map2 g))
    (StepF_lt (Map2 | + |) (Map2 |  |+|  |))
    Show that:
    (a-b)+(b-c)= (a-c) This needs that Map2 is a morphism.
*)
   Focus 3.
(* Closed, this is copied from Qmetric*)
unfold L1Ball. intros e a b H.
assert (forall x, (forall d : Qpos, x <= e+d) -> x <= e).
 intros. rsapply shift_zero_leEq_minus'.
 rsapply inv_cancel_leEq. rsapply approach_zero_weak.
 intros. replace LHS with (x[-](e:Q)). 
  rsapply shift_minus_leEq. replace RHS with (e+e0) by ring. rewrite <- (QposAsmkQpos H1).
  apply (H0 (mkQpos H1)).
 unfold cg_minus; simpl; ring.
apply H0. exact H.
(* *)
Focus 3. (* Equality, form Qmetric*)
unfold L1Ball. Check Distance.
assert (forall q:Q, 0<=q -> (forall e:Qpos, q<=e)->q==0).
assert (forall a b, ((Distance a b==0) ->(a===b))).
Admitted.

(*
Add Morphism L1Ball with signature QposEq ==> (StepF_eq Qeq) ==> (StepF_eq Qeq) ==> iff as Qball_wd.
intros [x1 Hx1] [x2 Hx2] H x3 x4 H0 x5 x6 H1.
unfold L1Ball.
rewrite H0.
rewrite H1.
unfold QposEq in H.
simpl in H.
rewrite H.
tauto.
Qed.


Definition L1_as_MetricSpace : MetricSpace :=
Build_MetricSpace L1ball_wd L1_is_MetricSpace.

Canonical Structure L1_as_MetricSpace.

 Do we need this?
Lemma QPrelengthSpace : PrelengthSpace Q_as_MetricSpace.
Proof.
assert (forall (e d1 d2:Qpos), e < d1+d2 -> forall (a b c:Q), ball e a b -> (c == (a*d2 + b*d1)/(d1+d2)%Qpos) -> ball d1 a c).
intros e d1 d2 He a b c Hab Hc.
simpl.
unfold Qball.
apply AbsSmall_wdr with ((d1/(d1+d2)%Qpos)*(a - b)).
apply AbsSmall_wdl with ((d1/(d1+d2)%Qpos)*(d1+d2)%Qpos);
 [|simpl; field; apply Qpos_nonzero].
rsapply mult_resp_AbsSmall.
rsapply less_leEq.
rsapply (div_resp_pos _  _ (d1:Q) (@Qpos_nonzero (d1+d2)%Qpos)); apply Qpos_prf.
destruct d1; destruct d2; rsapply (AbsSmall_trans _ (e:Q)); assumption.
simpl.
rewrite Hc.
pose (@Qpos_nonzero (d1 + d2)%Qpos).
QposField.
assumption.
intros a b e d1 d2 He Hab.
pose (c:= (a * d2 + b * d1) / (d1 + d2)%Qpos).
exists c.
apply (H e d1 d2 He a b c); try assumption.
reflexivity.
apply ball_sym.
eapply H.
rewrite Qplus_comm.
apply He.
apply ball_sym.
apply Hab.
unfold c.
unfold Qdiv.
apply Qmult_comp.
ring.
apply Qinv_comp.
QposRing.
Qed.
*)

(* TODO:
Is a metric space
Continuity of integration
Continuity of Map, Map2
Continuous functions are in the completion, i.e. there is an injection 
from continuous functions to integrable ones.
Integration is correct. Needs mesh. 

Write a tactic Done (auto with *, etc)
Find out how simple works with fold.
*)