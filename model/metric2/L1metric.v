Require Export StepFunctionSetoid.
Require Export Metric.
Require Import OpenUnit.
Require Import QArith.
Require Import QMinMax.
Require Import Qabs.
Require Import CornTac.

Set Implicit Arguments.

Open Local Scope sfscope.

Ltac arw := progress 
((repeat rewrite <- Ap_Map, <- Map_homomorphism);
 autorewrite with  StepF_rew).

Add Morphism StepFfoldProp
  with signature StepF_eq ==>  iff
 as StepFfoldProp_mor.
exact StepFfoldProp_morphism.
Qed.

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

Hint Rewrite Integral_glue: StepF_rew.

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
 rewrite Map_homomorphism in *.
 rewrite Ap_Map in *.
 rewrite MapGlue.
 do 2 rewrite Integral_glue.
 rewrite <- IHt1.
 rewrite <- IHt2.
 ring.
intros t.
arw.
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

Definition Qge0 : QS -> QS --> iffSetoid.
intros q.
exists (Qge q).
abstract (
simpl; intros x1 x2 Hx;
rewrite Hx;
reflexivity).
Defined.

Definition QgeS : QS --> QS --> iffSetoid.
exists (Qge0).
abstract (
intros x1 x2 Hx y; simpl in *;
rewrite Hx;
reflexivity).
Defined.

Definition StepF_le x y := (StepFfoldProp (QleS ^@> x <@> y)).

Lemma StepFfoldPropForall_Ap : 
 forall X (f:StepF (X --> iffSetoid)) (x:StepF X), (forall y, StepFfoldProp (f <@> leaf y)) -> StepFfoldProp (f <@> x).
Proof.
intros X f x H.
revert f H.
induction x using StepF_ind.
 intros f H.
 rapply H.
intros f H.
rewrite <- (glueSplit f o).
rewrite ApGlueGlue.
split.
 apply IHx1.
 intros y.
 assert (H0:=H y).
 rewrite <- (glueSplit f o) in H0.
 rewrite ApGlue in H0.
 destruct H0 as [H0 _].
 assumption.
apply IHx2.
intros y.
assert (H0:=H y).
rewrite <- (glueSplit f o) in H0.
rewrite ApGlue in H0.
destruct H0 as [_ H0].
assumption.
Qed.

Lemma StepFfoldPropForall_Map : 
 forall X (f:X --> iffSetoid) (x:StepF X), (forall a, f a) -> StepFfoldProp (f ^@> x).
Proof.
intros X f x H.
rewrite <- Ap_Map.
apply StepFfoldPropForall_Ap.
assumption.
Qed.

Lemma StepFfoldPropForall_Map2 : 
 forall X Y (f:X --> Y --> iffSetoid) x y, (forall a b, f a b) -> StepFfoldProp (f ^@> x <@> y).
Proof.
intros X Y f x y H.
apply StepFfoldPropForall_Ap.
intros b.
rewrite <- Ap_Map.
rewrite <- (Ap_commutative (leaf f) (leaf b)).
do 2 rewrite Ap_homomorphism.
rapply StepFfoldPropForall_Map.
intros a.
rapply H.
Qed.

Lemma StepFfoldPropForall_Map3 : 
 forall X Y Z (f:X --> Y --> Z --> iffSetoid) x y z, (forall a b c, f a b c) -> StepFfoldProp (f ^@> x <@> y <@> z).
Proof.
intros X Y Z f x y z H.
apply StepFfoldPropForall_Ap.
intros c.
rewrite <- Ap_Map.
rewrite <- (Ap_commutative ((leaf f) <@> x) (leaf c)).
rewrite <- Ap_composition.
do 2 rewrite Ap_homomorphism.
rewrite <- (Ap_commutative (leaf (compose flip f)) (leaf c)).
do 2 rewrite Ap_homomorphism.
rapply StepFfoldPropForall_Map2.
intros a b.
rapply H.
Qed.

Lemma StepF_le_refl:forall x, (StepF_le x x).
intros x.
unfold StepF_le.
cut (StepFfoldProp (join QleS ^@> x)).
 arw.
 tauto.
apply StepFfoldPropForall_Map.
intros.
simpl.
auto with *.
Qed.

Lemma StepFfoldPropglue_rew:(forall o x y, (StepFfoldProp (glue o x y))<->((StepFfoldProp x)/\StepFfoldProp y)).
auto with *.
Qed.

Hint Rewrite StepFfoldPropglue_rew:StepF_rew.

Definition conjr:iffSetoid -> iffSetoid-->iffSetoid.
intro b. apply (Build_Morphism iffSetoid iffSetoid (fun a  => a /\ b )).
abstract (simpl; intuition).
Defined.

Lemma StepFfoldPropMap: (forall b x, 
      (StepFfoldProp x /\ b)
   <->(StepFfoldProp (Map (conjr b:iffSetoid-->iffSetoid) x))).
induction x using StepF_ind.
 split;auto with *.
rewrite MapGlue. arw. intuition.
Qed. 

Definition conjl:iffSetoid -> iffSetoid-->iffSetoid.
intro b. apply (Build_Morphism iffSetoid iffSetoid (fun a  => b/\a )).
abstract (simpl; intuition).
Defined.

Lemma StepFfoldPropMap': (forall a x, 
      (a /\ StepFfoldProp x)
   <->(StepFfoldProp (Map (conjl a) x))).
induction x using StepF_ind.
 split; auto with *.
arw. intuition.
Qed.

(*Definition conj:(iffSetoid -> iffSetoid)-->iffSetoid.
intro b. apply (Build_Morphism iffSetoid iffSetoid (fun a  => b/\a )).
abstract (simpl; intuition).
Defined.*)


(*Should be moved:
Record Morphism (X Y:Setoid) :=
{evalMorphism :> X -> Y
;Morphism_prf : forall x1 x2, (st_eq X x1 x2) -> (st_eq Y (evalMorphism x1) (evalMorphism x2))
}.

Definition extEq (X:Type) (Y:Setoid) (f g:X -> Y) := forall x, st_eq Y (f x) (g x).
Definition extSetoid (X Y:Setoid) : Setoid.
intros X Y.
exists (Morphism X Y) (extEq Y).
split.
  intros x y; reflexivity.
 intros x y H a; symmetry; auto.
intros x y z Hxy Hyz a; transitivity (y a); auto.
Defined.

Notation "x --> y" := (extSetoid x y) (at level 70, right associativity) : sfstscope.
*)

(*Lemma StepFfoldPropMap2: (forall x y, 
      (StepFfoldProp x /\ StepFfoldProp y)
   <->(StepFfoldProp (conjl^@> x))). <@> y))).
unfold Map2.
induction x using StepF_ind. rapply StepFfoldPropMap'. 
intro y. set (H0:=IHx1 (SplitL y o)). set (H1:=IHx2 (SplitR y o)).
rewrite MapGlue.
rewrite <- (StepFfoldPropglue y o).
 do 2 rewrite StepFfoldPropglue_rew. revert H0 H1. 
do 2 intro. rewrite ApGlue. rewrite StepFfoldPropglue_rew. intuition.
Qed.
*)
(*
Lemma StepF_le_pos:forall x y, 
 (StepF_le x y) 
  <-> (StepFfoldProp 
  (Map ((fun (q:QS)=>(0>=q)):QS-->iffSetoid) 
  ((Qminus:QS-->QS-->QS) ^@> x <@> y))).
intros. unfold StepF_le. apply StepFfoldProp_morphism.
apply Map_morphism; auto with *.
clear A x y.
intros w w' x x' H HH. rewrite H. rewrite HH. clear H HH. auto with *.
split. intro. rewrite Qle_minus_iff in *.
replace RHS with (x0+-w) by ring. assumption.
intro H. rewrite Qle_minus_iff in *. 
replace RHS with (0+ - (w -x0)) by ring. assumption.
Qed.
*)

Lemma flipQleQge:(extEq (QS-->iffSetoid) (flip QgeS) QleS).
intros x y. simpl. auto with *.
Qed.
(*
Lemma StepF_le_ge:forall x y, 
 (StepF_le x y) <-> (StepFfoldProp (QgeS ^@> y <@> x)).
(* How to formulate this using flip*)
intros. unfold StepF_le.
apply StepFfoldProp_morphism.
transitivity (((flip (Map (Ap QgeS))) ^@> x) <@> y).
apply Ap_wd;auto with *. apply Map_wd;auto with *. apply flipQleQge. 
rewrite Ap_commutative.
2:apply (@Map2switch Prop iff Qle).
Qed.
*)
Definition Map3 X Y Z W (f:X --> Y --> Z --> W) a b c := f ^@> a <@> b <@> c.

Definition Map4 X Y Z W V (f:X --> Y --> Z --> W --> V) a b c d := f ^@> a <@> b <@> c <@> d.
(*
Definition Map5(X Y Z W V U:Type):=fun (f:X->Y->Z->W->V->U) (x:StepF X) (y:StepF Y) (z:StepF Z) (w:StepF W)(v:StepF V)=>
   (App (Map4 (fun x y z w=>(f x y z w)) x y z w) v).

Axiom Map4Map2Map2Map2:forall (X Y Z W V U UU:Type),
forall  (f:X->Y->U)(g:Z->W->V)(h:U->V->UU) 
(x:StepF X) (y:StepF Y) (z:StepF Z) (w:StepF W),
(Map2 h (Map2 f x y) (Map2 g z w))=
(Map4 (fun x y z w => (h (f x y) (g z w))) x y z w).

*)

Definition imp0:Prop->iffSetoid-->iffSetoid.
intro A.
exists (fun B:Prop=>(A->B)).
abstract (simpl; intuition).
Defined.

Definition imp:iffSetoid-->iffSetoid-->iffSetoid.
exists imp0.
abstract (simpl; unfold extEq; simpl; intuition).
Defined.

Definition StepF_imp (f g:StepF iffSetoid):Prop:=
(StepFfoldProp (imp ^@> f <@> g)).

Lemma StepF_imp_imp:forall x y:(StepF iffSetoid),
  (StepF_imp x y) ->
  ((StepFfoldProp x)->(StepFfoldProp y)).
induction x using StepF_ind. induction y  using StepF_ind.
   auto with *.
  unfold StepF_imp. unfold StepFfoldProp;simpl;intuition.
intros y.
unfold StepF_imp, Map2. arw.
intros.
rewrite <- (StepFfoldPropglue y o). arw. intuition. 
Qed.

Lemma StepF_le_trans:forall x y z, 
 (StepF_le x y)-> (StepF_le y z) ->(StepF_le x z).
intros x y z. unfold StepF_le.
intros H.
apply StepF_imp_imp.
revert H.
rapply StepF_imp_imp.
unfold StepF_imp.
pose (f:= ap
(compose (@ap _ _ _) (compose (compose (compose (@compose _ _ _) imp)) QleS))
(compose (flip (compose (@ap _ _ _) (compose (compose imp) QleS))) QleS)).
cut (StepFfoldProp (f ^@> x <@> y <@> z)).
 unfold f.
 arw.
 repeat rewrite Ap_Map.
 tauto.
apply StepFfoldPropForall_Map3.
intros a b c Hab Hbc.
clear f.
simpl in *.
eauto with qarith.
Qed.

Lemma L1ball_refl : forall e x, (L1Ball e x x).
Proof.
Lemma StepF_le_trans:forall x y z, 
 (StepF_le x y)-> (StepF_le y z) ->(StepF_le x z).
intros x y z. unfold StepF_le.
intros H.
apply StepF_imp_imp.

Lemma L1ball_refl : forall e x, (L1Ball e x x).
Proof.
intros e x.
unfold L1Ball, Distance.
assert (StepF_eq (QminusS ^@> x <@> x) (leaf (0:QS))).
 induction x using StepF_ind.
  change (x - x==0).
  ring.
 aw. 
 rapply glue_StepF_eq; auto with *.
unfold L1Norm.
rewrite H. 
compute. 
intro C. inversion C.
Qed.



Lemma L1_is_MetricSpace : 
 (is_MetricSpace (@StepF_eq QS) L1Ball).
split.
     apply (StepF_Sth QS).
    rapply L1ball_refl.
   (*Symm*)
   (* define a new function |x-y|  ???*)
   unfold symmetric. intros.
   assert (StepF_eq (Map QabsS (QminusS ^@> x <@> y)) 
           (Map QabsS (QminusS ^@> y <@> x))).
    do 2 rewrite MapMap2.
    assert (Map2 (fun x0 y0 : Q => Qabs (x0 - y0)) x y ===
Map2 (fun y0 x0 : Q => Qabs (x0 - y0)) x y).
    apply (Map2_morphism Q_Setoid Q_Setoid Q_Setoid); try apply (StepF_eq_refl Q_Setoid). 
    intros. rewrite H0. rewrite H1. reflexivity.
    intros.
    assert (H2:forall x' y', x'-y' == -(y'-x')). intros; ring. rewrite H2.
    apply Qabs_opp. rewrite H0. rapply Map2switch.
    unfold L1Ball, Distance, L1Norm. rewrite <- H0. exact H.
  (* Trans*)
  do 5 intro. unfold L1Ball, Distance, L1Norm. intros.
  assert (IntegralQ (Map Qabs (Map2 Qminus a b))+
         IntegralQ (Map Qabs (Map2 Qminus b c)) >=
         IntegralQ (Map Qabs (Map2 Qminus a c))).
   clear -c. rewrite Integral_linear.  do 2 rewrite MapMap2.
   cut (forall x y z o, x<=y->x<=z->x<=(o*y+(1-o)*z)).
   intro HH.
   assert (intpos:forall x y:(StepF Q), 
         (StepF_le x y)->(IntegralQ x <= IntegralQ y)).
    induction x.
     unfold StepF_le, IntegralQ. simpl. 
      induction y. simpl. auto with *.
      simpl. intros [H H1]. apply HH; auto with *.
     intro y. unfold StepF_le, IntegralQ. simpl. fold IntegralQ.
      assert (rew:IntegralQ y==IntegralQ (glue o (fst (Split y o)) (snd (Split y o)))). apply IntegralQ_mor. 
      (* This is broken rewrite glueSplit should work*) 
      change (y === glue o (SplitL y o) (SplitR y o)).
      (* something like unfold StepQ_eq.*)
      rapply (StepF_eq_sym Q_Setoid).
      apply (glueSplit Q_Setoid). 
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
   Focus 4.
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
