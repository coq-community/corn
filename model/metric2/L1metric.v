Require Import StepFunction.
Require Import OpenUnit.
Require Import QArith.
Require Import QMinMax.
Require Import Qabs.
Require Import CornTac.

Set Implicit Arguments.

Definition test1:=(leaf 1).
Definition test2:=(glue (ou 1/2) (leaf 0) (leaf 1)).

Definition Supnorm:(StepF Q)->Q:=(StepFfold Qabs (fun _=> Qmax)).
Eval compute in (Supnorm test2):Q.
Definition IntegralQ:(StepF Q)->Q:=(StepFfold (fun x => x) (fun b x y => (b*x+(1-b)*y))).
Eval compute in (IntegralQ test2):Q.
Definition L1Norm(f:StepF Q):Q:=(IntegralQ (Map Qabs f)).
Eval compute in (L1Norm test2):Q.
Definition Distance(f g:StepF Q):Q:=(L1Norm (Map2 Qminus f g)).
Eval compute in (Distance test1 test2):Q.
Eval compute in (Distance test2 test1):Q.
Definition L1Ball (e:Qpos)(f g:StepF Q):Prop:=(Distance f g)<=e.
Eval compute in (L1Ball (1#1)%Qpos test2 test1).
Definition Mesh (X:Type):(StepF X)->Q:=(StepFfold (fun x => 1)(fun b x y => (Qmax (b*x) ((1-b)*y)))).
Eval compute in (Mesh test2).

Section Equivalence1.
Variable X:Type.
Variable Xeq:X->X->Prop.
Hypothesis Xst:(Setoid_Theory X Xeq).
Variable Y:Type.
Variable Yeq:Y->Y->Prop.
Hypothesis Yst:(Setoid_Theory Y Yeq).

Notation "x === y" := (StepF_eq Xeq x y) (at level 60).

Add Setoid X Xeq Xst as Xth.

Hint Unfold StepFfoldProp StepFfold StepF_eq.

Definition App(X Y:Type):(StepF (X->Y))->(StepF X)->(StepF Y):=
fun f  s=> (Map2 (fun f => f) f s).

Lemma Appglue: forall o (f:StepF (X->Y)) g s t,
(StepF_eq Yeq (App (glue o f g) (glue o s t))
                                            (glue o (App f s) (App g t))).
unfold App. intros. rewrite Map2GlueGlue. apply (StepF_eq_refl Yst).
Qed.

Variable Z:Type.
Variable Zeq:Z->Z->Prop.
Hypothesis Zst:(Setoid_Theory Z Zeq).

(* Seems awkward to prove. 
intros. revert H1.
induction x.
simpl. intro H1.
*)
End Equivalence1.

(*
Section Equivalence3.
Variable X:Type.
Variable Xeq:X->X->Prop.
Hypothesis Xst:(Setoid_Theory X Xeq).
Variable Y:Type.
Variable Yeq:Y->Y->Prop.
Hypothesis Yst:(Setoid_Theory Y Yeq).
Variable Z:Type.
Variable Zeq:Z->Z->Prop.
Hypothesis Zst:(Setoid_Theory Z Zeq).

Hint Resolve (Seq_trans X Xeq Xst) (Seq_sym X Xeq Xst) (Seq_refl X Xeq Xst) Xst:starith.
Notation "x === y" := (StepF_eq Xeq x y) (at level 60).
Add Setoid (StepF Z) (StepF_eq Zeq) (StepF_Sth Zst Zst Zst) as StepF_thZ.
Add Setoid (StepF Y) (StepF_eq Yeq) (StepF_Sth Yst Yst Yst) as StepF_thY.


Lemma Map2Map: forall f:X->Y->Z, forall g,
    (forall x x' y y', (Xeq x x') -> (Yeq y y'-> (Zeq (f x y) (g x' y'))))
  -> forall s t, (StepF_eq Zeq (Map2 f s t) 
   (App (Map (fun x =>(g x)) s) t)).
intros f g fisg. induction s; simpl.
 intro t. unfold App. simpl. apply (map_resp_StepF_eq Yst Zst); auto with *.
intro t. 
 transitivity (App (glue o (Map (fun x : X => g x) s1) (Map (fun x : X => g x) s2)) ((glue o (fst (Split t o)) (snd (Split t o))))).
 destruct (Split t o) as [L R]. simpl. 
  elim (Q_dec o o) using Qdec_eq_ind; simpl; auto with *.
 intro H. clear H. rewrite (Appglue Zst o (Map (fun x : X => g x) s1) (Map (fun x : X => g x) s2)).
 eapply (glue_resp_StepF_eq Zst Zst Zst);auto with *.
unfold App. eapply Map2_morphism.
3: eapply (glueSplit Yst Yst Yst).
2:eapply StepF_eq_refl.

 setoid_replace t with ((glue o (fst (Split t o)) (snd (Split t o)))).


auto with *.

rewrite <-IHs1.

rewrite (Map2_morphism Xeq Yeq t).
rewrite <- (glueSplit_eq Yst t). 
*)

Section L1metric.

Notation "x === y" := (StepF_eq Qeq x y) (at level 60).
Lemma Qball_dec : forall e a b, {L1Ball e a b}+{~L1Ball e a b}.
intros e a b.
unfold L1Ball.
set (d:=Distance a b).
destruct (Qlt_le_dec_fast e d) as [Hdc|Hdc].
right. abstract auto with *.
left. exact Hdc.
Defined.
Require Import QArith_base.

Add Setoid (StepF Q) (StepF_eq Qeq) (StepF_Sth Q_Setoid) as StepFQ_Setoid.

(*
Lemma glueSplit1:forall o x0 x1 y, (glue o x0 x1)===y ->
 (x0 === fst (Split y o)) /\ (x1===snd (Split y o)).
intros.
assert ((glue o x0 x1)===(glue o (fst (Split y o)) (snd (Split y o)))).
transitivity y; auto with *. 
clear -y.
Focus 2. split. apply (glue_eq1 o x0 x1 (fst (Split y o)) (snd (Split y o)) H0).
 apply (glue_eq2 o x0 x1 (fst (Split y o)) (snd (Split y o)) H0).
*)
(*
Notation "'SplitL' s o":= (fst (Split s o)) (at level 100, no associativity).
Notation "'SplitR' s o":= (snd (Split s o)) (at level 100, no associativity).*)

Hint Resolve Q_Setoid.

Add Morphism IntegralQ 
  with signature   (StepF_eq Qeq) ==>  Qeq
 as IntegralQ_mor.
unfold IntegralQ.
induction x1.
intros x2 H. simpl. induction x2.
  simpl.  auto with *.
 simpl.
 symmetry in H.
 destruct H as [H0 H1] using (glue_eq_ind Qeq).
 rewrite <- IHx2_1; auto with *.
 rewrite <- IHx2_2; auto with *.
 ring.
intros x2 H.
destruct H as [H0 H1] using (glue_eq_ind Qeq).
simpl.
rewrite (IHx1_1 _ H0).
rewrite (IHx1_2 _ H1).
fold IntegralQ.
clear -o.
(*Should be a lemma?*)
revert o. rename x2 into x. induction x.
simpl. unfold IntegralQ. simpl. intros. ring.
intro p.
apply SplitLR_glue_ind; intros H.
  simpl.   (*This should be improved*) unfold IntegralQ; simpl; fold IntegralQ. 
  rewrite <-(IHx1 (OpenUnitDiv p o H)).
  unfold IntegralQ; simpl; fold IntegralQ. field; auto with *. (*why does this not work*)
 simpl. unfold IntegralQ; simpl; fold IntegralQ. 
 rewrite <-(IHx2 (OpenUnitDualDiv p o H)).
 unfold IntegralQ; simpl; fold IntegralQ. field; auto with *.
rewrite H.
reflexivity.
Qed.

(* 
Add Morphism Map
  with signature   (StepF_eq Qeq) ==>  Qeq
 as Map_mor.
Need to define equality on functions for this.

*)

Axiom Map2switch: forall f s t,
 (Map2 (fun x y : Q => (f x y)) s t ===
Map2 (fun y x : Q => (f x y)) t s).

Axiom Integral_linear:forall s t,
  (IntegralQ s)+(IntegralQ t)==(IntegralQ (Map2 Qplus s t)).
Require Import QMinMax.
Require Import COrdAbs.
Require Import Qordfield.
Require Import CornTac.

Print StepFfold.
Definition StepF_lt:=(fun x y=>(StepFfoldProp (Map2 Qlt x y))).

Lemma L1_is_MetricSpace : (is_MetricSpace (StepF_eq Qeq)  L1Ball).
split.
     apply (StepF_Sth Q_Setoid).
    intros e x. unfold L1Ball. unfold Distance. 
    assert ((Map2 Qminus x x)===(leaf 0)).
    induction x. unfold Map2. simpl. 
    assert (H:forall x y, x==y-> leaf x===leaf y).
    intros. unfold StepF_eq. simpl. auto with *.
    apply H. ring.
    rewrite Map2GlueGlue.
    apply glue_StepF_eq; auto with *.
    unfold L1Norm. 
    assert (H0:(Map Qabs (Map2 Qminus x x)) === (Map Qabs (leaf 0))). apply (Map_resp_StepF_eq Q_Setoid); auto with *.
      exact Qabs_wd. rewrite  H0. simpl. unfold IntegralQ. simpl. auto with *.
   intro. unfold symmetric, L1Ball, Distance, L1Norm. intros.
   (*Symm*)
   (* define a new function |x-y|  ???*)
   assert (((Map Qabs (Map2 Qminus x y))===(Map Qabs (Map2 Qminus y x)))).
    do 2 rewrite MapMap2.
    assert (Map2 (fun x0 y0 : Q => Qabs (x0 - y0)) x y ===
Map2 (fun y0 x0 : Q => Qabs (x0 - y0)) x y).
    apply (Map2_morphism Q_Setoid Q_Setoid Q_Setoid); try apply (StepF_eq_refl Q_Setoid). 
    intros. rewrite H0. rewrite H1. reflexivity.
    intros.
    assert (H2:forall x' y', x'-y' == -(y'-x')). intros; ring. rewrite H2.
    apply Qabs_opp. rewrite H0. apply Map2switch.
    rewrite <- H0. exact H.
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
      simpl. unfold StepFfoldProp. simpl. fold StepFfoldProp. intros [H H1].
      apply HH; auto with *.
     intro y. unfold StepF_lt, IntegralQ. simpl.
      destruct (Split y o) as [L R]. (*StepFfoldPropglue...*) fold IntegralQ.
      elim (Q_dec o o) using Qdec_eq_ind; simpl; auto with *. intro H. clear H.  
 rewrite StepFfoldPropglue2.
(* Should follow from f>=0, then int f>=0*)
(*     Focus 2. apply intpos. 
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