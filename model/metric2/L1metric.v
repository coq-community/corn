Require Import StepFunction.
Require Import OpenUnit.
Require Import QArith.
Require Import QMinMax.
Require Import Qabs.
Require Import CornTac.

Set Implicit Arguments.

Lemma PropST:(Setoid_Theory Prop iff).
split; intuition.
Qed.

Add Setoid (StepF Prop) (StepF_eq iff) (StepF_Sth PropST) as StepF_thProp.

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

Axiom App_mor2:forall f x y, (StepF_eq Yeq x y)-> 
 (StepF_eq Yeq (App f x) (App f y)).

Axiom AppMapMap:
   forall (f:Y->(Y->Y)) (g:Y->(Y->Y)) x y z, 
 (StepF_eq Yeq (App (Map f y) (App (Map g x) z)) 
        (App (Map (fun x y=> (f x) ((g x) y)) x) z)).

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


Axiom Map2switch: forall f s t,
 (Map2 f s t ===
Map2 (fun y x : Q => (f x y)) t s).

End Equivalence1.

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
Add Setoid (StepF Z) (StepF_eq Zeq) (StepF_Sth  Zst) as StepF_thZ.
Add Setoid (StepF Y) (StepF_eq Yeq) (StepF_Sth Yst) as StepF_thY.

Lemma Map2Map: forall f:X->Y->Z, forall g,
    (forall x x' y y', (Xeq x x') -> (Yeq y y'-> (Zeq (f x y) (g x' y'))))
  -> forall s t, (StepF_eq Zeq (Map2 f s t) 
   (App (Map (fun x =>(g x)) s) t)).
Admitted.
(*
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

End Equivalence3.

Section L1metric.

Definition StepQ := (StepF Q).
Definition StepQ_eq : StepQ -> StepQ -> Prop := (StepF_eq Qeq).

Notation "x === y" := (StepQ_eq x y) (at level 60).
Lemma Qball_dec : forall e a b, {L1Ball e a b}+{~L1Ball e a b}.
intros e a b.
unfold L1Ball.
set (d:=Distance a b).
destruct (Qlt_le_dec_fast e d) as [Hdc|Hdc].
right. abstract auto with *.
left. exact Hdc.
Defined.
Require Import QArith_base.

Add Setoid (StepQ) (StepQ_eq) (StepF_Sth Q_Setoid) as StepQ_Setoid.

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

Lemma IntegralSplit : forall (o:OpenUnit) x, 
 IntegralQ x ==
 o * IntegralQ (SplitL x o) + (1 - o) * IntegralQ (SplitR x o).
Proof.
intros o x.
revert o.
induction x.
unfold IntegralQ. simpl. intros. ring.
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
  with signature  StepQ_eq ==>  Qeq
 as IntegralQ_mor.
unfold IntegralQ.
induction x1.
intros x2 H. simpl. induction x2.
  simpl.  auto with *.
 simpl.
 destruct H as [H0 H1] using (eq_glue_ind Q_Setoid).
 rewrite <- IHx2_1; auto with *.
 rewrite <- IHx2_2; auto with *.
 ring.
intros x2 H.
destruct H as [H0 H1] using (glue_eq_ind Qeq).
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

Lemma Integral_linear:forall s t,
  (IntegralQ s)+(IntegralQ t)==(IntegralQ (Map2 Qplus s t)).
Proof.
induction s.
 induction t.
  reflexivity.
 unfold IntegralQ; simpl; fold IntegralQ.
 rewrite <- IHt1.
 rewrite <- IHt2.
 change (IntegralQ (leaf x)) with x.
 ring.
intros t.
rewrite Map2Glue.
unfold IntegralQ; simpl; fold IntegralQ.
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
Definition StepF_le:=(fun x y=>(StepFfoldProp (Map2 Qle x y))).

Lemma StepF_le_refl:forall x, (StepF_le x x).
unfold StepF_le. induction x.
 simpl. auto with *.
rewrite Map2GlueGlue. auto with *.
Qed.

Lemma StepFfoldPropglue_rew:(forall o x y, (StepFfoldProp (glue o x y))<->((StepFfoldProp x)/\StepFfoldProp y)).
auto with *.
Qed.

Lemma StepFfoldPropMap: (forall b x, 
      (StepFfoldProp x /\ b)
   <->(StepFfoldProp (Map (fun a  => a /\ b ) x))).
induction x.
 split.
  intro H. simpl. auto with *.
 simpl. auto with *.
simpl. do 2 rewrite StepFfoldPropglue_rew. intuition.
Qed. 

Lemma StepFfoldPropMap': (forall a x, 
      (a /\ StepFfoldProp x)
   <->(StepFfoldProp (Map (fun b  => a /\ b ) x))).
induction x.
 split.
  intro H. simpl. auto with *.
 simpl. auto with *.
simpl. do 2 rewrite StepFfoldPropglue_rew. intuition.
Qed.

Lemma StepFfoldPropMap2: (forall x y, 
      (StepFfoldProp x /\ StepFfoldProp y)
   <->(StepFfoldProp (Map2 (fun a b => a /\ b ) x y))).
induction x. simpl. apply StepFfoldPropMap'. 
intro y. set (H0:=IHx1 (SplitL y o)). set (H1:=IHx2 (SplitR y o)).
rewrite <- (StepFfoldPropglue y o).
 do 2 rewrite StepFfoldPropglue_rew. revert H0 H1. 
unfold SplitL, SplitR. simpl. destruct (Split y o) as [L R]. simpl.
do 2 intro. rewrite StepFfoldPropglue_rew. intuition.
Qed.

Lemma StepF_le_pos:forall x y, (StepF_le x y) <-> (StepFfoldProp (Map (fun q=>(0>=q)) (Map2 Qminus x y))).
intros. unfold StepF_le. apply StepFfoldProp_morphism.
rewrite MapMap2.
apply (Map2_morphism Q_Setoid PropST Q_Setoid); auto with *.
clear x y.
intros w w' x x' H HH. rewrite H. rewrite HH. clear H HH. auto with *.
split. intro. rewrite Qle_minus_iff in *.
replace RHS with (x0+-w) by ring. assumption.
intro H. rewrite Qle_minus_iff in *. 
replace RHS with (0+ - (w -x0)) by ring. assumption.
Qed.

Lemma StepF_le_ge:forall x y, (StepF_le x y) <-> (StepFfoldProp (Map2 Qge y x)).
intros. unfold StepF_le. 
apply StepFfoldProp_morphism.
apply (@Map2switch Prop iff Qle).
Qed.

Definition Map3(X Y Z W:Type):=fun (f:X->Y->Z->W) (x:StepF X) (y:StepF Y) (z:StepF Z) =>
   (App (Map2 (fun x y=>(f x y)) x y) z).

Definition Map4(X Y Z W V:Type):=fun (f:X->Y->Z->W->V) (x:StepF X) (y:StepF Y) (z:StepF Z) (w:StepF W)=>
   (App (Map3 (fun x y z=>(f x y z)) x y z) w).

Definition Map5(X Y Z W V U:Type):=fun (f:X->Y->Z->W->V->U) (x:StepF X) (y:StepF Y) (z:StepF Z) (w:StepF W)(v:StepF V)=>
   (App (Map4 (fun x y z w=>(f x y z w)) x y z w) v).

Axiom Map4Map2Map2Map2:forall (X Y Z W V U UU:Type),
forall  (f:X->Y->U)(g:Z->W->V)(h:U->V->UU) 
(x:StepF X) (y:StepF Y) (z:StepF Z) (w:StepF W),
(Map2 h (Map2 f x y) (Map2 g z w))=
(Map4 (fun x y z w => (h (f x y) (g z w))) x y z w).

Axiom Map5Map3Map2Map2: forall (Xf Yf Zf Wf Xg Yg Zg Zh:Type),
forall  (f:Xf->Yf->Zf->Wf)(g:Xg->Yg->Zg)(h:Wf->Zg->Zh) 
(xf:StepF Xf) (yf:StepF Yf) (zf:StepF Zf) 
(xg:StepF Xg) (yg:StepF Yg),
(Map2 h (Map3 f xf yf zf) (Map2 g xg yg))=
(Map5 (fun a b c d e => (h (f a b c) (g d e))) xf yf zf xg yg).

Lemma Map4Map32(X Y Z W:Type):forall (f:X->Y->Y->Z->W) 
(x:StepF X) (y:StepF Y) (z:StepF Z) ,
(Map4 f x y y z)=(Map3 (fun x y z=> (f x y y z)) x y z).
Admitted.

Axiom Map5Map1435: forall (X Y Z W:Type),
forall  (f:X->Y->Z->X->Z->W)
(x:StepF X) (y:StepF Y) (z:StepF Z) ,
((Map5 (fun a b c d e => (f a b c d e)) x y z x z)=
(Map3 (fun a b c => (f a b c a c)) x y z)).

Definition StepF_imp (f g:StepF Prop):Prop:=
(StepFfoldProp (Map2 (fun A B:Prop=>(A->B)) f g)).

Lemma StepF_imp_imp:forall x y:(StepF Prop),
  (StepF_imp x y) ->
  ((StepFfoldProp x)->(StepFfoldProp y)).
induction x. induction y.
   auto with *.
  unfold StepF_imp. simpl. unfold StepFfoldProp;simpl;intuition.
intros y H0.
unfold StepF_imp in H0. simpl in H0.
destruct (Split y o) using (Split_ind y o).
destruct H0 as [H0l H0r].
change ((StepFfoldProp x1 /\ StepFfoldProp x2) -> StepFfoldProp y).
intros [HH HH0]. rewrite <- (StepFfoldPropglue y o).
split. 
apply (IHx1 (SplitL y o)); auto with *.
apply (IHx2 (SplitR y o)); auto with *.
Qed.

Lemma StepF_le_trans:forall x y z, (StepF_le x y)-> (StepF_le y z) ->(StepF_le x z).
intros x y z. unfold StepF_le.
intros H H0.
assert (StepFfoldProp (Map2 (fun a b : Prop => a /\ b) 
        (Map2 Qle x y) (Map2 Qle y z))).
rewrite <- StepFfoldPropMap2;intuition.
clear H0 H.
assert (H:StepFfoldProp
       (Map2 (fun a b : Prop => a /\ b) (Map2 Qle x y) (Map2 Qle y z))
    -> StepFfoldProp (Map2 Qle x z)); auto.
clear H1.
apply StepF_imp_imp.
rewrite Map4Map2Map2Map2.
unfold StepF_imp.
rewrite Map4Map32.
rewrite Map5Map3Map2Map2.
rewrite Map5Map1435.
assert (StepF_eq iff 
(Map3 (fun a b c : Q => a <= b <= c -> a <= c) x y z)
(Map3 (fun a b c : Q => True) x y z)).
unfold Map3.
unfold App.
eapply (Map2_morphism Q_Setoid PropST).
Focus 6. (*Still seems difficult.*)
Admitted.

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

Lemma L1_is_MetricSpace : (is_MetricSpace (StepF_eq Qeq)  L1Ball).
split.
     apply (StepF_Sth Q_Setoid).
    rapply L1ball_refl.
   (*Symm*)
   (* define a new function |x-y|  ???*)
   unfold symmetric. intros.
   assert (((Map Qabs (Map2 Qminus x y))===(Map Qabs (Map2 Qminus y x)))).
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