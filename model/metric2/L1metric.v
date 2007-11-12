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

Lemma Qdec_eq_ind: forall a b:Q, forall P:{a<b}+{b<a}+{a==b}->Type,
 a==b-> (forall H, (P (inright _ H)))->forall x, (P x).
intros a b P H H1 [[H2|H2]|H2].
  elim (Qlt_not_le _ _ H2); auto with*.
  (* Need to prove a==b -> b<=a*)
  setoid_replace (a:Q) with (b:Q); auto with *.
 elim (Qlt_not_le _ _ H2); auto with*.
auto with *.
Qed.

Lemma Map2glue(X Y Z:Type): forall f:X->Y->Z, forall o s1 s2 s3 s4,
   (Map2 f (glue o s1 s2) (glue o s3 s4))=(glue o (Map2 f s1 s3) (Map2 f s2 s4))
.
intros. simpl.
elim (Q_dec o o) using Qdec_eq_ind; simpl; auto with *.
Qed.

Section Equivalence1.
Variable X:Type.
Variable Xeq:X->X->Prop.
Hypothesis Xst:(Setoid_Theory X Xeq).
Variable Y:Type.
Variable Yeq:Y->Y->Prop.
Hypothesis Yst:(Setoid_Theory Y Yeq).

Hint Resolve (Seq_trans X Xeq Xst) (Seq_sym X Xeq Xst) (Seq_refl X Xeq Xst):starith.
Notation "x === y" := (StepF_eq Xeq x y) (at level 60).

Add Setoid X Xeq Xst as Xth.

Hint Unfold StepFfoldProp StepFfold StepF_eq.

Definition App(X Y:Type):(StepF (X->Y))->(StepF X)->(StepF Y):=
fun f  s=> (Map2 (fun f x =>(f x)) f s).

Lemma Appglue: forall o (f:StepF (X->Y)) g s t,
(StepF_eq Yeq (App (glue o f g) (glue o s t))
                                            (glue o (App f s) (App g t))).
unfold App. intros. rewrite <- Map2glue. apply (StepF_eq_refl Yst).
Qed.

Variable Z:Type.
Variable Zeq:Z->Z->Prop.
Hypothesis Zst:(Setoid_Theory Z Zeq).

Lemma Map2_morphism: forall f g,
 (forall x x' y y', (Xeq x x')->(Yeq y y')->
    (Zeq (f x y) (g x' y')))->
  forall x x' y y', (StepF_eq Xeq x x')->(StepF_eq Yeq y y')->
 (StepF_eq Zeq (Map2 f x y) (Map2 g x' y')).
Admitted.
(* Seems awkward to prove. 
intros. revert H1.
induction x.
simpl. intro H1.
*)
End Equivalence1.

Hint Resolve StepF_eq_refl.

Section Equivalence2.
Variable X:Type.
Variable Xeq:X->X->Prop.
Hypothesis Xst:(Setoid_Theory X Xeq).

Hint Resolve (Seq_trans X Xeq Xst) (Seq_sym X Xeq Xst) (Seq_refl X Xeq Xst) Xst:starith.
Notation "x === y" := (StepF_eq Xeq x y) (at level 60).

Hint Resolve StepF_eq_symm StepF_eq_trans.

Lemma StepF_Sth : (Setoid_Theory (StepF X) (StepF_eq Xeq)).
split; intros; eauto.
Qed.
Add Setoid (StepF X) (StepF_eq Xeq) StepF_Sth as StepF_th.

Variable Y:Type.
Variable Yeq:Y->Y->Prop.
Hypothesis Yst:(Setoid_Theory Y Yeq).
Variable Z:Type.
Variable Zeq:Z->Z->Prop.
Hypothesis Zst:(Setoid_Theory Z Zeq).

(* Note the  Leibniz equality*)
Lemma MapMap2 (Y Z:Type): forall (f:Z->Z) (g:X->Y->Z) (x:StepF X) (y:StepF Y), 
  Map f (Map2 g x y)= (Map2 (fun x y => (f (g x y))) x y).
induction x. simpl. induction y.
  simpl; auto with *.
 simpl. rewrite IHy1. rewrite IHy2. auto with *.
simpl. intro y. destruct (Split y o) as [L R].
simpl. rewrite IHx1. rewrite IHx2. auto with *.
Qed.

Lemma Map2Map2Map2 (Y Z:Type): 
  forall (f:Z->Z->Z) (g:X->Y->Z) (h:X->Y->Z) 
          (x:StepF X) (y:StepF Y), 
  (Map2 f (Map2 g x y) (Map2 h x y))
  = (Map2 (fun x y => (f (g x y) (h x y))) x y).
induction x. simpl. induction y.
  simpl; auto with *.
 simpl.
 rewrite <-IHy1. rewrite <-IHy2.
 rapply Map2glue.
intro y. simpl. destruct (Split y o) as [L R].
rewrite <- IHx1. rewrite <- IHx2. apply Map2glue.
Qed.

Lemma glueSplit:
  forall (x : StepF X) (o : OpenUnit),
  (StepF_eq Xeq (glue o (fst (Split x o)) (snd (Split x o))) x).
intros.
unfold StepF_eq. simpl. destruct (Split x o) as [L R].
simpl.
split; eapply StepF_eq_refl; eauto.
Qed.

End Equivalence2.
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

Hint Resolve (StepF_eq_symm Q_Setoid) :starith.
Add Setoid (StepF Q) (StepF_eq Qeq) (StepF_Sth Q_Setoid) as StepFQ_Setoid.
Lemma leafglue:forall x o s t, (leaf x)===(glue o s t)->
  ((leaf x)===s)/\((leaf x)===t).
intros.
assert ((leaf x)===(glue o (fst (Split (leaf x) o)) (snd (Split (leaf x) o)))).
apply (StepF_eq_symm Q_Setoid Q_Setoid Q_Setoid).
apply (glueSplit Q_Setoid).
simpl in H0.
assert ((glue o s t)===(glue o (leaf x) (leaf x))).
transitivity (leaf x); auto with *. (* This should be removed*) apply (StepF_eq_symm Q_Setoid Q_Setoid Q_Setoid). auto with *. 
auto with *.
Qed.

Lemma glue_eq1:forall o x y x1 y1,
(glue o x y)===(glue o x1 y1) -> (x===x1).
intros.
cut (fst (Split (glue o x y) o)===(fst (Split (glue o x1 y1) o) )).
do 2 rewrite Splitglue.
simpl. auto with *.
rapply (SplitL_resp_Xeq Q_Setoid); auto with *.
Qed.

Lemma glue_eq2:forall o x y x1 y1,
(glue o x y)===(glue o x1 y1) -> (y===y1).
intros.
cut (snd (Split (glue o x y) o)===(snd (Split (glue o x1 y1) o) )).
do 2 rewrite Splitglue.
simpl. auto with *.
rapply (SplitR_resp_Xeq Q_Setoid); auto with *.
Qed.

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

Add Morphism IntegralQ 
  with signature   (StepF_eq Qeq) ==>  Qeq
 as IntegralQ_mor.
unfold IntegralQ.
induction x1.
intros x2 H. simpl. induction x2.
  simpl.  auto with *.
 set (a:=leafglue H); destruct a as [H0 H1].
 simpl. rewrite <- (IHx2_1 H0). rewrite <- (IHx2_2 H1).
 ring.
intros x2 H. simpl. rewrite (IHx1_1 (fst (Split x2 o))).
(* bug ?*)
destruct  H as [H0 H1] using (glue_eq_ind Qeq);auto with *.
rewrite (IHx1_2 (snd (Split x2 o))).
destruct  H as [H0 H1] using (glue_eq_ind Qeq);auto with *.
clear -o.
fold IntegralQ.
(*Should be a lemma?*)
revert o. rename x2 into x. induction x.
simpl. unfold IntegralQ. simpl. intros. ring.
simpl. intro p. destruct (Q_dec p o) as [[H|H]| H].
  simpl.   (*This should be improved*) unfold IntegralQ; simpl; fold IntegralQ. 
  rewrite <-(IHx1 (OpenUnitDiv p o H)). destruct (Split x1 (OpenUnitDiv p o H)) as [L R]; simpl.
  unfold IntegralQ; simpl; fold IntegralQ. field; auto with *. (*why does this not work*)
  simpl. unfold IntegralQ; simpl; fold IntegralQ. 
  rewrite <-(IHx2 (OpenUnitDualDiv p o H)). destruct (Split x2 (OpenUnitDualDiv p o H)) as [L R]; simpl.
  unfold IntegralQ; simpl; fold IntegralQ. field; auto with *.
  simpl.  (*This should be improved*) unfold IntegralQ; simpl; fold IntegralQ. rewrite H. auto with *.
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
Lemma L1_is_MetricSpace : (is_MetricSpace (StepF_eq Qeq)  L1Ball).
split.
     apply (StepF_Sth Q_Setoid).
    intros e x. unfold L1Ball. unfold Distance. 
    assert ((Map2 Qminus x x)===(leaf 0)).
    induction x. unfold Map2. simpl. 
    assert (H:forall x y, x==y-> leaf x===leaf y).
    intros. unfold StepF_eq. simpl. auto with *.
    apply H. change (x-x) with (x+-x). apply Qplus_opp_r. (* why is this not in the hints database*)
    simpl.  elim (Q_dec o o) using Qdec_eq_ind; simpl; auto with *. intro H. clear H.
    apply glue_StepF_eq; auto with *.
    unfold L1Norm. 
    assert (H0:(Map Qabs (Map2 Qminus x x)) === (Map Qabs (leaf 0))). apply (Map_resp_StepF_eq Q_Setoid); auto with *. exact Q_Setoid.
      exact Qabs_wd. rewrite  H0. simpl. unfold IntegralQ. simpl. auto with *.
   intro. unfold symmetric, L1Ball, Distance, L1Norm. intros.
   (*Symm*)
   (* define a new function |x-y|  ???*)
   assert (((Map Qabs (Map2 Qminus x y))===(Map Qabs (Map2 Qminus y x)))).
    do 2 rewrite MapMap2.
    assert (Map2 (fun x0 y0 : Q => Qabs (x0 - y0)) x y ===
Map2 (fun y0 x0 : Q => Qabs (x0 - y0)) x y).
    apply (Map2_morphism Qeq Qeq); try apply (StepF_eq_refl Q_Setoid). 
    intros. rewrite H0. rewrite H1.
    assert (H2:x'-y' == -(y'-x')). ring. rewrite H2.
    apply Qabs_opp. rewrite H0. apply Map2switch.
    rewrite <- H0. exact H.
  (* Trans*)
  do 5 intro. unfold L1Ball, Distance, L1Norm. intros.
  assert (IntegralQ (Map Qabs (Map2 Qminus a b))+
         IntegralQ (Map Qabs (Map2 Qminus b c)) <=
         IntegralQ (Map Qabs (Map2 Qminus a c))).
   clear -c. rewrite Integral_linear.  do 2 rewrite MapMap2.
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
assert (forall a b : Q, (forall e : Qpos,  e a b) -> a == b).
(*intros.
rsapply cg_inv_unique_2.
rsapply AbsSmall_approach_zero.
intros.
rewrite <- (QposAsmkQpos H0).
apply (H (mkQpos H0)).*)
Qed.

Add Morphism Qball with signature QposEq ==> Qeq ==> Qeq ==> iff as Qball_wd.
intros [x1 Hx1] [x2 Hx2] H x3 x4 H0 x5 x6 H1.
unfold Qball.
unfold AbsSmall.
simpl.
rewrite H0.
rewrite H1.
unfold QposEq in H.
simpl in H.
rewrite H.
tauto.
Qed.

Definition Q_as_MetricSpace : MetricSpace :=
Build_MetricSpace Qball_wd Q_is_MetricSpace.

Canonical Structure Q_as_MetricSpace.

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