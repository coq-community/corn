Require Export Metric.
Require Import QArith.
Require Import CornTac.
Require Import Qauto.
Require Import Qabs.
Require Import QMinMax.

Set Implicit Arguments.
Record OpenUnit:={OpenUnitasQ:> Q;
OpenUnitprf:0<OpenUnitasQ/\OpenUnitasQ<1}.

Notation "'ou' x":=(@Build_OpenUnit x (conj (refl_equal Lt) (refl_equal Lt))) (at level 60, no associativity).
Require Import Qordfield.
Require Import COrdFields.
Definition OpenUnitMult (a b:OpenUnit):OpenUnit.
intros a b.
exists (a * b).
abstract(destruct a as [a [Ha0 Ha1]]; destruct b as [b [Hb0 Hb1]];
split; simpl;
 [rsapply mult_resp_pos; assumption
 |change (1:Q) with (1*1);
 rsapply mult_resp_less_both;auto with *]).
Defined.

(* x^(n+1) *)
Definition Powern:OpenUnit->nat->OpenUnit.
fix 2.
intro x. destruct 1 as [| n].
 exact x.
exact (OpenUnitMult x (Powern x n)).
Defined.

Definition half:=(ou 1/2).

Definition OpenUnitDiv (a b:OpenUnit):(a<b)->OpenUnit.
intros a b p.
exists (a/b).
abstract (destruct a as [a [Ha0 Ha1]]; destruct b as [b [Hb0 Hb1]];
split; simpl;[
 apply Qlt_shift_div_l; auto; ring_simplify;  auto|
 apply Qlt_shift_div_r; auto; ring_simplify;  auto]).
Defined.

Definition OpenUnitDual (a:OpenUnit):OpenUnit.
intros a.
exists (1-a).
abstract (destruct a as [a [Ha0 Ha1]];
simpl; split; rewrite  Qlt_minus_iff in *;[
(replace RHS with (1+-a) by ring); auto|
(replace RHS with (a+-0) by ring); auto]).
Defined.

Eval compute in (ou (1/2)).
Eval compute in (OpenUnitDual (ou (1/2))):Q.

Definition OpenUnitMinus (b a:OpenUnit):(a<b)->OpenUnit.
intros b a p.
exists (b-a).
abstract (destruct a as [a [Ha0 Ha1]]; destruct b as [b [Hb0 Hb1]];
split; simpl;simpl in p;
rewrite  Qlt_minus_iff in *;[
(replace RHS with (b+-a) by ring); auto|
(replace RHS with ((1+-b)+(a+-0)) by ring); Qauto_pos]).
Defined.

(*1/4<1/2*)
Lemma quarter_lt_half:(Powern (ou 1/2) (S O))<(ou 1/2).
compute; auto.
Defined.

Eval compute in (OpenUnitMinus (ou 1/2) (Powern (ou 1/2) (S O)) quarter_lt_half):Q.

(* (b-a)/(1-a) *)
Definition OpenUnitAux (b a:OpenUnit):(a<b)->OpenUnit.
intros b a p.
exists ((b-a)/(1-a)).
abstract(destruct a as [a [Ha0 Ha1]]; destruct b as [b [Hb0 Hb1]];
split; simpl;simpl in p;
[ apply Qlt_shift_div_l;
 [rewrite  Qlt_minus_iff in *; (replace RHS with (1+-a) by ring); auto
 |rewrite  Qlt_minus_iff in *; ring_simplify; auto]
| apply Qlt_shift_div_r;
 [rewrite Qlt_minus_iff in *; (replace RHS with (1+-a) by ring); auto
 |rewrite Qlt_minus_iff in *; ring_simplify; (replace RHS with (1-b) by ring); auto]]).
Defined.

Eval compute in (OpenUnitAux (ou 1/2) (Powern (ou 1/2) (S O)) quarter_lt_half):Q.
 
Inductive StepF(X:Type):Type:=
|leaf:X->(StepF X)
|glue:OpenUnit->(StepF X)->(StepF X)->(StepF X).

Definition test1:=(leaf 1). 
Definition test2:=(glue (ou 1/2) (leaf 0) (leaf 1)).

Definition Map(X Y:Type):(X->Y)->(StepF X)->(StepF Y).
fix 4. intros X Y f [x| a t1 t2].
 exact (leaf (f x)).
exact (glue a (Map _ _ f t1) (Map _ _ f t2)).
Defined.

Definition Split (X:Type): (StepF X)-> OpenUnit -> ((StepF X)*(StepF X)).
fix 2.
intros X s a.
destruct s as [x | b t1 t2].
 exact (leaf x , leaf x).

destruct (Q_dec a b) as [[H|H]|H].
   destruct (Split X t1 (OpenUnitDiv a b H)) as [L R].
  exact (L, (glue (OpenUnitAux b a H) R t2)).
  destruct (Split X t2 (OpenUnitAux a b H)) as [L R].
  refine ((glue (OpenUnitDiv b a H) t1 L), R).
  exact (t1,t2).
Defined.

Eval compute in (Split test2 (ou 1/4)).

Definition SplitL (X:Type) (s:StepF X) (o:OpenUnit) : (StepF X) :=
fst (Split s o).

Definition SplitR (X:Type) (s:StepF X) (o:OpenUnit) : (StepF X) :=
snd (Split s o).

Definition Map2 (X Y Z:Type):
  (X->Y->Z)->(StepF X)-> (StepF Y) -> (StepF Z).
fix 5. 
intros X Y Z f s t.
destruct s as [x | b t1 t2].
exact (Map (f x) t).
destruct (Split t b) as [L R].
exact (glue b (Map2 X Y Z f t1 L) (Map2 X Y Z f t2 R)).
Defined.

Definition StepFfold:=
(*
fix 5.
intros X Y f g s.
 destruct s as [x | b t1 t2].
 exact (f x).
 exact (g b (StepFfold X Y f g t1) (StepFfold X Y f g t2)).
Defined.*)
fix StepFfold (X Y : Type) (f : X -> Y) (g : OpenUnit -> Y -> Y -> Y)
              (s : StepF X) {struct s} : Y :=
  match s with
  | leaf x => f x
  | glue b t1 t2 => g b (StepFfold X Y f g t1) (StepFfold X Y f g t2)
  end.

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

Require Import Setoid.
Section Equivalence.
Variable X:Type.
Variable Xeq:X->X->Prop.
Hypothesis Xst:(Setoid_Theory X Xeq).
Hint Resolve (Seq_trans X Xeq Xst) (Seq_sym X Xeq Xst) (Seq_refl X Xeq Xst):foo.
Print Setoid_Theory.

Definition StepFfoldProp:=StepFfold (fun x => x ) (fun _ a b => a /\ b ).

Definition StepF_eq (f g:StepF X):Prop:=
( StepFfoldProp (Map2 Xeq f g)).
(*
Fixpoint StepFfoldProp (s : StepF Prop) {struct s} : Prop :=
  match s with
  | leaf x => x
  | glue _ t1 t2 => (StepFfoldProp t1)/\ (StepFfoldProp t2)
  end.

Definition StepF_eq (f g:StepF X):Prop:=
( (fix StepFfoldProp (s : StepF Prop) {struct s} : Prop :=
  match s with
  | leaf x => x
  | glue _ t1 t2 => (StepFfoldProp t1)/\ (StepFfoldProp t2)
  end) (Map2 Xeq f g)).
*)

Hint Unfold StepFfoldProp StepFfold StepF_eq.
Lemma Qdec_eq_ind: forall a b:Q, forall P:{a<b}+{b<a}+{a==b}->Type,
 a==b-> (forall H, (P (inright _ H)))->forall x, (P x).
intros a b P H H1 [[H2|H2]|H2].
  elim (Qlt_not_le _ _ H2); auto with*.
  (* Need to prove a==b -> b<=a*) 
  setoid_replace (a:Q) with (b:Q); auto with *.
 elim (Qlt_not_le _ _ H2); auto with*.
auto with *.
Qed.

Notation "x === y" := (StepF_eq x y) (at level 100).

Lemma StepF_eq_refl:forall x : StepF X, x === x.
intro s.
induction s.
compute. apply Seq_refl; auto.
unfold StepF_eq. simpl. elim (Q_dec o o) using Qdec_eq_ind; simpl; auto with *.
Qed.

Hint Resolve StepF_eq_refl:sfarith.

Print Setoid_Theory.
Lemma glue_resp_Qeq:forall s t:StepF X, forall a b:OpenUnit, a==b -> (StepF_eq (glue a s t) (glue b s t)).
intros s t a b H.
unfold StepF_eq; simpl.
elim (Q_dec a b) using Qdec_eq_ind;auto with *.
intros H1.
change ((StepF_eq s s) /\ (StepF_eq t t)); auto with *.
Qed.

Lemma StepF_eq_aux:forall s s1 s2, forall a, (StepF_eq s1 (fst (Split s a))) -> (StepF_eq s2 (snd (Split s a))) ->(StepF_eq (glue a s1 s2) s).
intros s s1 s2 a. unfold StepF_eq. simpl. 
intros.
destruct (Split s a) as [s3 s4].
simpl in *. auto with *.
Qed.



Hint Resolve StepF_eq_aux glue_resp_Qeq:starith.
Lemma glueSplit_eq:forall s:StepF X, forall a:OpenUnit, 
 (glue a (fst (Split s a)) (snd (Split s a))) === s.
auto with *.
Qed.

Lemma Mapleaf(Y:Type): forall f:X->Y, 
  forall x, (Map f (leaf x))=(leaf (f x)).
 simpl;auto.
Qed.

Lemma Mapglue(Y:Type): forall f:X->Y, (forall o s1 s2, ((Map f (glue o s1 s2))=(glue o (Map f s1) (Map f s2)))).
 simpl;auto.
Qed.

 Hint Resolve Mapglue Mapleaf:foo.
Lemma splitmap(Y:Type):forall x:(StepF X), forall a, forall f:X->Y, 
    (Split (Map f x) a) = let (l,r) := Split x a in (Map f l,Map f r).
intros Y s. induction s. simpl; auto.
intros a f.
rewrite Mapglue. simpl. destruct (Q_dec a o) as [[H0|H0]|H0].
rewrite IHs1. destruct (Split s1 (OpenUnitDiv a o H0)). auto with *. 
rewrite IHs2. destruct (Split s2 (OpenUnitAux a o H0)). auto with *. 
auto.
Qed.

Lemma fstsplitmap(Y:Type): forall x:(StepF X), forall a, forall f:X->Y, 
    fst (Split (Map f x) a) = Map f (fst (Split x a)).
intros. rewrite splitmap. destruct (Split x a). simpl. auto.
Qed.

Lemma sndsplitmap(Y:Type): forall x:(StepF X), forall a, forall f:X->Y, 
    snd (Split (Map f x) a) = Map f (snd (Split x a)).
intros. rewrite splitmap. destruct (Split x a). simpl. auto.
Qed.

End  Equivalence.
Section Equivalence1.
Variable X:Type.
Variable Xeq:X->X->Prop.
Hypothesis Xst:(Setoid_Theory X Xeq).
Variable Y:Type.
Variable Yeq:Y->Y->Prop.
Hypothesis Yst:(Setoid_Theory Y Yeq).

Hint Resolve (Seq_trans X Xeq Xst) (Seq_sym X Xeq Xst) (Seq_refl X Xeq Xst):foo.
Notation "x === y" := (StepF_eq Xeq x y) (at level 60).
Print StepF_eq.

Add Setoid X Xeq Xst as Xth.

Hint Resolve splitmap fstsplitmap sndsplitmap:foo.
Hint Unfold StepFfoldProp StepFfold StepF_eq.
Lemma map_resp_StepF_eq: forall f:X->Y, 
    (forall x y, (Xeq x y)-> (Yeq (f x) (f y))) ->
    forall s t:(StepF X), (s === t) -> (StepF_eq Yeq (Map f s) (Map f t)).
intros f H.

induction s. induction t.
  unfold StepF_eq;simpl;auto with *. 
 rewrite Mapglue. rewrite Mapleaf. 
 unfold StepF_eq. unfold StepFfoldProp. simpl;  intuition.
simpl. intros t H0.
unfold StepF_eq in H0. simpl in H0.
unfold StepF_eq. simpl.
rewrite splitmap. destruct ( Split t o) as [L R].
destruct H0 as [H1 H2]. split. apply IHs1. apply H1.
apply IHs2. apply H2.

(*
assert ((glue o s1 s2) ===
  (glue o (fst (Split t o)) (snd (Split t o)))).
 generalize H0. unfold StepF_eq;simpl.
 elim (Q_dec o o) using Qdec_eq_ind;auto with *.
 destruct (Split t o). simpl. intuition. 

apply StepF_eq_aux. 
 rewrite fstsplitmap.
 apply IHs1.
 generalize H1. unfold StepF_eq;simpl.
 elim (Q_dec o o) using Qdec_eq_ind;auto with *;simpl; intuition.
rewrite sndsplitmap.
apply IHs2.
generalize H1. unfold StepF_eq;simpl.
elim (Q_dec o o) using Qdec_eq_ind;auto with *;simpl; intuition.
*)
Qed.
(*
Lemma leaf_eq:forall x y:X, (leaf x===leaf y) -> (Xeq x y).
auto with *.
Qed.

Lemma leaf_eq':forall x y:X, (Xeq x y) -> (leaf x===leaf y).
auto with *.
Qed.
*)
End Equivalence1.

Hint Resolve StepF_eq_refl.

Section Equivalence2.
Variable X:Type.
Variable Xeq:X->X->Prop.
Hypothesis Xst:(Setoid_Theory X Xeq).
Add Setoid X Xeq Xst as Xth1.

Hint Resolve (Seq_trans X Xeq Xst) (Seq_sym X Xeq Xst) (Seq_refl X Xeq Xst):foo.
Notation "x === y" := (StepF_eq Xeq x y) (at level 60).

(* Add Setoid X Xeq Xst as Xth.*)
Lemma StepFfoldPropglue:forall y o,
 StepFfoldProp (glue o (fst (Split y o)) (snd (Split y o))) <->
StepFfoldProp y.
induction y.
  unfold StepF_eq, StepFfoldProp.
  simpl; tauto.
simpl.
intro o0.
destruct (Q_dec o0 o) as [[H|H]|H].
   generalize (IHy1 (OpenUnitDiv o0 o H)).
   destruct (Split y1 (OpenUnitDiv o0 o H)) as [l r].
   simpl.
   change ((StepFfoldProp l /\StepFfoldProp r <-> StepFfoldProp y1) ->
(StepFfoldProp l /\ StepFfoldProp r /\ StepFfoldProp y2 <->
  StepFfoldProp y1 /\ StepFfoldProp y2)).
   tauto.
  generalize (IHy2 (OpenUnitAux o0 o H)).
  destruct (Split y2 (OpenUnitAux o0 o H)) as [l r].
  simpl.
  change ((StepFfoldProp l /\StepFfoldProp r <-> StepFfoldProp y2) ->
((StepFfoldProp y1 /\ StepFfoldProp l) /\ StepFfoldProp r <->
  StepFfoldProp y1 /\ StepFfoldProp y2)).
  tauto.
simpl.
reflexivity.
Qed.

Hint Resolve splitmap fstsplitmap sndsplitmap StepFfoldPropglue:foo.
Lemma StepFfoldProp_morphism:forall x y:(StepF Prop),
  (StepF_eq iff x y) ->
  ((StepFfoldProp x)<->(StepFfoldProp y)).
induction x. induction y.
   auto with *.
  unfold StepF_eq. simpl. unfold StepFfoldProp;simpl;intuition.
intros y H0.
unfold StepF_eq in H0. simpl in H0.
transitivity (StepFfoldProp ((glue o (fst (Split y o)) (snd (Split y 
o))))).
  change ((StepFfoldProp x1 /\ StepFfoldProp x2) <->
  ((StepFfoldProp (fst (Split y o)) /\ (StepFfoldProp (snd (Split y 
o)))))).
  destruct (Split y o) as [l r].
  destruct H0 as [H0l H0r].
  rewrite (IHx1 l); try assumption.
  rewrite (IHx2 r); try assumption.
  simpl.
  tauto.
auto with *.
Qed.

(*
The next goal:

Lemma Split_morphism1: forall o a b, a === b ->
   (fst (Split a o)) === (fst (Split b o)).
intros o a b H.
 unfold Split. destruct  (Q_dec o o0) as [[H1 | H2]  | H3]; auto with *.

  Not clear how to continue


End Equivalence2.

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
Hint Resolve (Seq_trans X Xeq Xst) (Seq_sym X Xeq Xst) (Seq_refl X Xeq Xst):foo.
Hint Resolve (Seq_trans Y Yeq Yst) (Seq_sym Y Yeq Yst) (Seq_refl Y Yeq Yst):foo.
Lemma Map2_morphism2:forall f, (forall x x' y y',
  (Xeq x x) -> (Yeq y y')-> (Zeq (f x y) (f x' y'))) ->
  forall s t t', (StepF_eq Yeq t t') ->
  (StepF_eq Zeq (Map2 f s t) (Map2 f s t')).
intros f H.
induction t. induction t'. 
   unfold StepF_eq. simpl. unfold StepFfoldProp. simpl.
   intro Hxx0. induction s.
    simpl. auto with *.
    simpl.  elim (Q_dec o o) using Qdec_eq_ind;simpl;auto with *.
 intro. 
 Does not seem like fun.

simpl in H0.
 split; auto with *.
    apply IHs1.
simpl.
   unfold Map2; simpl. auto with *.
  unfold StepF_eq. simpl. unfold StepFfoldProp;simpl;intuition.
intros y H0.
unfold StepF_eq in H0. simpl in H0.
transitivity (StepFfoldProp ((glue o (fst (Split y o)) (snd (Split y 
o))))).
  change ((StepFfoldProp x1 /\ StepFfoldProp x2) <->
  ((StepFfoldProp (fst (Split y o)) /\ (StepFfoldProp (snd (Split y 
o)))))).
  destruct (Split y o) as [l r].
  destruct H0 as [H0l H0r].
  rewrite (IHx1 l); try assumption.
  rewrite (IHx2 r); try assumption.
  simpl.
  tauto.
auto with *.
Qed.
*)

Axiom PropST:(Setoid_Theory Prop iff).

Lemma StepF_eq_trans:forall x y z : StepF X, (x === y) -> y === z -> x === z.
induction x. intros.
 unfold StepF_eq;simpl;auto with *.
  cut (StepFfoldProp (Map (Xeq x) y)); try auto.
 rewrite (StepFfoldProp_morphism (Map (Xeq x) y) (Map (Xeq x) z));try auto.
 apply (map_resp_StepF_eq Xst PropST); auto with *.
 intros x0 y0 Hx0y0. rewrite Hx0y0. intuition.
intros.
unfold StepF_eq. 
rewrite <- (StepFfoldProp_morphism (Map2 Xeq (glue o x1 x2) y) (Map2 Xeq (glue o x1 x2) z)).
2:auto with *.

fold StepFfoldProp.

revert H.
unfold StepF_eq. simpl. 
(*rewrite (StepFfoldProp_morphism (Map2 iff (Map2 Xeq (glue o x1 x2) y) (Map2 Xeq (glue o x1 x2) z))
                  ((Map2 Xeq (glue o x1 x2) z))).*)

destruct (Split y o). destruct (Split z o).
assert (forall ss tt, (StepFfoldProp (glue o ss tt))<-> (StepFfoldProp ss/\ StepFfoldProp tt)).
 unfold StepFfoldProp. simpl. intuition.
rewrite H. intros [H1 H2].
(* Should be a lemma?*)
 unfold StepF_eq. simpl.

Lemma StepF_eq_symm:forall x y : StepF X, StepF_eq x y -> StepF_eq y x.
intro s. unfold StepF_eq. induction s. 
 intros t. simpl. induction t. 
  simpl. auto with *. 
 simpl. intuition.
simpl. intro t. destruct t as [y | b t1 t2].


 destruct y  simpl. intuition.
induction y. simpl; intuition.

unfold Map2. destruct (Split t b). simpl. auto with *.


 unfold Map2. unfold StepFfold. simpl. intuition. clear H1. simpl. apply H0. intros.
*)
destruct t as [y | b t1 t2].
destruct s as [x | a s1 s2].

Lemma StepF_eq_trans:forall x y z : StepF X, StepF_eq x y -> StepF_eq y z -> StepF_eq x z.


Lemma StepFst: Setoid_Theory (StepF X) StepF_eq.


(* TODO:
setoid eq 
Is a metric space
Continuity of integration
Continuity of Map, Map2
Continuous functions are in the completion, i.e. there is an injection 
from continuous functions to integrable ones.
Integration is correct. Needs mesh. 

Write a tactic Done (auto with *, etc)
Find out how simple works with fold.
*)
