Require Export Metric.
Require Import QArith.
Require Import CornTac.
Require Import Qauto.
Require Import Qabs.
Require Import QMinMax.

Set Implicit Arguments.
Record OpenUnit:={OpenUnitasQ:> Q;
OpenUnitprf:0<OpenUnitasQ/\OpenUnitasQ<1}.

Inductive StepF(X:Type):Type:=
|leaf:X->(StepF X)
|glue:OpenUnit->(StepF X)->(StepF X)->(StepF X).

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
Definition test1:=(leaf 1). 
Definition test2:=(glue (ou 1/2) (leaf 0) (leaf 1)).

Definition Map(X Y:Type):(X->Y)->(StepF X)->(StepF Y).
fix 4. intros X Y f [x| a t1 t2].
 exact (leaf (f x)).
exact (glue a (Map _ _ f t1) (Map _ _ f t2)).
Defined.

Implicit Arguments Map [X Y].

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

Implicit Arguments Split [X].

Definition Map2 (X Y Z:Type):
  (X->Y->Z)->(StepF X)-> (StepF Y) -> (StepF Z).
fix 5. 
intros X Y Z f s t.
destruct s as [x | b t1 t2].
exact (Map (f x) t).
destruct (Split t b) as [L R].
exact (glue b (Map2 X Y Z f t1 L) (Map2 X Y Z f t2 R)).
Defined.

Implicit Arguments Map2 [X Y Z].

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

 Hint Resolve Mapglue Mapleaf:starith.
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

Hint Resolve (Seq_trans X Xeq Xst) (Seq_sym X Xeq Xst) (Seq_refl X Xeq Xst):starith.
Notation "x === y" := (StepF_eq Xeq x y) (at level 60).

Add Setoid X Xeq Xst as Xth.

Hint Resolve splitmap fstsplitmap sndsplitmap:starith.
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
Qed.

End Equivalence1.

Hint Resolve StepF_eq_refl.

Section Equivalence2.
Variable X:Type.
Variable Xeq:X->X->Prop.
Hypothesis Xst:(Setoid_Theory X Xeq).

Hint Resolve (Seq_trans X Xeq Xst) (Seq_sym X Xeq Xst) (Seq_refl X Xeq Xst) Xst:starith.
Notation "x === y" := (StepF_eq Xeq x y) (at level 60).

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

Hint Resolve splitmap fstsplitmap sndsplitmap StepFfoldPropglue:starith.
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

Lemma leaf_eq:forall x y, (leaf x)===(leaf y)->(Xeq x y).
intros. auto with *.
Qed.
Hint Resolve leaf_eq:starith.

Axiom PropST:(Setoid_Theory Prop iff).

Axiom StepF_eq_trans:forall x y z : StepF X, (x === y) -> y === z -> x === z.

(* This should be a reduction but apparently isn't*)
Lemma StepFfoldPropglue2: forall o x y,
 (StepFfoldProp (glue o x y))<->((StepFfoldProp x)/\(StepFfoldProp y)).
intros.
unfold StepFfoldProp. simpl. intuition.
Qed.

Hint Resolve (Seq_trans X Xeq Xst) (Seq_sym X Xeq Xst) (Seq_refl X Xeq Xst):starith.
Hint Resolve StepFfoldPropglue2:starith.

Axiom pair_split_resp_eq_fst :
  forall x y o, x===y ->
  (fst (Split x o) === fst (Split y o)).

Axiom pair_split_resp_eq_snd :
  forall x y o, x===y ->
  (snd (Split x o) === snd (Split y o)).

Lemma Splitglue(X:Type): forall x y:StepF X, forall o, 
  (Split (glue o x y) o)=(x,  y).
intros. simpl.
 elim (Q_dec o o) using Qdec_eq_ind; simpl; auto with *.
Qed.

Lemma glue_resp_StepF_eq:forall x x' y y' o,
  (x===x')->(y===y')->
  (glue o x y)===(glue o x' y').
intros.
unfold StepF_eq.
simpl.
 elim (Q_dec o o) using Qdec_eq_ind; simpl; auto with *.
 intro HH. clear HH. rewrite StepFfoldPropglue2.
intuition.
Qed.

Hint Resolve pair_split_resp_eq_fst pair_split_resp_eq_snd
Splitglue glue_resp_StepF_eq:starith.

Lemma StepF_eq_symm:forall y x: StepF X, StepF_eq Xeq x y -> StepF_eq Xeq y x.
intros y. induction y.
 unfold StepF_eq. simpl. intro x0. induction x0. 
  unfold StepFfoldProp. simpl. auto with *. 
 simpl. repeat rewrite StepFfoldPropglue2. intuition auto with *.
intros x H.
pose (H0:=(pair_split_resp_eq_fst _ _  o H)).
rewrite Splitglue in H0. simpl in H0.
pose (H1:=(pair_split_resp_eq_snd _ _  o H)).
rewrite Splitglue in H1. simpl in H1.
eapply StepF_eq_trans.
apply (glue_resp_StepF_eq _ _ _ _ o (IHy1 _ H0) (IHy2 _ H1)).
(* The following should be a lemma.*)
clear -x Xst. apply glueSplit_eq. auto with *.
Qed.

Hint Resolve StepF_eq_symm StepF_eq_trans:starith.

Lemma StepF_Sth : (Setoid_Theory (StepF X) (StepF_eq Xeq)).
split; intros; auto with *.
eapply StepF_eq_trans;eauto.
Qed.
Add Setoid (StepF X) (StepF_eq Xeq) StepF_Sth as StepF_th.

(*
We seem to need even more conditions
Variable Y:Type.
Variable Yeq:Y->Y->Prop.
Hypothesis Yst:(Setoid_Theory Y Yeq).
Add Setoid Y Yeq Yst as Yth.

Lemma StepFfold_morphism:forall f g, 
  (forall x y, (Xeq x y)->((Yeq (f x) (f y)))) ->
  (forall o o' y1 y2 y1' y2', 
    (o==o'->(Yeq y1 y1')->(Yeq y2 y2')->
      (Yeq (g o y1 y2) (g o y1 y2))))->
  forall s t:(StepF X),
  (StepF_eq Xeq s t) ->
  (Yeq (StepFfold f g s) (StepFfold f g t)).
induction s. induction t.
  simpl;auto with *.
 intro H1. assert (((leaf x)===t1)/\(leaf x)===t2); auto with *.
 destruct H2 as [H2 H3]. simpl. 
 transitivity (g o (StepFfold f (fun x : OpenUnit => g x) (leaf x)) (StepFfold f (fun x : OpenUnit => g x) (leaf x))) .
 simpl.
rewrite <- (IHt1 H2). auto with *.
 unfold StepF_eq. simpl. rewrite StepFfoldPropglue2.
 intros [H1  H2]. intuition auto with *.
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
Qed.*)

End Equivalence2.

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
apply (StepF_eq_symm Q_Setoid).
apply (glueSplit_eq Q_Setoid).
simpl in H0.
assert ((glue o s t)===(glue o (leaf x) (leaf x))).
transitivity (leaf x); auto with *. 
auto with *.
Qed.

Lemma glue_eq1:forall o x y x1 y1,
(glue o x y)===(glue o x1 y1) -> (x===x1).
intros.
cut (fst (Split (glue o x y) o)===(fst (Split (glue o x1 y1) o) )).
do 2 rewrite Splitglue.
simpl. auto with *.
apply pair_split_resp_eq_fst; auto with *.
Qed.

Lemma glue_eq2:forall o x y x1 y1,
(glue o x y)===(glue o x1 y1) -> (y===y1).
intros.
cut (snd (Split (glue o x y) o)===(snd (Split (glue o x1 y1) o) )).
do 2 rewrite Splitglue.
simpl. auto with *.
apply pair_split_resp_eq_snd; auto with *.
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

Notation "'SplitL' s o":= (fst (Split s o)) (at level 100, no associativity).
Notation "'SplitR' s o":= (snd (Split s o)) (at level 100, no associativity).
Axiom glue_eq_ind: forall s1 s2 s a (P:Prop),
   (s1 === ( fst (Split  s a ))  -> 
   s2 === (snd (Split s a)) -> P) ->
  (glue a s1 s2 === s) -> P.

Add Morphism IntegralQ 
  with signature   (StepF_eq Qeq) ==>  Qeq
 as L1Norm_mor.
unfold IntegralQ.
induction x1.
intros x2 H. simpl. induction x2.
  simpl.  auto with *.
 set (a:=leafglue H); destruct a as [H0 H1].
 simpl. rewrite <- (IHx2_1 H0). rewrite <- (IHx2_2 H1).
 ring.
intros x2 H. simpl. rewrite (IHx1_1 (fst (Split x2 o))).
(* bug ?*)
destruct  H as [H0 H1] using glue_eq_ind;auto with *.
rewrite (IHx1_2 (snd (Split x2 o))).
destruct  H as [H0 H1] using glue_eq_ind;auto with *.
clear -o.
fold IntegralQ.
(*Should be a lemma?*)
revert o. rename x2 into x. induction x.
simpl. unfold IntegralQ. simpl. intros. ring.
simpl. intro p. destruct (Q_dec p o) as [[H|H]| H].
  simpl.   (*This should be improved*) unfold IntegralQ; simpl; fold IntegralQ. 
  rewrite <-(IHx1 (OpenUnitDiv p o H)). destruct (Split x1 (OpenUnitDiv p o H)) as [L R]; simpl.
  unfold IntegralQ; simpl; fold IntegralQ. ring. (*why does this not work*)
ETC.


Lemma L1_is_MetricSpace : (is_MetricSpace (StepF_eq Qeq)  L1Ball).
split.
     apply StepF_Sth. exact Q_Setoid.
    intros e x. unfold L1Ball. unfold Distance. 
    assert ((Map2 Qminus x x)===(leaf 0)).
    induction x. unfold Map2. simpl. 
    assert (H:forall x y, x==y-> leaf x===leaf y).
    intros. unfold StepF_eq. simpl. auto with *.
    apply H. change (x-x) with (x+-x). apply Qplus_opp_r. (* why is this not in the hints database*)
    simpl.  elim (Q_dec o o) using Qdec_eq_ind; simpl; auto with *. intro H. clear H.
    apply StepF_eq_aux; auto with *.
    unfold L1Norm. rewrite H.



(*
simpl.
apply AbsSmall_wdr with 0.
apply (zero_AbsSmall _ (e:Q)).
apply less_leEq.
apply Qpos_prf.
simpl; ring.
intros e x y. 
unfold Qball.
rsapply AbsSmall_minus.
intros [e1  He1] [e2 He2] a b c H1 H2.
unfold Qball.
apply AbsSmall_wdr with ((a-b)+(b-c)).
autorewrite with QposElim.
rsapply AbsSmall_plus; assumption.
simpl; ring.
intros e a b H.
unfold Qball.
assert (forall x, (forall d : Qpos, x <= e+d) -> x <= e).
intros.
rsapply shift_zero_leEq_minus'.
rsapply inv_cancel_leEq.
rsapply approach_zero_weak.
intros.
replace LHS with (x[-](e:Q)).
rsapply shift_minus_leEq.
replace RHS with (e+e0) by ring.
rewrite <- (QposAsmkQpos H1).
apply (H0 (mkQpos H1)).
unfold cg_minus; simpl; ring.
split.
rsapply inv_cancel_leEq.
replace RHS with (e:Q) by ring.
apply H0.
intros.
destruct (H d).
rsapply inv_cancel_leEq.
replace RHS with (a-b) by ring.
destruct e; destruct d; apply H1.
apply H0.
intros d.
destruct (H d).
destruct e; destruct d; apply H2.
intros.
rsapply cg_inv_unique_2.
rsapply AbsSmall_approach_zero.
intros.
rewrite <- (QposAsmkQpos H0).
apply (H (mkQpos H0)).
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