Require Export Metric.
Require Import QArith.
Require Import CornTac.
Require Import Qauto.
Require Import Qabs.
Require Import QMinMax.
(* TODO:
Define parition on (0,1)
This is a step function to the unit type.
Need to implement split(s,a) where a is in (0,1)
Define Map (s,f)
And StepF-rec
*)

Set Implicit Arguments.
Record OpenUnit:={OpenUnitasQ:> Q;
OpenUnitprf:0<OpenUnitasQ/\OpenUnitasQ<1}.

Inductive StepF(X:Type):Type:=
|leaf:X->(StepF X)
|glue:OpenUnit->(StepF X)->(StepF X)->(StepF X).

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

Definition OpenUnitMinus (b a:OpenUnit):(a<b)->OpenUnit.
intros b a p.
exists (b-a).
abstract (destruct a as [a [Ha0 Ha1]]; destruct b as [b [Hb0 Hb1]];
split; simpl;simpl in p;
rewrite  Qlt_minus_iff in *;[
(replace RHS with (b+-a) by ring); auto|
(replace RHS with ((1+-b)+(a+-0)) by ring); Qauto_pos]).
Defined.

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

Print OpenUnitDiv.
 
Definition Split (X:Type): (StepF X)-> OpenUnit -> ((StepF X)*(StepF X)).
fix 2.
intros X s a.
destruct s as [x | b t1 t2].
 exact (leaf x , leaf x).

destruct (Q_dec a b) as [[H|H]|H].
   destruct (Split X t1 (OpenUnitDiv a b H)) as [L R].
  exact ((glue (OpenUnitAux b a H) t1 L), R).
  destruct (Split X t2 (OpenUnitAux a b H)) as [L R].
  refine ((glue (OpenUnitDiv b a H) t1 L), R).
  exact (t1,t2).
Defined.

Implicit Arguments Split [X].

Definition Map2 (X Y Z:Type):(X->Y->Z)->(StepF X)-> (StepF Y) -> (StepF Z).
fix 5.
intros X Y Z f s t.
destruct s as [x | b t1 t2].
exact (Map (f x) t).
destruct (Split t b) as [L R].
exact (glue b (Map2 X Y Z f t1 L) (Map2 X Y Z f t2 R)).
Defined.

Implicit Arguments Map2 [X Y Z].

Print Map2.
(*
Definition IntegralQ:(StepF Q)->Q.
fix 1.
intro s.
destruct s as [x | b t1 t2].
 exact x.
exact ((b*(IntegralQ t1)+(1-b)*(IntegralQ t2))).
Defined.*)

Definition StepFfold(X Y:Type)(f:X->Y)(g:OpenUnit->Y->Y->Y):(StepF X)->Y.
fix 5.
intros X Y f g s.
 destruct s as [x | b t1 t2].
 exact (f x).
 exact (g b (StepFfold X Y f g t1) (StepFfold X Y f g t2)).
Defined.
(* Implicit Arguments StepFfold [X Y].*)

Definition Supnorm:(StepF Q)->Q:=(StepFfold Qabs (fun _=> Qmax)).
Definition IntegralQ:(StepF Q)->Q:=(StepFfold (fun x => x) (fun b x y => (b*x+(1-b)*y))).
Definition L1Norm(f:StepF Q):Q:=(IntegralQ (Map Qabs f)).
Definition Distance(f g:StepF Q):Q:=(L1Norm (Map2 Qminus f g)).

Definition L1Ball (e:Qpos)(f g:StepF Q):Prop:=(Distance f g)<=e.

Require Import Setoid.
Section Equivalence.
Variable X:Type.
Variable Xeq:X->X->Prop.
Hypothesis Xst:(Setoid_Theory X Xeq).

Definition StepF_eq (f g:StepF X):Prop:=
( StepFfold (fun x => x ) (fun _ a b => a /\ b ) (Map2 Xeq f g)).

Lemma StepF_eq_refl:forall x : StepF X, StepF_eq x x.
intro s.
induction s.
compute. apply Seq_refl; auto.
unfold StepF_eq. simpl. destruct (Q_dec o o) as [[H |H] |H]; try
(elim (Qlt_not_le _ _ H); auto with *). 
simpl. auto with *.
Qed.

Lemma StepF_eq_symm:forall x y : StepF X, StepF_eq x y -> StepF_eq y x.
intro s. unfold StepF_eq. induction s.
simpl. intros y H.
Assumed.
Lemma StepF_eq_trans:forall x y z : StepF X, StepF_eq x y -> StepF_eq y z -> StepF_eq x z




auto with *.

in *.


auto with *.

in *.
auto with *.

in *.
Lemma StepFst: Setoid_Theory (StepF X) StepF_eq.

(* TODO:
setoid eq 
Is a metric space
Continuity of integration
Cotinuity of Map, Map2
Continuous functions are in the completion, i.e. there is an injection 
from continuous functions to integrable ones.
Integration is correct.
*)