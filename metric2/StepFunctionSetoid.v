Require Export StepFunction.
Require Import OpenUnit.
Require Import CornTac.
Require Import Qauto.
Require Import Qordfield.
Require Import COrdFields.

Set Implicit Arguments.

Record Setoid: Type :=
{ st_car:>Type;
  st_eq:st_car-> st_car ->Prop;
  st_isSetoid: Setoid_Theory _ st_eq
}.

Add Setoid st_car st_eq st_isSetoid as genericSetoid.

Definition iffSetoid : Setoid.
exists Prop iff.
split; tauto.
Defined.

Section StepF_Functions.

Variable X:Setoid.

Definition StepF := StepF X.

Definition leaf : X -> StepF := (@leaf X).

Definition glue : OpenUnit -> StepF -> StepF -> StepF := (@glue X).

Lemma StepF_ind : forall (P : StepF -> Prop),
       (forall x : X, P (leaf x)) ->
       (forall (o : OpenUnit) (s : StepF),
        P s -> forall s0 : StepF, P s0 -> P (glue o s s0)) ->
       forall s : StepF, P s.
Proof.
intros P H0 H1 s.
induction s.
 rapply H0.
rapply H1; auto.
Qed.

Definition StepFfold  : forall Y, (X -> Y) -> (OpenUnit -> Y -> Y -> Y) -> StepF -> Y := (@StepFfold X).
Definition Mirror : StepF -> StepF := (@Mirror X).
Definition SplitL : StepF -> OpenUnit -> StepF := (@SplitL X).
Definition SplitR : StepF -> OpenUnit -> StepF := (@SplitR X).
End StepF_Functions.

Implicit Arguments leaf [X].

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

Open Local Scope sfstscope.

Definition Map (X Y:Setoid) : (X-->Y)->(StepF X)->(StepF Y) := (@Map X Y).
Implicit Arguments Map [X Y].
Notation "f ^@> x" := (Map f x) (at level 15, left associativity) : sfstscope.

Definition Ap (X Y:Setoid) : (StepF (X --> Y))->(StepF X)->(StepF Y) := fun f x => (@Ap X Y (StepFunction.Map (@evalMorphism X Y) f) x).
Notation "f <@> x" := (Ap f x) (at level 15, left associativity) : sfstscope.

Lemma MirrorGlue : forall (X : Setoid) (o : OpenUnit) (al ar : StepF X),
       Mirror (glue o al ar) = glue (OpenUnitDual o) (Mirror ar) (Mirror al).
Proof.
reflexivity.
Qed.

Lemma MapGlue : forall (X Y : Setoid) (f : (X --> Y))
         (o : OpenUnit) (al ar : StepF X),
       f ^@> (glue o al ar) = glue o (f ^@> al) (f ^@> ar).
Proof.
reflexivity.
Qed.

Lemma ApGlue : forall (X Y : Setoid) (fl fr : StepF (X --> Y))
         (o : OpenUnit) (b : StepF X),
       (glue o fl fr) <@> b = glue o (fl <@> (SplitL b o)) (fr <@> (SplitR b o)).
Proof.
intros X Y fl fr o b.
unfold Ap.
simpl (StepFunction.Map (@evalMorphism X Y) (glue o fl fr)).
rewrite ApGlue.
reflexivity.
Qed.

Lemma ApGlueGlue : forall (X Y : Setoid) (fl fr : StepF (X --> Y)) (o : OpenUnit) (l r : StepF X),
       (glue o fl fr) <@> (glue o l r) = glue o (fl <@> l) (fr <@> r).
Proof.
intros X Y fl fr o l r.
unfold Ap.
simpl (StepFunction.Map (@evalMorphism X Y) (glue o fl fr)).
unfold glue.
rewrite ApGlueGlue.
reflexivity.
Qed.

Lemma SplitLGlue : forall (X : Setoid) (x y : StepF X) (o : OpenUnit),
       SplitL (glue o x y) o = x.
Proof.
intros X.
exact (@SplitLGlue X).
Qed.

Lemma SplitRGlue : forall (X : Setoid) (x y : StepF X) (o : OpenUnit),
       SplitR (glue o x y) o = y.
Proof.
intros X.
exact (@SplitRGlue X).
Qed.

Lemma SplitLR_glue_ind : forall (X : Setoid) (s1 s2 : StepF X) (a b : OpenUnit)
         (P : StepF X -> StepF X -> Prop),
       (forall H : a < b,
        P (SplitL s1 (OpenUnitDiv a b H)) (glue (OpenUnitDualDiv b a H) (SplitR s1 (OpenUnitDiv a b H)) s2)) ->
       (forall H : b < a,
        P (glue (OpenUnitDiv b a H) s1 (SplitL s2 (OpenUnitDualDiv a b H))) (SplitR s2 (OpenUnitDualDiv a b H))) ->
       (a == b -> P s1 s2) -> P (SplitL (glue b s1 s2) a) (SplitR (glue b s1 s2) a).
Proof.
intros X.
exact (@SplitLR_glue_ind X).
Qed.

Lemma SplitL_glue_ind : forall (X : Setoid) (s1 s2 : StepF X) (a b : OpenUnit)
         (P : StepF X -> Prop),
       (forall H : a < b, P (SplitL s1 (OpenUnitDiv a b H))) ->
       (forall H : b < a, P (glue (OpenUnitDiv b a H) s1 (SplitL s2 (OpenUnitDualDiv a b H)))) -> 
       (a == b -> P s1) -> P (SplitL (glue b s1 s2) a).
Proof.
intros X.
exact (@SplitL_glue_ind X).
Qed.

Lemma SplitR_glue_ind : forall (X : Setoid) (s1 s2 : StepF X) (a b : OpenUnit)
         (P : StepF X -> Prop),
       (forall H : a < b, P (glue (OpenUnitDualDiv b a H) (SplitR s1 (OpenUnitDiv a b H)) s2)) ->
       (forall H : b < a, P (SplitR s2 (OpenUnitDualDiv a b H))) ->
       (a == b -> P s2) -> P (SplitR (glue b s1 s2) a).
Proof.
intros X.
exact (@SplitR_glue_ind X).
Qed.

Lemma SplitLMap : forall (X Y : Setoid) (x : StepF X) (a : OpenUnit) (f : X --> Y),
       SplitL (Map f x) a = Map f (SplitL x a).
Proof.
intros X Y x a f.
unfold Map, SplitL.
rewrite SplitLMap.
reflexivity.
Qed.

Lemma SplitRMap : forall (X Y : Setoid) (x : StepF X) (a : OpenUnit) (f : X --> Y),
       SplitR (Map f x) a = Map f (SplitR x a).
Proof.
intros X Y x a f.
unfold Map, SplitR.
rewrite SplitRMap.
reflexivity.
Qed.

Section EquivalenceA.
Variable X:Setoid.

Definition StepFfoldProp : StepF iffSetoid -> Prop := (StepFfold (X:=iffSetoid) (fun x => x ) (fun _ a b => a /\ b )).

Definition st_eqS0 : X -> X --> iffSetoid.
intros x.
exists (st_eq X x).
abstract (
intros x1 x2 Hx;
simpl;
rewrite Hx;
reflexivity).
Defined.

Definition st_eqS : X --> X --> iffSetoid.
exists (st_eqS0).
abstract (
intros x1 x2 Hx y;
simpl;
rewrite Hx;
reflexivity).
Defined.

Definition StepF_eq (f g:StepF X):Prop:=
(StepFfoldProp (st_eqS ^@> f <@> g)).

Notation "x === y" := (StepF_eq x y) (at level 70).

Lemma glue_StepF_eq:forall (s:StepF X) (s1 s2:StepF X), forall a, s1 === (SplitL s a) -> s2 === (SplitR s a) -> (glue a s1 s2) === s.
intros s s1 s2 a H0 H1.
unfold StepF_eq.
rewrite MapGlue.
rewrite ApGlue.
split; assumption.
Qed.

Lemma glue_eq_ind : forall (s1 s2 s:StepF X) a (P:Prop), (s1 === SplitL s a -> s2 === SplitR s a -> P) -> (glue a s1 s2 === s) -> P.
Proof.
intros s1 s2 s a P H H0.
unfold StepF_eq in *.
rewrite MapGlue in *.
rewrite ApGlue in H0.
destruct H0.
auto.
Qed.

Lemma StepF_eq_refl:forall x : StepF X, x === x.
induction x using StepF_ind.
 change (st_eq X x x).
 reflexivity.
apply glue_StepF_eq.
simpl; rewrite SplitLGlue; assumption.
simpl; rewrite SplitRGlue; assumption.
Qed.

Hint Resolve StepF_eq_refl.

Lemma StepF_Qeq_eq : forall (s t:StepF X), (StepF_Qeq s t) -> s === t.
Proof.
induction s using StepF_ind;
 induction t using StepF_ind;
  try contradiction; simpl.
 intros H.
 rewrite H.
 auto with *.
intros [H [H0 H1]].
apply glue_StepF_eq.
 apply IHs1.
 rapply SplitL_glue_ind; intros H2;
  try (elim (Qlt_not_le _ _ H2); rewrite H); auto with *.
apply IHs2.
rapply SplitR_glue_ind; intros H2;
 try (elim (Qlt_not_le _ _ H2); rewrite H); auto with *.
Qed.

Lemma glueSplit:forall (s : StepF X), forall a, (glue a (SplitL s a) (SplitR s a)) === s.
intros s a.
rapply glue_StepF_eq; auto with *.
Qed.

End EquivalenceA.

Hint Resolve StepF_eq_refl : sfarith.

Notation "x == y" := (StepF_eq x y) (at level 70) : sfstscope.

Section EquivalenceB.
Variable X Y:Setoid.

Lemma Map_resp_StepF_eq: forall f:X-->Y,
    (forall x y, (st_eq X x y)-> (st_eq Y (f x) (f y))) ->
    forall s t:(StepF X), s == t -> (Map f s) == (Map f t).
intros f H.
induction s using StepF_ind. induction t using StepF_ind.
  unfold StepF_eq, Map2, StepFfoldProp ;simpl;auto with *.
 unfold StepF_eq, Map2, StepFfoldProp. simpl;  intuition.
simpl. intros t H0.
unfold StepF_eq, Map2 in H0.
rewrite MapGlue in H0.
rewrite ApGlue in H0.
unfold StepF_eq, Map2.
repeat rewrite MapGlue.
rewrite ApGlue.
rewrite SplitLMap.
rewrite SplitRMap.
destruct H0 as [H0l H0R].
split.
 apply IHs1; auto.
apply IHs2; auto.
Qed.

End EquivalenceB.

Lemma StepFfoldPropglue:forall (y:StepF iffSetoid) o,
 StepFfoldProp (glue o (SplitL y o) (SplitR y o)) <-> StepFfoldProp y.
induction y using StepF_ind.
  unfold StepF_eq, StepFfoldProp.
  simpl; tauto.
simpl.
intro o0.
apply SplitLR_glue_ind; intros H.
  generalize (IHy1 (OpenUnitDiv o0 o H)).
  unfold StepFfoldProp; simpl; tauto.
 generalize (IHy2 (OpenUnitDualDiv o0 o H)).
 unfold StepFfoldProp; simpl; tauto.
simpl.
reflexivity.
Qed.

Lemma StepFfoldProp_morphism:forall x y:(StepF iffSetoid),
  (StepF_eq x y) ->
  ((StepFfoldProp x)<->(StepFfoldProp y)).
induction x using StepF_ind. induction y using StepF_ind.
   auto with *.
  unfold StepF_eq. simpl. unfold StepFfoldProp;simpl;intuition.
intros y H0.
unfold StepF_eq, Map2 in H0.
rewrite MapGlue in H0.
rewrite ApGlue in H0.
destruct H0 as [H0l H0r].
change ((StepFfoldProp x1 /\ StepFfoldProp x2) <-> StepFfoldProp y).
rewrite (IHx1 (SplitL y o)); auto with *.
rewrite (IHx2 (SplitR y o)); auto with *.
rapply StepFfoldPropglue.
Qed.


Section EquivalenceC.

Variable X:Setoid.

Hint Resolve StepF_Qeq_eq StepF_Qeq_refl SplitL_resp_Qeq SplitR_resp_Qeq.

Lemma StepF_eq_resp_Qeq : forall (s t : StepF X) u v, (StepF_Qeq s t) -> (StepF_Qeq u v) -> s == u -> t == v.
Proof.
induction s using StepF_ind; induction t using StepF_ind; try contradiction.
 intros u v Hst Huv Hsu.
 simpl in Hst.
 unfold StepF_eq in *.
 rewrite <- Hst.
 rewrite <- (StepFfoldProp_morphism ((st_eqS X) ^@> leaf x <@> u)); auto.
 rapply (Map_resp_StepF_eq); auto with *.
 intros a b Hab.
 simpl.
 rewrite Hab.
 reflexivity.
intros u v [H [Hst0 Hst1]] Huv Hsu.
destruct Hsu as [Hsu1 Hsu2] using (glue_eq_ind s1).
apply glue_StepF_eq.
 eapply IHs1.
   assumption.
  unfold SplitL; apply SplitL_resp_Qeq.
   apply H.
  apply Huv.
 assumption.
eapply IHs2.
  assumption.
 unfold SplitR; apply SplitR_resp_Qeq.
  apply H.
 apply Huv.
assumption.
Qed.

Lemma Mirror_eq_Mirror : forall (s t : StepF X), Mirror s == Mirror t <-> s == t.
Proof.
induction s using StepF_ind.
 induction t using StepF_ind; simpl.
  reflexivity.
 change (leaf x == (Mirror t2) /\ leaf x == (Mirror t1) <-> leaf x == t1 /\ leaf x == t2).
 tauto.
intros t.
rewrite MirrorGlue.
split; apply (@glue_eq_ind X); intros H0 H1.
 apply glue_StepF_eq.
  rewrite <- IHs1.
  eapply StepF_eq_resp_Qeq;[| |apply H1]; auto with *.
  apply StepF_Qeq_sym.
  rapply MirrorSplitL_Qeq; auto with *.
 rewrite <- IHs2.
 eapply StepF_eq_resp_Qeq;[| |apply H0]; auto with *.
 apply StepF_Qeq_sym.
 rapply MirrorSplitR_Qeq; auto with *.
apply glue_StepF_eq.
 apply StepF_eq_resp_Qeq with (Mirror s2) (Mirror (SplitR t o)); auto.
  rapply MirrorSplitR_Qeq; apply Qeq_refl.
 rewrite IHs2.
 assumption.
apply StepF_eq_resp_Qeq with (Mirror s1) (Mirror (SplitL t o)); auto.
 rapply MirrorSplitL_Qeq; apply Qeq_refl.
rewrite IHs1.
assumption.
Qed.

Lemma StepFfoldPropSplitL : 
 forall (s : StepF iffSetoid) a, StepFfoldProp s -> StepFfoldProp (SplitL s a).
Proof.
induction s; intros a H.
 assumption.
destruct H.
rapply SplitL_glue_ind; intros Hao.
  apply IHs1; assumption.
 split.
  assumption.
 apply IHs2.
 assumption.
assumption.
Qed.

Lemma SplitL_resp_Xeq : forall (s1 s2 : StepF X) a, s1 == s2 -> SplitL s1 a == SplitL s2 a.
Proof.
induction s1 using StepF_ind.
 intros s2 a H.
 unfold StepF_eq in *.
 change (StepFfoldProp ((st_eqS X x:X-->iffSetoid) ^@> SplitL s2 a)).
 rewrite <- SplitLMap.
 apply StepFfoldPropSplitL.
 assumption.
intros s2 a H.
destruct H using (glue_eq_ind s1_1).
apply SplitL_glue_ind; intros Hao.
  apply StepF_eq_resp_Qeq with (SplitL s1_1 (OpenUnitDiv a o Hao)) (SplitL (SplitL s2 o) (OpenUnitDiv a o Hao)); auto.
  rapply SplitLSplitL.
  simpl; field; auto with *.
 apply glue_StepF_eq.
  apply StepF_eq_resp_Qeq with s1_1 (SplitL s2 o); auto.
  apply StepF_Qeq_sym.
  rapply SplitLSplitL.
  simpl; field; auto with *.
 apply StepF_eq_resp_Qeq with (SplitL s1_2 (OpenUnitDualDiv a o Hao)) (SplitL (SplitR s2 o) (OpenUnitDualDiv a o Hao)); auto.
 rapply SplitLSplitR; simpl; field; auto with *.
apply StepF_eq_resp_Qeq with s1_1 (SplitL s2 o); auto with *.
rapply SplitL_resp_Qeq; auto.
symmetry.
assumption.
Qed.

Lemma SplitR_resp_Xeq : forall (s1 s2:StepF X) a, s1 == s2 -> SplitR s1 a == SplitR s2 a.
Proof.
intros s1 s2 a H.
pose (b:=OpenUnitDual a).
apply StepF_eq_resp_Qeq with (Mirror (SplitL (Mirror s1) b)) (Mirror (SplitL (Mirror s2) b)); 
 try (unfold Mirror, SplitR, SplitL, b;eapply StepF_Qeq_trans;[apply Mirror_resp_Qeq; apply StepF_Qeq_sym; apply MirrorSplitR_Qeq; reflexivity|apply MirrorMirror]).
rewrite Mirror_eq_Mirror.
apply SplitL_resp_Xeq.
rewrite Mirror_eq_Mirror.
assumption.
Qed.

Lemma StepF_eq_trans:forall x y z : StepF X, x == y -> y == z -> x == z.
induction x using StepF_ind. intros.
 unfold StepF_eq in *.
 set (A:=((st_eqS X:X-->X-->iffSetoid) ^@> leaf x)) in *.
 rewrite <- (StepFfoldProp_morphism (A <@> y)); auto with *.
 rapply (Map_resp_StepF_eq); auto with *.
 intros a b Hab.
 simpl.
 rewrite Hab.
 reflexivity.
intros.
destruct H using (glue_eq_ind x1).
apply glue_StepF_eq.
 eapply IHx1.
  apply H.
 apply SplitL_resp_Xeq.
 assumption.
eapply IHx2.
 apply H1.
apply SplitR_resp_Xeq.
assumption.
Qed.

Lemma glue_resp_StepF_eq:forall (x x' y y':StepF X) o,
  (x==x')->(y==y')->
  (glue o x y)==(glue o x' y').
intros.
unfold StepF_eq.
rewrite MapGlue.
rewrite ApGlueGlue.
split; assumption.
Qed.

Lemma StepF_eq_sym :forall x y: StepF X, x == y -> y == x.
intros x y.
revert x.
induction y using StepF_ind.
 unfold StepF_eq. simpl. intro x0. induction x0.
  unfold StepFfoldProp. simpl. intros. symmetry; assumption.
 simpl. unfold StepFfoldProp; simpl; intuition; auto with *.
intros x H.
assert (H0:=(SplitL_resp_Xeq _ _ o H)).
rewrite SplitLGlue in H0.
assert (H1:=(SplitR_resp_Xeq _ _ o H)).
rewrite SplitRGlue in H1.
apply glue_StepF_eq;auto with *.
Qed.

End EquivalenceC.

Add Relation StepF StepF_eq
 reflexivity proved by StepF_eq_refl
 symmetry proved by StepF_eq_sym
 transitivity proved by StepF_eq_trans
 as StepF_SetoidTheory.

Hint Resolve StepF_eq_sym StepF_eq_trans.

Lemma StepF_Sth (X:Setoid) : (Setoid_Theory (StepF X) (@StepF_eq X)).
split; intros; eauto with sfarith.
Qed.

Lemma glue_injl X :forall o (x y x1 y1:StepF X),
(glue o x y)==(glue o x1 y1) -> (x==x1).
intros.
destruct H as [H _] using (glue_eq_ind x).
rewrite SplitLGlue in H.
assumption.
Qed.

Lemma glue_injr X :forall o (x y x1 y1:StepF X),
(glue o x y)==(glue o x1 y1) -> (y==y1).
intros.
destruct H as [_ H] using (glue_eq_ind x).
rewrite SplitRGlue in H.
assumption.
Qed.

Lemma eq_glue_ind X : forall (s1 s2 s : StepF X) (a : OpenUnit) (P : Prop),
       ((SplitL s a) == s1 -> (SplitR s a) == s2 -> P) ->
       s == (glue a s1 s2) -> P.
Proof.
intros X s1 s2 s a P H H0.
symmetry in H0.
destruct H0 as [H0l H0r] using (glue_eq_ind s1).
symmetry in H0l, H0r.
auto.
Qed.

Lemma MirrorSplitR X : forall (s : StepF X) (a b : OpenUnit),
  (b == OpenUnitDual a)%Q ->
  (Mirror (SplitR s a)) == (SplitL (Mirror s) b).
Proof.
intros.
apply StepF_Qeq_eq; auto with *.
rapply MirrorSplitR_Qeq; auto with *.
Qed.

Lemma MirrorSplitL X : forall (s : StepF X) (a b : OpenUnit),
  (b == OpenUnitDual a)%Q ->
  (Mirror (SplitL s a)) == (SplitR (Mirror s) b).
Proof.
intros.
apply StepF_Qeq_eq; auto with *.
rapply MirrorSplitL_Qeq; auto with *.
Qed.

Lemma SplitRAp :forall (X Y:Setoid) (f : StepF (Y --> X)) (s : StepF Y) (o : OpenUnit),
  (SplitR (f <@> s) o) == (SplitR f o <@> SplitR s o).
Proof.
intros X Y f s o.
apply StepF_Qeq_eq; auto with *.
unfold Ap, SplitR.
rewrite <- StepFunction.SplitRMap.
rapply SplitRAp_Qeq.
Qed.

Lemma SplitLAp :forall (X Y:Setoid) (f : StepF (Y --> X)) (s : StepF Y) (o : OpenUnit),
  (SplitL (f <@> s) o) == (SplitL f o <@> SplitL s o).
Proof.
intros X Y f s o.
apply StepF_Qeq_eq; auto with *.
unfold Ap, SplitL.
rewrite <- StepFunction.SplitLMap.
rapply SplitLAp_Qeq.
Qed.

Add Morphism leaf with signature st_eq ==> StepF_eq as leaf_wd.
auto.
Qed.

Add Morphism glue with signature ou_eq ==> StepF_eq ==> StepF_eq ==> StepF_eq as glue_wd.
intros X o1 o2 Ho x1 x2 Hx y1 y2 Hy.
transitivity (glue o1 x2 y2).
apply glue_resp_StepF_eq; auto.
apply StepF_Qeq_eq.
repeat split; auto; reflexivity.
Qed.

Add Morphism SplitL with signature StepF_eq ==> ou_eq ==> StepF_eq as SplitL_wd.
Proof.
intros X x1 x2 Hx o1 o2 Ho.
transitivity (SplitL x2 o1).
 apply SplitL_resp_Xeq; auto.
apply StepF_Qeq_eq.
rapply SplitL_resp_Qeq; auto; reflexivity.
Qed.

Add Morphism SplitR with signature StepF_eq ==> ou_eq ==> StepF_eq as SplitR_wd.
Proof.
intros X x1 x2 Hx o1 o2 Ho.
transitivity (SplitR x2 o1).
 apply SplitR_resp_Xeq; auto.
apply StepF_Qeq_eq.
rapply SplitR_resp_Qeq; auto; reflexivity.
Qed.

Add Morphism Map with signature st_eq ==> StepF_eq ==> StepF_eq as Map_wd.
Proof.
intros X Y f g Hfg s t Hst.
apply StepF_eq_trans with (f ^@> t); auto with *.
 destruct f as [f Hf].
 apply (Map_resp_StepF_eq); auto with *.
clear - Hfg.
induction t.
 rapply Hfg.
rapply glue_resp_StepF_eq; assumption.
Qed.

Add Morphism Ap with signature StepF_eq ==> StepF_eq ==> StepF_eq as Ap_wd.
Proof.
intros X Y f g.
revert g.
induction f using StepF_ind; intros g Hfg.
 intros s.
 change (leaf (X:=X --> Y) x <@> s) with (x ^@> s).
 revert s.
 induction g using StepF_ind; intros.
  simpl.
  rapply Map_wd; auto with *.
 symmetry.
 rewrite ApGlue.
 destruct Hfg as [Hfg0 Hfg1] using (eq_glue_ind g1).
 apply glue_StepF_eq; symmetry.
  rewrite SplitLMap.
  apply IHg1; try rewrite H; auto with *.
 rewrite SplitRMap.
 apply IHg2; try rewrite H; auto with *.
intros s s' Hs.
destruct Hfg as [Hfg0 Hfg1] using (glue_eq_ind f1).
rewrite ApGlue.
apply glue_StepF_eq; auto with *.
 rewrite SplitLAp.
 apply IHf1; try rewrite Hs; auto with *.
rewrite SplitRAp.
apply IHf2; try rewrite Hs; auto with *.
Qed.

Definition compose0 (X Y Z:Setoid) : (Y-->Z) -> (X --> Y) -> X --> Z.
intros X Y Z f0 f1.
exists (compose f0 f1).
abstract (
destruct f0 as [f0 Hf0];
destruct f1 as [f1 Hf1];
intros x1 x2 Hx;
rapply Hf0;
rapply Hf1;
assumption).
Defined.

Definition compose1 (X Y Z:Setoid) : (Y-->Z) -> (X --> Y) --> X --> Z.
intros X Y Z f0.
exists (compose0 f0).
abstract (
destruct f0 as [f0 Hf0];
intros x1 x2 H y;
rapply Hf0;
rapply H).
Defined.

Definition compose (X Y Z:Setoid) : (Y-->Z) --> (X --> Y) --> X --> Z.
intros X Y Z.
exists (@compose1 X Y Z).
abstract (
intros x1 x2 H y z;
rapply H).
Defined.

Implicit Arguments compose [X Y Z].

Lemma Map_composition X Y Z: forall (a:StepF (Y-->Z)) (b:StepF (X-->Y)) (c:StepF X),
 ((@compose X Y Z) ^@> a <@> b <@> c) == (a <@> (b <@> c)).
Proof.
induction a using StepF_ind.
 simpl.
 intros b.
 induction b using StepF_ind.
  simpl.
  intros c.
  induction c using StepF_ind.
   auto with *.
  change (@compose X Y Z ^@> leaf (X:=Y --> Z) x <@> leaf (X:=X --> Y) x0 <@> glue o c1 c2)
   with (@compose X Y Z x x0 ^@> glue o c1 c2).
  rewrite MapGlue.
  apply glue_StepF_eq.
   rewrite IHc1.
   repeat rewrite (SplitLAp).
   repeat rewrite SplitLGlue.
   reflexivity.
  rewrite IHc2.
  repeat rewrite (SplitRAp).
  repeat rewrite SplitRGlue.
  reflexivity.
 intros c.
 change (compose x ^@> glue o b1 b2 <@> c == x ^@> (glue o b1 b2 <@> c)).
 rewrite MapGlue, ApGlue.
 apply glue_StepF_eq.
  rewrite IHb1.
  rewrite SplitLMap.
  rewrite SplitLAp.
  rewrite SplitLGlue.
  reflexivity.
 rewrite IHb2.
 rewrite SplitRMap.
 rewrite (SplitRAp).
 rewrite SplitRGlue.
 reflexivity.
intros b c.
rewrite MapGlue.
repeat rewrite ApGlue.
apply glue_resp_StepF_eq.
 rewrite IHa1.
 rewrite SplitLAp.
 reflexivity.
rewrite IHa2.
rewrite SplitRAp.
reflexivity.
Qed.

Lemma Ap_composition : forall (X Y Z:Setoid) (a:StepF (Y-->Z)) (b:StepF (X-->Y)) (c:StepF X),
 ((leaf (@compose X Y Z)) <@> a <@> b <@> c) == (a <@> (b <@> c)).
Proof.
exact Map_composition.
Qed.

Definition const0 (X Y:Setoid) : X->Y-->X.
intros X Y x.
exists (fun y => x).
abstract (
intros x1 x2 Hx;
reflexivity).
Defined.

Definition const (X Y:Setoid) : X-->Y-->X.
intros X Y.
exists (@const0 X Y).
abstract (
intros x1 x2 Hx y;
assumption).
Defined.

Implicit Arguments const [X Y].

Lemma Ap_discardable X Y : forall (a:StepF X) (b:StepF Y),
 ((@const _ _) ^@> a <@> b == a).
Proof.
induction a using StepF_ind.
 induction b using StepF_ind.
  auto with *.
 simpl.
 rapply glue_StepF_eq; assumption.
intros b.
rewrite MapGlue.
rewrite ApGlue.
rewrite IHa1.
rewrite IHa2.
reflexivity.
Qed.

Definition flip0 (X Y Z:Setoid) : (X-->Y-->Z)->Y->X-->Z.
intros X Y Z f y.
exists (fun x => f x y).
abstract (
destruct f as [f Hf];
intros x1 x2 H;
apply Hf;
auto).
Defined.

Definition flip1 (X Y Z:Setoid) : (X-->Y-->Z)->Y-->X-->Z.
intros X Y Z f.
exists (flip0 f).
abstract (
destruct f as [f Hf];
intros x1 x2 H y;
simpl;
destruct (f y) as [g Hg];
rapply Hg;
auto).
Defined.

Definition flip (X Y Z:Setoid) : (X-->Y-->Z)-->Y-->X-->Z.
intros X Y Z.
exists (@flip1 X Y Z).
abstract (
intros x1 x2 H y z;
rapply H).
Defined.

Implicit Arguments flip [X Y Z].

Lemma Ap_commutative W X Y : forall (f:StepF (W --> X --> Y)) (x:StepF X) (w:StepF W),
 ((@flip _ _ _) ^@> f <@> x <@> w) == (f <@> w <@> x).
Proof.
induction f using StepF_ind.
 simpl.
 intros a.
 induction a using StepF_ind.
  simpl.
  intros b.
  induction b using StepF_ind.
   auto with *.
  change (flip x x0 ^@> glue o b1 b2== x^@> glue o b1 b2 <@> leaf x0).
  rewrite MapGlue.
  apply glue_StepF_eq.
   (*Setoid rewrite bug*)
   set (A:=(SplitL (x ^@> glue o b1 b2 <@> leaf x0) o)).
   rewrite IHb1.
   unfold A; clear A.
   set (A:=x ^@> b1 <@> leaf x0).
   rewrite (SplitLAp).
   rewrite SplitLMap.
   rewrite SplitLGlue.
   auto with *.
  (*Setoid rewrite bug*)
  set (A:=(SplitR (x ^@> glue o b1 b2 <@> leaf x0) o)).
  rewrite IHb2.
  unfold A; clear A.
  set (A:=x ^@> b2 <@> leaf x0).
  rewrite (SplitRAp).
  rewrite SplitRMap.
  rewrite SplitRGlue.
  auto with *.
 intros w.
 change (flip x ^@> glue o a1 a2 <@> w == x ^@> w <@> glue o a1 a2).
 rewrite MapGlue, ApGlue.
 apply glue_StepF_eq.
  set (A:=(SplitL (x ^@> w <@> glue o a1 a2) o)).
  rewrite IHa1.
  unfold A; clear A.
  set (A:=x ^@> SplitL w o <@> a1).
  rewrite (SplitLAp).
  rewrite SplitLMap.
  rewrite SplitLGlue.
  auto with *.
 set (A:=(SplitR (x ^@> w <@> glue o a1 a2) o)).
 rewrite IHa2.
 unfold A; clear A.
 set (A:=x ^@> SplitR w o <@> a2).
 rewrite (SplitRAp).
 rewrite SplitRMap.
 rewrite SplitRGlue.
 auto with *.
intros x w.
rewrite MapGlue.
do 4 rewrite ApGlue.
apply glue_resp_StepF_eq; auto.
Qed.

Definition join0 (X Y:Setoid) : (X-->X-->Y)->X-->Y.
intros X Y f.
exists (fun y => f y y).
abstract (
destruct f as [f Hf];
intros x1 x2 H;
simpl;
transitivity (f x1 x2);
[destruct (f x1) as [g Hg];
 rapply Hg; auto
|apply Hf; auto]).
Defined.

Definition join (X Y:Setoid) : (X-->X-->Y)-->X-->Y.
intros X Y.
exists (@join0 X Y).
abstract (
intros x1 x2 H y;
rapply H).
Defined.

Implicit Arguments join [X Y].

Lemma Ap_copyable X Y : forall (f:StepF (X --> X --> Y)) (x:StepF X),
 ((@join _ _) ^@> f <@> x) == (f <@> x <@> x).
Proof.
induction f using StepF_ind.
 intros a.
 simpl ((@join _ _) ^@> leaf x).
 induction a using StepF_ind.
  auto with *.
 change (join x ^@> glue o a1 a2 == x ^@> glue o a1 a2 <@> glue o a1 a2).
 do 2 rewrite MapGlue.
 rewrite ApGlue.
 apply glue_resp_StepF_eq.
  rewrite SplitLGlue.
  auto.
 rewrite SplitRGlue.
 auto.
intros x.
rewrite MapGlue.
do 3 rewrite ApGlue.
apply glue_resp_StepF_eq; auto.
Qed.
