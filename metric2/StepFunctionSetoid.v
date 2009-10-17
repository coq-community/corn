(*
Copyright © 2007-2008 Russell O’Connor

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
Require Export RSetoid.
Require Export StepFunction.
Require Import OpenUnit.
Require Import CornTac.
Require Import Qauto.
Require Import Qordfield.
Require Import COrdFields.

Set Implicit Arguments.

Open Local Scope Q_scope.

Section StepF_Functions.

Variable X:Setoid.

(**
** Step Functions over setoids
In this section we redevelop step functions over a setoid X.
Here we shadow the old Step Function operations to operate over
setoids.
*)

Definition StepF := StepF X.

(** We lift the constructors and destructors to the setoid version *)
Definition constStepF : X -> StepF := (@constStepF X).

Definition glue : OpenUnit -> StepF -> StepF -> StepF := (@glue X).

Lemma StepF_ind : forall (P : StepF -> Prop),
       (forall x : X, P (constStepF x)) ->
       (forall (o : OpenUnit) (s : StepF),
        P s -> forall s0 : StepF, P s0 -> P (glue o s s0)) ->
       forall s : StepF, P s.
Proof.
 intros P H0 H1 s.
 induction s.
  apply H0.
 apply H1; auto.
Qed.

Definition StepFfold  : forall Y, (X -> Y) -> (OpenUnit -> Y -> Y -> Y) -> StepF -> Y := (@StepFfold X).
Definition Mirror : StepF -> StepF := (@Mirror X).
Definition SplitL : StepF -> OpenUnit -> StepF := (@SplitL X).
Definition SplitR : StepF -> OpenUnit -> StepF := (@SplitR X).
End StepF_Functions.

(* begin hide *)
Implicit Arguments constStepF [X].
(* end hide *)
Open Local Scope setoid_scope.

(** We lift ap to the setoid version.  Map is a notation calling ap so
that all lemmas about ap automatically apply to ap *)
Definition Ap (X Y:Setoid) : (StepF (X --> Y))->(StepF X)->(StepF Y) := fun f x => (@Ap X Y (StepFunction.Map (@evalMorphism X Y) f) x).
Notation "f <@> x" := (Ap f x) (at level 15, left associativity) : sfstscope.
Notation "f ^@> x" := (Ap (constStepF f) x) (at level 15, left associativity) : sfstscope.
Notation "f <@^ x" := (Ap f (constStepF x)) (at level 15, left associativity) : sfstscope.

Open Local Scope sfstscope.

(** We lift lemmas about map, ap, mirror, and glue *)
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
       SplitL (f ^@> x) a = f ^@> (SplitL x a).
Proof.
 intros X Y x a f.
 unfold Ap, SplitL.
 simpl.
 rewrite SplitLMap.
 reflexivity.
Qed.

Lemma SplitRMap : forall (X Y : Setoid) (x : StepF X) (a : OpenUnit) (f : X --> Y),
       SplitR (f ^@> x) a = f ^@> (SplitR x a).
Proof.
 intros X Y x a f.
 unfold Ap, SplitR.
 simpl.
 rewrite SplitRMap.
 reflexivity.
Qed.

Section EquivalenceA.
Variable X:Setoid.
(** A step function over [Prop], a characteristic function, can be
folded into [Prop], which holds for the always true characteristic
function *)
Definition StepFfoldProp : StepF iffSetoid -> Prop := (StepFfold (X:=iffSetoid) (fun x => x ) (fun _ a b => a /\ b )).

Definition st_eqS0 : X -> X --> iffSetoid.
Proof.
 intros x.
 exists (st_eq x).
 abstract ( intros x1 x2 Hx; simpl; rewrite -> Hx; reflexivity).
Defined.

Definition st_eqS : X --> X --> iffSetoid.
Proof.
 exists (st_eqS0).
 abstract ( intros x1 x2 Hx y; simpl; rewrite -> Hx; reflexivity).
Defined.
(**
** Equivalence
An equivalence relation on step functions is implemented by lifiting
the equivalence relation on the underlying setoid to step functions.
The results is a characteristic function saying where two step functions
are equivalent.  The step functions are considered equivalent if this
characteristic function says they are equivalent everywhere.
*)
Definition StepF_eq (f g:StepF X):Prop:=
(StepFfoldProp (st_eqS ^@> f <@> g)).

Notation "x === y" := (StepF_eq x y) (at level 70).

(** With equality defined we can complete the proof that split is the
opposite of glue *)
Lemma glue_StepF_eq:forall (s:StepF X) (s1 s2:StepF X), forall a, s1 === (SplitL s a) -> s2 === (SplitR s a) -> (glue a s1 s2) === s.
Proof.
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
 rewrite -> MapGlue in *.
 rewrite ApGlue in H0.
 destruct H0.
 auto.
Qed.
(** The equivalence relation is reflexive *)
Lemma StepF_eq_refl:forall x : StepF X, x === x.
Proof.
 induction x using StepF_ind.
  change (st_eq x x).
  reflexivity.
 apply glue_StepF_eq.
  simpl; rewrite SplitLGlue; assumption.
 simpl; rewrite SplitRGlue; assumption.
Qed.
(* begin hide *)
Hint Resolve StepF_eq_refl.
(* end hide *)
(** StepF_Qeq is a refinement of any setoid equality *)
Lemma StepF_Qeq_eq : forall (s t:StepF X), (StepF_Qeq s t) -> s === t.
Proof.
 induction s using StepF_ind; induction t using StepF_ind; try contradiction; simpl.
  intros H.
  rewrite H.
  auto with *.
 intros [H [H0 H1]].
 apply glue_StepF_eq.
  apply IHs1.
  apply SplitL_glue_ind; intros H2; try (elim (Qlt_not_le _ _ H2); rewrite -> H); auto with *.
 apply IHs2.
 apply SplitR_glue_ind; intros H2; try (elim (Qlt_not_le _ _ H2); rewrite -> H); auto with *.
Qed.

Lemma glueSplit:forall (s : StepF X), forall a, (glue a (SplitL s a) (SplitR s a)) === s.
Proof.
 intros s a.
 apply glue_StepF_eq; auto with *.
Qed.

End EquivalenceA.
(* begin hide *)
Hint Resolve StepF_eq_refl : sfarith.
(* end hide *)
Notation "x == y" := (StepF_eq x y) (at level 70) : sfstscope.

Section EquivalenceB.
Variable X Y:Setoid.

Lemma Map_resp_StepF_eq: forall f:X-->Y,
    (forall x y, (st_eq x y)-> (st_eq (f x) (f y))) ->
    forall s t:(StepF X), s == t -> (f ^@> s) == (f ^@> t).
Proof.
 intros f H.
 induction s using StepF_ind. induction t using StepF_ind.
  unfold StepF_eq, Map2, StepFfoldProp ;simpl;auto with *.
  unfold StepF_eq, Map2, StepFfoldProp. simpl;  intuition.
  intros t H0.
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
Proof.
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
Proof.
 induction x using StepF_ind. induction y using StepF_ind.
  auto with *.
  unfold StepF_eq. simpl. unfold StepFfoldProp;simpl;intuition.
  intros y H0.
 unfold StepF_eq, Map2 in H0.
 rewrite MapGlue in H0.
 rewrite ApGlue in H0.
 destruct H0 as [H0l H0r].
 change ((StepFfoldProp x1 /\ StepFfoldProp x2) <-> StepFfoldProp y).
 rewrite -> (IHx1 (SplitL y o)); auto with *.
 rewrite -> (IHx2 (SplitR y o)); auto with *.
 apply: StepFfoldPropglue.
Qed.

Lemma StepFfoldPropSplitR
     : forall (s : StepF iffSetoid) (a : OpenUnit),
       StepFfoldProp s -> StepFfoldProp (SplitR s a).
Proof.
 intros s a H.
 rewrite <- (StepFfoldPropglue s a) in H.
 destruct H; auto.
Qed.

Lemma StepFfoldPropSplitL
     : forall (s : StepF iffSetoid) (a : OpenUnit),
       StepFfoldProp s -> StepFfoldProp (SplitL s a).
Proof.
 intros s a H.
 rewrite <- (StepFfoldPropglue s a) in H.
 destruct H; auto.
Qed.

Section EquivalenceC.

Variable X:Setoid.
(* begin hide *)
Hint Resolve StepF_Qeq_eq StepF_Qeq_refl SplitL_resp_Qeq SplitR_resp_Qeq.
(* end hide *)
Lemma StepF_eq_resp_Qeq : forall (s t : StepF X) u v, (StepF_Qeq s t) -> (StepF_Qeq u v) -> s == u -> t == v.
Proof.
 induction s using StepF_ind; induction t using StepF_ind; try contradiction.
  intros u v Hst Huv Hsu.
  simpl in Hst.
  unfold StepF_eq in *.
  rewrite <- Hst.
  rewrite <- (StepFfoldProp_morphism ((st_eqS X) ^@> constStepF x <@> u)); auto.
  apply: (Map_resp_StepF_eq); auto with *.
  intros a b Hab.
  simpl.
  rewrite -> Hab.
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
  change (constStepF x == (Mirror t2) /\ constStepF x == (Mirror t1) <-> constStepF x == t1 /\ constStepF x == t2).
  tauto.
 intros t.
 rewrite MirrorGlue.
 split; apply (@glue_eq_ind X); intros H0 H1.
  apply glue_StepF_eq.
   rewrite <- IHs1.
   eapply StepF_eq_resp_Qeq;[| |apply H1]; auto with *.
   apply StepF_Qeq_sym.
   apply MirrorSplitL_Qeq; auto with *.
  rewrite <- IHs2.
  eapply StepF_eq_resp_Qeq;[| |apply H0]; auto with *.
  apply StepF_Qeq_sym.
  apply MirrorSplitR_Qeq; auto with *.
 apply glue_StepF_eq.
  apply StepF_eq_resp_Qeq with (Mirror s2) (Mirror (SplitR t o)); auto.
   apply MirrorSplitR_Qeq; apply Qeq_refl.
  rewrite -> IHs2.
  assumption.
 apply StepF_eq_resp_Qeq with (Mirror s1) (Mirror (SplitL t o)); auto.
  apply MirrorSplitL_Qeq; apply Qeq_refl.
 rewrite -> IHs1.
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
   apply SplitLSplitL.
   simpl; field; auto with *.
  apply glue_StepF_eq.
   apply StepF_eq_resp_Qeq with s1_1 (SplitL s2 o); auto.
   apply StepF_Qeq_sym.
   apply SplitLSplitL.
   simpl; field; auto with *.
  apply StepF_eq_resp_Qeq with (SplitL s1_2 (OpenUnitDualDiv a o Hao)) (SplitL (SplitR s2 o) (OpenUnitDualDiv a o Hao)); auto.
  apply SplitLSplitR; simpl; field; auto with *.
 apply StepF_eq_resp_Qeq with s1_1 (SplitL s2 o); auto with *.
 apply SplitL_resp_Qeq; auto.
 symmetry.
 assumption.
Qed.

Lemma SplitR_resp_Xeq : forall (s1 s2:StepF X) a, s1 == s2 -> SplitR s1 a == SplitR s2 a.
Proof.
 intros s1 s2 a H.
 pose (b:=OpenUnitDual a).
 apply StepF_eq_resp_Qeq with (Mirror (SplitL (Mirror s1) b)) (Mirror (SplitL (Mirror s2) b));
   try (unfold Mirror, SplitR, SplitL, b;eapply StepF_Qeq_trans;[apply Mirror_resp_Qeq; apply StepF_Qeq_sym; apply MirrorSplitR_Qeq; reflexivity|apply MirrorMirror]).
 rewrite -> Mirror_eq_Mirror.
 apply SplitL_resp_Xeq.
 rewrite -> Mirror_eq_Mirror.
 assumption.
Qed.

(** equalitiy is transitive *)
Lemma StepF_eq_trans:forall x y z : StepF X, x == y -> y == z -> x == z.
Proof.
 induction x using StepF_ind. intros.
  unfold StepF_eq in *.
  set (A:=((st_eqS X:X-->X-->iffSetoid) ^@> constStepF x)) in *.
  rewrite <- (StepFfoldProp_morphism (A <@> y)); auto with *.
  apply: (Map_resp_StepF_eq); auto with *.
  intros a b Hab.
  simpl.
  rewrite -> Hab.
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
Proof.
 intros.
 unfold StepF_eq.
 rewrite MapGlue.
 rewrite ApGlueGlue.
 split; assumption.
Qed.

(** equality is symmetric *)
Lemma StepF_eq_sym :forall x y: StepF X, x == y -> y == x.
Proof.
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
(* begin hide *)
Add Parametric Relation X : (StepF X) (@StepF_eq X)
 reflexivity proved by (@StepF_eq_refl X)
 symmetry proved by (@StepF_eq_sym X)
 transitivity proved by (@StepF_eq_trans X)
 as StepF_SetoidTheory.

Hint Resolve StepF_eq_sym StepF_eq_trans.

Add Morphism (StepFfoldProp)
  with signature (@StepF_eq iffSetoid) ==>  iff
 as StepFfoldProp_mor.
Proof.
 exact StepFfoldProp_morphism.
Qed.
(* end hide *)
Lemma StepF_Sth (X:Setoid) : (Setoid_Theory (StepF X) (@StepF_eq X)).
 split; unfold Reflexive, Symmetric, Transitive; eauto with sfarith.
Qed.
(**
** Common subdivision view
This lemma allows to do induction over two step function as if the
functions had the same subdivisions.
*)
Lemma StepF_ind2 : forall (X Y : Setoid) (P : StepF X -> StepF Y -> Prop),
       (forall (s s0 : StepF X) (t t0 : StepF Y),
        (s==s0) -> (t==t0) -> P s t -> P s0 t0) ->
       (forall (x:X) (y:Y), P (constStepF x) (constStepF y)) ->
       (forall (o : OpenUnit) (s s0 : StepF X) (t t0 : StepF Y),
        P s t -> P s0 t0 -> P (glue o s s0) (glue o t t0)) ->
       forall (s:StepF X) (t:StepF Y), P s t.
Proof.
 intros X Y P wd c0 c1.
 induction s using StepF_ind.
  induction t using StepF_ind.
   apply c0.
  apply wd with (s:=(glue o (constStepF x) (constStepF x))) (t:=glue o t1 t2); try reflexivity.
   apply (glueSplit (constStepF x) o).
  apply c1; assumption.
 intros t.
 eapply wd.
   reflexivity.
  apply glueSplit with (a:=o).
 apply c1; auto.
Qed.

Lemma glue_injl X :forall o (x y x1 y1:StepF X),
(glue o x y)==(glue o x1 y1) -> (x==x1).
Proof.
 intros.
 destruct H as [H _] using (glue_eq_ind x).
 rewrite SplitLGlue in H.
 assumption.
Qed.

Lemma glue_injr X :forall o (x y x1 y1:StepF X),
(glue o x y)==(glue o x1 y1) -> (y==y1).
Proof.
 intros.
 destruct H as [_ H] using (glue_eq_ind x).
 rewrite SplitRGlue in H.
 assumption.
Qed.

(** Decompose an equality over glue into two parts *)
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
 apply MirrorSplitR_Qeq; auto with *.
Qed.

Lemma MirrorSplitL X : forall (s : StepF X) (a b : OpenUnit),
  (b == OpenUnitDual a)%Q ->
  (Mirror (SplitL s a)) == (SplitR (Mirror s) b).
Proof.
 intros.
 apply StepF_Qeq_eq; auto with *.
 apply MirrorSplitL_Qeq; auto with *.
Qed.

(** Lift the distribution lemmas between ap and split to work over step
functions *)
Lemma SplitRAp :forall (X Y:Setoid) (f : StepF (Y --> X)) (s : StepF Y) (o : OpenUnit),
  (SplitR (f <@> s) o) == (SplitR f o <@> SplitR s o).
Proof.
 intros X Y f s o.
 apply StepF_Qeq_eq; auto with *.
 unfold Ap, SplitR.
 rewrite <- StepFunction.SplitRMap.
 apply SplitRAp_Qeq.
Qed.

Lemma SplitLAp :forall (X Y:Setoid) (f : StepF (Y --> X)) (s : StepF Y) (o : OpenUnit),
  (SplitL (f <@> s) o) == (SplitL f o <@> SplitL s o).
Proof.
 intros X Y f s o.
 apply StepF_Qeq_eq; auto with *.
 unfold Ap, SplitL.
 rewrite <- StepFunction.SplitLMap.
 apply SplitLAp_Qeq.
Qed.
(* begin hide *)
Add Parametric Morphism s : (@constStepF s) with signature (@st_eq s) ==> (@StepF_eq s) as constStepF_wd.
Proof.
 auto.
Qed.

Add Parametric Morphism s : (@glue s) with signature ou_eq ==> (@StepF_eq s) ==> (@StepF_eq s) ==> (@StepF_eq s) as glue_wd.
Proof.
 intros o1 o2 Ho x1 x2 Hx y1 y2 Hy.
 transitivity (glue o1 x2 y2).
  apply glue_resp_StepF_eq; auto.
 apply StepF_Qeq_eq.
 repeat split; auto; reflexivity.
Qed.

Add Parametric Morphism X : (@SplitL X) with signature (@StepF_eq X) ==> ou_eq ==> (@StepF_eq X) as SplitL_wd.
Proof.
 intros x1 x2 Hx o1 o2 Ho.
 transitivity (SplitL x2 o1).
  apply SplitL_resp_Xeq; auto.
 apply StepF_Qeq_eq.
 apply SplitL_resp_Qeq; auto; reflexivity.
Qed.

Add Parametric Morphism X : (@SplitR X) with signature (@StepF_eq X) ==> ou_eq ==> (@StepF_eq X) as SplitR_wd.
Proof.
 intros x1 x2 Hx o1 o2 Ho.
 transitivity (SplitR x2 o1).
  apply SplitR_resp_Xeq; auto.
 apply StepF_Qeq_eq.
 apply SplitR_resp_Qeq; auto; reflexivity.
Qed.

Add Parametric Morphism X Y : (@Ap X Y) with signature (@StepF_eq (extSetoid X Y)) ==> (@StepF_eq X) ==> (@StepF_eq Y) as Ap_wd.
Proof.
 intros f.
 induction f using StepF_ind; intros g Hfg.
  induction g using StepF_ind; intros x1.
   simpl.
   induction x1 using StepF_ind; intros x2.
    induction x2 using StepF_ind.
     intros H.
     transitivity (x ^@> (constStepF x2)).
      destruct x as [x Hx].
      clear Hfg. apply: Hx ; assumption.
      apply: Hfg.
    intros H.
    rewrite MapGlue.
    symmetry.
    symmetry in H.
    destruct H as [Hl Hr] using (glue_eq_ind x2_1).
    apply glue_StepF_eq.
     symmetry.
     symmetry in Hl.
     apply IHx2_1.
     assumption.
    symmetry.
    symmetry in Hr.
    apply IHx2_2.
    assumption.
   intros H.
   rewrite MapGlue.
   destruct H as [Hl Hr] using (glue_eq_ind x1_1).
   apply glue_StepF_eq.
    rewrite SplitLMap.
    apply IHx1_1; auto.
   rewrite SplitRMap.
   apply IHx1_2; auto.
  symmetry.
  rewrite ApGlue.
  destruct Hfg as [Hfg0 Hfg1] using (eq_glue_ind g1).
  apply glue_StepF_eq; symmetry.
   rewrite SplitLMap.
   apply IHg1; try rewrite -> H0; auto with *.
  rewrite SplitRMap.
  apply IHg2; try rewrite -> H0; auto with *.
 intros s s' Hs.
 destruct Hfg as [Hfg0 Hfg1] using (glue_eq_ind f1).
 rewrite ApGlue.
 apply glue_StepF_eq; auto with *.
  rewrite -> SplitLAp.
  apply IHf1; try rewrite -> Hs; auto with *.
 rewrite -> SplitRAp.
 apply IHf2; try rewrite -> Hs; auto with *.
Qed.
(* end hide *)
Lemma GlueAp : forall (X Y : Setoid) (f : StepF (X --> Y)) (o : OpenUnit) (l r : StepF X),
       f <@> (glue o l r) == glue o ((SplitL f o) <@> l) ((SplitR f o) <@> r).
Proof.
 intros X Y f o l r.
 set (A:= ((SplitL f o)<@>l)).
 set (B:= ((SplitR f o)<@>r)).
 rewrite <- (glueSplit f o).
 rewrite ApGlueGlue.
 reflexivity.
Qed.
(**
** Applicative Functor
Here we prove the axioms of an applicative functor.
*)
Lemma Map_homomorphism (X Y:Setoid) : forall (f:X-->Y) (a:X),
 (f ^@> constStepF a) == (constStepF (f a)).
Proof.
 reflexivity.
Qed.

Lemma Map_identity X : forall (a:StepF X),
 (@id X) ^@> a == a.
Proof.
 intros X a.
 rewrite <- Map_identity.
 reflexivity.
Qed.

Lemma Map_composition X Y Z: forall (a:StepF (Y-->Z)) (b:StepF (X-->Y)) (c:StepF X),
 ((@compose X Y Z) ^@> a <@> b <@> c) == (a <@> (b <@> c)).
Proof.
 induction a using StepF_ind.
  simpl.
  apply StepF_ind2; auto with *.
   intros s s0 t t0 Hs Ht.
   rewrite -> Hs, Ht.
   auto.
  intros o s s0 t t0 H H0.
  rewrite -> Map_homomorphism.
  rewrite ApGlueGlue.
  do 2 rewrite MapGlue.
  rewrite ApGlueGlue.
  rewrite <- H.
  rewrite <- H0.
  reflexivity.
 intros b c.
 rewrite MapGlue.
 repeat rewrite ApGlue.
 apply glue_resp_StepF_eq.
  rewrite -> IHa1.
  rewrite -> SplitLAp.
  reflexivity.
 rewrite -> IHa2.
 rewrite -> SplitRAp.
 reflexivity.
Qed.

(** Here we show that the rest of the BCKW combinators lift to
step functions.  Hence all of the lambda calculus lifts to operate
over step functions.  Step functions form about a nice of an
applicative functor as is possible. *)
Lemma Map_discardable X Y : forall (a:StepF X) (b:StepF Y),
 ((@const _ _) ^@> a <@> b == a).
Proof.
 intros X Y.
 apply StepF_ind2; auto with *.
  intros s s0 t t0 Hs Ht.
  rewrite -> Hs, Ht; auto.
 intros o s s0 t t0 H0 H1.
 rewrite MapGlue.
 rewrite ApGlueGlue.
 rewrite -> H0, H1;reflexivity.
Qed.

Lemma Map_commutative W X Y : forall (f:StepF (W --> X --> Y)) (x:StepF X) (w:StepF W),
 ((@flip _ _ _) ^@> f <@> x <@> w) == (f <@> w <@> x).
Proof.
 induction f using StepF_ind.
  simpl.
  apply StepF_ind2; auto with *.
   intros s s0 t t0 Hs Ht.
   rewrite -> Hs, Ht;auto.
  intros o s s0 t t0 H0 H1.
  rewrite -> Map_homomorphism.
  do 2 rewrite MapGlue.
  do 2 rewrite ApGlueGlue.
  rewrite -> H0, H1; reflexivity.
 intros x w.
 rewrite MapGlue.
 do 4 rewrite ApGlue.
 apply glue_resp_StepF_eq; auto.
Qed.

Lemma Map_copyable X Y : forall (f:StepF (X --> X --> Y)) (x:StepF X),
 ((@join _ _) ^@> f <@> x) == (f <@> x <@> x).
Proof.
 intros X Y.
 apply StepF_ind2; auto with *.
  intros s s0 t t0 Hs Ht.
  rewrite -> Hs, Ht; auto.
 intros o s s0 t t0 H0 H1.
 rewrite MapGlue.
 do 3 rewrite ApGlueGlue.
 rewrite -> H0, H1;reflexivity.
Qed.
(* begin hide *)
Hint Rewrite
 ApGlueGlue ApGlue GlueAp SplitRAp SplitLAp SplitLGlue SplitRGlue
 Map_homomorphism : StepF_rew.

Hint Rewrite
 Map_composition
 Map_discardable
 Map_commutative
 Map_identity
 Map_copyable : StepF_eval.
(* end hide *)
(** This tactic is usefully for symbolically evaluating functions written
in (BCKWI) combinator form that are ap'ed to step functions *)
Ltac evalStepF := progress
(repeat rewrite <- Map_homomorphism; autorewrite with StepF_eval).

Lemma Ap_interchange (X Y:Setoid) : forall (f:StepF (X-->Y)) (a:X),
 (f <@^ a) == (flip id a) ^@> f.
Proof.
 intros X Y f a.
 evalStepF.
 reflexivity.
Qed.

(** Map'ing the S combinator (which is also called ap) *)
Lemma Map_ap X Y Z : forall (f:StepF (X --> Y --> Z)) (x:StepF (X --> Y)) (a:StepF X),
 ((@ap _ _ _) ^@> f <@> x <@> a) == (f <@> a <@> (x <@> a)).
Proof.
 intros X Y Z f x a.
 unfold ap.
 evalStepF.
 reflexivity.
Qed.
(* begin hide *)
Hint Rewrite Map_ap : StepF_eval.
(* end hide *)
Ltac rewriteStepF := autorewrite with StepF_rew.

Lemma StepFfoldPropForall_Ap :
 forall X (f:StepF (X --> iffSetoid)) (x:StepF X), (forall y, StepFfoldProp (f <@> constStepF y)) -> StepFfoldProp (f <@> x).
Proof.
 intros X f x H.
 revert f H.
 induction x using StepF_ind.
  intros f H.
  apply H.
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

(** A common case that we will encounter is that a predicate holds for
all step functions when it is define via map (or map2 or map3) and the
underlying function holds for all X. *)
Lemma StepFfoldPropForall_Map :
 forall X (f:X --> iffSetoid) (x:StepF X), (forall a, f a) -> StepFfoldProp (f ^@> x).
Proof.
 intros X f x H.
 apply StepFfoldPropForall_Ap.
 assumption.
Qed.

Lemma StepFfoldPropForall_Map2 :
 forall X Y (f:X --> Y --> iffSetoid) x y, (forall a b, f a b) -> StepFfoldProp (f ^@> x <@> y).
Proof.
 intros X Y f x y H.
 apply StepFfoldPropForall_Ap.
 intros b.
 rewrite <- (Map_commutative (constStepF f) (constStepF b)).
 rewriteStepF.
 apply StepFfoldPropForall_Map.
 intros a.
 apply: H.
Qed.

Lemma StepFfoldPropForall_Map3 :
 forall X Y Z (f:X --> Y --> Z --> iffSetoid) x y z, (forall a b c, f a b c) -> StepFfoldProp (f ^@> x <@> y <@> z).
Proof.
 intros X Y Z f x y z H.
 apply StepFfoldPropForall_Ap.
 intros c.
 rewrite <- (Map_commutative ((constStepF f) <@> x) (constStepF c)).
 rewrite <- Map_composition.
 rewriteStepF.
 rewrite <- (Map_commutative (constStepF (compose flip f)) (constStepF c)).
 rewriteStepF.
 apply StepFfoldPropForall_Map2.
 intros a b.
 apply: H.
Qed.

(** The implication operation can be lifted to work on characteristic
functions *)
Definition imp0:Prop->iffSetoid-->iffSetoid.
Proof.
 intro A.
 exists (fun B:Prop=>(A->B)).
 abstract (simpl; intuition).
Defined.

Definition imp:iffSetoid-->iffSetoid-->iffSetoid.
Proof.
 exists imp0.
 abstract (simpl; unfold extEq; simpl; intuition).
Defined.

Definition StepF_imp (f g:StepF iffSetoid):Prop:=
(StepFfoldProp (imp ^@> f <@> g)).

Lemma StepFfoldPropglue_rew:(forall o x y, (StepFfoldProp (glue o x y))<->((StepFfoldProp x)/\StepFfoldProp y)).
Proof.
 auto with *.
Qed.
(* begin hide *)
Hint Rewrite StepFfoldPropglue_rew:StepF_rew.
(* end hide *)
Lemma StepF_imp_imp:forall x y:(StepF iffSetoid),
  (StepF_imp x y) ->
  ((StepFfoldProp x)->(StepFfoldProp y)).
Proof.
 induction x using StepF_ind. induction y  using StepF_ind.
  auto with *.
  unfold StepF_imp. unfold StepFfoldProp;simpl;intuition.
  intros y.
 unfold StepF_imp, Map2.
 rewriteStepF.
 intros.
 rewrite <- (StepFfoldPropglue y o).
 rewriteStepF.
 intuition.
Qed.
