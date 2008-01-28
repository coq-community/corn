Require Export ProductMetric.
Require Export Complete.
Require Import Qauto.

Set Implicit Arguments.

Section CompleteProduct.

Variable X Y:MetricSpace.
Let XY := ProductMS X Y.

Lemma fst_uc : is_UniformlyContinuousFunction (fun p:XY => fst p) Qpos2QposInf.
Proof.
intros e a b [H _].
assumption.
Qed.

Open Local Scope uc_scope.

Definition pi1 : XY --> X :=
Build_UniformlyContinuousFunction fst_uc.

Lemma snd_uc : is_UniformlyContinuousFunction (fun p:XY => snd p) Qpos2QposInf.
Proof.
intros e a b [_ H].
assumption.
Qed.

Definition pi2 : XY --> Y :=
Build_UniformlyContinuousFunction snd_uc.

Definition Cfst_raw (p:Complete XY) (e:QposInf) : X :=
(fst (approximate p e)).

Definition Csnd_raw (p:Complete XY) (e:QposInf) : Y :=
(snd (approximate p e)).

Lemma Cfst_prf : forall p, is_RegularFunction (Cfst_raw p).
Proof.
intros p e1 e2.
destruct (regFun_prf p e1 e2).
auto.
Qed.

Lemma Csnd_prf : forall p, is_RegularFunction (Csnd_raw p).
Proof.
intros p e1 e2.
destruct (regFun_prf p e1 e2).
auto.
Qed.

Definition Cfst_fun (p:Complete XY) : Complete X :=
Build_RegularFunction (Cfst_prf p).

Definition Csnd_fun (p:Complete XY) : Complete Y :=
Build_RegularFunction (Csnd_prf p).

Lemma Cfst_uc : is_UniformlyContinuousFunction Cfst_fun Qpos2QposInf.
Proof.
intros e a b H e1 e2.
destruct (H e1 e2).
auto.
Qed.

Lemma Csnd_uc : is_UniformlyContinuousFunction Csnd_fun Qpos2QposInf.
Proof.
intros e a b H e1 e2.
destruct (H e1 e2).
auto.
Qed.

Definition Cfst : Complete XY --> Complete X :=
Build_UniformlyContinuousFunction Cfst_uc.

Definition Csnd : Complete XY --> Complete Y :=
Build_UniformlyContinuousFunction Csnd_uc.

Lemma pair_uc_l : forall y:Y, @is_UniformlyContinuousFunction X XY (fun x => (x,y)) Qpos2QposInf.
Proof.
intros y e a b H.
split; auto.
apply ball_refl.
Qed.

Lemma pair_uc_r : forall x:X, @is_UniformlyContinuousFunction Y XY (fun y => (x,y)) Qpos2QposInf.
Proof.
intros x e a b H.
split; auto.
apply ball_refl.
Qed.

Definition Strength_raw (p: ProductMS (Complete X) (Complete Y)) (e:QposInf): XY :=
(approximate (fst p) e,approximate (snd p) e).

Lemma Strength_prf : forall p, is_RegularFunction (Strength_raw p).
Proof.
intros [p1 p2] e1 e2.
split; simpl; apply regFun_prf.
Qed.

Definition Strength_fun (p: ProductMS (Complete X) (Complete Y)) : Complete XY :=
Build_RegularFunction (Strength_prf p).

Lemma Strength_uc : is_UniformlyContinuousFunction Strength_fun Qpos2QposInf.
Proof.
intros e a b [Hl Hr] e1 e2.
split; simpl; auto.
Qed.

Definition Strength : (ProductMS (Complete X) (Complete Y)) --> (Complete (ProductMS X Y)) :=
Build_UniformlyContinuousFunction Strength_uc.

Lemma StrengthCorrect1 : forall p,
ms_eq (Strength ((Cfst p), (Csnd p))) p.
Proof.
intros p e1 e2.
destruct (regFun_prf p e1 e2).
split; simpl; auto.
Qed.

Lemma StrengthCorrect2 : forall p q,
ms_eq (Cfst (Strength (p,q))) p.
Proof.
intros p q e1 e2.
apply (regFun_prf p e1 e2).
Qed.

Lemma StrengthCorrect3 : forall p q,
ms_eq (Csnd (Strength (p,q))) q.
Proof.
intros p q e1 e2.
apply (regFun_prf q e1 e2).
Qed.

End CompleteProduct.

Implicit Arguments Strength [X Y].
Implicit Arguments Cfst [X Y].
Implicit Arguments Csnd [X Y].