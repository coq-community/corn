Require Export QArith.
Require Export StepFunctionSetoid.
Require Import Qabs.
Require Import Bool.
Require Import CornTac.

Set Implicit Arguments.

Open Local Scope setoid_scope.
Open Local Scope sfstscope.

Section QS.

Lemma QS:(Setoid).
exists Q Qeq.
split; unfold reflexive, transitive, symmetric; eauto with qarith.
Defined.

Definition QabsS : QS-->QS.
exists Qabs.
abstract(
simpl; intros x1 x2 Hx;
rewrite Hx;
reflexivity).
Defined.

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

Definition QoppS : QS --> QS.
exists (Qopp).
abstract (
simpl; intros x1 x2 Hx; simpl in *;
rewrite Hx;
reflexivity).
Defined.

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

Definition QscaleS : QS -> QS --> QS.
intros q.
exists (Qmult q).
abstract (
intros x1 x2 Hx; simpl in *;
rewrite Hx;
reflexivity).
Defined.

Definition QmultS : QS --> QS --> QS.
exists (QscaleS).
abstract (
intros x1 x2 Hx y; simpl in *;
rewrite Hx;
reflexivity).
Defined.

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

End QS.

Notation "'StepQ'" := (StepF QS) : StepQ_scope.

Delimit Scope StepQ_scope with SQ.
Bind Scope StepQ_scope with StepF.

Open Local Scope StepQ_scope.

Definition StepQplus (s t:StepQ) : StepQ := QplusS ^@> s <@> t.
Definition StepQopp (s:StepQ) : StepQ := QoppS ^@> s.
Definition StepQminus (s t:StepQ) : StepQ := QminusS ^@> s <@> t.
Definition StepQmult (s t:StepQ) : StepQ := QmultS ^@> s <@> t.
Notation "x + y" := (StepQplus x y) : StepQ_scope.
Notation "- x" := (StepQopp x) : StepQ_scope.
Notation "x - y" := (StepQminus x y) : StepQ_scope.
Notation "x * y" := (StepQmult x y) : StepQ_scope.


Add Morphism StepQplus with signature (@StepF_eq QS) ==> (@StepF_eq QS) ==> (@StepF_eq QS) as StepQplus_wd.
Proof.
intros.
unfold StepQplus.
rewrite H.
rewrite H0.
reflexivity.
Qed.

Add Morphism StepQopp with signature (@StepF_eq QS) ==> (@StepF_eq QS) as StepQopp_wd.
Proof.
intros.
unfold StepQopp.
rewrite H.
reflexivity.
Qed.

Add Morphism StepQminus with signature (@StepF_eq QS) ==> (@StepF_eq QS) ==> (@StepF_eq QS) as StepQminus_wd.
Proof.
intros.
unfold StepQminus.
rewrite H.
rewrite H0.
reflexivity.
Qed.

Add Morphism StepQmult with signature (@StepF_eq QS) ==> (@StepF_eq QS) ==> (@StepF_eq QS) as StepQmult_wd.
Proof.
intros.
unfold StepQmult.
rewrite H.
rewrite H0.
reflexivity.
Qed.

Definition StepQsrt : (@ring_theory (StepQ) (constStepF (0:QS)) (constStepF (1:QS)) StepQplus StepQmult StepQminus StepQopp (@StepF_eq QS)).
constructor; 
 intros; 
 unfold StepF_eq, StepQplus, StepQminus, StepQopp, StepQmult; 
 rewriteStepF;
 set (g:=st_eqS QS).

set (z:=QplusS 0).
set (f:=(join (compose g z))).
cut (StepFfoldProp (f ^@> x)).
 unfold f; evalStepF; tauto.
apply StepFfoldPropForall_Map.
intros a.
unfold f; simpl; ring.

set (f:=ap
 (compose (@ap _ _ _) (compose (compose g) QplusS))
 (flip (QplusS))).
cut (StepFfoldProp (f ^@> x <@> y)).
 unfold f; evalStepF; tauto.
apply StepFfoldPropForall_Map2.
intros a b.
change (a + b == b + a)%Q.
ring.

set (f:=ap
 (compose (@ap _ _ _) (compose (compose (compose (compose (@ap _ _ _)) (@compose _ _ _) g)) (compose (flip (@compose _ _ _) QplusS) (compose (@compose _ _ _) QplusS))))
 (compose (compose QplusS) QplusS)).
cut (StepFfoldProp (f ^@> x <@> y <@> z)).
 unfold f; evalStepF; tauto.
apply StepFfoldPropForall_Map3.
intros a b c.
change (a + (b + c) == a + b + c)%Q.
ring.

set (z:=(QmultS 1)).
set (f:=(join (compose g z))).
cut (StepFfoldProp (f ^@> x)).
 unfold f; evalStepF; tauto.
apply StepFfoldPropForall_Map.
intros a.
unfold f; simpl; ring.

set (f:=ap
 (compose (@ap _ _ _) (compose (compose g) QmultS))
 (flip (QmultS))).
cut (StepFfoldProp (f ^@> x <@> y)).
 unfold f; evalStepF; tauto.
apply StepFfoldPropForall_Map2.
intros a b.
change (a * b == b * a)%Q.
ring.

set (f:=ap
 (compose (@ap _ _ _) (compose (compose (compose (compose (@ap _ _ _)) (@compose _ _ _) g)) (compose (flip (@compose _ _ _) QmultS) (compose (@compose _ _ _) QmultS))))
 (compose (compose QmultS) QmultS)).
cut (StepFfoldProp (f ^@> x <@> y <@> z)).
 unfold f; evalStepF; tauto.
apply StepFfoldPropForall_Map3.
intros a b c.
change (a * (b * c) == a * b * c)%Q.
ring.

set (f:= ap
 (compose (@ap _ _ _) (compose (compose (compose (@ap _ _ _) (compose (compose g) QmultS))) QplusS))
 (compose (flip (@compose _ _ _) QmultS) (compose (@ap _ _ _) (compose (compose QplusS) QmultS)))).
cut (StepFfoldProp (f ^@> x <@> y <@> z)).
 unfold f; evalStepF; tauto.
apply StepFfoldPropForall_Map3.
intros a b c.
change ((a + b) * c == a*c + b*c)%Q.
ring.

set (f:= ap
 (compose (@ap _ _ _) (compose (compose g) QminusS))
 (compose (flip (@compose _ _ _) QoppS) QplusS)).
cut (StepFfoldProp (f ^@> x <@> y)).
 unfold f; evalStepF; tauto.
apply StepFfoldPropForall_Map2.
intros a b.
change (a - b == a + - b)%Q.
ring.

set (z:=(0:QS)).
set (f:= compose (flip g z) (ap QplusS QoppS)).
cut (StepFfoldProp (f ^@> x)).
 unfold f; evalStepF; tauto.
apply StepFfoldPropForall_Map.
intros a.
change (a + - a == 0)%Q.
ring.
Qed.

Definition StepQisZero:(StepQ)->bool:=(StepFfold (fun (x:QS) => Qeq_bool x 0) (fun _  x y => x && y)).

Definition StepQeq_bool (x y:StepQ) : bool := StepQisZero (x-y).

Lemma StepQeq_bool_correct : forall x y, StepQeq_bool x y = true -> x == y.
Proof.
intros x y H.
destruct StepQsrt.
rewrite <- (Radd_0_l x).
rewrite <- (Ropp_def y).
transitivity (y + (constStepF (0:QS))).
 set (z:=constStepF (X:=QS) 0).
 rewrite <- (Radd_assoc).
 apply StepQplus_wd.
  reflexivity.
 rewrite Radd_comm.
 rewrite <- Rsub_def.
 unfold StepF_eq.
 revert H.
 unfold StepQeq_bool.
 generalize (x-y).
 intros s H.
 induction s.
  rapply Qeq_bool_eq.
  assumption.
 symmetry in H.
 destruct (andb_true_eq _ _ H) as [H1 H2].
 split.
  apply IHs1; symmetry; assumption.
 apply IHs2; symmetry; assumption.
rewrite Radd_comm.
apply Radd_0_l.
Qed.

Lemma StepQRing_Morphism : ring_eq_ext StepQplus StepQmult StepQopp (@StepF_eq QS).
split.
  apply StepQplus_wd.
 apply StepQmult_wd.
apply StepQopp_wd.
Qed.

Ltac isStepQcst t :=
  match t with
  | constStepF ?q => isQcst q
  | glue ?o ?l ?r => 
   match isStepQcst l with
   |true => match isStepQcst r with
            |true => isQcst o
            |false => false
            end
   |false => false
   end
  | _ => false
  end.

Ltac StepQcst t :=
  match isStepQcst t with
    true => t
    | _ => NotConstant
  end.

Add Ring StepQRing : StepQsrt
 (decidable StepQeq_bool_correct,
  setoid (StepF_Sth QS) StepQRing_Morphism,
  constants [StepQcst]).

Definition StepQabs (s:StepQ) : StepQ := QabsS ^@> s.

Add Morphism StepQabs with signature (@StepF_eq QS) ==> (@StepF_eq QS) as StepQabs_wd.
Proof.
intros.
unfold StepQabs.
rewrite H.
reflexivity.
Qed.

(** 
** A Partial Order on Step Functions. *)
Definition StepQ_le x y := (StepFfoldProp (QleS ^@> x <@> y)).
(* begin hide *)
Add Morphism StepQ_le 
  with signature (@StepF_eq QS) ==> (@StepF_eq QS) ==> iff
 as StepQ_le_wd.
unfold StepQ_le.
intros x1 x2 Hx y1 y2 Hy.
rewrite Hx.
rewrite Hy.
reflexivity.
Qed.
(* end hide *)
Notation "x <= y" := (StepQ_le x y) (at level 70) : sfstscope.

Lemma StepQ_le_refl:forall x, (x <= x).
intros x.
unfold StepQ_le.
cut (StepFfoldProp (join QleS ^@> x)).
 evalStepF.
 tauto.
apply StepFfoldPropForall_Map.
intros.
simpl.
auto with *.
Qed.

Lemma StepQ_le_trans:forall x y z, 
 (x <= y)-> (y <= z) ->(x <= z).
intros x y z. unfold StepQ_le.
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
 evalStepF.
 tauto.
apply StepFfoldPropForall_Map3.
intros a b c Hab Hbc.
clear f.
simpl in *.
eauto with qarith.
Qed.

Lemma StepQabsOpp : forall x, StepQabs (-x) == StepQabs (x).
Proof.
intros x.
unfold StepF_eq.
set (g:=(st_eqS QS)).
set (f:=(ap
(compose g (compose QabsS QoppS))
QabsS)).
cut (StepFfoldProp (f ^@> x)).
 unfold f.
 evalStepF.
 tauto.
apply StepFfoldPropForall_Map.
intros a.
rapply Qabs_opp.
Qed.

Lemma StepQabs_triangle : forall x y, StepQabs (x+y) <= StepQabs x + StepQabs y.
Proof.
intros x y.
set (f:=(ap
(compose ap (compose (compose (compose QleS QabsS)) QplusS))
(compose (flip (@compose _ _ _) QabsS) (compose QplusS QabsS)))).
cut (StepFfoldProp (f ^@> x <@> y)).
 unfold f.
 evalStepF.
 tauto.
apply StepFfoldPropForall_Map2.
intros a b.
rapply Qabs_triangle.
Qed.
