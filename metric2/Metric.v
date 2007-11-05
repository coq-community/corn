(*
Copyright © 2006 Russell O’Connor

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

Require Import Setoid.
Require Import Relation_Definitions.
Require Export Qpossec.
Require Import COrdFields2.
Require Import Qordfield.
Require Import QMinMax.
Require Import List.
Require Import CornTac.

Set Implicit Arguments.

Record is_MetricSpace (X:Type) (Xeq: relation X) (B: Qpos -> relation X) : Prop :=
{ msp_Xsetoid: Setoid_Theory X Xeq
; msp_refl: forall e, reflexive _ (B e)
; msp_sym: forall e, symmetric _ (B e)
; msp_triangle: forall e1 e2 a b c, B e1 a b -> B e2 b c -> B (e1 + e2)%Qpos a c
; msp_closed: forall e a b, (forall d, B (e+d)%Qpos a b) -> B e a b
; msp_eq: forall a b, (forall e, B e a b) -> Xeq a b
}.

Record MetricSpace : Type :=
{ ms :> Type
; ms_eq : ms -> ms -> Prop
; ball : Qpos -> ms -> ms -> Prop
; ball_wd : forall (e1 e2:Qpos), (e1==e2) -> 
            forall x1 x2, (ms_eq x1 x2) -> 
            forall y1 y2, (ms_eq y1 y2) -> 
            (ball e1 x1 y1 <-> ball e2 x2 y2)
; msp : is_MetricSpace ms_eq ball
}.

Implicit Arguments ball [m].
Implicit Arguments ms_eq [m].

Add Setoid ms ms_eq (fun X => @msp_Xsetoid _ _ _ (@msp X)) as ms_setoid.

(*This is intended to be used as a ``type cast'' that Coq won't randomly make disappear.
  It is useful when defining setoid rewrite lemmas for ms_eq.*)
Definition ms_id (m:MetricSpace) (x:m) : m := x.
Implicit Arguments ms_id [m].

Add Morphism ball with signature QposEq ==> ms_eq ==> ms_eq ==> iff as ball_compat.
intros m.
exact (@ball_wd m).
Qed.

Section Metric_Space.

Variable X : MetricSpace.

Lemma ball_refl : forall e (a:X), ball e a a.
Proof.
apply (msp_refl (msp X)).
Qed.

Lemma ball_sym : forall e (a b:X), ball e a b -> ball e b a.
Proof.
apply (msp_sym (msp X)).
Qed.

Lemma ball_triangle : forall e1 e2 (a b c:X), ball e1 a b -> ball e2 b c -> ball (e1+e2) a c.
Proof.
apply (msp_triangle (msp X)).
Qed.

Lemma ball_closed :  forall e (a b:X), (forall d, ball (e+d) a b) -> ball e a b.
Proof.
apply (msp_closed (msp X)).
Qed.

Lemma ball_eq : forall (a b:X), (forall e, ball e a b) -> ms_eq a b.
Proof.
apply (msp_eq (msp X)).
Qed.

Lemma ball_eq_iff : forall (a b:X), (forall e, ball e a b) <-> ms_eq a b.
Proof.
split.
apply ball_eq.
intros H e.
rewrite H.
apply ball_refl.
Qed.

Lemma ball_weak : forall e d (a b:X), ball e a b -> ball (e+d) a b.
Proof.
intros e d a b B1.
eapply ball_triangle.
apply B1.
apply ball_refl.
Qed.

Hint Resolve ball_weak : metric.

Lemma ball_weak_le : forall (e d:Qpos) (a b:X), e<=d ->  ball e a b -> ball d a b.
Proof.
intros e d a b Hed B1.
destruct (Qle_lt_or_eq _ _ Hed).
destruct (Qpos_lt_plus H) as [c Hc].
rewrite <- Q_Qpos_plus in Hc.
change (QposEq d (e+c)) in Hc.
rewrite Hc; clear - B1.
auto with *.
change (QposEq e d) in H.
rewrite <- H.
assumption.
Qed.

Section Prelength_Space.

Definition PrelengthSpace :=
forall (a b:X) (e d1 d2:Qpos), e < d1+d2 -> ball e a b -> 
{c:X | ball d1 a c & ball d2 c b}.

Hypothesis prelength : PrelengthSpace.

Lemma trail : forall dl e (a b:X),
 ball e a b ->
 e < QposSum dl -> 
 let n := length dl in
 {f : nat -> X | f 0 = a /\ f n = b 
               & forall i z, i < n -> ball (nth i dl z) (f i) (f (S i))}%nat.
Proof.
induction dl.
intros e a b H H1.
simpl in *.
elim (less_antisymmetric_unfolded _ (e:Q) 0);solve[assumption|apply Qpos_prf].

rename a into x.
intros e a b B pe.
simpl in pe.

destruct dl.
simpl in *.
pose (f:= (fun n => match n with O => a | S _ => b end)).
exists f; auto.
intros [|i] z H;[|elimtype False; auto with *].
clear z H.
ring_simplify in pe.
apply ball_weak_le with e.
apply Qlt_le_weak; assumption.
assumption.

set (Sigma := QposSum (q::dl)).
pose (g := ((Qmax 0 (e-x))+Sigma)/2).
assert ((Qmax 0 (e-x))<Sigma).
apply Qmax_case.
intros.
rsapply less_leEq_trans.
instantiate (1:=(q:Q)).
apply Qpos_prf.
unfold Sigma.
simpl.
replace LHS with (q+0) by ring.
rsapply plus_resp_leEq_lft.
apply QposSumNonNeg.
intros.
rsapply shift_minus_less.
replace RHS with (x+Sigma) by ring.
assumption.
assert (Hg1:=Smallest_less_Average _ _ _ H).
assert (0<g).
rsapply leEq_less_trans.
apply Qmax_ub_l.
apply Hg1.
set (g' := (mkQpos H0):Qpos).
assert (Hg:g'=g:>Q).
rapply QposAsmkQpos.
assert (e<x+g').
rsapply shift_less_plus'.
rsapply leEq_less_trans.
apply Qmax_ub_r.
rewrite Hg.
apply Hg1.
assert (g'<Sigma).
rewrite Hg.
rsapply Average_less_Greatest.
assumption.
destruct (prelength _ _ H1 B) as [c Hc1 Hc2].
destruct (IHdl _ _ _ Hc2 H2) as [f' [Hf'1 Hf'2] Hf'3].
exists (fun n => match n with O => a | S n' => f' n' end).
auto.
intros [|i] z Hi.
simpl.
congruence.
rapply Hf'3.
auto with *.
Qed.

End Prelength_Space.

End Metric_Space.
