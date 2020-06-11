(*
Copyright © 2006-2008 Russell O’Connor

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

Require Export CoRN.algebra.RSetoid.
Require Import Coq.Relations.Relation_Definitions.
Require Export CoRN.model.structures.QposInf.
Require Import CoRN.model.totalorder.QMinMax.
Require Import CoRN.model.totalorder.QposMinMax.
Require Import CoRN.stdlib_omissions.List.
Require Import CoRN.stdlib_omissions.Q.

Require CoRN.model.structures.QnnInf.
Import QnnInf.notations.

Local Open Scope Q_scope.

Set Implicit Arguments.

(**
* Metric Space
In this version, a metric space over a setoid X is characterized by a
ball relation B where B e x y is intended to mean that the two points
x and y are within e of each other ( d(x,y)<=e ).  This is characterized
by the axioms given in the record structure below.
*)

Record is_MetricSpace (X : RSetoid) (B: Q -> relation X) : Prop :=
{ msp_refl: forall e, 0 <= e -> Reflexive (B e)
; msp_sym: forall e, Symmetric (B e)
; msp_triangle: forall e1 e2 a b c, B e1 a b -> B e2 b c -> B (e1 + e2) a c
; msp_closed: forall e a b, (forall d, 0 < d -> B (e + d) a b) -> B e a b
; msp_eq: forall a b, (forall e, 0 < e -> B e a b) -> st_eq a b
; msp_nonneg : forall e a b, B e a b -> 0 <= e
}.

Record MetricSpace : Type :=
{ msp_is_setoid :> RSetoid
; ball : Q -> msp_is_setoid -> msp_is_setoid -> Prop
; ball_wd : forall (e1 e2:Q), (e1 == e2) ->
            forall x1 x2, (st_eq x1 x2) ->
            forall y1 y2, (st_eq y1 y2) ->
            (ball e1 x1 y1 <-> ball e2 x2 y2)
; msp : is_MetricSpace msp_is_setoid ball
}.

(* begin hide *)
Arguments ball [m].

(*This is intended to be used as a ``type cast'' that Coq won't randomly make disappear.
  It is useful when defining setoid rewrite lemmas for st_eq.*)
Definition ms_id (m:MetricSpace) (x:m) : m := x.
Arguments ms_id [m].

Add Parametric Morphism (m:MetricSpace) : (@ball m)
    with signature Qeq ==> (@st_eq m) ==> (@st_eq m) ==> iff as ball_compat.
Proof.
 exact (@ball_wd m).
Qed.
(* end hide *)

Section Metric_Space.

(*
** Ball lemmas
*)

Variable X : MetricSpace.

(** These lemmas give direct access to the ball axioms of a metric space
*)

Lemma ball_refl : forall e (a:X), 0 <= e -> ball e a a.
Proof.
 intros. apply (msp_refl (msp X) H).
Qed.

Lemma ball_sym : forall e (a b:X), ball e a b -> ball e b a.
Proof.
 apply (msp_sym (msp X)).
Qed.

Lemma ball_triangle : forall e1 e2 (a b c:X),
    ball e1 a b -> ball e2 b c -> ball (e1 + e2) a c.
Proof.
 apply (msp_triangle (msp X)).
Qed.

Lemma ball_closed :  forall e (a b:X),
    (forall d, 0 < d -> ball (e + d) a b) -> ball e a b.
Proof.
 apply (msp_closed (msp X)).
Qed.

Lemma ball_eq : forall (a b:X), (forall e, 0 < e -> ball e a b) -> st_eq a b.
Proof.
 apply (msp_eq (msp X)).
Qed.

Lemma ball_eq_iff : forall (a b:X),
    (forall e, 0 < e -> ball e a b) <-> st_eq a b.
Proof.
 split.
  apply ball_eq.
 intros H e epos.
 apply (ball_wd X eq_refl a b H b b (reflexivity _)).
 apply ball_refl. apply Qlt_le_weak, epos.
Qed.

(** The ball constraint on a and b can always be weakened.  Here are
two forms of the weakening lemma.
*)

Lemma ball_weak : forall e d (a b:X),
    0 <= d -> ball e a b -> ball (e + d) a b.
Proof.
 intros e d a b dpos B1.
 eapply ball_triangle.
  apply B1.
 apply ball_refl. exact dpos.
Qed.

Hint Resolve ball_refl ball_triangle ball_weak : metric.

Lemma ball_weak_le : forall (e d:Q) (a b:X),
    e <= d ->  ball e a b -> ball d a b.
Proof.
 intros e d a b Hed B1.
 setoid_replace d with (e + (d-e)) by ring.
 apply (ball_triangle _ _ _ b). exact B1.
 apply ball_refl.
 unfold Qminus. rewrite <- Qle_minus_iff. exact Hed.
Qed.

End Metric_Space.
(* begin hide *)
Hint Resolve ball_refl ball_sym ball_triangle ball_weak : metric.
(* end hide *)

(** We can easily generalize ball to take the ratio from Q or QnnInf: *)

(* TODO remove *)
Section gball.

  Context {m: MetricSpace}.

  Definition gball (q: Q) (x y: m): Prop :=
    ball q x y.

  Definition gball_ex (e: QnnInf): relation m :=
    match e with
    | QnnInf.Finite e' => gball (proj1_sig e')
    | QnnInf.Infinite => fun _ _ => True
    end.

  Lemma ball_gball (q: Q) (x y: m): gball q x y <-> ball q x y.
  Proof.
    reflexivity.
  Qed.

  Global Instance gball_Proper: Proper (Qeq ==> @st_eq m ==> @st_eq m ==> iff) gball.
  Proof with auto.
   intros x y E a b F v w G.
   unfold gball.
   rewrite E. rewrite F. rewrite G. reflexivity.
  Qed.

  Global Instance gball_ex_Proper: Proper (QnnInf.eq ==> @st_eq m ==> @st_eq m ==> iff) gball_ex.
  Proof.
   repeat intro.
   destruct x, y. intuition. intuition. intuition.
   apply gball_Proper; assumption.
  Qed.

  Global Instance gball_refl (e: Q): 0 <= e -> Reflexive (gball e).
  Proof with auto.
   repeat intro.
   unfold gball. apply ball_refl, H.
  Qed.

  Global Instance gball_ex_refl (e: QnnInf): Reflexive (gball_ex e).
  Proof.
   destruct e. intuition.
   apply gball_refl, proj2_sig.
  Qed.

  Global Instance gball_sym (e: Q): Symmetric (gball e).
  Proof.
    unfold gball. intros x y.
    apply ball_sym.
  Qed.

  Lemma gball_ex_sym (e: QnnInf): Symmetric (gball_ex e).
  Proof. destruct e. auto. simpl. apply gball_sym. Qed.

  Lemma gball_triangle (e1 e2: Q) (a b c: m):
    gball e1 a b -> gball e2 b c -> gball (e1 + e2) a c.
  Proof with auto with *.
   unfold gball.
   intros. apply (ball_triangle _ _ _ _ b); assumption.
  Qed. 

  Lemma gball_ex_triangle (e1 e2: QnnInf) (a b c: m):
    gball_ex e1 a b -> gball_ex e2 b c -> gball_ex (e1 + e2)%QnnInf a c.
  Proof. destruct e1, e2; auto. simpl. apply gball_triangle. Qed.

  Lemma gball_0 (x y: m): gball 0 x y <-> st_eq x y.
  Proof.
    split.
    - intro H. apply ball_eq. intros. unfold gball in H.
      apply (@ball_weak_le m 0 e).
      apply Qlt_le_weak, H0. exact H.
    - intros. unfold gball. rewrite H.
      apply ball_refl. apply Qle_refl.
  Qed.

  Lemma gball_weak_le (q q': Q): q <= q' -> forall x y, gball q x y -> gball q' x y.
  Proof.
    intros. exact (ball_weak_le m x y H H0).
  Qed.

  Lemma gball_pos {e : Q} (e_pos : 0 < e) (x y : m)
    : ball e x y <-> gball e x y.
  Proof.
  unfold gball. reflexivity.
  Qed.

  Lemma gball_neg (e : Q) (x y : m) : e < 0 -> ~ gball e x y.
  Proof.
    intros e_neg abs. unfold gball in abs. 
    apply (Qlt_not_le _ _ e_neg).
    exact (msp_nonneg (msp m) _ _ _ abs).
  Qed.

  Lemma gball_closed (e : Q) (x y : m) :
     (forall d : Q, 0 < d -> gball (e + d) x y) -> gball e x y.
  Proof.
  intro C. (*change (gball e x y).*) unfold gball.
  apply ball_closed. exact C.
  Qed.

  Lemma gball_closed_eq (x y : m) : (forall d : Q, 0 < d -> gball d x y) -> st_eq x y.
  Proof.
    intro C. apply ball_eq. exact C.
  Qed.

End gball.
