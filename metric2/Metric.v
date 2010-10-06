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

Require Export RSetoid.
Require Import Relation_Definitions.
Require Export Qpossec.
Require Import COrdFields2.
Require Import Qordfield.
Require Import QMinMax.
Require Import List.
Require Import CornTac.

Require QnnInf.
Import QnnInf.notations.

Open Local Scope Q_scope.

Set Implicit Arguments.
(**
* Metric Space
In this version, a metric space over a setoid X is characterized by a
ball relation B where B e x y is intended to mean that the two points
x and y are within e of each other ( d(x,y)<=e ).  This is characterized
by the axioms given in the record structure below.
*)

Record is_MetricSpace (X:Setoid) (B: Qpos -> relation X) : Prop :=
{ msp_refl: forall e, Reflexive (B e)
; msp_sym: forall e, Symmetric (B e)
; msp_triangle: forall e1 e2 a b c, B e1 a b -> B e2 b c -> B (e1 + e2)%Qpos a c
; msp_closed: forall e a b, (forall d, B (e+d)%Qpos a b) -> B e a b
; msp_eq: forall a b, (forall e, B e a b) -> st_eq a b
}.

Record MetricSpace : Type :=
{ msp_is_setoid :> Setoid
; ball : Qpos -> msp_is_setoid -> msp_is_setoid -> Prop
; ball_wd : forall (e1 e2:Qpos), (QposEq e1 e2) ->
            forall x1 x2, (st_eq x1 x2) ->
            forall y1 y2, (st_eq y1 y2) ->
            (ball e1 x1 y1 <-> ball e2 x2 y2)
; msp : is_MetricSpace msp_is_setoid ball
}.

(* begin hide *)
Implicit Arguments ball [m].

(*This is intended to be used as a ``type cast'' that Coq won't randomly make disappear.
  It is useful when defining setoid rewrite lemmas for st_eq.*)
Definition ms_id (m:MetricSpace) (x:m) : m := x.
Implicit Arguments ms_id [m].

Add Parametric Morphism (m:MetricSpace) : (@ball m) with signature QposEq ==> (@st_eq m) ==> (@st_eq m) ==> iff as ball_compat.
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

Lemma ball_eq : forall (a b:X), (forall e, ball e a b) -> st_eq a b.
Proof.
 apply (msp_eq (msp X)).
Qed.

Lemma ball_eq_iff : forall (a b:X), (forall e, ball e a b) <-> st_eq a b.
Proof.
 split.
  apply ball_eq.
 intros H e.
 rewrite -> H.
 apply ball_refl.
Qed.

(** The ball constraint on a and b can always be weakened.  Here are
two forms of the weakening lemma.
*)

Lemma ball_weak : forall e d (a b:X), ball e a b -> ball (e+d) a b.
Proof.
 intros e d a b B1.
 eapply ball_triangle.
  apply B1.
 apply ball_refl.
Qed.

Hint Resolve ball_refl ball_triangle ball_weak : metric.

Lemma ball_weak_le : forall (e d:Qpos) (a b:X), e<=d ->  ball e a b -> ball d a b.
Proof.
 intros e d a b Hed B1.
 destruct (Qle_lt_or_eq _ _ Hed).
  destruct (Qpos_lt_plus H) as [c Hc].
  rewrite <- Q_Qpos_plus in Hc.
  change (QposEq d (e+c)) in Hc.
  rewrite -> Hc; clear - B1.
  auto with *.
 change (QposEq e d) in H.
 rewrite <- H.
 assumption.
Qed.

End Metric_Space.
(* begin hide *)
Hint Resolve ball_refl ball_sym ball_triangle ball_weak : metric.
(* end hide *)

(** We can easily generalize ball to take the ratio from Q or QnnInf: *)

Section gball.

  Context {m: MetricSpace}.

  Definition gball (q: Q) (x y: m): Prop :=
    match Qdec_sign q with
    | inl (inl _) => False (* q < 0, silly *)
    | inl (inr p) => ball (exist (Qlt 0) q p) x y (* 0 < q, normal *)
    | inr _ => x[=]y (* q == 0 *)
    end.
      (* Program can make this definition slightly cleaner, but the resulting term is much nastier... *)

  Definition gball_ex (e: QnnInf): relation m :=
    match e with
    | QnnInf.Finite e' => gball (proj1_sig e')
    | QnnInf.Infinite => fun _ _ => True
    end.

  Lemma ball_gball (q: Qpos) (x y: m): gball q x y <-> ball q x y.
  Proof with auto.
   unfold gball.
   intros [q p] ??. simpl.
   destruct Qdec_sign as [[A | A] | A].
     exfalso.
     apply (Qlt_is_antisymmetric_unfolded q 0)...
    apply ball_wd; reflexivity.
   exfalso.
   apply (Qlt_irrefl 0).
   rewrite <- A at 2...
  Qed.

  Global Instance gball_Proper: Proper (Qeq ==> @st_eq m ==> @st_eq m ==> iff) gball.
  Proof with auto.
   intros x y E a b F v w G.
   unfold gball.
   destruct Qdec_sign as [[A | B] | C];
    destruct Qdec_sign as [[P | Q] | R].
           reflexivity.
          exfalso. apply (Qlt_irrefl 0). apply Qlt_trans with x... rewrite E...
         exfalso. apply (Qlt_irrefl 0). rewrite <- R at 1. rewrite <- E...
        exfalso. apply (Qlt_irrefl 0). apply Qlt_trans with x... rewrite E...
       apply ball_wd...
      exfalso. apply (Qlt_irrefl 0). rewrite <- R at 2. rewrite <- E...
     exfalso. apply (Qlt_irrefl 0). rewrite <- C at 1. rewrite E...
    exfalso. apply (Qlt_irrefl 0). rewrite <- C at 2. rewrite E...
   rewrite F G. reflexivity.
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
   unfold gball.
   destruct Qdec_sign as [[?|?]|?].
     apply (Qlt_not_le e 0)...
    apply ball_refl.
   reflexivity.
  Qed.

  Global Instance gball_ex_refl (e: QnnInf): Reflexive (gball_ex e).
  Proof.
   destruct e. intuition.
   apply gball_refl, proj2_sig.
  Qed.

  Global Instance gball_sym (e: Q): Symmetric (gball e).
  Proof with auto.
   unfold gball. repeat intro.
   destruct Qdec_sign as [[?|?]|?]...
    apply ball_sym...
   symmetry...
  Qed.

  Lemma gball_ex_sym (e: QnnInf): Symmetric (gball_ex e).
  Proof. destruct e. auto. simpl. apply gball_sym. Qed.

  Lemma gball_triangle (e1 e2: Q) (a b c: m):
    gball e1 a b -> gball e2 b c -> gball (e1 + e2) a c.
  Proof with auto with *.
   unfold gball.
   intros.
   destruct (Qdec_sign e1) as [[A|B]|C].
     exfalso...
    destruct (Qdec_sign e2) as [[?|?]|?].
      intuition.
     destruct (Qdec_sign (e1 + e2)) as [[?|?]|?].
       assert (0 < e1 + e2).
        apply Qplus_lt_0_compat...
       revert H1. apply Qle_not_lt...
      simpl.
      setoid_replace (exist (Qlt 0) (e1 + e2) q0) with (exist (Qlt 0) e1 B + exist (Qlt 0) e2 q)%Qpos by reflexivity.
      apply ball_triangle with b...
     exfalso.
     assert (0 < e1 + e2).
      apply Qplus_lt_0_compat...
     revert H1. rewrite q0.
     apply Qlt_irrefl.
    destruct (Qdec_sign (e1 + e2)) as [[?|?]|?].
      revert q0. rewrite q. rewrite Qplus_0_r. apply Qle_not_lt...
     apply ball_gball. simpl. rewrite q Qplus_0_r. rewrite <- H0. apply ball_gball in H. assumption.
    exfalso.
    revert q0. rewrite q. rewrite Qplus_0_r. intro. clear H. revert B. rewrite H1. apply Qlt_irrefl.
   destruct (Qdec_sign e2) as [[?|?]|?].
     intuition.
    apply ball_gball in H0.
    simpl in H0.
    destruct (Qdec_sign (e1 + e2)) as [[?|?]|?].
      revert q0. rewrite C. rewrite Qplus_0_l. apply Qle_not_lt...
     apply ball_gball. simpl.
     rewrite C Qplus_0_l H...
    exfalso. revert q0. rewrite C Qplus_0_l. intro. clear H0. revert q. rewrite H1. apply Qlt_irrefl.
   destruct (Qdec_sign (e1 + e2)) as [[?|?]|?].
     revert q0. rewrite C q Qplus_0_l. apply Qlt_irrefl.
    exfalso. revert q0. rewrite C q Qplus_0_l. apply Qlt_irrefl.
   transitivity b...
  Qed. (* TODO: THE HORROR!! *)

  Lemma gball_ex_triangle (e1 e2: QnnInf) (a b c: m):
    gball_ex e1 a b -> gball_ex e2 b c -> gball_ex (e1 + e2)%QnnInf a c.
  Proof. destruct e1, e2; auto. simpl. apply gball_triangle. Qed.

  Lemma gball_0 (x y: m): gball 0 x y <-> x [=] y.
  Proof. reflexivity. Qed.

  Lemma gball_weak_le (q q': Q): q <= q' -> forall x y, gball q x y -> gball q' x y.
  Proof with auto.
   intros ?? E ?? F.
   unfold gball in F.
   destruct Qdec_sign as [[A | B] | C].
     intuition.
    assert (0 < q') as q'p. apply Qlt_le_trans with q...
    apply (ball_gball (exist _ q' q'p)).
    apply ball_weak_le with (exist _ q B)...
   rewrite F.
   apply gball_refl.
   rewrite <- C...
  Qed.

End gball.
