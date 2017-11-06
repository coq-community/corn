(*
Copyright © 2008 Russell O’Connor

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

Require Import CoRN.reals.Max_AbsIR.
Require Export CoRN.reals.fast.CRArith.
Require Import CoRN.model.metric2.Qmetric.
Require Import Coq.QArith.Qabs.
Require Import CoRN.model.totalorder.QMinMax.
Require Import CoRN.reals.fast.CRcorrect.
Require Import CoRN.reals.fast.CRIR.
Require Import CoRN.tactics.CornTac.
Require Import CoRN.logic.Stability.

Local Open Scope Q_scope.
(**
** Absolute Value
*)
Lemma Qabs_uc_prf : is_UniformlyContinuousFunction
 (Qabs:Q_as_MetricSpace -> Q_as_MetricSpace) Qpos2QposInf.
Proof.
 intros e a b Hab.
 simpl in *.
 unfold Qball in *.
 rewrite <- AbsSmall_Qabs in *.
 apply Qabs_case.
  intros _.
  eapply Qle_trans;[|apply Hab].
  apply Qabs_triangle_reverse.
 intros _.
 stepl (Qabs b - Qabs a); [| simpl; ring].
 setoid_replace (a - b) with (- (b - a)) in Hab; [| simpl; ring].
 rewrite -> Qabs_opp in Hab.
 eapply Qle_trans;[|apply Hab].
 apply Qabs_triangle_reverse.
Qed.

Local Open Scope uc_scope.

Definition Qabs_uc : Q_as_MetricSpace --> Q_as_MetricSpace :=
Build_UniformlyContinuousFunction Qabs_uc_prf.

Definition CRabs : CR --> CR := Cmap QPrelengthSpace Qabs_uc.

Lemma CRabs_correct : forall x,
 (IRasCR (AbsIR x) == CRabs (IRasCR x))%CR.
Proof.
 intros x.
 apply stableEq.
  apply Complete_stable.
  apply stableQ.
 generalize (leEq_or_leEq _ [0] x).
 cut ((x[<=][0] or [0][<=]x) -> (IRasCR (AbsIR x) == CRabs (IRasCR x))%CR).
  unfold Not.
  tauto.
 intros [H|H].
  transitivity (IRasCR ([--]x)).
   apply IRasCR_wd.
   apply AbsIR_eq_inv_x; auto.
  rewrite -> IR_opp_as_CR.
  rewrite -> IR_leEq_as_CR in H.
  rewrite -> IR_Zero_as_CR in H.
  revert H.
  generalize (IRasCR x).
  intros m Hm.
  rewrite -> CRle_min_r in Hm.
  rewrite -> CRmin_boundAbove in Hm.
  setoid_replace (CRabs m)%CR with (- (- (CRabs m)))%CR.
   apply CRopp_wd.
   rewrite <- Hm.
   apply: regFunEq_e.
   intros e.
   simpl.
   rewrite -> Qabs_neg; auto with *.
   rewrite -> Qopp_involutive.
   apply: ball_refl.
  cut (CRabs m== - - CRabs m)%CR.
   intros. assumption.
  ring.
 transitivity (IRasCR x).
  apply IRasCR_wd.
  apply AbsIR_eq_x; auto.
 rewrite -> IR_leEq_as_CR in H.
 rewrite -> IR_Zero_as_CR in H.
 revert H.
 generalize (IRasCR x).
 intros m Hm.
 rewrite -> CRle_max_r in Hm.
 rewrite -> CRmax_boundBelow in Hm.
 rewrite <- Hm.
 apply: regFunEq_e.
 intros e.
 simpl.
 rewrite -> Qabs_pos; auto with *.
Qed.

Lemma approximate_CRabs (x: CR) (e: Qpos):
  approximate (CRabs x) e = Qabs (approximate x e).
Proof. reflexivity. Qed.

Lemma CRabs_AbsSmall : forall a b, (CRabs b[<=]a) <-> AbsSmall a b.
Proof.
 intros a b.
 rewrite <- (CRasIRasCR_id a).
 rewrite <- (CRasIRasCR_id b).
 rewrite <- CRabs_correct.
 rewrite <- IR_AbsSmall_as_CR.
 rewrite <- IR_leEq_as_CR.
 split.
  apply AbsIR_imp_AbsSmall.
 apply AbsSmall_imp_AbsIR.
Qed.

Local Open Scope CR_scope.

Lemma CRabs_pos : forall x:CR, 0 <= x -> CRabs x == x.
Proof.
 intros x.
 rewrite <- (CRasIRasCR_id x).
 rewrite <- CRabs_correct.
 intros H.
 apply IRasCR_wd.
 apply AbsIR_eq_x.
 rewrite -> IR_leEq_as_CR.
 rewrite -> IR_Zero_as_CR.
 auto.
Qed.

Lemma CRabs_0: CRabs 0 == 0.
Proof. apply CRabs_pos, CRle_refl. Qed.

Lemma CRabs_neg: forall x, x <= 0 -> CRabs x == - x.
Proof.
 intros x.
 rewrite <- (CRasIRasCR_id x).
 rewrite <- CRabs_correct.
 intros H.
 rewrite <- IR_opp_as_CR.
 apply IRasCR_wd.
 apply AbsIR_eq_inv_x.
 rewrite -> IR_leEq_as_CR.
 rewrite -> IR_Zero_as_CR.
 auto.
Qed.

Lemma CRabs_cases
  (P: CR -> Prop)
  {Pp: Proper (@st_eq _ ==> iff) P}
  {Ps: forall x, Stable (P x)}:
    forall x, ((0 <= x -> P x) /\ (x <= 0 -> P (- x))) <-> P (CRabs x).
Proof with auto.
 intros.
 apply from_DN.
 apply (DN_bind (CRle_dec x 0)).
 intro.
 apply DN_return.
 destruct H.
  rewrite (CRabs_neg _ c)...
  intuition.
  revert H.
  rewrite (proj2 (CRle_def x 0))...
  rewrite CRopp_0...
 rewrite (CRabs_pos _ c)...
 intuition.
 revert H.
 rewrite (proj2 (CRle_def x 0))...
 rewrite CRopp_0...
Qed.

Lemma CRabs_opp (x: CR): CRabs (-x) == CRabs x.
Proof with auto.
 intros.
 apply from_DN.
 apply (DN_bind (CRle_dec x 0)).
 intros [A | B]; apply DN_return.
  rewrite (CRabs_neg _ A).
  apply CRabs_pos.
  change (-0 <= -x).
  apply -> CRle_opp...
 rewrite (CRabs_pos _ B).
 rewrite CRabs_neg.
  apply CRopp_opp.
 change (-x <= -0).
 apply -> CRle_opp...
Qed.

Lemma CRabs_scale (a : Q) (x : CR) : CRabs (scale a x) == scale (Qabs a) (CRabs x).
Proof.
apply lift_eq_complete with (f := uc_compose CRabs (scale a)) (g := uc_compose (scale (Qabs a)) CRabs).
intros q e1 e2. change (ball (e1 + e2) (Qabs (a * q)) (Qabs a * Qabs q)%Q).
apply <- ball_eq_iff. apply Qabs_Qmult.
Qed.

(* begin hide *)
(* Another proof *)

Lemma CRabs_scale' (a : Q) (x : CR) : CRabs (scale a x) == scale (Qabs a) (CRabs x).
Proof.
unfold CRabs, scale. setoid_rewrite <- fast_MonadLaw2.
apply map_eq_complete. intro q. apply Qabs_Qmult.
Qed.

(* end hide *)

Lemma CRabs_CRmult_Q (a : Q) (x : CR) : CRabs ('a * x) == '(Qabs a) * (CRabs x).
Proof. rewrite !CRmult_scale. apply CRabs_scale. Qed.

Definition CRdistance (x y: CR): CR := CRabs (x - y).

Lemma CRdistance_CRle (r x y: CR): x - r <= y /\ y <= x + r <-> CRdistance x y <= r.
Proof.
 intros. unfold CRdistance.
 rewrite CRabs_AbsSmall.
 unfold AbsSmall. simpl.
 rewrite (CRplus_le_l (x - r) y (r - y)).
 CRring_replace (r - y + (x - r)) (x - y).
 CRring_replace (r - y + y) r.
 rewrite (CRplus_le_l y (x + r) (-r - y)).
 CRring_replace (-r - y + y) (-r).
 CRring_replace (- r - y + (x + r)) (x - y).
 intuition.
Qed.

Lemma CRdistance_comm (x y: CR): CRdistance x y == CRdistance y x.
Proof.
 unfold CRdistance. intros.
 CRring_replace (x - y) (-(y - x)).
 apply CRabs_opp.
Qed.

Import canonical_names.

Program Instance CR_abs : Abs CR := fun x => CRabs x.
Next Obligation. split; [apply CRabs_pos | apply CRabs_neg]. Qed.

