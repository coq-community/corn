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

Require Import Max_AbsIR.
Require Export CRArith.
Require Import Qmetric.
Require Import Qabs.
Require Import QMinMax.
Require Import CRcorrect.
Require Import CRIR.
Require Import CornTac.
Require Import Stability.

Open Local Scope Q_scope.
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

Open Local Scope uc_scope.

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
 generalize (leEq_or_leEq _ Zero x).
 cut ((x[<=]Zero or Zero[<=]x) -> (IRasCR (AbsIR x) == CRabs (IRasCR x))%CR).
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

Lemma CRabs_pos : forall x:CR, ('0 <= x -> CRabs x == x)%CR.
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

Lemma CRabs_0: (CRabs ('0) == '0)%CR.
Proof. apply CRabs_pos, CRle_refl. Qed.

Lemma CRabs_neg: forall x, (x <= '0 -> CRabs x == - x)%CR.
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
    forall x, ((('0 <= x -> P x) /\ (x <= '0 -> P (- x))) <-> P (CRabs x))%CR.
Proof with auto.
 intros.
 apply from_DN.
 apply (DN_bind (CRle_dec x ('0)%CR)).
 intro.
 apply DN_return.
 destruct H.
  rewrite (CRabs_neg _ c)...
  intuition.
  revert H.
  rewrite (proj2 (CRle_def x ('0)%CR))...
  rewrite CRopp_0...
 rewrite (CRabs_pos _ c)...
 intuition.
 revert H.
 rewrite (proj2 (CRle_def x ('0)%CR))...
 rewrite CRopp_0...
Qed.

Definition CRdistance (x y: CR): CR := CRabs (x - y)%CR.

Hint Immediate CRle_refl.

Lemma CRdistance_CRle (r x y: CR): (x - r <= y /\ y <= x + r <-> CRdistance x y <= r)%CR.
Proof.
 intros. unfold CRdistance.
 rewrite CRabs_AbsSmall.
 unfold AbsSmall. simpl.
 rewrite (CRplus_le_l (x - r)%CR y (r - y)%CR).
 assert (r - y + (x - r) == x - y)%CR as E by ring. rewrite E. clear E.
 assert (r - y + y == r)%CR as E by ring. rewrite E. clear E.
 rewrite (CRplus_le_l y (x + r)%CR (-r - y)%CR).
 assert (- r - y + y == - r)%CR as E by ring. rewrite E. clear E.
 assert (- r - y + (x + r) == x - y)%CR as E by ring. rewrite E. clear E.
 intuition.
Qed.
