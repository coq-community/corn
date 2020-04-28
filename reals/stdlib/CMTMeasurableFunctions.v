(*
Copyright © 2020 Vincent Semeria

This program is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License
along with this program;  If not, see <https://www.gnu.org/licenses/>.
*)


Require Import QArith.
Require Import ConstructiveReals.
Require Import ConstructiveAbs.
Require Import ConstructiveSum.
Require Import ConstructiveLimits.
Require Import ConstructivePartialFunctions.
Require Import CMTbase.
Require Import CMTIntegrableFunctions.
Require Import CMTFullSets.
Require Import CMTIntegrableSets.
Require Import CMTprofile.

Local Open Scope ConstructiveReals.


(* A function f is measurable when it is integrable on any
   integrable rectangle A * [-k,k]. *)
Definition MeasurableFunction {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS))) : Type
  := forall (A : (X (ElemFunc IS)) -> Prop) (k : positive),
    IntegrableSet A
    -> IntegrableFunction (XmaxConst (XminConst (Xmult (CharacFunc A) f)
                                               (CR_of_Q _ (Z.pos k # 1)))
                                    (CR_of_Q _ (Z.neg k # 1))).

Lemma MeasurableFunctionExtensional
  : forall {IS : IntegrationSpace}
           (f g : PartialFunction (X (ElemFunc IS))),
    PartialRestriction f g
    -> MeasurableFunction f
    -> MeasurableFunction g.
Proof.
  intros IS f g [d c] fMes A k Aint.
  apply (IntegrableFunctionExtensional
           (XmaxConst (XminConst (Xmult (CharacFunc A) f)
                                 (CR_of_Q (RealT (ElemFunc IS)) (Z.pos k # 1)))
                      (CR_of_Q (RealT (ElemFunc IS)) (Z.neg k # 1)))).
  2: exact (fMes A k Aint).
  split.
  - intros x xdf. simpl in xdf. destruct xdf.
    split. exact s. exact (d x d0).
  - intros. simpl. destruct xD, xG.
    rewrite (c x d1 (d x d1)), (DomainProp g x (d x d1) d3).
    destruct d0. destruct d2. reflexivity. contradiction.
    destruct d2. contradiction. reflexivity.
Qed.

Lemma MeasurableFunctionFull
  : forall {IS : IntegrationSpace}
      (f : PartialFunction (X (ElemFunc IS))),
    MeasurableFunction f
    -> almost_everywhere (Domain f).
Proof.
  intros IS f fMes.
  destruct (@PositiveMeasureSubsetExists IS) as [A Aint Apos].
  specialize (fMes A 1%positive Aint).
  exists (XmaxConst (XminConst (Xmult (CharacFunc A) f) (CR_of_Q (RealT (ElemFunc IS)) 1))
              (CR_of_Q (RealT (ElemFunc IS)) (-1))).
  split. exact fMes.
  intros x xD. apply xD.
Qed.

Lemma IntegrableMeasurable
  : forall {IS : IntegrationSpace}
      (f : PartialFunction (X (ElemFunc IS))),
    IntegrableFunction f
    -> MeasurableFunction f.
Proof.
  intros IS f fInt A k Aint. 
  apply IntegrableMaxConst. apply IntegrableMinConst.
  exact (RestrictedIntegrable fInt Aint).
  apply CR_of_Q_pos. reflexivity.
  apply (CRlt_le_trans _ (CR_of_Q _ 0)). apply CR_of_Q_lt. reflexivity.
  rewrite CR_of_Q_zero. apply CRle_refl.
Qed.

Lemma MeasurableConst
  : forall {IS : IntegrationSpace}
      (a : CRcarrier (RealT (ElemFunc IS))),
    MeasurableFunction (Xconst (X (ElemFunc IS)) a).
Proof.
  intros IS a A k Aint. apply IntegrableMaxConst.
  apply IntegrableMinConst.
  apply (IntegrableFunctionExtensional (Xscale a (CharacFunc A))).
  - split. intros x xdf.
    split. exact xdf. simpl. trivial. intros. simpl.
    destruct xG. destruct xD. destruct d. apply CRmult_comm.
    contradiction. destruct d. contradiction. apply CRmult_comm.
  - apply IntegrableScale, Aint.
  - rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
  - rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
Qed.

Definition MeasurableSet {IS : IntegrationSpace}
           (A : (X (ElemFunc IS)) -> Prop) : Type
  := MeasurableFunction (CharacFunc A).

Lemma MeasurableSetEquiv
  : forall {IS : IntegrationSpace}
      (A : (X (ElemFunc IS)) -> Prop),
    prod (MeasurableSet A
          -> (forall B : (X (ElemFunc IS)) -> Prop,
                IntegrableSet B -> IntegrableFunction (Xmult (CharacFunc A) (CharacFunc B))))
         ((forall B : (X (ElemFunc IS)) -> Prop,
                IntegrableSet B -> IntegrableFunction (Xmult (CharacFunc A) (CharacFunc B))) -> MeasurableSet A).
Proof.
  intros IS A.
  assert (forall B x xD xG k,
             partialApply (Xmult (CharacFunc A) (CharacFunc B)) x xD ==
  partialApply
    (XmaxConst
       (XminConst (Xmult (CharacFunc B) (CharacFunc A))
          (CR_of_Q (RealT (ElemFunc IS)) (Z.pos k # 1)))
       (CR_of_Q (RealT (ElemFunc IS)) (Z.neg k # 1))) x xG).
  { intros. rewrite applyXmaxConst, CRmax_left.
    rewrite applyXminConst, CRmin_left. destruct xD, xG.
    simpl. destruct d. destruct d2. 2: contradiction.
    destruct d0. destruct d1. 2: contradiction. reflexivity.
    destruct d1. contradiction. apply CRmult_comm.
    rewrite CRmult_0_l. destruct d2. contradiction.
    rewrite CRmult_0_r. reflexivity.
    apply (CRle_trans _ 1). simpl. destruct xG.
    destruct d. destruct d0. rewrite CRmult_1_l. apply CRle_refl.
    rewrite CRmult_1_l. apply CRlt_asym, CRzero_lt_one. rewrite CRmult_0_l.
    apply CRlt_asym, CRzero_lt_one. rewrite <- CR_of_Q_one.
    apply CR_of_Q_le. unfold Qle, Qnum, Qden. rewrite Z.mul_1_l, Z.mul_1_r.
    destruct k; discriminate.
    apply (CRle_trans _ 0).
    rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
    apply CRmin_glb. simpl. destruct xG, d. rewrite CRmult_1_l.
    destruct d0. apply CRlt_asym, CRzero_lt_one. apply CRle_refl.
    rewrite CRmult_0_l. apply CRle_refl.
    rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate. }
  split.
  - intros Ames B Bint. specialize (Ames B 1%positive Bint).
    refine (IntegrableFunctionExtensional _ _ _ Ames). split.
    + intros x xdf. destruct xdf. split. exact d0. exact d.
    + intros x xD xG. symmetry. apply H.
  - intros H0 B k Bint. specialize (H0 B Bint).
    refine (IntegrableFunctionExtensional _ _ _ H0). split.
    + intros x xdf. destruct xdf. split. exact d0. exact d.
    + intros x xD xG. apply H.
Qed.


Lemma IntegrableMeasurableSet
  : forall {IS : IntegrationSpace}
      (A : X (ElemFunc IS) -> Prop),
    IntegrableSet A -> MeasurableSet A.
Proof.
  intros IS A Aint B k Bint.
  apply IntegrableMaxConst. apply IntegrableMinConst.
  apply (IntegrableExtensionalAE (CharacFunc (fun x => B x /\ A x))).
  - exists (Xplus (CharacFunc A) (CharacFunc B)).
    split. exact (IntegrablePlus _ _ Aint Bint).
    intros. split. apply H. apply H.
  - exists (CharacFunc A). split. exact Aint.
    intros. simpl. destruct dG. clear H. destruct d0.
    + (* In a *) rewrite CRmult_1_r.
      destruct d, dF. reflexivity. contradict n. split; assumption.
      destruct a0. contradiction. reflexivity.
    + (* Not in a *) rewrite CRmult_0_r.
      destruct dF. destruct a. contradiction. reflexivity.
  - exact (IntegrableSetIntersect _ _ Bint Aint).
  - apply CR_of_Q_pos. reflexivity.
  - apply (CRlt_le_trans _ (CR_of_Q _ 0)).
    apply CR_of_Q_lt. reflexivity. rewrite CR_of_Q_zero. apply CRle_refl.
Qed.

(* In finite integration spaces, like probability spaces, measurable is
   equivalent to integrable. *)
Lemma MeasurableIntegrableSubset
  : forall {IS : IntegrationSpace}
      (A B : X (ElemFunc IS) -> Prop),
    IntegrableSet B
    -> MeasurableSet A
    -> (forall x : X (ElemFunc IS), A x -> B x)
    -> IntegrableSet A.
Proof.
  intros IS A B Bint Ames incl.
  specialize (Ames B 1%positive Bint).
  refine (IntegrableFunctionExtensional _ _ _ Ames). split.
  - intros x xdf. exact (snd xdf).
  - intros. destruct xG.
    + (* in A *)
      simpl. destruct xD. destruct d.
      2: contradict n; exact (incl x a). destruct d0.
      rewrite CRmult_1_l, CRmin_left, CRmax_left. reflexivity.
      rewrite <- CR_of_Q_one. apply CR_of_Q_le. discriminate.
      rewrite CR_of_Q_one. apply CRle_refl. contradiction.
    + (* not in A *)
      simpl. destruct xD. destruct d0. contradiction.
      rewrite CRmult_0_r, CRmin_left, CRmax_left. reflexivity.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
Qed.

Lemma TruncOpp : forall {R : ConstructiveReals} (x : CRcarrier R) (k : positive),
    - CRmax (CRmin x (CR_of_Q _ (Z.pos k # 1)))
            (CR_of_Q _ (Z.neg k # 1))
    == CRmax (CRmin (-x) (CR_of_Q _ (Z.pos k # 1)))
             (CR_of_Q _ (Z.neg k # 1)).
Proof.
  intros. destruct (CRltLinear R).
  setoid_replace (-x) with (-CRone R * x).
  destruct (s (CR_of_Q R (Z.neg k # 1)) x 0).
  rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
  rewrite CRmax_left, (CRmin_left (- (1) * x)).
  - setoid_replace (CR_of_Q R (Z.neg k # 1))
      with (-CRone R * CR_of_Q R (Z.pos k # 1)).
    rewrite CRmax_min_mult_neg. rewrite <- CRopp_mult_distr_l.
    rewrite CRmult_1_l. reflexivity.
    apply (CRplus_le_reg_l 1). rewrite CRplus_opp_r, CRplus_0_r.
    apply CRlt_asym, CRzero_lt_one.
    rewrite <- CRopp_mult_distr_l, CRmult_1_l, <- CR_of_Q_opp.
    apply CR_of_Q_morph. reflexivity.
  - rewrite <- CRopp_mult_distr_l, CRmult_1_l.
    rewrite <- (CRopp_involutive (CR_of_Q R (Z.pos k # 1))).
    apply CRopp_ge_le_contravar. rewrite <- CR_of_Q_opp.
    apply (CRle_trans _ (CR_of_Q R (Z.neg k # 1))).
    apply CR_of_Q_le. apply Qle_refl. apply CRlt_asym, c.
  - apply CRmin_glb. apply CRlt_asym, c. apply CR_of_Q_le. discriminate.
  - rewrite CRmin_left, (CRmax_left (CRmin (- (1) * x) (CR_of_Q R (Z.pos k # 1)))).
    setoid_replace (CR_of_Q R (Z.pos k # 1))
      with (-CRone R * CR_of_Q R (Z.neg k # 1)).
    rewrite CRmin_max_mult_neg, <- CRopp_mult_distr_l, CRmult_1_l. reflexivity.
    apply (CRplus_le_reg_l 1). rewrite CRplus_opp_r, CRplus_0_r.
    apply CRlt_asym, CRzero_lt_one.
    rewrite <- CRopp_mult_distr_l, CRmult_1_l, <- CR_of_Q_opp.
    apply CR_of_Q_morph. reflexivity.
    apply CRmin_glb. apply (CRle_trans _ 0).
    rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
    rewrite <- CRopp_mult_distr_l, CRmult_1_l, <- CRopp_0.
    apply CRopp_ge_le_contravar, CRlt_asym, c.
    apply CR_of_Q_le. discriminate.
    apply (CRle_trans _ 0). apply CRlt_asym, c.
    rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
  - rewrite <- CRopp_mult_distr_l, CRmult_1_l. reflexivity.
Qed.

Lemma TruncPosNeg : forall {R : ConstructiveReals} (y : CRcarrier R) (k : positive),
   CRmax (CRmin (CRmax 0 y) (CR_of_Q R (Z.pos k # 1)))
    (CR_of_Q R (Z.neg k # 1)) +
  CRmax (CRmin (CRmin 0 y) (CR_of_Q R (Z.pos k # 1)))
    (CR_of_Q R (Z.neg k # 1)) ==
  CRmax (CRmin y (CR_of_Q R (Z.pos k # 1)))
    (CR_of_Q R (Z.neg k # 1)).
Proof.
  intros.
  rewrite (CRmax_left (CRmin (CRmax 0 y) (CR_of_Q R (Z.pos k # 1)))).
  rewrite (CRmin_left (CRmin 0 y)).
  - destruct (CRltLinear R).
    destruct (s (CR_of_Q R (Z.neg k # 1)) y 0).
    + rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
    + rewrite (CRmax_left (CRmin y (CR_of_Q R (Z.pos k # 1)))).
      rewrite (CRmax_left (CRmin 0 y)).
      destruct (s 0 y (CR_of_Q R (Z.pos k # 1))).
      rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
      rewrite CRmax_right, (CRmin_left 0 y). rewrite CRplus_0_r. reflexivity.
      apply CRlt_asym, c0. apply CRlt_asym, c0.
      rewrite (CRmin_left y), CRmin_left.
      unfold CRmax, CRmin.
      rewrite CRplus_0_l, <- CRmult_plus_distr_r.
      unfold CRminus. rewrite CRplus_assoc, <- (CRplus_comm (- CRabs R (y + - 0))).
      rewrite <- (CRplus_assoc (CRabs R (y + - 0))), CRplus_opp_r, CRplus_0_l.
      apply (CRmult_eq_reg_r (CR_of_Q R 2)).
      left. rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
      rewrite CRmult_assoc, <- CR_of_Q_mult.
      setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
      rewrite (CR_of_Q_plus R 1 1), CR_of_Q_one, CRmult_1_r, CRmult_plus_distr_l.
      rewrite CRmult_1_r. reflexivity.
      apply CRmax_lub.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
      apply CRlt_asym, c0. apply CRlt_asym, c0.
      apply CRmin_glb.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
      apply CRlt_asym, c. apply CRmin_glb.
      apply CRlt_asym, c. apply CR_of_Q_le. discriminate.
    + rewrite (CRmax_left 0 y). rewrite (CRmin_right 0 y).
      rewrite CRmin_left, CRplus_0_l. rewrite CRmin_left. reflexivity.
      apply (CRle_trans _ 0). apply CRlt_asym, c.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
      apply CRlt_asym, c. apply CRlt_asym, c.
  - apply (CRle_trans _ 0). apply CRmin_l.
    rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
  - apply CRmin_glb. apply (CRle_trans _ 0).
    rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate. apply CRmax_l.
    apply CR_of_Q_le. discriminate.
Qed.

Definition MeasurablePosNegParts {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS)))
  : MeasurableFunction (XposPart f)
    -> MeasurableFunction (XnegPart f)
    -> MeasurableFunction f.
Proof.
  intros fMes gMes A k Aint.
  apply (IntegrableFunctionExtensional
           (Xminus
              (XmaxConst (XminConst (Xmult (CharacFunc A) (XposPart f))
                                    (CR_of_Q (RealT (ElemFunc IS)) (Z.pos k # 1)))
                         (CR_of_Q (RealT (ElemFunc IS)) (Z.neg k # 1)))
              (XmaxConst (XminConst (Xmult (CharacFunc A) (XnegPart f))
                                    (CR_of_Q (RealT (ElemFunc IS)) (Z.pos k # 1)))
                         (CR_of_Q (RealT (ElemFunc IS)) (Z.neg k # 1))))).
  - split. intros x xdf. simpl. simpl in xdf. destruct xdf. split.
    apply p. apply p. intros. simpl.
    destruct xD, d, d0, d1, d2, xG.
    setoid_replace (if d5 then CRone (RealT (ElemFunc IS)) else 0)
      with (if d then CRone (RealT (ElemFunc IS)) else 0).
    setoid_replace (if d0 then CRone (RealT (ElemFunc IS)) else 0)
      with (if d then CRone (RealT (ElemFunc IS)) else 0).
    destruct d.
    + rewrite CRmult_1_l, CRmult_1_l, CRmult_1_l.
      rewrite (DomainProp f x d6 d1), (DomainProp f x d4 d1),
      (DomainProp f x d2 d1), (DomainProp f x d3 d1). clear d6 d4 d3 d2.
      generalize (partialApply f x d1). intro y.
      rewrite (CRmult_comm (CR_of_Q (RealT (ElemFunc IS)) (1 # 2))).
      rewrite <- CRposPartAbsMax.
      rewrite (CRmult_comm (CR_of_Q (RealT (ElemFunc IS)) (1 # 2))).
      do 2 rewrite <- CRopp_mult_distr_l. do 2 rewrite CRmult_1_l.
      rewrite TruncOpp, CRopp_mult_distr_l, CRopp_plus_distr.
      rewrite CRopp_involutive, <- (CRplus_comm y).
      pose proof (CRnegPartAbsMin y). unfold CRminus in H.
      rewrite <- H. clear H. apply TruncPosNeg.
    + rewrite CRmult_0_l, CRmult_0_l, CRmult_0_l.
      rewrite CRmin_left, CRmax_left, CRplus_0_l, CRmult_0_r. reflexivity.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
    + destruct d0. destruct d. reflexivity. contradiction. destruct d.
      contradiction. reflexivity.
    + destruct d5. destruct d. reflexivity. contradiction. destruct d.
      contradiction. reflexivity.
  - apply IntegrableMinus. apply fMes, Aint. apply gMes, Aint.
Qed.

Lemma CR_cv_max : forall {R : ConstructiveReals} (un : nat -> CRcarrier R) (l a : CRcarrier R),
    CR_cv R un l
    -> CR_cv R (fun n : nat => CRmax (un n) a)
             (CRmax l a).
Proof.
  intros. intro p. specialize (H p) as [n H].
  exists n. intros.
  apply (CRle_trans _ _ _ (CRmax_contract _ _ a)).
  exact (H i H0).
Qed.

Lemma CR_cv_min : forall {R : ConstructiveReals} (un : nat -> CRcarrier R) (l a : CRcarrier R),
    CR_cv R un l
    -> CR_cv R (fun n : nat => CRmin (un n) a)
             (CRmin l a).
Proof.
  intros. intro p. specialize (H p) as [n H].
  exists n. intros.
  apply (CRle_trans _ _ _ (CRmin_contract _ _ a)).
  exact (H i H0).
Qed.

Lemma MeasurableSetCompl
  : forall {IS : IntegrationSpace}
      (A : (X (ElemFunc IS)) -> Prop),
    MeasurableSet A -> MeasurableSet (fun x => ~A x).
Proof.
  intros IS A Ameas. apply MeasurableSetEquiv. intros B Bint. 
  destruct (MeasurableSetEquiv A) as [H _]. specialize (H Ameas B Bint).
  refine (IntegrableFunctionExtensional
           _ _ _ (IntegrableMinus Bint H)).
  split.
  - intros x. simpl. intros. destruct H0, p. split. 
    destruct s0. right. intro abs. contradiction. left. exact n. exact s.
  - intros. destruct xD, d.
    + (* In B *)
      simpl. destruct d0. destruct d0. 2: contradiction.
      destruct xG. destruct d1. 2: contradiction.
      destruct d. destruct d0. contradiction.
      rewrite CRmult_1_r, CRmult_1_r, CRmult_1_r. apply CRplus_opp_r.
      destruct d0. 2: contradiction. rewrite CRmult_0_l, CRmult_0_r.
      rewrite CRmult_1_l, CRplus_0_r. reflexivity.
    + (* Not in B *)
      simpl. destruct xG. destruct d0. destruct d2. contradiction.
      destruct d1. contradiction. rewrite CRmult_0_r, CRmult_0_r, CRmult_0_r.
      apply CRplus_0_l.
Qed.

Lemma MeasurableIntersectIntegrable
  : forall {IS : IntegrationSpace}
      {A B : (X (ElemFunc IS)) -> Prop},
    MeasurableSet A
    -> IntegrableSet B
    -> IntegrableSet (fun x => A x /\ B x).
Proof.
  intros IS A B Ames Bint. 
  pose proof (MeasurableSetEquiv A) as [Aint _].
  specialize (Aint Ames B Bint).
  refine (IntegrableFunctionExtensional _ _ _ Aint). split.
  - intros x [d d0]. destruct d, d0.
    left. split; assumption.
    right. intros [_ abs]. contradiction.
    right. intros [abs _]. contradiction.
    right. intros [abs _]. contradiction.
  - intros. simpl. destruct xD. destruct d.
    destruct xG. destruct d0. apply CRmult_1_r.
    destruct a0; contradiction. destruct d0.
    contradict n. split; assumption. apply CRmult_0_r.
    rewrite CRmult_0_l. destruct xG. destruct a; contradiction. reflexivity.
Qed. 

Lemma MeasurableSetUnion
  : forall {IS : IntegrationSpace}
      (A B : (X (ElemFunc IS)) -> Prop),
    MeasurableSet A
    -> MeasurableSet B
    -> MeasurableSet (fun x => A x \/ B x).
Proof.
  intros IS A B Ameas Bmeas. apply MeasurableSetEquiv.
  intros C Cint.
  pose proof (MeasurableSetEquiv A) as [Aint _].
  pose proof (MeasurableSetEquiv B) as [Bint _].
  apply (IntegrableFunctionExtensional
           (Xminus
              (Xplus (Xmult (CharacFunc A) (CharacFunc C))
                     (Xmult (CharacFunc B) (CharacFunc C)))
              (Xmult (CharacFunc A) (CharacFunc (fun x => B x /\ C x))))).
  - split.
    + intros x. simpl. intros. destruct H, p, p. split. 2: exact s0.
      destruct s. left. left. exact a. destruct p1, s.
      left. right. exact b. right. intro abs. destruct abs; contradiction.
    + intros. destruct xD.
      rewrite (applyXminus (Xplus (Xmult (CharacFunc A) (CharacFunc C))
          (Xmult (CharacFunc B) (CharacFunc C))) (Xmult (CharacFunc A) (CharacFunc (fun x0 : X (ElemFunc IS) => B x0 /\ C x0))) x d d0).
      destruct d. rewrite (applyXplus _ _ x d d1).
      destruct d. rewrite (applyXmult _ _ x d d2).
      destruct d1. rewrite (applyXmult _ _ x d1 d3).
      rewrite (DomainProp _ x d3 d2). clear d3.
      destruct d0. rewrite (applyXmult _ _ x d0 d3).
      rewrite (DomainProp _ x d0 d). clear d0.
      destruct xG. rewrite (applyXmult _ _ x d0 d4).
      rewrite (DomainProp _ x d4 d2). clear d4.
      simpl. destruct d2. rewrite CRmult_1_r, CRmult_1_r, CRmult_1_r.
      destruct d1. destruct d3.
      destruct d. destruct d0. rewrite CRmult_1_r.
      unfold CRminus. rewrite CRplus_assoc, CRplus_opp_r. apply CRplus_0_r.
      contradict n. left. exact a0. destruct d0.
      rewrite CRmult_0_l, CRplus_0_l. unfold CRminus.
      rewrite CRopp_0, CRplus_0_r. reflexivity.
      contradict n0. right. exact b.
      contradict n. split; assumption.
      destruct d3. destruct a; contradiction.
      rewrite CRmult_0_r. destruct d. destruct d0.
      rewrite CRplus_0_r. unfold CRminus.
      rewrite CRopp_0, CRplus_0_r. reflexivity.
      contradict n1. left. exact a. destruct d0. destruct o; contradiction.
      rewrite CRplus_0_l. apply CRplus_opp_r.
      destruct d3. destruct a. contradiction.
      rewrite CRmult_0_r, CRmult_0_r, CRmult_0_r, CRplus_0_l.
      apply CRplus_opp_r.
  - apply IntegrableMinus. apply IntegrablePlus.
    apply (Aint Ameas), Cint. apply (Bint Bmeas), Cint.
    apply (Aint Ameas).
    exact (MeasurableIntersectIntegrable Bmeas Cint).
Qed.

Definition MeasurableSetUnionIterate
           {IS : IntegrationSpace}
           (An : nat -> X (ElemFunc IS) -> Prop)
           (aInt : forall n:nat, MeasurableSet (An n))
  : forall n:nat, MeasurableSet (UnionIterate An n).
Proof.
  induction n.
  - apply aInt.
  - simpl. apply MeasurableSetUnion. apply IHn. apply aInt.
Defined.

Lemma MeasurableSetIntersection
  : forall {IS : IntegrationSpace}
      (A B : (X (ElemFunc IS)) -> Prop),
    MeasurableSet A
    -> MeasurableSet B
    -> MeasurableSet (fun x => A x /\ B x).
Proof.
  intros IS A B Ameas Bmeas. apply MeasurableSetEquiv.
  intros C Cint.
  pose proof (MeasurableSetEquiv A) as [Aint _].
  pose proof (MeasurableSetEquiv B) as [Bint _]. 
  pose proof (MeasurableFunctionFull _ Bmeas) as Bfull. 
  specialize (Aint Ameas). specialize (Bint Bmeas).
  apply (IntegrableExtensionalAE
           (Xmult (CharacFunc A) (CharacFunc (fun x => B x /\ C x)))).
  - destruct Bfull.
    exists (Xplus x (Xmult (CharacFunc A) (CharacFunc C))). split.
    apply IntegrablePlus. apply p. apply Aint. exact Cint.
    intros. destruct p, H, d1. specialize (d x0 d0).
    split. 2: exact d2. simpl. destruct d1. destruct d.
    2: right; intros [H1 H0]; contradiction.
    left. split; assumption. right.
    intros [H H0]. contradiction.
  - exists (CharacFunc C). split. exact Cint. intros. simpl.
    destruct dF, dG. clear H. destruct d2. destruct d0.
    destruct d1. destruct d. reflexivity. destruct a0; contradiction.
    destruct d. contradict n. split. exact a0. apply a. reflexivity.
    rewrite CRmult_0_r. destruct d1. contradict n.
    split. apply a. exact c. rewrite CRmult_0_l. reflexivity.
    rewrite CRmult_0_r. destruct d0. destruct a; contradiction.
    apply CRmult_0_r.
  - apply Aint.
    apply (IntegrableFunctionExtensional
             (Xmult (CharacFunc B) (CharacFunc C))).
    split. intros x xdf. destruct xdf.
    destruct d. destruct d0. left. split; assumption.
    right. intro abs. destruct abs. contradiction.
    right. intro abs. destruct abs. contradiction.
    intros. 2: apply Bint; assumption. 
    simpl. destruct xD. destruct d. destruct d0.
    destruct xG. apply CRmult_1_l. contradict n. split; assumption.
    destruct xG. destruct a; contradiction. apply CRmult_0_r.
    rewrite CRmult_0_l. destruct xG. destruct a; contradiction. reflexivity.
Qed.

Lemma Rcauchy_complete_cv
  : forall {R : ConstructiveReals } (un : nat -> CRcarrier R)
      (cau : CR_cauchy R un) (a : CRcarrier R),
    CR_cv R un a
    -> ((let (x,_) := CR_complete R un cau in x) == a)%ConstructiveReals.
Proof.
  intros. destruct (CR_complete R un cau).
  exact (CR_cv_unique un _ _ c H).
Qed.

Lemma SigmaFiniteLimit
  : forall {R : ConstructiveReals} (A : CRcarrier R -> Prop),
    @PartialRestriction R _
      (XpointwiseLimit (fun n => CharacFunc (fun x => -CR_of_Q R (Z.of_nat n # 1) <= x
                                                /\ x <= CR_of_Q R (Z.of_nat n # 1)
                                                /\ A x)))
      (CharacFunc A).
Proof.
  split.
  - intros x [xnD H]. destruct (CRup_nat (CRabs _ x)) as [n H0].
    apply CRabs_lt in H0. destruct H0.
    destruct (xnD n) as [isin|isout].
    + left. apply isin.
    + right. intro abs. apply isout. repeat split. 3: exact abs.
      2: apply CRlt_asym, c.
      rewrite <- (CRopp_involutive x).
      apply CRopp_ge_le_contravar. apply CRlt_asym, c0.
  - intros. simpl.
    destruct (CRup_nat (CRabs _ x)) as [n nup].
    apply CRabs_lt in nup. destruct nup.
    destruct xD as [xnD H], xG.
    + (* in A *)
      unfold CharacFunc, Domain, inject_Z in xnD.
      unfold CharacFunc, partialApply in H.
      apply Rcauchy_complete_cv.
      intro p. exists n. intros. destruct (xnD i).
      unfold CRminus. rewrite CRplus_opp_r.
      rewrite CRabs_right, <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
      apply CRle_refl. exfalso. apply n0. repeat split.
      3: exact a.
      rewrite <- (CRopp_involutive x).
      apply CRopp_ge_le_contravar.
      apply (CRle_trans _ (CR_of_Q R (Z.of_nat n # 1))).
      apply CRlt_asym, c0. apply CR_of_Q_le. unfold Qle, Qnum, Qden.
      do 2 rewrite Z.mul_1_r. apply Nat2Z.inj_le, H0.
      apply (CRle_trans _ (CR_of_Q R (Z.of_nat n # 1))).
      apply CRlt_asym, c. apply CR_of_Q_le. unfold Qle, Qnum, Qden.
      do 2 rewrite Z.mul_1_r. apply Nat2Z.inj_le, H0.
    + (* not in A, constant sequence at 0. *)
      unfold CharacFunc, partialApply in H.
      apply Rcauchy_complete_cv. intro p. exists O.
      intros. destruct (xnD i). exfalso.
      destruct a, H2. contradiction.
      unfold CRminus. rewrite CRopp_0, CRplus_0_r.
      rewrite CRabs_right. rewrite <- CR_of_Q_zero.
      apply CR_of_Q_le. discriminate. apply CRle_refl.
Qed.

Lemma SigmaFiniteMonotone
  : forall {R : ConstructiveReals} (A : CRcarrier R -> Prop),
    let fn := fun n => @CharacFunc R _ (fun x => -CR_of_Q R (Z.of_nat n # 1) <= x
                                      /\ x <= CR_of_Q R (Z.of_nat n # 1)
                                      /\ A x) in
    forall n:nat, partialFuncLe (fn n) (fn (S n)).
Proof.
  intros R A fn n x xdf xdg. simpl.
  destruct xdf.
  - destruct xdg. apply CRle_refl. exfalso.
    apply n0. destruct a, H0. repeat split. 3: exact H1.
    apply (CRle_trans _ (- CR_of_Q R (Z.of_nat n # 1))).
    apply CRopp_ge_le_contravar. apply CR_of_Q_le.
    unfold Qle, Qnum, Qden.
    do 2 rewrite Z.mul_1_r. apply Nat2Z.inj_le, le_S, le_refl. exact H.
    apply (CRle_trans _ (CR_of_Q R (Z.of_nat n # 1)) _ H0).
    apply CR_of_Q_le. unfold Qle, Qnum, Qden.
    do 2 rewrite Z.mul_1_r. apply Nat2Z.inj_le, le_S, le_refl.
  - destruct xdg. apply CRlt_asym, CRzero_lt_one. apply CRle_refl.
Qed.

(* A classical hypothesis, to explain the relation with the
   classical Lebesgue measure. *)
Definition IncrSeqCvT : Type
  := forall (R : ConstructiveReals) (un : nat -> CRcarrier R) (a : CRcarrier R),
    (forall n:nat, un n <= un (S n))
    -> (forall n:nat, un n <= a)
    -> CR_cauchy R un.

(* This proves that a Lebesgue-measurable function is Bishop-measurable,
   when we assume the classical theorem IncrSeqCvT.
   Because non-negative Lebesgue-measurable functions are non-decreasing
   limits of simple functions, which are Bishop-measurable. *)
Definition MeasurableMonotoneConvergenceClassical
           {IS : IntegrationSpace}
           (fn : nat -> PartialFunction (X (ElemFunc IS)))
  : (forall n:nat, MeasurableFunction (fn n))
    -> (forall n:nat, partialFuncLe (fn n) (fn (S n)))
    -> IncrSeqCvT
         (* The sequence fn is assumed to converge everywhere,
            because the sequence fn is derived from a hypothetical
            Lebesgue-measurable function f, that we want to prove
            is Bishop-integrable.

            This hypothesis is necessary, to replace the convergence of
            integrals in the constructive monotone convergence theorem.
            For example, the sequence of constant measurable functions n
            converges nowhere, so we cannot conclude that the empty
            function is measurable. *)
    -> (forall x : X (ElemFunc IS),
           Domain (XpointwiseLimit fn) x)
    -> MeasurableFunction (XpointwiseLimit fn).
Proof.
  intros fnMes H cl cv A k Aint.
  assert (forall n:nat, partialFuncLe
    (XmaxConst (XminConst (Xmult (CharacFunc A) (fn n)) (CR_of_Q (RealT (ElemFunc IS)) (Z.pos k # 1)))
       (CR_of_Q (RealT (ElemFunc IS)) (Z.neg k # 1)))
    (XmaxConst
       (XminConst (Xmult (CharacFunc A) (fn (S n))) (CR_of_Q (RealT (ElemFunc IS)) (Z.pos k # 1)))
       (CR_of_Q (RealT (ElemFunc IS)) (Z.neg k # 1)))).
  { intros n x xdf xdg.
    simpl. destruct xdf, xdg. destruct d.
    destruct d1. 2: contradiction. rewrite CRmult_1_l, CRmult_1_l.
    apply CRmax_lub.
    apply (CRle_trans _ (CRmin (partialApply (fn (S n)) x d2) (CR_of_Q (RealT (ElemFunc IS)) (Z.pos k # 1)))).
    2: apply CRmax_l.
    apply CRmin_glb. 2: apply CRmin_r.
    apply (CRle_trans _ (partialApply (fn n) x d0)).
    apply CRmin_l. apply H. apply CRmax_r.
    destruct d1. contradiction. rewrite CRmult_0_l, CRmult_0_l. apply CRle_refl. }
  assert (forall n : nat,
        (fun n0 : nat => Integral (fnMes n0 A k Aint)) n <=
        (fun n0 : nat => Integral (fnMes n0 A k Aint)) (S n)).
  { intro n. apply IntegralNonDecreasing. apply H0. }
  assert (forall n : nat,
        (fun n0 : nat => Integral (fnMes n0 A k Aint)) n <=
        MeasureSet Aint * CR_of_Q (RealT (ElemFunc IS)) (Z.pos k # 1)).
  { intro n.
    apply (CRle_trans _ (Integral (IntegrableScale (CharacFunc A)
                                                     (CR_of_Q (RealT (ElemFunc IS)) (Z.pos k # 1))
                                                     Aint))).
    apply IntegralNonDecreasing. intros x xdf xdg.
    simpl. destruct xdf, xdg. destruct d. 2: contradiction.
    rewrite CRmult_1_l, CRmult_1_r. apply CRmax_lub.
    apply CRmin_r. apply CR_of_Q_le. discriminate.
    destruct d. contradiction. rewrite CRmult_0_l, CRmult_0_r.
    apply CRmax_lub. apply CRmin_l. rewrite <- CR_of_Q_zero.
    apply CR_of_Q_le. discriminate.
    rewrite IntegralScale. apply CRle_refl. }
  destruct (CR_complete _ _ (cl _ (fun n => Integral (fnMes n A k Aint))
                 (MeasureSet Aint * CR_of_Q _ (Z.pos k # 1))
                 H1 H2)) as [l lcv].
  destruct (IntegralMonotoneConvergence
              IS (fun n => XmaxConst
       (XminConst (Xmult (CharacFunc A) (fn n))
                  (CR_of_Q (RealT (ElemFunc IS)) (Z.pos k # 1))) (CR_of_Q (RealT (ElemFunc IS)) (Z.neg k # 1)))
              (fun n => fnMes n A k Aint) l H0 lcv).
  apply (IntegrableFunctionExtensional
           (XpointwiseLimit
           (fun n : nat =>
            XmaxConst
              (XminConst (Xmult (CharacFunc A) (fn n)) (CR_of_Q (RealT (ElemFunc IS)) (Z.pos k # 1)))
              (CR_of_Q (RealT (ElemFunc IS)) (Z.neg k # 1))))).
  2: exact x.
  split. intros y ydf. simpl. simpl in ydf. destruct ydf.
  split. exact (fst (x0 O)). exists (fun n => snd (x0 n)).
  specialize (cv y). destruct cv.
  apply (CR_cauchy_eq (fun n : nat => partialApply (fn n) y (x1 n))).
  2: exact c1. intro n. apply DomainProp.
  intros. apply applyPointwiseLimit. apply CR_cv_max.
  apply CR_cv_min. destruct xD, xG. destruct d.
  - setoid_replace (partialApply (Xmult (CharacFunc A) (XpointwiseLimit fn)) x0 (left a, d0))
      with (partialApply (XpointwiseLimit fn) x0 d0).
    2: simpl; rewrite CRmult_1_l; reflexivity.
    pose proof (applyPointwiseLimit fn x0 d0
                                    (partialApply (XpointwiseLimit fn) x0 d0)) as [H3 _].
    apply (CR_cv_eq _ (fun n : nat => partialApply (fn n) x0 (let (xn, _) := d0 in xn n))).
    intro n. simpl. destruct (x1 n), d. rewrite CRmult_1_l. apply DomainProp.
    contradiction. apply H3. reflexivity.
  - setoid_replace (partialApply (Xmult (CharacFunc A) (XpointwiseLimit fn)) x0 (right n, d0))
      with (CRzero (RealT (ElemFunc IS))).
    2: simpl; rewrite CRmult_0_l; reflexivity.
    apply (CR_cv_eq _ (fun _ => 0)). intros.
    simpl. destruct (x1 n0), d. contradiction. rewrite CRmult_0_l. reflexivity.
    intro p. exists O. intros. unfold CRminus.
    rewrite CRplus_opp_r, CRabs_right, <- CR_of_Q_zero.
    apply CR_of_Q_le. discriminate. apply CRle_refl.
Qed.

(*
Lemma MeasurableSetUnionCountable
  : forall {IS : IntegrationSpace}
      (An : nat -> ((X (ElemFunc IS)) -> Prop)),
    (forall n:nat, MeasurableSet (An n))
    -> IncrSeqCvT (* Maybe we can weaken this classical hypothesis *)
    -> MeasurableSet (fun x => exists n:nat, An n x).
Proof.
  intros IS An AnMeas IncrSeqCv.
  apply MeasurableSetEquiv.
  intros B Bint.
  (* Integrate union intersected with B by the monotone convergence theorem.
     The limit of the intersected integrals will come from majoration and
     IncrSeqCv. *)
  assert (forall n : nat, IntegrableFunction
                     (Xmult (CharacFunc (UnionIterate An n)) (CharacFunc B)))
    as unionMes.
  { intro n. pose proof (MeasurableSetUnionIterate An AnMeas). 
    pose proof (MeasurableSetEquiv (UnionIterate An n)) as [mes _].
    exact (mes (X n) B Bint). } 
  assert (forall n : nat, @partialFuncLe (RealT (ElemFunc IS)) _
         (Xmult (CharacFunc (UnionIterate An n)) (CharacFunc B))
         (Xmult (CharacFunc (UnionIterate An (S n))) (CharacFunc B))).
  { intros n x xdf xdg. simpl. destruct xdf, xdg.
    destruct d0. destruct d2. 2: contradiction.
    rewrite CRmult_1_r, CRmult_1_r. destruct d. destruct d1.
    apply CRle_refl. contradict n0. left. exact u.
    destruct d1. apply CRlt_asym, CRzero_lt_one. apply CRle_refl.
    rewrite CRmult_0_r. destruct d2. contradiction.
    rewrite CRmult_0_r. apply CRle_refl. }
  assert (forall n : nat, Integral (unionMes n) <= Integral Bint).
  { shelve. }
  specialize (IncrSeqCv _ (fun n : nat => Integral (unionMes n))
                        (Integral Bint)
                        (fun n => IntegralNonDecreasing _ _ _ _ (H n)) H0).
  apply CR_complete in IncrSeqCv. destruct IncrSeqCv as [l lcv].
  destruct (IntegralMonotoneConvergence
              IS (fun n => Xmult (CharacFunc (UnionIterate An n)) (CharacFunc B))
              unionMes l H lcv) as [limInt _].
  apply (IntegrableFunctionExtensional
           (XpointwiseLimit
                (fun n : nat => Xmult (CharacFunc (UnionIterate An n)) (CharacFunc B)))).
  2: exact limInt. split.
  - intros x [xn c]. split. 2: apply (xn O).
    clear lcv l. apply CR_complete in c. destruct c as [l lcv].
    split. 2: exact H1. destruct H2 as [xn c].

    destruct H. simpl.
    destruct H0.
    left. destruct e. exists x0. apply H. right. intro abs.
    contradict n. destruct abs. exists x0. split; assumption.
    destruct H0. exfalso. destruct e, H. contradiction. 
    simpl. right. intro abs. destruct abs.
    + intros x [H|H]. simpl. left. destruct H. split.
      exists x0. apply H. apply H. right. intros [[n H0] H1].
      apply H. exists n. split; assumption.
    + intros. simpl. destruct xD, xG. reflexivity.
      exfalso. apply n. destruct e. split. exists x0.
      apply H. apply H.
      exfalso. apply n. destruct a, H. exists x0. split; assumption.
      reflexivity.
  - assert (forall n:nat, IntegrableSet (fun x => An n x /\ B x)) as AnInt.
    { intro n. apply AnMeas, Bint. }
    specialize (IncrSeqCv _ (fun n : nat =>
     MeasureSet
       (IntegrableSetUnionIterate
          (fun (n0 : nat) (x : X (ElemFunc IS)) => An n0 x /\ B x) AnInt n))
                          (MeasureSet Bint)).
    apply CR_complete in IncrSeqCv.
    destruct IncrSeqCv as [l lim].
    + apply (IntegrableSetCountableUnion _ AnInt l lim).
    + intros. apply IntegralNonDecreasing. intros x xdf xdg.
      simpl. destruct xdf. destruct xdg. apply CRle_refl.
      exfalso. apply n0. apply applyUnionIterate.
      apply applyUnionIterate in u. destruct u. exists x0.
      destruct H, H0. repeat split; try assumption.
      apply (le_trans _ _ _ H), le_S, le_refl.
      destruct xdg. apply CRlt_asym, CRzero_lt_one. apply CRle_refl.
    + intros. apply IntegralNonDecreasing. intros x xdf xdg.
      simpl. destruct xdf. destruct xdg. apply CRle_refl.
      exfalso. apply applyUnionIterate in u. destruct u, H, H0.
      contradiction.
      destruct xdg. apply CRlt_asym, CRzero_lt_one. apply CRle_refl.
Qed.
*)

Definition IntegralSupport {IS : IntegrationSpace}
       (f : PartialFunction (X (ElemFunc IS)))
       (fInt : IntegrableFunction f)
       (A : (X (ElemFunc IS)) -> Prop)
       (eps : CRcarrier (RealT (ElemFunc IS))) : Type :=
  { isupp_int : IntegrableSet A
                & IntegralDistance
                    fInt (RestrictedIntegrable fInt isupp_int) < eps }.

Lemma IntegralSupportExists
  : forall {IS : IntegrationSpace}
      (f : PartialFunction (X (ElemFunc IS)))
      (fInt : IntegrableFunction f)
      (eps : CRcarrier (RealT (ElemFunc IS))),
    0 < eps
    -> { t : CRcarrier _
            & prod (t < eps)
                   (IntegralSupport
                      f fInt
                      (fun x => exists xD:Domain (Xabs f) x,
                           t <= partialApply (Xabs f) x xD) eps) }.
Proof.
  intros. 
  pose proof (InverseImageIntegrableAE (Xabs f) (IntegrableAbs fInt))
    as [jumps invIm].
  pose proof (Un_cv_nat_real _ _ (IntegralTruncateLimitZero f fInt)
                             eps H) as [n nmaj].
  pose proof (CRuncountable jumps 0 _ (CRmin_lt _ _ _ (invSuccRealPositive n) H))
    as [t [[tpos tmin] tcont]].
  specialize (invIm t tpos tcont) as [invIm _].
  exists t. split. apply (CRlt_le_trans _ _ _ tmin). apply CRmin_r.
  exists invIm.
  specialize (nmaj n (le_refl n)). refine (CRle_lt_trans _ _ _ _ nmaj).
  unfold CRminus. rewrite CRopp_0, CRplus_0_r, CRabs_right.
  apply IntegralNonDecreasing. intros x xdf xdg.
  destruct xdf, d0, d0. 
  - (* t <= |f x| *)
    apply (CRle_trans _ 0).
    simpl. rewrite CRmult_1_l.
    rewrite <- CRopp_mult_distr_l, CRmult_1_l, (DomainProp f x d1 d).
    rewrite CRplus_opp_r, CRabs_right. apply CRle_refl. apply CRle_refl.
    simpl. apply CRmin_glb. apply CRabs_pos.
    rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
  - (* |f x| < t *)
    apply (CRle_trans _ (CRabs _ (partialApply f x d))).
    simpl. rewrite CRmult_0_l, CRmult_0_r, CRplus_0_r. apply CRle_refl.
    assert (CRabs _ (partialApply f x d) <= t).
    { intro abs. contradict n0. exists d. apply CRlt_asym, abs. }
    clear n0. apply CRmin_glb.
    rewrite applyXabs, (DomainProp f x xdg d). apply CRle_refl.
    apply (CRle_trans _ _ _ H0). apply CRlt_asym.
    apply (CRlt_le_trans _ _ _ tmin). apply CRmin_l.
  - apply IntegralNonNeg. intros x xdf. apply CRmin_glb.
    apply CRabs_pos. rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
Qed.

Definition RestrictedMeasurable_pos
           {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS)))
           (A : (X (ElemFunc IS)) -> Prop)
  : IntegrableFunction f
    -> MeasurableSet A
    -> nonNegFunc f
    -> IntegrableFunction (Xmult (CharacFunc A) f).
Proof.
  intros fInt Ames fPos. 
  (* Make a sequence of supports converging to f's integral. *)
  assert (forall n:nat, 0 < CRpow (CR_of_Q (RealT (ElemFunc IS)) (1#2)) n).
  { intro n. apply pow_lt, CR_of_Q_pos. reflexivity. }
  pose proof (fun n:nat => IntegralSupportExists
                        f fInt _ (H n)) as Bn.
  assert (forall n:nat, IntegrableFunction
                   (Xmult (CharacFunc (fun x => A x /\ let (t,_) := Bn n in
           exists xD : Domain (Xabs f) x, t <= partialApply (Xabs f) x xD
                                                   )) f))
    as fnInt.
  { intro n. apply (RestrictedIntegrable fInt).
    pose proof (MeasurableSetEquiv A) as [H0 _].
    destruct (Bn n) as [t p], p, i as [i c0].
    specialize (H0 Ames _ i).
    refine (IntegrableFunctionExtensional _ _ _ H0).
    split. intros x xdf. destruct xdf, d.
    2: right; intro abs; destruct abs; contradiction.
    destruct d0. left. split; assumption.
    right; intro abs; destruct abs; contradiction.
    intros. destruct xD. simpl. destruct d.
    rewrite CRmult_1_l. destruct d0,xG. reflexivity.
    contradict n0. split; assumption.
    contradict n0. apply a0. reflexivity. rewrite CRmult_0_l.
    destruct xG. contradict n0. apply a. reflexivity. }
  assert (forall n:nat, IntegrableFunction
                   (Xmult (CharacFunc (fun x => let (t,_) := Bn n in
           exists xD : Domain (Xabs f) x, t <= partialApply (Xabs f) x xD)) f))
    as gnInt.
  { intro n. apply (RestrictedIntegrable fInt).
    destruct (Bn n) as [t p], p, i as [i c0]. exact i. }
  destruct (series_cv_maj
              (fun n : nat =>
                 Integral (IntegrableAbs (IntegrableMinus (fnInt (S n)) (fnInt n))))
              (fun n:nat => CRpow (CR_of_Q (RealT (ElemFunc IS)) (1#2)) n
                       * CR_of_Q _ 2)
              (CR_of_Q _ 2 * CR_of_Q _ 2)) as [l lcv].
  - intro n. rewrite CRabs_right.
    2: apply IntegralNonNeg; intros x xdf; apply CRabs_pos.
    apply (CRle_trans _ (Integral (IntegrableAbs (IntegrableMinus (gnInt (S n)) (gnInt n))))).
    apply IntegralNonDecreasingAE.
    destruct (Bn n) as [t p], p, i as [i c0].
    exists (Xmult (CharacFunc A) (CharacFunc (fun x => 
           exists xD : Domain (Xabs f) x, t <= partialApply (Xabs f) x xD
                                                   ))).
    split. 
    pose proof (MeasurableSetEquiv A) as [H0 _].
    specialize (H0 Ames _ i). exact H0. 
    intros x xdA xdf xdg.
    simpl. destruct xdf, xdg, d, d1, d0, d2. destruct xdA, d7.
    + (* x in A *)
      rewrite (DomainProp f x d6 d5). clear d6.
      rewrite (DomainProp f x d4 d3). clear d4.
      destruct d. destruct d1. 2: contradict n0; apply a0.
      destruct d0. destruct d2. apply CRle_refl.
      contradict n0. apply a1. destruct d2. 2: apply CRle_refl.
      contradict n0. split. exact a. exact e.
      destruct d1. contradict n0. split. exact a. apply y.
      destruct d0. destruct d2. apply CRle_refl.
      contradict n2. apply a0. destruct d2. 2: apply CRle_refl.
      contradict n2. split. exact a. exact e.
    + (* x not in A *)
      destruct d. contradict n0. apply a. rewrite CRmult_0_l.
      destruct d0. contradict n0. apply a. rewrite CRmult_0_l.
      rewrite CRmult_0_r, CRplus_0_r, CRabs_right.
      apply CRabs_pos. apply CRle_refl.
    + apply (CRle_trans _ _ _ (IntegralDistance_triang _ _ _ _ fInt _)).
      rewrite (CR_of_Q_plus _ 1 1), CR_of_Q_one, CRmult_plus_distr_l.
      rewrite CRmult_1_r. apply CRplus_le_compat. generalize (gnInt (S n)).
      intro i. simpl in i. destruct (Bn (S n)), p, i0.
      apply CRlt_asym, (CRlt_trans _ (CRpow (CR_of_Q (RealT (ElemFunc IS)) (1 # 2)) (S n))).
      refine (CRle_lt_trans _ _ _ _ c0).
      apply IntegralNonDecreasing. intros y ydf ydg.
      rewrite (DomainProp _ y ydf ydg). apply CRle_refl.
      apply (CRlt_le_trans _ (CR_of_Q _ 1
                              * CRpow (CR_of_Q (RealT (ElemFunc IS)) (1 # 2)) n)).
      apply CRmult_lt_compat_r. apply pow_lt, CR_of_Q_pos. reflexivity.
      apply CR_of_Q_lt. reflexivity.
      rewrite CR_of_Q_one, CRmult_1_l. apply CRle_refl.
      generalize (gnInt n).
      intro i. simpl in i. destruct (Bn n), p, i0.
      apply CRlt_asym. refine (CRle_lt_trans _ _ _ _ c0).
      apply IntegralNonDecreasing. intros y ydf ydg.
      rewrite (DomainProp _ y ydf ydg). apply CRle_refl.
  - apply series_cv_scale. exact GeoHalfTwo.
  - destruct (IntegrableXpointwiseLimit _ fnInt l (fst lcv)) as [limInt _].
    pose proof (MeasurableFunctionFull _ Ames) as [h hint].
    refine (IntegrableExtensionalAE _ _ _ _ limInt). destruct hint.
    + exists (Xplus h f). split. exact (IntegrablePlus _ _ i fInt).
      intros. destruct H0. split.
      specialize (d x d0). exact d. exact d1.
    + exists h. destruct hint. split. exact i. intros. 
      clear d H0 i h. destruct dG. apply applyPointwiseLimit.
      intro p. destruct (CRltLinear (RealT (ElemFunc IS))) as [_ s].
      assert (0 < CR_of_Q (RealT (ElemFunc IS)) (1 # (2*p))).
      { apply CR_of_Q_pos. reflexivity. }
      specialize (s 0 (partialApply f x d0) _ H0) as [c|c].
      * (* 0 < f x. x will eventually be in the support,
           then the left term becomes 0. *)
        simpl in c.
        apply (CR_cv_open_above _ _ _ (@GeoCvZero (RealT (ElemFunc IS)))) in c.
        destruct c as [n nmaj]. exists n. intros i H1. 
        specialize (nmaj i H1). destruct dF.
        generalize (x0 i). intros. 
        destruct (Bn i) as [t r], r, i0 as [j c1], d1.
        simpl. rewrite (DomainProp f x d2 d0). clear d2.
        destruct d. destruct d1. unfold CRminus.
        rewrite CRplus_opp_r, CRabs_right.
        rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate. apply CRle_refl.
        contradict n0. split. exact a. exists d0.
        apply CRlt_asym, (CRlt_trans _ _ _ c0), (CRlt_le_trans _ _ _ nmaj). 
        apply CRle_abs. destruct d1. destruct a. contradiction.
        unfold CRminus.
        rewrite CRmult_0_l, CRplus_opp_r, CRabs_right.
        rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate. apply CRle_refl.
      * (* f x < 1 / 2p *)
        exists O. intros.
        apply (CRle_trans _ _ _ (CRabs_triang _ _)).
        setoid_replace (1#p) with ((1#(2*p)) + (1#(2*p)))%Q.
        2: rewrite Qinv_plus_distr; reflexivity.
        rewrite CR_of_Q_plus. apply CRplus_le_compat.
        destruct dF, (x0 i). simpl. destruct d1.
        rewrite CRmult_1_l, CRabs_right, (DomainProp f x d2 d0).
        apply CRlt_asym, c. apply fPos. rewrite CRmult_0_l, CRabs_right.
        rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
        apply CRle_refl. 
        rewrite CRabs_opp. simpl. destruct d.
        rewrite CRmult_1_l, CRabs_right. apply CRlt_asym, c.
        apply fPos. rewrite CRmult_0_l, CRabs_right.
        rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
        apply CRle_refl. 
Qed.

Definition RestrictedMeasurable
           {IS : IntegrationSpace}
           {f : PartialFunction (X (ElemFunc IS))}
           {A : (X (ElemFunc IS)) -> Prop}
  : IntegrableFunction f
    -> MeasurableSet A
    -> IntegrableFunction (Xmult (CharacFunc A) f).
Proof.
  intros fInt Ames. 
  apply (IntegrableFunctionExtensional
           (Xminus (Xmult (CharacFunc A) (XposPart f))
                   (Xmult (CharacFunc A) (XnegPart f)))).
  - split. intros x xdf. destruct xdf. split. apply d. apply d.
    intros. destruct xD, xG.
    rewrite (applyXmult _ _ x d1 d2).
    rewrite <- (SplitPosNegParts _ x _ (snd d) (snd d0)).
    rewrite (applyXminus (Xmult (CharacFunc A) (XposPart f))
                         (Xmult (CharacFunc A) (XnegPart f)) x d d0).
    destruct d, d0.
    rewrite (applyXmult _ _ x d d3), (applyXmult _ _ x d0 d4).
    rewrite (DomainProp _ x d0 d), (DomainProp _ x d1 d).
    unfold CRminus. rewrite CRmult_plus_distr_l, CRopp_mult_distr_r.
    reflexivity.
  - apply IntegrableMinus. apply RestrictedMeasurable_pos.
    apply IntegrablePosPart, fInt. exact Ames.
    apply applyXposPartNonNeg.
    apply RestrictedMeasurable_pos.
    apply IntegrableNegPart, fInt. exact Ames.
    apply applyXnegPartNonNeg.
Qed.


(* IntegrableSet (fun x => A x /\ ~B x) is not enough,
   because it leads to ~~B. *)
Record SetApprox {IS : IntegrationSpace}
       (A : (X (ElemFunc IS)) -> Prop) (Aint : IntegrableSet A)
       (eps : CRcarrier (RealT (ElemFunc IS))) : Type
  := { sa_approx : (X (ElemFunc IS)) -> Prop;
       sa_bint : IntegrableSet sa_approx;
       sa_mes : MeasureSet Aint - MeasureSet sa_bint < eps;
       sa_inc : forall x, sa_approx x -> A x; }.

(* Generators for integrable sets, akin to a basis for a topology. *)
Definition IntegrableSetsGen (IS : IntegrationSpace) : Type
  := forall (A : (X (ElemFunc IS)) -> Prop) (Aint : IntegrableSet A)
       (eps : CRcarrier (RealT (ElemFunc IS))),
    0 < eps -> SetApprox A Aint eps.

(* Increasing sequence of subsets of A that converge towards A,
   and which disjoint increments are generators. *)
Fixpoint IntegrableApproxSequence
         {IS : IntegrationSpace}
         (gen : IntegrableSetsGen IS)
         (A : (X (ElemFunc IS)) -> Prop) (Aint : IntegrableSet A)
         (n : nat) {struct n}
  : { U : X (ElemFunc IS) -> Prop  &  IntegrableSet U }.
Proof.
  destruct n as [|p].
  - destruct (gen A Aint 1 (CRzero_lt_one _)).
    exists sa_approx0. exact sa_bint0.
  - destruct (IntegrableApproxSequence IS gen A Aint p) as [U Uint].
    exists (fun x => U x \/ (sa_approx _ _ _ (gen _ (IntegrableSetDifference A U Aint Uint)
                  (CRpow (CR_of_Q _ (1#2)) (S p))
                  (pow_lt _ (S p) (CR_of_Q_pos (1#2) eq_refl))) x)).
    exact (IntegrableSetUnion _ _ Uint (sa_bint _ _ _ (gen _ (IntegrableSetDifference A U Aint Uint)
                  (CRpow (CR_of_Q _ (1#2)) (S p))
                  (pow_lt _ (S p) (CR_of_Q_pos (1#2) eq_refl))))).
Defined.

Lemma IntegrableApproxSequenceInc
  : forall {IS : IntegrationSpace}
      (gen : IntegrableSetsGen IS)
      (A : X (ElemFunc IS) -> Prop)
      (Aint : IntegrableSet A) (n : nat) (x : X (ElemFunc IS)),
    let (U,_) := IntegrableApproxSequence gen A Aint n in
    U x -> A x.
Proof.
  induction n.
  - intros. simpl. destruct (gen A Aint 1 (CRzero_lt_one (RealT (ElemFunc IS)))).
    apply sa_inc0.
  - intros. simpl. destruct (IntegrableApproxSequence gen A Aint n).
    intros. destruct H. apply IHn, H.
    apply (sa_inc _ _ _ _ x H).
Qed.

Lemma IntegrableApproxSequenceIncr
  : forall {IS : IntegrationSpace}
      (gen : IntegrableSetsGen IS)
      (A : X (ElemFunc IS) -> Prop)
      (Aint : IntegrableSet A) (i j : nat) (x : X (ElemFunc IS)),
    le i j
    -> (let (U,_) := IntegrableApproxSequence gen A Aint i in U x)
    -> (let (U,_) := IntegrableApproxSequence gen A Aint j in U x).
Proof.
  induction j.
  - intros. inversion H. subst i. exact H0.
  - intros. apply Nat.le_succ_r in H. destruct H.
    specialize (IHj x H).
    simpl; destruct (IntegrableApproxSequence gen A Aint j).
    left. exact (IHj H0). subst i. exact H0.
Qed.

Lemma IntegrableApproxSequenceBound
  : forall {IS : IntegrationSpace}
      (gen : IntegrableSetsGen IS)
      (A : X (ElemFunc IS) -> Prop)
      (Aint : IntegrableSet A) (n : nat)
      (Uint : IntegrableSet
                (let (U,_) := IntegrableApproxSequence gen A Aint n in U)),
    MeasureSet Aint - MeasureSet Uint
    < CRpow (CR_of_Q _ (1#2)) n.
Proof.
  intros. destruct n.
  - simpl. simpl in Uint.
    destruct (gen A Aint 1 (CRzero_lt_one (RealT (ElemFunc IS)))).
    apply (CRle_lt_trans
             _ (MeasureSet Aint - MeasureSet sa_bint0)).
    apply CRplus_le_compat_l, CRopp_ge_le_contravar.
    apply MeasureNonDecreasing. intros. exact H.
    exact sa_mes0.
  - simpl.
    pose proof (IntegrableApproxSequenceInc gen A Aint n) as Uinc.
    simpl in Uint; 
    destruct (IntegrableApproxSequence gen A Aint n) as [U Vint].
    apply (CRle_lt_trans _ (MeasureSet (IntegrableSetDifference A U Aint Vint)
                            - MeasureSet (sa_bint _ _ _ 
              (gen (fun x0 : X (ElemFunc IS) => A x0 /\ ~ U x0)
                 (IntegrableSetDifference A U Aint Vint)
                 (CR_of_Q (RealT (ElemFunc IS)) (1 # 2) *
                  CRpow (CR_of_Q (RealT (ElemFunc IS)) (1 # 2)) n)
                 (pow_lt (CR_of_Q (RealT (ElemFunc IS)) (1 # 2)) 
                    (S n) (CR_of_Q_pos (1 # 2) eq_refl)))))).
    2: apply sa_mes.
    rewrite <- MeasureDifferenceIncluded, <- MeasureDifferenceIncluded.
    apply MeasureNonDecreasing. intros. destruct H.
    split. split. exact H. intro abs. apply H0. left. exact abs.
    intro abs. apply H0. right. exact abs. intros. 
    exact (sa_inc _ _ _ _ x H). intros. destruct H.
    2: exact (proj1 (sa_inc _ _ _ _ x H)). apply Uinc, H.
Qed. 

Lemma IntegrableApproxSequenceLimit
  : forall {IS : IntegrationSpace}
      (gen : IntegrableSetsGen IS)
      (A : X (ElemFunc IS) -> Prop)
      (Aint : IntegrableSet A),
    { intUnion : IntegrableSet
                   (fun x => exists n:nat, let (U,_) := IntegrableApproxSequence
                                                gen A Aint n in U x)
    | MeasureSet intUnion == MeasureSet Aint }.
Proof.
  intros.
  assert (forall n:nat, IntegrableSet
                   (fun x => let (U, _) := IntegrableApproxSequence gen A Aint n in U x))
    as seqInt.
  { intro n. destruct (IntegrableApproxSequence gen A Aint n). exact i. }
  apply (IntegrableSetCountableUnion
              (fun n x => let (U,_) := IntegrableApproxSequence gen A Aint n in U x)
              seqInt (MeasureSet Aint)).
  intro p. pose proof (@GeoCvZero (RealT (ElemFunc IS)) p) as [n ncv].
  exists n. intros i H.
  rewrite CRabs_minus_sym, CRabs_right.
  - apply (CRle_trans _ (MeasureSet Aint - MeasureSet (seqInt i))).
    apply CRplus_le_compat_l, CRopp_ge_le_contravar.
    apply MeasureNonDecreasing. intros.
    apply applyUnionIterate. exists i. exact (conj (le_refl i) H0).
    specialize (ncv i H).
    apply (CRle_trans _ (CRpow (CR_of_Q _ (1#2)) i)).
    generalize (seqInt i). intro iint.
    pose proof (IntegrableApproxSequenceBound gen A Aint i).
    destruct (IntegrableApproxSequence gen A Aint i).
    apply CRlt_asym, X.
    unfold CRminus in ncv. rewrite CRopp_0, CRplus_0_r, CRabs_right in ncv.
    exact ncv. apply pow_le. rewrite <- CR_of_Q_zero.
    apply CR_of_Q_le. discriminate.
  - rewrite <- (CRplus_opp_r (MeasureSet Aint)).
    apply CRplus_le_compat_l, CRopp_ge_le_contravar.
    apply MeasureNonDecreasing. intros. apply applyUnionIterate in H0.
    destruct H0, H0.
    pose proof (IntegrableApproxSequenceInc gen A Aint x0 x).
    destruct (IntegrableApproxSequence gen A Aint x0). exact (H2 H1).
Qed.

(* It is enough to truncate on generator sets to prove that
   a function is measurable. Bishop's lemma 4.9. *)
Lemma MeasurableGen
  : forall {IS : IntegrationSpace}
      (h : PartialFunction (X (ElemFunc IS))),
    (forall (A : (X (ElemFunc IS)) -> Prop) (Aint : IntegrableSet A)
       (k : positive)
       (eps : CRcarrier (RealT (ElemFunc IS))) (epsPos : 0 < eps),
        { B : SetApprox A Aint eps &
        IntegrableFunction
          (XmaxConst (XminConst (Xmult (CharacFunc (sa_approx _ _ _ B)) h)
                                (CR_of_Q _ (Z.pos k # 1)))
                     (CR_of_Q _ (Z.neg k # 1))) })
    -> MeasurableFunction h.
Proof.
  intros IS f fMes A n Aint. 
  pose (fun S Sint eps epsPos => let (B,_) := fMes S Sint n eps epsPos in B) as gen.
  (* Make a disjoint sequence of subsets B_k that converges to A
     in measure. Bound h by n so that B_k h converges monotonically
     towards (union B_k) h. *)
  pose (fun k:nat => match k with
                | O => let (U,_):=IntegrableApproxSequence gen A Aint O in U
                | S i => let (U,Uint):=IntegrableApproxSequence gen A Aint i in
                        sa_approx _ _ _
                                  (gen _ (IntegrableSetDifference A U Aint Uint)
                                       (CRpow (CR_of_Q (RealT (ElemFunc IS)) (1 # 2)) k)
                                       (pow_lt (CR_of_Q (RealT (ElemFunc IS)) (1 # 2)) 
                                               k (CR_of_Q_pos (1 # 2) eq_refl)))
                end) as Bk.
  assert (forall k:nat, IntegrableSet (Bk k)) as BkInt.
  { intro k. unfold Bk. destruct k.
    - destruct (IntegrableApproxSequence gen A Aint 0). exact i.
    - destruct (IntegrableApproxSequence gen A Aint k). apply sa_bint. }
  assert (forall k:nat, Integral (BkInt (S k)) <= CRpow (CR_of_Q _ (1 # 2)) k) as BkMaj.
  { intro k. pose proof (IntegrableApproxSequenceBound gen A Aint k). 
    pose proof (IntegrableApproxSequenceInc gen A Aint k).
    destruct (IntegrableApproxSequence gen A Aint k) as [U Uint] eqn:des.
    apply (CRle_trans _ (MeasureSet (IntegrableSetDifference A U Aint Uint))).
    apply IntegralNonDecreasing. intros x xdf xdg.
    simpl. simpl in xdf. destruct xdf. rewrite des in y.
    destruct xdg. apply CRle_refl. contradict n0.
    exact (sa_inc _ _ _ _ x y).
    destruct xdg. apply CRlt_asym, CRzero_lt_one. apply CRle_refl.
    rewrite MeasureDifferenceIncluded. apply CRlt_asym, X.
    intros. exact (H x H0). }
  pose (fun k:nat => (XmaxConst
              (XminConst
                 (Xmult (CharacFunc (Bk k)) f)
                 (CR_of_Q (RealT (ElemFunc IS)) (Z.pos n # 1)))
              (CR_of_Q (RealT (ElemFunc IS)) (Z.neg n # 1)))) as fk.
  assert (forall k:nat, IntegrableFunction (fk k)) as fkInt.
  { unfold fk, Bk. intro k. destruct k.
    - simpl. unfold gen. 
      destruct (fMes A Aint n 1 (CRzero_lt_one (RealT (ElemFunc IS)))), x; apply i.
    - destruct (IntegrableApproxSequence gen A Aint k) as [U Uint].
      unfold gen.
      destruct (fMes (fun x : X (ElemFunc IS) => A x /\ ~ U x)
                     (IntegrableSetDifference A U Aint Uint) n
                     (CRpow (CR_of_Q (RealT (ElemFunc IS)) (1 # 2)) (S k))
                     (pow_lt (CR_of_Q (RealT (ElemFunc IS)) (1 # 2)) 
                             (S k) (CR_of_Q_pos (1 # 2) eq_refl)))
        as [B Bint].
      refine (IntegrableFunctionExtensional _ _ _ Bint). split.
      + intros y yD. exact yD.
      + intros. rewrite (DomainProp _ x xD xG). reflexivity. }
  assert (forall (i : nat) x (xkD : forall k:nat, Domain (CharacFunc (Bk k)) x),
             (let (U, _) := IntegrableApproxSequence gen A Aint i in U x)
             -> @CRsum (RealT (ElemFunc IS))
                      (fun k : nat => partialApply _ x (xkD k)) i == 1) as BkDisjoint.
  { induction i.
    - intros. simpl.
      destruct (xkD O). reflexivity. contradict n0.
      simpl. simpl in H.
      destruct (gen A Aint 1 (CRzero_lt_one (RealT (ElemFunc IS)))). exact H.
    - intros. specialize (IHi x xkD).
      simpl in H; destruct (IntegrableApproxSequence gen A Aint i) as [U Uint] eqn:des.
      destruct H.
      (* In U so last term is zero. *)
      specialize (IHi H). rewrite <- (CRplus_0_r 1). simpl.
      simpl in IHi. rewrite IHi. clear IHi. apply CRplus_morph. reflexivity.
      destruct (xkD (S i)). 2: reflexivity. exfalso.
      unfold Bk in b. rewrite des in b.
      pose proof (sa_inc _ _ _ _ x b). destruct H0. contradiction.
      (* Not in U x so all previous terms are 0 in the sum. *)
      clear IHi.
      rewrite <- (CRplus_0_l 1). simpl. apply CRplus_morph.
      pose proof (sa_inc _ _ _ _ x H). destruct H0. clear H.
      rewrite (CRsum_eq _ (fun k => 0)), sum_const, CRmult_0_l. reflexivity.
      intros. destruct (xkD i0). 2: reflexivity. contradict H1.
      pose proof (IntegrableApproxSequenceIncr
                    gen A Aint i0 i x H). rewrite des in H1.
      apply H1. clear H1.
      unfold Bk in b. destruct i0. 
      destruct (IntegrableApproxSequence gen A Aint 0); exact b. 
      simpl; destruct (IntegrableApproxSequence gen A Aint i0).
      right. exact b.
      (* In last Bk so last term equals 1. *)
      destruct (xkD (S i)). reflexivity. contradict n0.
      simpl. rewrite des. exact H. } 
  assert (forall (i j : nat) x (xkD : forall k:nat, Domain (fk k) x)
            (dG : Domain (Xmult (CharacFunc A) f) x),
             (let (U, _) := IntegrableApproxSequence gen A Aint j in U x)
             -> le j i
             -> CRsum (fun k : nat => partialApply (fk k) x (xkD k)) i
               == partialApply (XmaxConst
          (XminConst (Xmult (CharacFunc A) f)
             (CR_of_Q _ (Z.pos n # 1)))
          (CR_of_Q _ (Z.neg n # 1))) x dG) as fkDisjoint.
  { intros. unfold fk.
    rewrite (CRsum_eq _ (fun k:nat =>
                           partialApply _ x (fst (xkD k))
                           * partialApply (XmaxConst
          (XminConst f
             (CR_of_Q _ (Z.pos n # 1)))
          (CR_of_Q _ (Z.neg n # 1))) x 
       (snd (xkD O)))).
    - rewrite sum_scale.
      rewrite (BkDisjoint i x (fun k => fst (xkD k))), CRmult_1_l.
      simpl. destruct dG, d. rewrite CRmult_1_l, (DomainProp f x _ d0).
      reflexivity. contradict n0.
      pose proof (IntegrableApproxSequenceInc gen A Aint j x).
      destruct (IntegrableApproxSequence gen A Aint j). exact (H1 H).
      exact (IntegrableApproxSequenceIncr
               gen A Aint j i x H0 H).
    - intros. simpl. destruct (xkD i0), d. simpl.
      do 2 rewrite CRmult_1_l. rewrite (DomainProp f x d0 (snd (xkD 0%nat))).
      reflexivity. simpl. rewrite CRmult_0_l, CRmult_0_l.
      rewrite CRmin_left, CRmax_left. reflexivity.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate. } 
  destruct (series_cv_maj (fun k : nat => Integral (IntegrableAbs (fkInt k)))
                          (fun k => match k with
                                 | O => MeasureSet (BkInt O)
                                 | S i => (CRpow (CR_of_Q _ (1 # 2)) i) end
                                 * CR_of_Q _ (Z.pos n # 1))
                          ((CR_of_Q _ 2 + MeasureSet (BkInt O))
                           * CR_of_Q _ (Z.pos n # 1)))
    as [l lcv].
  - intro k. unfold fk. rewrite CRabs_right.
    apply (CRle_trans
             _ (Integral (IntegrableScale _ (CR_of_Q _ (Z.pos n # 1))
                                          (BkInt k)))).
    apply IntegralNonDecreasing. intros x xdf xdg.
    simpl. destruct xdf, xdg, d.
    rewrite CRmult_1_l, CRmult_1_r.
    apply CRabs_le. split. rewrite <- CR_of_Q_opp.
    setoid_replace (- (Z.pos n # 1))%Q with (Z.neg n # 1).
    apply CRmax_r. reflexivity. apply CRmax_lub.
    apply CRmin_r. apply CR_of_Q_le. discriminate.
    contradiction. contradiction.
    rewrite CRmult_0_l, CRmult_0_r. rewrite CRmin_left, CRmax_left, CRabs_right.
    apply CRle_refl. apply CRle_refl.
    rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
    rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
    rewrite IntegralScale, CRmult_comm.
    destruct k. rewrite CRmult_comm. apply CRle_refl.
    rewrite CRmult_comm. apply CRmult_le_compat_r. rewrite <- CR_of_Q_zero.
    apply CR_of_Q_le. discriminate. exact (BkMaj k).
    apply IntegralNonNeg. intros x xdf. apply CRabs_pos.
  - apply series_cv_scale.
    apply (series_cv_shift (fun n0 : nat => match n0 with
     | 0%nat => MeasureSet (BkInt 0%nat)
     | S i => CRpow (CR_of_Q (RealT (ElemFunc IS)) (1 # 2)) i
     end) O); simpl. exact GeoHalfTwo.
  - destruct lcv.
    pose proof (IntegrableFunctionsComplete IS fk fkInt l s) as [rep repcv]. 
    apply (IntegrableExtensionalAE (XinfiniteSumAbs (IntFn rep))).
    + exists (Xplus (CharacFunc A) (XinfiniteSumAbs (IntFn rep))).
      split. apply IntegrablePlus. apply Aint.
      exists rep. apply PartialRestriction_refl. intros. split. exact (fst H).
      destruct repcv, p. clear c0. specialize (d x (snd H)).
      destruct d as [xn d]. pose proof (xn O). destruct H0. exact d1.
    + pose proof (IntegrableApproxSequenceLimit gen A Aint) as [Uint Umes].
      destruct (MeasureZeroAE _ (IntegrableSetDifference A _ Aint Uint)) as [h hInt].
      rewrite MeasureDifferenceIncluded.
      rewrite Umes. unfold CRminus. apply CRplus_opp_r.
      intros. destruct H.
      pose proof (IntegrableApproxSequenceInc gen A Aint x0 x).
      destruct (IntegrableApproxSequence gen A Aint x0). exact (H0 H). 
      exists (Xplus (CharacFunc (fun x : X (ElemFunc IS) =>
            exists n : nat,
              let (U, _) := IntegrableApproxSequence gen A Aint n in U x))
               h).
      split. exact (IntegrablePlus _ _ Uint (fst hInt)).
      intros. destruct H, hInt. specialize (n0 x d0).
      destruct repcv, p. rewrite (c0 x dF (d1 x dF)). clear c0.
      destruct d.
      (* Inside union *)
      clear n0. destruct e. apply applyInfiniteSumAbs. intro p.
      exists x0. intros. rewrite (fkDisjoint i0 x0 x _ dG).
      unfold CRminus. rewrite CRplus_opp_r, CRabs_right.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
      apply CRle_refl. exact H. exact H0.
      (* Outside A *)
      assert (~ A x).
      { intro abs. apply n0. split; assumption. }
      clear n1 n0 i d0 h. transitivity (CRzero (RealT (ElemFunc IS))).
      apply applyInfiniteSumAbs.
      apply (CR_cv_eq _ (fun _ => 0)). 2: apply CR_cv_const.
      intros. rewrite <- (CRmult_0_l (INR (S n0))).
      rewrite (CRsum_eq _ (fun _ => 0)). symmetry. apply sum_const.
      intros. unfold fk. simpl.
      destruct (domainInfiniteSumAbsIncReverse
            (fun k : nat =>
             XmaxConst
               (XminConst (Xmult (CharacFunc (Bk k)) f)
                  (CR_of_Q (RealT (ElemFunc IS)) (Z.pos n # 1)))
               (CR_of_Q (RealT (ElemFunc IS)) (Z.neg n # 1))) x 
            (d1 x dF) i), d.
      contradict H. unfold Bk in b.
      destruct i.
      pose proof (IntegrableApproxSequenceInc gen A Aint O x).
      destruct (IntegrableApproxSequence gen A Aint 0). exact (H b).
      destruct (IntegrableApproxSequence gen A Aint i).
      exact (proj1 (sa_inc _ _ _ _ x b)). 
      rewrite CRmult_0_l, CRmin_left, CRmax_left. reflexivity.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
      simpl. destruct dG, d. contradiction.
      rewrite CRmult_0_l, CRmin_left, CRmax_left. reflexivity.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
    + exists rep. apply PartialRestriction_refl. 
Qed.

Lemma CR_cv_maj : forall {R : ConstructiveReals}
                    (un vn : nat -> CRcarrier R) (s : CRcarrier R),
    (forall n:nat, CRabs R (un (S n) - un n) <= vn n)
    -> series_cv vn s
    -> { l : CRcarrier R & prod (CR_cv _ un l) (l <= s + un O) }.
Proof.
  intros. 
  destruct (series_cv_maj (fun n => un (S n) - un n) vn s H H0) as [l [lcv lmaj]].
  apply (CR_cv_eq (fun n => un (S n) - un O)) in lcv.
  - exists (l + un O). split. apply (CR_cv_shift _ 1).
    apply (CR_cv_eq _ (fun n => un (S n) - un O + un O)).
    intros. unfold CRminus. rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
    rewrite Nat.add_comm. reflexivity. apply CR_cv_plus.
    exact lcv. apply CR_cv_const. unfold CRminus.
    apply CRplus_le_compat_r. exact lmaj.
  - induction n. reflexivity. simpl. rewrite IHn. clear IHn.
    rewrite CRplus_comm. unfold CRminus. rewrite CRplus_assoc.
    apply CRplus_morph. reflexivity.
    rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l. reflexivity.
Qed.

(* Bishop's lemma 4.10. We strengthen the previous lemma by
   allowing the function to approximate within epsilon on each
   generator subset. This proves that continuous functions are
   measurable, because they are approximated by piecewise-constant functions. *)
Lemma MeasurableGenApprox
  : forall {IS : IntegrationSpace}
      (h : PartialFunction (X (ElemFunc IS))),
    almost_everywhere (Domain h)
    -> (forall (A : (X (ElemFunc IS)) -> Prop) (Aint : IntegrableSet A)
         (n : positive)
         (eps : CRcarrier (RealT (ElemFunc IS))) (epsPos : 0 < eps),
          { fB : prod (PartialFunction (X (ElemFunc IS)))
                      (SetApprox A Aint eps)
                & prod (IntegrableFunction (fst fB))
                       (forall (x : X (ElemFunc IS)) (xdh : Domain h x)
                          (xdf : Domain (fst fB) x),
                           sa_approx _ _ _ (snd fB) x
                           -> CRabs _ (partialApply (XmaxConst (XminConst h 
                                                                       (CR_of_Q _ (Z.pos n # 1)))
                                                            (CR_of_Q _ (Z.neg n # 1)))
                                                 x xdh
                                    - partialApply _ x xdf) < eps) })
    -> MeasurableFunction h.
Proof.
  intros IS h dom H. apply MeasurableGen.
  intros A Aint k eps epsPos. specialize (H A Aint k).
  (* We define another family of generator sets and call the previous lemma on it. *)
  assert (forall (i:nat), 0 < eps * CRpow (CR_of_Q _ (1 # 2)) i) as H0.
  { intros. apply (CRmult_lt_0_compat _ _ _ epsPos).
    apply pow_lt, CR_of_Q_pos. reflexivity. }
  pose (fun (i:nat) => sa_approx
                    _ _ _ (let (fB,_) := H (eps * CRpow (CR_of_Q _ (1#2)) (S i))
                                           (H0 (S i)) in
                           snd fB))
    as Bi.
  assert ({ BI : IntegrableSet (fun x => forall i:nat, Bi i x)
                 & MeasureSet Aint - MeasureSet BI < eps })
    as Bint.
  { destruct (CR_cv_maj
                (fun n => - MeasureSet (IntegrableSetIntersectIterate
                                     _ (fun i => sa_bint _ _ _ (let (fB,_) := H (eps * CRpow (CR_of_Q _ (1 # 2)) (S i)) (H0 (S i)) in snd fB)) n))
                (fun n => (CRpow (CR_of_Q _ (1 # 2)) (2 + n) * eps))
                (CR_of_Q _ (1 # 2) * eps)).
    intro n. unfold CRminus. rewrite CRopp_involutive, CRplus_comm.
    pose proof (@MeasureDifferenceIncluded IS). unfold CRminus in H1.
    rewrite <- H1, CRabs_right. clear H1.
    2: apply MeasureNonNeg.
    apply (CRle_trans _ (MeasureSet Aint
                         - MeasureSet (sa_bint _ _ _
          (let (fB,_) := H (eps * CRpow (CR_of_Q _ (1 # 2)) (2 + n))
             (H0 (2 + n)%nat) in snd fB)))).
    rewrite <- MeasureDifferenceIncluded.
    apply MeasureNonDecreasing. intros. destruct H1. split.
    apply (sa_inc _ _ _ (let (fB,_) := H (eps * CRpow (CR_of_Q _ (1 # 2)) (S n))
                             (H0 (S n)) in snd fB)).
    destruct n; apply H1. intro abs. contradict H2.
    split; assumption. apply sa_inc.
    rewrite <- (CRmult_comm eps). apply CRlt_asym. apply sa_mes.
    clear H1. intros. apply H1.
    apply (series_cv_eq (fun n : nat => CRpow (CR_of_Q _ (1 # 2)) n
                                   * ((CR_of_Q _ (1 # 2)) * (CR_of_Q _ (1 # 2)) * eps))).
    intros. simpl. rewrite <- CRmult_assoc.
    apply CRmult_morph. 2: reflexivity.
    rewrite (CRmult_comm (CRpow (CR_of_Q _ (1 # 2)) n)), <- CRmult_assoc.
    reflexivity.
    apply (CR_cv_proper _ (CR_of_Q _ 2 * (CR_of_Q _ (1 # 2) * CR_of_Q _ (1 # 2) * eps))).
    apply series_cv_scale. exact GeoHalfTwo.
    rewrite <- CRmult_assoc, <- CRmult_assoc, <- (CR_of_Q_mult _ 2).
    setoid_replace (2 * (1#2))%Q with 1%Q.
    rewrite CR_of_Q_one, CRmult_1_l. reflexivity. reflexivity.
    destruct p. simpl in c0. apply CR_cv_opp in c.
    apply (CR_cv_eq (fun n : nat => MeasureSet
           (IntegrableSetIntersectIterate
              _ (fun i : nat =>
               sa_bint A Aint
                 (eps * CRpow (CR_of_Q (RealT (ElemFunc IS)) (1 # 2)) (S i))
                 (let (fB, _) := H
                    (eps * CRpow (CR_of_Q (RealT (ElemFunc IS)) (1 # 2)) (S i))
                    (H0 (S i)) in snd fB)) n))) in c.
    destruct (IntegrableSetCountableIntersect _ _ _ c)
      as [intersectInt c1].
    exists intersectInt. clear c. rewrite <- CRopp_involutive, <- c1 in c0.
    clear c1 x. apply (CRplus_le_compat_l (MeasureSet Aint)) in c0.
    rewrite (CRplus_comm (CR_of_Q (RealT (ElemFunc IS)) (1 # 2) * eps)) in c0.
    rewrite <- CRplus_assoc in c0. 
    apply (CRle_lt_trans _ _ _ c0). clear c0.
    apply (CRlt_le_trans _ (eps * (CR_of_Q (RealT (ElemFunc IS)) (1 # 2) * 1)
                            + CR_of_Q (RealT (ElemFunc IS)) (1 # 2) * eps)).
    apply CRplus_lt_compat_r. apply sa_mes.
    rewrite CRmult_1_r, CRmult_comm, <- CRmult_plus_distr_r, <- CR_of_Q_plus.
    setoid_replace ((1 # 2) + (1 # 2))%Q with 1%Q.
    rewrite CR_of_Q_one, CRmult_1_l. apply CRle_refl. reflexivity.
    intro n. apply CRopp_involutive. }
  assert (forall (x : X (ElemFunc IS)), (forall i : nat, Bi i x) -> A x).
  { intros. unfold Bi in H1. exact (sa_inc _ _ _ _ x (H1 O)). }
  destruct Bint as [BI Bmaj].
  exists (Build_SetApprox IS A Aint eps _ BI Bmaj H1).
  pose (fun i:nat => let (fB,_) := H (eps * CRpow (CR_of_Q _ (1#2)) (S i))
                                (H0 (S i)) in fst fB) as fi.
  assert (forall i:nat, IntegrableFunction
                   (Xmult (CharacFunc (fun x => forall i : nat, Bi i x))
                          (fi i))) as fiInt.
  { intro i. unfold fi.
    destruct (H (eps * CRpow (CR_of_Q _ (1 # 2)) (S i)) (H0 (S i))).
    exact (RestrictedIntegrable (fst p) BI). } 
  destruct (series_cv_maj 
              (fun n : nat => Integral (IntegrableAbs
               (IntegrableMinus (fiInt (S n)) (fiInt n))))
              (fun n:nat => CRpow (CR_of_Q _ (1#2)) n
                       * (CR_of_Q _ 2 * eps * MeasureSet BI))
              (CR_of_Q _ 2 * (CR_of_Q _ 2 * eps * MeasureSet BI)))
    as [l lcv].
  - intro n. rewrite CRabs_right.
    destruct dom as [hdom [hdomInt dom]].
    apply (CRle_trans _ (Integral (IntegrablePlus _ _
                                     (IntegrableScale _ 0 hdomInt)
                                     (IntegrableScale _ (CR_of_Q _ 2 * (eps * CRpow (CR_of_Q _ (1 # 2)) n)) BI)))).
    apply IntegralNonDecreasing. intros x xdf xdg. 
    unfold fi. unfold fi in xdf.
    destruct xdg as [d d0]. destruct d0.
    pose proof (b n) as bn. unfold Bi in bn.
    pose proof (b (S n)) as bSn. unfold Bi in bSn.
    destruct (H (eps * CRpow (CR_of_Q _ (1 # 2)) (S n)) (H0 (S n)))
      as [x0 p].
    destruct (H (eps * CRpow (CR_of_Q _ (1 # 2)) (S (S n))) (H0 (S (S n))))
      as [x1 p0].
    rewrite applyXabs.
    + setoid_replace (partialApply (Xminus
          (Xmult (CharacFunc (fun x2 : X (ElemFunc IS) => forall i : nat, Bi i x2)) (fst x1))
          (Xmult (CharacFunc (fun x2 : X (ElemFunc IS) => forall i : nat, Bi i x2)) (fst x0)))
                                   x xdf)
        with (partialApply _ x (fst xdf)
            - partialApply
             (XmaxConst (XminConst h (CR_of_Q _ (Z.pos k # 1)))
                (CR_of_Q _ (Z.neg k # 1))) x (dom x d)
            + (partialApply
             (XmaxConst (XminConst h (CR_of_Q _ (Z.pos k # 1)))
                (CR_of_Q _ (Z.neg k # 1))) x (dom x d)
            - partialApply (Xmult (CharacFunc (fun x2 : X (ElemFunc IS) => forall i : nat, Bi i x2))
             (fst x0)) x (snd xdf))).
      apply (CRle_trans _ _ _ (CRabs_triang _ _)).
      rewrite applyXplus, applyXscale, CRmult_0_l, CRplus_0_l.
      rewrite applyXscale, (CR_of_Q_plus _ 1 1), CR_of_Q_one.
      rewrite CRmult_plus_distr_r, CRmult_plus_distr_r, CRmult_1_l.
      apply CRplus_le_compat.
      destruct xdf, d1, d0, d0. simpl.
      rewrite CRmult_1_r, CRmult_1_l. apply CRlt_asym.
      destruct p0. specialize (c x (dom x d) d3).
      apply (CRle_lt_trans _ (CRabs (RealT (ElemFunc IS))
        (partialApply
           (XmaxConst (XminConst h (CR_of_Q (RealT (ElemFunc IS)) (Z.pos k # 1)))
              (CR_of_Q (RealT (ElemFunc IS)) (Z.neg k # 1))) x 
           (dom x d) - partialApply (fst x1) x d3))).
      rewrite CRabs_minus_sym. apply CRle_refl.
      apply (CRlt_le_trans
               _ (eps * CRpow (CR_of_Q (RealT (ElemFunc IS)) (1 # 2)) (S (S n)))).
      apply c. exact bSn.
      simpl. rewrite <- CRmult_assoc.
      rewrite <- CRmult_assoc. apply CRmult_le_compat_r.
      apply pow_le. rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
      rewrite <- (CRmult_1_r eps), CRmult_assoc, CRmult_assoc.
      apply CRmult_le_compat_l. apply CRlt_asym, epsPos.
      rewrite CRmult_1_l, <- CR_of_Q_one, <- CR_of_Q_mult.
      apply CR_of_Q_le. discriminate.
      contradiction. 
      destruct xdf, d1, d1. simpl. rewrite CRmult_1_r, CRmult_1_l.
      apply CRlt_asym.
      apply (CRlt_le_trans _ (eps * CRpow (CR_of_Q _ (1 # 2)) (S n))).
      apply (snd p). 
      exact bn. apply CRmult_le_compat_l. apply CRlt_asym, epsPos.
      rewrite <- (CRmult_1_l (CRpow (CR_of_Q (RealT (ElemFunc IS)) (1 # 2)) n)).
      apply CRmult_le_compat_r.
      apply pow_le. rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
      rewrite <- CR_of_Q_one. apply CR_of_Q_le. discriminate.
      contradiction.
      unfold CRminus. rewrite CRplus_assoc. 
      destruct xdf.
      rewrite (applyXminus (Xmult
          (CharacFunc
             (fun x2 : X (ElemFunc IS) => forall i : nat, Bi i x2)) (fst x1)) (Xmult
          (CharacFunc
             (fun x2 : X (ElemFunc IS) => forall i : nat, Bi i x2))
          (fst x0)) x d0 d1).
      apply CRplus_morph. reflexivity.
      rewrite <- CRplus_assoc, CRplus_opp_l, CRplus_0_l. reflexivity.
    + (* out of B *)
      simpl. rewrite CRmult_0_r, CRmult_0_l.
      destruct xdf, d0, d0. contradiction. rewrite CRmult_0_l.
      destruct d1, d0. contradiction. rewrite CRmult_0_l, CRmult_0_r.
      rewrite CRabs_right. apply CRle_refl. rewrite CRplus_0_r. apply CRle_refl.
    + (* Integral majoration *)
      rewrite IntegralPlus, IntegralScale, CRmult_0_r, CRplus_0_l.
      rewrite IntegralScale. rewrite CRmult_comm, <- CRmult_assoc, <- CRmult_assoc.
      rewrite (CRmult_comm (CR_of_Q (RealT (ElemFunc IS)) 2 * eps)).
      apply CRle_refl.
    + apply IntegralNonNeg. intros x xdf.
      rewrite applyXabs. apply CRabs_pos.
  - apply series_cv_scale. exact GeoHalfTwo.
  - destruct lcv.
    destruct (IntegrableXpointwiseLimit _ fiInt l s) as [limInt fcv]. clear s.
    refine (IntegrableExtensionalAE _ _ _ _ limInt).
    + destruct dom as [hdom [hdomInt dom]].
      exists (Xplus hdom (XpointwiseLimit
                (fun i : nat =>
                 Xmult
                   (CharacFunc (fun x : X (ElemFunc IS) => forall i0 : nat, Bi i0 x))
                   (fi i)))). split.
      apply IntegrablePlus. exact hdomInt. exact limInt.
      intros x [xdf xdg]. split.
      2: exact (dom x xdf). simpl. destruct xdg as [xDn xdg].
      destruct (xDn O). exact d.
    + destruct dom as [hdom [hdomInt dom]]. exists hdom. split.
      exact hdomInt. intros. unfold sa_approx.
      apply applyPointwiseLimit. destruct dG, d. simpl in s.
      (* Inside the intersection, the fi converge towards h. *)
      apply (CR_cv_proper _ (partialApply (XmaxConst
          (XminConst h
             (CR_of_Q (RealT (ElemFunc IS)) (Z.pos k # 1)))
          (CR_of_Q (RealT (ElemFunc IS)) (Z.neg k # 1))) x d0)).
      2: simpl; rewrite CRmult_1_l; reflexivity.
      apply (CR_cv_eq _ (fun n : nat => partialApply (fi n) x
                                                (let (xn, _) := dF in snd (xn n)))).
      intro n. simpl. destruct dF, (x0 n), d.
      rewrite CRmult_1_l. reflexivity. contradiction. 
      intro p.
      assert (CR_cv _ (fun i => CRpow (CR_of_Q _ (1 # 2)) i * eps) 0).
      { apply (CR_cv_proper _ (0 * eps)).
        apply CR_cv_scale. exact GeoCvZero. apply CRmult_0_l. }
      specialize (H3 p) as [j jmaj]. exists j. intros.
      specialize (jmaj j (le_refl j)).
      unfold fi. destruct dF. destruct (x0 i). unfold snd.
      unfold fi in d1. unfold Bi in s. specialize (s i).
      destruct (H (eps * CRpow (CR_of_Q _ (1 # 2)) (S i)) (H0 (S i))).
      destruct p0 as [i0 c1]. rewrite CRabs_minus_sym. specialize (c1 x).
      apply (CRle_trans _ (eps * CRpow (CR_of_Q _ (1 # 2)) (S i))).
      apply CRlt_asym, c1, s. clear c1. 
      refine (CRle_trans _ _ _ _ jmaj).
      unfold CRminus. rewrite CRopp_0, CRplus_0_r.
      rewrite CRabs_right, CRmult_comm. apply CRmult_le_compat_r.
      apply CRlt_asym, epsPos.
      apply Nat.le_exists_sub in H3. destruct H3, H3. subst i.
      rewrite <- (CRmult_1_l (CRpow (CR_of_Q _ (1 # 2)) j)).
      replace (S (x2 + j)) with (S x2 + j)%nat. 2: reflexivity.
      rewrite <- pow_plus_distr. apply CRmult_le_compat_r.
      apply pow_le. rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
      apply (CRmult_le_reg_l (CRpow (CR_of_Q _ 2) (S x2))).
      apply pow_lt, CR_of_Q_pos. reflexivity. rewrite pow_mult.
      rewrite <- (pow_proper 1). rewrite pow_one, CRmult_1_r.
      apply pow_R1_Rle. rewrite <- CR_of_Q_one. apply CR_of_Q_le. discriminate.
      rewrite <- CR_of_Q_mult, <- CR_of_Q_one. apply CR_of_Q_morph. reflexivity.
      apply CRmult_le_0_compat. 
      apply pow_le. rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
      apply CRlt_asym, epsPos.
      (* Outside the intersection, 0 == 0. *)
      unfold sa_approx in n. apply (CR_cv_eq _ (fun _ => 0)).
      intros. simpl. destruct dF, (x0 n0), d.
      contradiction. rewrite CRmult_0_l. reflexivity.
      apply (CR_cv_proper _ 0). apply CR_cv_const.
      simpl. rewrite CRmult_0_l, CRmin_left, CRmax_left. reflexivity.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
      rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate.
Qed.

(* The convergence in measure of a series of functions.
   It is the constructive counterpart of the pointwise convergence,
   weaker than uniform convergence. It is designed so that
   when a sequence fn of measurable functions converges towards
   function f, then f is measurable also (as would happen classically
   with pointwise convergence).

   For example the sequence of triangles (-1/n, 0), (0,n), (1/n,0)
   converges in measure towards 0. To prove that, take N an integer
   such as 2/N < eps. The SetApprox B simply removes the interval
   [-1/N, 1/N], where all the mass is.

   However the integrals of the triangles are all 1, which does not
   converge towards 0. *)
Definition CvMeasure {IS : IntegrationSpace}
           (fn : nat -> @PartialFunction (RealT (ElemFunc IS)) (X (ElemFunc IS)))
           (f : @PartialFunction (RealT (ElemFunc IS)) (X (ElemFunc IS))) : Type
  := forall (A : (X (ElemFunc IS)) -> Prop) (Aint : IntegrableSet A)
       (eps : CRcarrier (RealT (ElemFunc IS))),
    0 < eps
    -> { N : nat  &  forall n:nat, le N n
         -> { B : SetApprox A Aint eps
                 & (forall x xdf xdfn, sa_approx _ _ _ B x
                       -> CRabs _ (partialApply f x xdf - partialApply (fn n) x xdfn)
                         < eps) } }.

Lemma CvMeasureMeasurable
  : forall {IS : IntegrationSpace}
      (fn : nat -> @PartialFunction (RealT (ElemFunc IS)) (X (ElemFunc IS)))
      (f : @PartialFunction (RealT (ElemFunc IS)) (X (ElemFunc IS))),
    almost_everywhere (Domain f)
    -> (forall n:nat, MeasurableFunction (fn n))
    -> CvMeasure fn f
    -> MeasurableFunction f.
Proof.
  intros IS fn f fFull fnMes fnCv.
  apply (MeasurableGenApprox f fFull). intros.
  specialize (fnCv A Aint eps epsPos) as [N Ncv].
  specialize (Ncv N (le_refl N)) as [B Bcv].
  specialize (fnMes N A n Aint).
  exists (pair (XmaxConst
               (XminConst (Xmult (CharacFunc A) (fn N))
                  (CR_of_Q (RealT (ElemFunc IS)) (Z.pos n # 1)))
               (CR_of_Q (RealT (ElemFunc IS)) (Z.neg n # 1))) B).
  split. exact fnMes. unfold fst, snd. intros. 
  specialize (Bcv x xdh (snd xdf) H).
  refine (CRle_lt_trans _ _ _ _ Bcv). clear Bcv.
  rewrite applyXmaxConst, applyXmaxConst.
  apply (CRle_trans _ _ _ (CRmax_contract _ _ _)).
  rewrite applyXminConst, applyXminConst.
  apply (CRle_trans _ _ _ (CRmin_contract _ _ _)).
  simpl. destruct xdf, d. rewrite CRmult_1_l. apply CRle_refl.
  contradict n0. apply (sa_inc _ _ _ _ x H).
Qed.

(* fn converging in measure towards 0 is not enough to guarantee
   that the limit of I(fn) converge towards 0. An extra hypothesis
   of domination suffices. *)
Record IntegralDominated {IS : IntegrationSpace}
       (fn : nat -> @PartialFunction (RealT (ElemFunc IS)) (X (ElemFunc IS)))
       (fnInt : forall n:nat, IntegrableFunction (fn n))
       (eps : CRcarrier (RealT (ElemFunc IS))) : Type :=
  { idom_support : (X (ElemFunc IS)) -> Prop; 
    idom_idx : nat;
    idom_delta : CRcarrier (RealT (ElemFunc IS));
    idom_delta_pos : 0 < idom_delta;
    idom_int : IntegrableSet idom_support;
    idom_dom : forall (B : X (ElemFunc IS) -> Prop) (Bmes : MeasurableSet B) (n:nat),
        le idom_idx n
        -> Integral (MeasurableIntersectIntegrable Bmes idom_int) < idom_delta
        -> Integral (RestrictedMeasurable (fnInt n) Bmes) < eps }.
       
(* Bishop's lemma 4.14. *)
Lemma DominatedMeasureCvZero
  : forall {IS : IntegrationSpace}
      (fn : nat -> @PartialFunction (RealT (ElemFunc IS)) (X (ElemFunc IS)))
      (fnInt : forall n:nat, IntegrableFunction (fn n)),
    CvMeasure fn (Xconst _ 0)
    -> (forall n:nat, nonNegFunc (fn n))
    -> (forall (eps : CRcarrier (RealT (ElemFunc IS))) (epsPos : 0 < eps),
          IntegralDominated fn fnInt eps)
    -> CR_cv _ (fun n:nat => Integral (fnInt n)) 0.
Proof.
  intros IS fn fnInt fnCvZero fnPos fnDominated.
  apply Un_cv_real_nat. intros eps epsPos.
  assert (0 < eps * CR_of_Q _ (1#2)) as halfEpsPos.
  { apply CRmult_lt_0_compat. exact epsPos.
    apply CR_of_Q_pos. reflexivity. }
  destruct (fnDominated _ halfEpsPos).
  assert (0 < MeasureSet idom_int0 + 1) as H.
  { apply (CRlt_le_trans _ 1). apply CRzero_lt_one.
    rewrite <- (CRplus_0_l 1), <- CRplus_assoc. apply CRplus_le_compat_r.
    rewrite CRplus_0_r. apply MeasureNonNeg. }
  assert (0 < CRmin (eps * CR_of_Q _ (1#2) * CRinv _ _ (inr H)) idom_delta0)
    as H0.
  { apply CRmin_lt. 2: exact idom_delta_pos0.
    apply CRmult_lt_0_compat. apply CRmult_lt_0_compat.
    exact epsPos. apply CR_of_Q_pos. reflexivity.
    apply CRinv_0_lt_compat, H. }
  specialize (fnCvZero idom_support0 idom_int0 _ H0) as [N Nmaj].
  exists (max N idom_idx0). intros.
  specialize (Nmaj i (le_trans _ _ _ (Nat.le_max_l _ _) H1)) as [[C Cint] Cmaj].
  unfold sa_approx in Cmaj.
  assert (Integral
            (MeasurableIntersectIntegrable
               (MeasurableSetCompl C (IntegrableMeasurable (CharacFunc C) Cint))
               idom_int0) < idom_delta0) as H2.
  { apply (CRlt_le_trans
             _ (CRmin (eps * CR_of_Q _ (1#2) * (/ (MeasureSet idom_int0 + 1)) (inr H)) idom_delta0)).
    2: apply CRmin_r.
    refine (CRle_lt_trans _ _ _ _ sa_mes0).
    rewrite <- MeasureDifferenceIncluded. 2: exact sa_inc0.
    apply IntegralNonDecreasing. intros x xdf xdg. simpl.
    destruct xdf. destruct xdg. apply CRle_refl.
    contradict n. split; apply a.
    destruct xdg. apply CRlt_asym, CRzero_lt_one. apply CRle_refl. }
  assert (le idom_idx0 i).
  { apply (le_trans _ (max N idom_idx0)). apply Nat.le_max_r. exact H1. }
  specialize (idom_dom0 _ _ _ H3 H2). clear H2 H3.
  apply (CRle_lt_trans
           _ (Integral
                (RestrictedMeasurable
                   (fnInt i) (MeasurableSetCompl
                                C (IntegrableMeasurable (CharacFunc C) Cint)))
              + Integral (RestrictedIntegrable (fnInt i) Cint))).
  unfold CRminus. rewrite CRopp_0, CRplus_0_r, CRabs_right.
  - rewrite <- IntegralPlus. apply IntegralNonDecreasing. intros x xdf xdg.
    simpl. destruct xdg, d, d0.
    rewrite (DomainProp _ x d2 xdf), (DomainProp _ x d1 xdf).
    destruct d, d0. contradiction.
    rewrite CRmult_0_l, CRmult_1_l, CRplus_0_r. apply CRle_refl.
    rewrite CRmult_0_l, CRmult_1_l, CRplus_0_l. apply CRle_refl.
    contradiction.
  - exact (IntegralNonNeg _ _ (fnPos i)). 
  - apply (CRlt_le_trans _ (eps * CR_of_Q (RealT (ElemFunc IS)) (1 # 2)
                            + eps * CR_of_Q (RealT (ElemFunc IS)) (1 # 2))).
    apply (CRplus_lt_le_compat _ _ _ _ idom_dom0). clear idom_dom0.
    apply (CRle_trans _ (MeasureSet Cint * (eps * CR_of_Q (RealT (ElemFunc IS)) (1 # 2) *
            (/ (MeasureSet idom_int0 + 1)) (inr H)))).
    unfold MeasureSet. rewrite <- IntegralScale. apply IntegralNonDecreasing.
    + intros x xdf xdg. simpl. destruct xdf, d, xdg.
      rewrite CRmult_1_l, CRmult_1_r. clear c0. 
      specialize (Cmaj x Logic.I d0 c). apply CRlt_asym in Cmaj.
      simpl in Cmaj. unfold CRminus in Cmaj.
      rewrite CRplus_0_l, CRabs_opp, CRabs_right in Cmaj.
      apply (CRle_trans _ _ _ Cmaj (CRmin_l _ _)).
      apply fnPos. contradiction. contradiction.
      rewrite CRmult_0_l, CRmult_0_r. apply CRle_refl.
    + rewrite CRmult_comm, CRmult_assoc.
      apply (CRle_trans _ (eps * CR_of_Q (RealT (ElemFunc IS)) (1 # 2) * 1)).
      2: rewrite CRmult_1_r; apply CRle_refl.
      apply CRmult_le_compat_l. apply CRmult_le_0_compat.
      apply CRlt_asym, epsPos. rewrite <- CR_of_Q_zero.
      apply CR_of_Q_le. discriminate.
      apply (CRmult_le_reg_l (MeasureSet idom_int0 + 1) _ _ H).
      rewrite CRmult_1_r, <- CRmult_assoc, CRinv_r, CRmult_1_l.
      apply (CRle_trans _ (MeasureSet idom_int0 + 0)).
      rewrite CRplus_0_r. exact (MeasureNonDecreasing _ _ _ _ sa_inc0).
      apply CRplus_le_compat_l. apply CRlt_asym, CRzero_lt_one.
    + rewrite <- CRmult_plus_distr_l, <- CR_of_Q_plus.
      setoid_replace ((1 # 2) + (1 # 2))%Q with 1%Q. 2: reflexivity.
      rewrite CR_of_Q_one, CRmult_1_r. apply CRle_refl.
Qed.

Lemma DominatedConvergence
  : forall {IS : IntegrationSpace}
      (fn : nat -> @PartialFunction (RealT (ElemFunc IS)) (X (ElemFunc IS)))
      (fnInt : forall n:nat, IntegrableFunction (fn n))
      (f g : @PartialFunction (RealT (ElemFunc IS)) (X (ElemFunc IS)))
      (fInt : IntegrableFunction f),
    CvMeasure fn f
    -> IntegrableFunction g
    -> (forall n:nat, partialFuncLe (Xabs (fn n)) g)
    -> CR_cv _ (fun n:nat => Integral (fnInt n)) (Integral fInt).
Proof.
  intros IS fn fnInt f g fInt cvfn gInt fnle.
  assert (CvMeasure (fun n : nat => Xabs (Xminus (fn n) f))
                    (Xconst (X (ElemFunc IS)) 0))
    as cvZero.
  { intros A Aint eps epsPos. specialize (cvfn A Aint eps epsPos) as [N Nmaj].
    exists N. intros. specialize (Nmaj n H) as [B Bapprox].
    exists B. intros. destruct xdfn. specialize (Bapprox x d0 d H0). 
    refine (CRle_lt_trans _ _ _ _ Bapprox).
    simpl. rewrite (CRabs_minus_sym (partialApply f x d0)).
    unfold CRminus. rewrite CRplus_0_l, CRabs_opp.
    rewrite CRabs_right. 2: apply CRabs_pos.
    rewrite <- CRopp_mult_distr_l, CRmult_1_l. apply CRle_refl. }
  assert (forall n : nat, nonNegFunc (Xabs (Xminus (fn n) f))).
  { intros n x xdf. apply CRabs_pos. }
  assert (forall (eps : CRcarrier (RealT (ElemFunc IS))) (p : positive),
             0 < eps -> 0 < eps * CR_of_Q _ (1#p)) as deltaPos.
  { intros. apply (CRmult_lt_0_compat _ _ _ H0).
    apply CR_of_Q_pos. reflexivity. }
  assert (forall eps : CRcarrier (RealT (ElemFunc IS)),
       0 < eps ->
       IntegralDominated
         (fun n : nat => Xabs (Xminus (fn n) f))
         (fun n : nat => IntegrableAbs (IntegrableMinus (fnInt n) fInt)) eps)
    as domin.
  { intros eps epsPos.
    destruct (IntegralSupportExists
                _ (IntegrablePlus _ _ gInt (IntegrableAbs fInt))
                _ (deltaPos eps 2%positive epsPos))
      as [t [_ [tsupp tdist]]].
    remember (fun x : X (ElemFunc IS) =>
           exists xD : Domain (Xabs (Xplus g (Xabs f))) x,
             t <= partialApply (Xabs (Xplus g (Xabs f))) x xD) as A.
    destruct (Un_cv_nat_real
                _ _ (IntegralTruncateLimit _ (IntegrablePlus _ _ gInt (IntegrableAbs fInt)))
                _ (deltaPos eps 4%positive epsPos)) as [n nmaj].
    apply (Build_IntegralDominated
             IS _ _ _ _
             O _ (deltaPos eps (4 * Pos.of_nat (S n))%positive epsPos) tsupp).
    intros B Bmes i _ H0.
    apply (CRle_lt_trans
             _ (Integral
                  (RestrictedIntegrable (IntegrableAbs (IntegrableMinus (fnInt i) fInt)) (MeasurableIntersectIntegrable Bmes tsupp))
                + Integral
                    (RestrictedMeasurable (IntegrableAbs (IntegrableMinus (fnInt i) fInt)) (MeasurableSetCompl _ (IntegrableMeasurable _ tsupp))))). 
    - rewrite <- IntegralPlus; apply IntegralNonDecreasing.
      intros x xdf xdg. simpl. destruct xdf, xdg, d0, d1, d2, d4, d5.
      rewrite (DomainProp f x d7 d3); clear d7.
      rewrite (DomainProp f x d6 d3); clear d6.
      rewrite (DomainProp _ x d5 d0); clear d5.
      rewrite (DomainProp _ x d4 d0); clear d4.
      rewrite <- CRmult_plus_distr_r. apply CRmult_le_compat_r.
      apply CRabs_pos.
      destruct d. destruct d1. destruct d2.
      destruct a; contradiction. rewrite CRplus_0_r. apply CRle_refl.
      rewrite CRplus_0_l. destruct d2. apply CRle_refl.
      contradict n1. intro abs. contradict n0. split; assumption.
      destruct d1. destruct d2.
      destruct a; contradiction. rewrite CRplus_0_r. apply CRlt_asym, CRzero_lt_one.
      rewrite CRplus_0_l. destruct d2. apply CRlt_asym, CRzero_lt_one.
      apply CRle_refl.
    - apply (CRle_lt_trans
             _ (Integral
                  (RestrictedIntegrable
                     (IntegrablePlus _ _ gInt (IntegrableAbs fInt))
                     (MeasurableIntersectIntegrable Bmes tsupp))
                + Integral
                    (RestrictedMeasurable
                       (IntegrablePlus _ _ gInt (IntegrableAbs fInt))
                       (MeasurableSetCompl _ (IntegrableMeasurable _ tsupp))))).
      apply CRplus_le_compat.
      + apply IntegralNonDecreasing. intros x xdf xdg.
        destruct xdf, xdg. rewrite applyXmult, applyXmult.
        rewrite (DomainProp _ x d1 d). apply CRmult_le_compat_l.
        simpl. destruct d. apply CRlt_asym, CRzero_lt_one. apply CRle_refl.
        simpl. destruct d2, d0.
        apply (CRle_trans _ _ _ (CRabs_triang _ _)). apply CRplus_le_compat.
        apply fnle. rewrite <- CRopp_mult_distr_l, CRmult_1_l, CRabs_opp.
        rewrite (DomainProp f x d4 d3). apply CRle_refl.
      + apply IntegralNonDecreasing. intros x xdf xdg.
        destruct xdf, xdg. rewrite applyXmult, applyXmult.
        rewrite (DomainProp _ x d1 d). apply CRmult_le_compat_l.
        simpl. destruct d. apply CRlt_asym, CRzero_lt_one. apply CRle_refl.
        simpl. destruct d0, d2. rewrite <- CRopp_mult_distr_l, CRmult_1_l.
        apply (CRle_trans _ _ _ (CRabs_triang _ _)).
        apply CRplus_le_compat. apply fnle.
        rewrite CRabs_opp, (DomainProp f x d4 d3). apply CRle_refl.
      + apply (CRlt_le_trans _ (eps * CR_of_Q (RealT (ElemFunc IS)) (1 # 2)
                                + eps * CR_of_Q (RealT (ElemFunc IS)) (1 # 2))).
        apply CRplus_le_lt_compat. specialize (nmaj (S n) (le_S _ _ (le_refl n))).
        apply CRlt_asym in nmaj. rewrite CRabs_minus_sym, CRabs_right in nmaj.
        apply (CRplus_le_reg_r
                 (- (MeasureSet (MeasurableIntersectIntegrable Bmes tsupp)
                     * CR_of_Q _ (Z.of_nat (S n) #1)))).
        apply (CRle_trans _ (eps * CR_of_Q (RealT (ElemFunc IS)) (1 # 4))).
        apply (CRle_trans _ (Integral (RestrictedIntegrable (IntegrablePlus g (Xabs f) gInt (IntegrableAbs fInt)) (MeasurableIntersectIntegrable Bmes tsupp))
                             - Integral (RestrictedIntegrable
           (IntegrableMinInt (Xplus g (Xabs f)) (S n)
              (IntegrablePlus g (Xabs f) gInt (IntegrableAbs fInt))) (MeasurableIntersectIntegrable Bmes tsupp)))).
        apply CRplus_le_compat_l. apply CRopp_ge_le_contravar. 
        unfold MeasureSet.
        rewrite <- IntegralScale. apply IntegralNonDecreasing.
        intros x xdf xdg. simpl. destruct xdf, d0.
        destruct d. rewrite CRmult_1_l. destruct xdg.
        rewrite CRmult_1_r. apply CRmin_r. contradiction.
        rewrite CRmult_0_l. destruct xdg.
        rewrite CRmult_1_r, <- CR_of_Q_zero. apply CR_of_Q_le.
        destruct n; discriminate. rewrite CRmult_0_r. apply CRle_refl.
        refine (CRle_trans _ _ _ _ nmaj).
        rewrite <- IntegralMinus, <- IntegralMinus. apply IntegralNonDecreasing.
        intros x xdf xdg. simpl.
        destruct xdf, d, d1, d0, d3, xdg, d5, d6.
        rewrite (DomainProp g x d3 d1), (DomainProp g x d6 d1),
        (DomainProp g x d5 d1), (DomainProp f x d8 d2), (DomainProp f x d7 d2),
        (DomainProp f x d4 d2).
        destruct d. destruct d0. 2: contradiction.
        rewrite CRmult_1_l, CRmult_1_l. apply CRle_refl.
        rewrite CRmult_0_l. destruct d0. contradiction.
        rewrite CRmult_0_l. rewrite CRmult_0_r, CRplus_0_l.
        rewrite <- CRopp_mult_distr_l, CRmult_1_l.
        rewrite <- (CRplus_opp_r (CRmin (partialApply g x d1 + CRabs (RealT (ElemFunc IS)) (partialApply f x d2)) (INR (S n)))).
        apply CRplus_le_compat_r. apply CRmin_l.
        rewrite <- CRplus_0_r.
        setoid_replace (eps * CR_of_Q (RealT (ElemFunc IS)) (1 # 2))
          with (eps * CR_of_Q (RealT (ElemFunc IS)) (1 # 4)
                + eps * CR_of_Q (RealT (ElemFunc IS)) (1 # 4)).
        rewrite CRplus_assoc. apply CRplus_le_compat_l.
        rewrite <- (CRplus_opp_r (MeasureSet (MeasurableIntersectIntegrable Bmes tsupp) *
                                 CR_of_Q (RealT (ElemFunc IS)) (Z.of_nat (S n) # 1))).
        apply CRplus_le_compat_r.
        apply (CRmult_le_reg_r (CR_of_Q (RealT (ElemFunc IS)) (1 # Pos.of_nat (S n)))).
        apply CR_of_Q_pos. reflexivity.
        rewrite CRmult_assoc, <- CR_of_Q_mult.
        setoid_replace ((Z.of_nat (S n) # 1) * (1 # Pos.of_nat (S n)))%Q with 1%Q.
        rewrite CR_of_Q_one, CRmult_1_r.
        rewrite CRmult_assoc, <- CR_of_Q_mult.
        setoid_replace ((1 # 4) * (1 # Pos.of_nat (S n)))%Q
          with (1 # 4 * Pos.of_nat (S n))%Q.
        apply CRlt_asym, H0. reflexivity.
        unfold Qeq, Qmult, Qnum, Qden.
        rewrite Z.mul_1_r, Z.mul_1_r, Z.mul_1_l, Pos.mul_1_l.
        unfold Z.of_nat. rewrite Pos.of_nat_succ. reflexivity.
        rewrite <- CRmult_plus_distr_l. apply CRmult_morph.
        reflexivity. rewrite <- CR_of_Q_plus. apply CR_of_Q_morph.
        reflexivity.
        rewrite <- IntegralMinus. apply IntegralNonNeg.
        intros x xdf. simpl. destruct xdf, d, d0.
        rewrite <- CRopp_mult_distr_l, CRmult_1_l.
        rewrite <- (CRplus_opp_r (CRmin (partialApply g x d0 + CRabs (RealT (ElemFunc IS)) (partialApply f x d2)) (INR (S n)))).
        apply CRplus_le_compat_r.
        rewrite (DomainProp g x d0 d), (DomainProp f x d2 d1). apply CRmin_l.
        refine (CRle_lt_trans _ _ _ _ tdist).
        apply IntegralNonDecreasing. intros x xdf xdg.
        simpl. destruct xdf, xdg, d0, d1, d2, d5. 
        destruct d. 2: rewrite CRmult_0_l; apply CRabs_pos.
        rewrite CRmult_1_l. destruct d2. contradiction.
        rewrite CRmult_0_l, CRmult_0_r, CRplus_0_r.
        rewrite (DomainProp g x d1 d0), (DomainProp f x d4 d3).
        apply CRle_abs. rewrite <- CRmult_plus_distr_l, <- CR_of_Q_plus.
        setoid_replace ((1 # 2) + (1 # 2))%Q with 1%Q.
        rewrite CR_of_Q_one, CRmult_1_r. apply CRle_refl.
        reflexivity. }
  intro p.
  destruct (DominatedMeasureCvZero
              (fun n : nat => Xabs (Xminus (fn n) f))
              (fun n => IntegrableAbs (IntegrableMinus (fnInt n) fInt))
              cvZero H domin p) as [n nmaj].
  exists n. intros. specialize (nmaj i H0).
  unfold CRminus in nmaj. rewrite CRopp_0, CRplus_0_r, CRabs_right in nmaj.
  refine (CRle_trans _ _ _ _ nmaj). clear nmaj.
  refine (CRle_trans _ _ _ _ (IntegralTriangle _ _)). 
  rewrite (CRabs_morph _ (Integral (IntegrableMinus (fnInt i) fInt))).
  apply CRle_refl. rewrite <- IntegralMinus. reflexivity. 
  apply IntegralNonNeg. intros x xdf. apply CRabs_pos.
Qed.
