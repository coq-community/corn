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


(*
   We now move from functions to integrable sets, ie measures. We will
   prove the properties of measures up to monotonous continuity.

   Given an integration space IS on a base type X, a subset
   A : X -> Prop is declared integrable when it is almost everywhere
   decidable, i.e. when there is an integrable function
   f : X -> {0, 1} such as A x when f x == 1 and ~A x when f x == 0.
   The integral of f will be called the measure of A. Because integrable
   functions are stable under extensions, this definition is
   equivalent to requiring that the biggest characteristic function
   with domain { x : X  &  { A x } + { ~A x } } is integrable.

   This simplifies the theory of Bishop and Cheng, by avoiding the
   unnecessary concept of complemented set.
 *)

Require Import Logic.ConstructiveEpsilon.
Require Import QArith.
Require Import ConstructiveReals.
Require Import ConstructiveAbs.
Require Import ConstructiveSum.
Require Import ConstructiveLimits.
Require Import ConstructiveDiagonal.
Require Import ConstructivePartialFunctions.

Require Import CMTbase.
Require Import CMTIntegrableFunctions.
Require Import CMTFullSets.
Require Import CMTPositivity.

Local Open Scope ConstructiveReals.


Definition CharacFunc {R : ConstructiveReals} {X : Set} (A : X -> Prop)
  : @PartialFunction R X.
Proof.
  apply (Build_PartialFunctionXY
           X (CRcarrier R) (CReq R) (fun x:X => { A x } + { ~A x })
           (fun x dec => if dec then CR_of_Q R 1 else CR_of_Q R 0) ).
  intros. destruct p,q.
  reflexivity. contradiction. contradiction. reflexivity.
Defined.

Definition IntegrableSet {IS : IntegrationSpace}
           (A : (X (ElemFunc IS)) -> Prop) : Type
  := IntegrableFunction (CharacFunc A).

Definition MeasureSet {IS : IntegrationSpace}
           {A : X (ElemFunc IS) -> Prop}
  : IntegrableSet A -> CRcarrier (RealT (ElemFunc IS))
  := Integral.


(*********************************************************)
(** * Integration of complemented sets                   *)
(*********************************************************)

Definition PartialFunctionBoolR
           {X : Set} {R : ConstructiveReals}
           (f : @PartialFunctionXY X bool eq)
  : @PartialFunction R X.
Proof.
  apply (Build_PartialFunctionXY
           X (CRcarrier R) (CReq R) (Domain f)
           (fun x dec => if partialApply f x dec then CR_of_Q R 1 else CR_of_Q R 0)).
  intros. rewrite (DomainProp f x p q). reflexivity.
Defined. 

(* As announced, we prove that Definition IntegrableSet is equivalent
   to the more general formulation that the subset is almost everywhere decidable. *)
Lemma IntegrableSetAEdecidable
  : forall {IS : IntegrationSpace}
      (A : (X (ElemFunc IS)) -> Prop)
      (f : @PartialFunctionXY (X (ElemFunc IS)) bool eq),
    IntegrableFunction (PartialFunctionBoolR f)
    -> (forall (x : X (ElemFunc IS)) (dec : Domain f x),
          if partialApply f x dec then A x else ~A x)
    -> IntegrableSet A.
Proof.
  intros IS A f fInt. destruct fInt.
  exists x. apply (PartialRestriction_trans _ _ (PartialFunctionBoolR f) _ p).
  split.
  - intros y yD. simpl in yD. specialize (H y yD).
    destruct (partialApply f y yD).
    left. exact H. right. exact H.
  - intros. simpl. specialize (H x0 xD).
    destruct (partialApply f x0 xD), xG. reflexivity. 3: reflexivity.
    contradiction. contradiction.
Qed.

Definition IntegrableSetExtensional
           {IS : IntegrationSpace}
           (A B : (X (ElemFunc IS)) -> Prop)
  : (forall x:X (ElemFunc IS), { A x } + { ~A x } -> (A x <-> B x))
    -> IntegrableSet A
    -> IntegrableSet B.
Proof.
  intros H Aint.
  apply (IntegrableFunctionExtensional (CharacFunc A)).
  2: exact Aint.
  split.
  - intros x xdf. destruct xdf. left. apply H.
    left. exact a. exact a.
    right. intro abs. apply H in abs. contradiction.
    right. exact n.
  - intros. simpl. destruct xD, xG. reflexivity.
    apply H in a. contradiction. left. exact a.
    apply H in b. contradiction. right. exact n. reflexivity.
Qed.

(* ~~A can constructively be bigger than A, but when A is integrable
   then so is ~~A, with same measure. *)
Definition IntegrableSetNotNot
           {IS : IntegrationSpace}
           (A : (X (ElemFunc IS)) -> Prop)
  : IntegrableSet A -> IntegrableSet (fun x => ~~A x).
Proof.
  intro Aint. 
  apply (IntegrableSetExtensional A).
  split. intros H0 abs. contradiction.
  intro abs. destruct H. exact a. contradiction. exact Aint.
Qed.

Lemma MeasureExtensional
  : forall {IS : IntegrationSpace}
      (A B : (X (ElemFunc IS)) -> Prop)
      (Aint : IntegrableSet A) (Bint : IntegrableSet B),
    (forall x:X (ElemFunc IS),
        { A x } + { ~A x } -> { B x } + { ~B x }
        -> (A x <-> B x))
    -> MeasureSet Aint == MeasureSet Bint.
Proof.
  intros. apply IntegralExtensional.
  intros. simpl. destruct xdf, xdg. reflexivity. 3: reflexivity.
  exfalso. rewrite H in a. contradiction.
  left. exact a. right. exact n.
  exfalso. rewrite <- H in b. contradiction.
  right. exact n. left. exact b.
Qed.

Lemma MeasureEmptyZero
  : forall {IS : IntegrationSpace}
      (A : X (ElemFunc IS) -> Prop)
      (aInt : IntegrableSet A),
    (forall x:X (ElemFunc IS), { A x } + { ~A x } -> ~A x)
    -> MeasureSet aInt == 0.
Proof.
  intros. transitivity (Integral (@IntegrableZero IS)).
  apply IntegralExtensional.
  intros. simpl.
  destruct xdf. 2: reflexivity. exfalso.
  specialize (H x (left a)). contradiction.
  apply IntegralZeroIsZero.
Qed.

Lemma MeasureNonNeg : forall {IS : IntegrationSpace}
                        (A : X (ElemFunc IS) -> Prop)
                        (aInt : IntegrableSet A),
    0 <= MeasureSet aInt.
Proof.
  intros. apply (CRle_trans _ (Integral (@IntegrableZero IS))).
  rewrite IntegralZeroIsZero. apply CRle_refl.
  apply IntegralNonDecreasing. intros x xdf xdg.
  simpl. destruct xdg. apply CRlt_asym, CRzero_lt_one.
  apply CRle_refl.
Qed.

Lemma MeasureNonDecreasing
  : forall {IS : IntegrationSpace}
      (A B : X (ElemFunc IS) -> Prop)
      (aInt : IntegrableSet A)
      (bInt : IntegrableSet B),
    (forall x : X (ElemFunc IS), A x -> B x)
    -> MeasureSet aInt <= MeasureSet bInt.
Proof.
  intros. apply IntegralNonDecreasing.
  intros x xdf xdg. simpl. destruct xdf, xdg.
  apply CRle_refl. exfalso. specialize (H x a). contradiction.
  apply CRlt_asym, CRzero_lt_one. apply CRle_refl.
Qed.

Lemma MeasureZeroAE
  : forall {IS : IntegrationSpace}
      (Z : X (ElemFunc IS) -> Prop)
      (zInt : IntegrableSet Z),
    MeasureSet zInt == 0
    -> almost_everywhere (fun x => ~Z x).
Proof.
  intros.
  destruct (IntegrableFunctionsComplete
              IS (fun _:nat => CharacFunc Z) (fun _ => zInt) 0) as [rep [p s]].
  - apply (CR_cv_eq _ (fun _:nat => 0)). 2: apply CR_cv_const.
    intro n. rewrite sum_const. unfold MeasureSet in H.
    rewrite <- (CRmult_0_l (INR (S n))).
    apply CRmult_morph. 2: reflexivity. rewrite <- H.
    apply IntegralExtensional. intros. rewrite applyXabs.
    rewrite (DomainProp _ x xdf xdg). rewrite CRabs_right.
    reflexivity. simpl. destruct xdg. apply CRlt_asym, CRzero_lt_one.
    apply CRle_refl.
  - exists (XinfiniteSumAbs (IntFn rep)). split.
    + exists rep. apply PartialRestriction_refl.
    + intros x H0 abs. destruct p. specialize (d x H0) as [xn xncv].
      apply CR_complete in xncv. destruct xncv as [l lcv].
      apply (CR_cv_eq (fun n:nat => CR_of_Q _ (Z.of_nat (S n) # 1))) in lcv.
      specialize (lcv 1%positive) as [n ncv].
      destruct (CRup_nat (1+l)) as [k kup].
      specialize (ncv (max n k) (Nat.le_max_l _ _)).
      apply (CRle_trans _ _ _ (CRle_abs _)) in ncv.
      apply (CRplus_le_compat_r l) in ncv.
      unfold CRminus in ncv. rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r in ncv.
      apply ncv. apply (CRlt_le_trans _ _ _ kup).
      apply CR_of_Q_le. unfold Qle, Qnum, Qden. rewrite Z.mul_1_r, Z.mul_1_r.
      apply Nat2Z.inj_le, le_S, Nat.le_max_r.
      intro n. rewrite <- (CRsum_eq (fun _ => 1)).
      rewrite sum_const, CRmult_1_l. reflexivity.
      intros. simpl. destruct (xn i).
      rewrite CRabs_right. reflexivity. apply CRlt_asym, CRzero_lt_one.
      contradiction.
Qed.

Lemma domainXinfinitePosNeg
  : forall {R : ConstructiveReals} {X : Set}
           (fn : nat -> @PartialFunction R X) (x : X),
    (Domain (XinfiniteSumAbs (fun n => XposPart (fn n))) x)
    -> (Domain (XinfiniteSumAbs (fun n => XnegPart (fn n))) x)
    -> Domain (XinfiniteSumAbs fn) x.
Proof.
  intros. destruct H, H0.
  exists (fun n => fst (x0 n)).
  apply CR_complete in c. apply CR_complete in c0. destruct c,c0.
  apply (Rcv_cauchy_mod _ (x2+x3)).
  pose proof (series_cv_plus _ _ _ _ c c0).
  apply (series_cv_eq (fun n : nat =>
         (fun n0 : nat => CRabs R (partialApply (XposPart (fn n0)) x (x0 n0))) n +
         (fun n0 : nat => CRabs R (partialApply (XnegPart (fn n0)) x (x1 n0))) n)).
  intro n. rewrite CRabs_right, CRabs_right.
  simpl. destruct (x0 n), (x1 n). rewrite <- CRmult_plus_distr_l.
  rewrite <- CRopp_mult_distr_l, CRmult_1_l, CRplus_comm, CRplus_assoc.
  rewrite <- (CRplus_assoc (- partialApply (fn n) x d2)).
  rewrite (DomainProp (fn n) x d2 d), CRplus_opp_l, CRplus_0_l.
  apply (CRmult_eq_reg_l (CR_of_Q R 2)). right. apply CR_of_Q_pos. reflexivity.
  rewrite <- CRmult_assoc, <- CR_of_Q_mult.
  setoid_replace (2 * (1 # 2))%Q with 1%Q. 2: reflexivity.
  rewrite (CR_of_Q_plus R 1 1), CRmult_1_l.
  rewrite CRmult_plus_distr_r, CRmult_1_l.
  rewrite (DomainProp (fn n) x (fst (d,d0)) d0), (DomainProp (fn n) x d1 d0).
  reflexivity. apply applyXnegPartNonNeg. apply applyXposPartNonNeg.
  exact H.
Qed.

(* This will provide a very nice proof that the Cauchy reals are uncountable. *)
Lemma PositiveMeasureInhabited
  : forall {IS : IntegrationSpace}
      (A : X (ElemFunc IS) -> Prop)
      (aInt : IntegrableSet A),
    0 < MeasureSet aInt -> { x : X (ElemFunc IS) | A x }.
Proof.
  intros. destruct aInt.
  destruct (splitIntegralSumPosNeg
              (IntFn x) (IntFnL x)
              (IntAbsSum x) (IntAbsSumCv x)), s, p0, p0.
  assert (series_cv
            (fun k : nat => Iabs (XposPart (IntFn x k))
                                 (LposPartStable (IntFn x k) (IntFnL x k))) x0).
  { apply (series_cv_eq (fun n0 : nat =>
                           I IS (XposPart (IntFn x n0)) (LposPartStable (IntFn x n0) (IntFnL x n0)))).
    2: exact s0. intro n. apply IExtensional.
    intros. rewrite applyXabs, CRabs_right, (DomainProp _ x2 xF y).
    reflexivity. apply applyXposPartNonNeg. }
  destruct (IntegrableContinuous
              (XinfiniteSumAbs (fun n : nat => XposPart (IntFn x n)))
              (fun n => XnegPart (IntFn x n))
              (existT _
               (Build_IntegralRepresentation
                  IS (fun n => XposPart (IntFn x n))
                  (fun n => LposPartStable _ (IntFnL x n)) x0 H0)
               (pair (fun y yD => yD) (fun x2 xD xG => DomainProp _ x2 xD xG)))
              (fun n => IntegrableL _ (LnegPartStable (IntFn x n) (IntFnL x n)))).
  - intro n. apply applyXnegPartNonNeg.
  - exists x1. split.
    apply (series_cv_eq (fun n0 : nat =>
          I IS (XnegPart (IntFn x n0)) (LnegPartStable (IntFn x n0) (IntFnL x n0)))).
    2: exact s1. intro n. rewrite IntegralLstable. reflexivity.
    unfold Integral. apply (CRlt_le_trans _ x0).
    apply (CRplus_lt_reg_r (-x1)). rewrite CRplus_opp_r.
    pose proof (IntegralCv x).
    setoid_replace (x0 + - x1) with (IntegralSeries x). exact H.
    apply (series_cv_unique (fun n : nat => I IS (IntFn x n) (IntFnL x n))).
    2: exact H1. unfold CRminus in s. exact s.
    unfold IntegralSeries.
    destruct (series_cv_maj
       _ _ x0
       (fun n : nat =>
          integralAbsMaj (XposPart (IntFn x n))
                         (LposPartStable (IntFn x n) (IntFnL x n))) H0), p0.
    setoid_replace x0 with x2. apply CRle_refl.
    apply (series_cv_unique
             (fun k : nat => Iabs (XposPart (IntFn x k))
                             (LposPartStable (IntFn x k) (IntFnL x k))) _ _ H0).
    apply (series_cv_eq (fun n : nat => I IS (XposPart (IntFn x n))
                                     (LposPartStable (IntFn x n) (IntFnL x n)))).
    2: exact s2. intro n. apply IExtensional. intros.
    rewrite applyXabs, CRabs_right. apply DomainProp.
    apply applyXposPartNonNeg.
  - clear H. destruct x2;
    unfold ConstructivePartialFunctions.cpx,
    ConstructivePartialFunctions.cpxF,
    ConstructivePartialFunctions.cpxFn in s2.
    exists cpx. destruct s2, p0, p.
    assert (Domain (XinfiniteSumAbs (IntFn x)) cpx).
    { apply (domainXinfinitePosNeg _ _ cpxF).
      exists cpxFn. apply (Rcv_cauchy_mod _ x2).
      apply (series_cv_eq
               (fun n : nat => partialApply (XnegPart (IntFn x n)) cpx (cpxFn n))).
      2: exact s2. intro n. rewrite CRabs_right. reflexivity.
      apply applyXnegPartNonNeg. }
    pose proof (c0 cpx H (d _ H)).
    simpl (partialApply (CharacFunc A) cpx (d cpx H)) in H1.
    destruct (d cpx H). exact a. exfalso. clear n.
    apply applyInfiniteSumAbs in H1.
    pose proof (series_cv_unique
                  _ 0 (partialApply (XinfiniteSumAbs
                                       (fun n : nat => XposPart (IntFn x n))) cpx cpxF-x2) H1).
    clear H1. apply CRlt_minus in c. destruct H2. 2: contradiction.
    destruct cpxF.
    apply (series_cv_eq
            (fun n : nat =>
               partialApply (XposPart (IntFn x n)) cpx (x3 n)
               - partialApply (XnegPart (IntFn x n)) cpx (cpxFn n))).
    intro n. apply SplitPosNegParts.
    apply series_cv_minus. 2: exact s2.
    apply (series_cv_eq
             (fun n => partialApply (XposPart (IntFn x n)) cpx
                                 (domainInfiniteSumAbsIncReverse
                                    _ cpx
                                    (existT _ x3 c1) n))).
    intro n. apply DomainProp.
    apply applyInfiniteSumAbs. reflexivity.
Qed.

Definition IntegrableSetIntersect
           {IS : IntegrationSpace}
           (A B : X (ElemFunc IS) -> Prop)
           (aInt : IntegrableSet A)
           (bInt : IntegrableSet B)
  : IntegrableSet (fun x => A x /\ B x).
Proof.
  apply (IntegrableFunctionExtensional
           (Xmin (CharacFunc A) (CharacFunc B))).
  - split.
    + intros x xdf. simpl. destruct xdf, d0, d0.
      destruct d. destruct d0.
      left. split; assumption. right.
      intros [abs _]. contradiction. right. intros [_ abs]. contradiction.
    + intros.
      assert (Domain (@CharacFunc (RealT (ElemFunc IS)) _ A) x) as H.
      { destruct (CharacFunc A), (CharacFunc B); simpl; apply xD. }
      assert (Domain (@CharacFunc (RealT (ElemFunc IS)) _ B) x) as H0.
      { destruct (CharacFunc A), (CharacFunc B); simpl; apply xD. }
      rewrite (applyXmin _ _ _ H H0).
      destruct H. destruct H0.
      (* In intersection *)
      rewrite CRmin_left. simpl. destruct xG.
      reflexivity. exfalso. apply n. split; assumption.
      apply CRle_refl.
      (* Not in intersection *)
      destruct xG.
      exfalso. apply n; apply a0.
      rewrite CRmin_right. reflexivity. apply CRlt_asym, CRzero_lt_one.
      destruct H0. destruct xG.
      exfalso. apply n, a.
      rewrite CRmin_left. reflexivity. apply CRlt_asym, CRzero_lt_one.
      rewrite CRmin_left. destruct xG.
      exfalso. apply n, a.
      reflexivity. apply CRle_refl.
  - apply IntegrableMin; assumption.
Defined.

Lemma MeasureIntersectSym
  : forall {IS : IntegrationSpace}
      (A B : X (ElemFunc IS) -> Prop)
      (aInt : IntegrableSet A)
      (bInt : IntegrableSet B),
    MeasureSet (IntegrableSetIntersect A B aInt bInt)
    == MeasureSet (IntegrableSetIntersect B A bInt aInt).
Proof.
  intros. unfold MeasureSet. apply IntegralExtensional. intros.
  destruct xdf,xdg; simpl. reflexivity.
  exfalso. apply n. split; apply a.
  exfalso. apply n. split; apply a.
  reflexivity.
Qed.

Definition IntegrableSetUnion {IS : IntegrationSpace}
           (A B : X (ElemFunc IS) -> Prop)
           (aInt : IntegrableSet A)
           (bInt : IntegrableSet B)
  : IntegrableSet (fun x => A x \/ B x).
Proof.
  apply (IntegrableFunctionExtensional
           (Xmax (CharacFunc A) (CharacFunc B))).
  - split.
    + intros x xdf. simpl. destruct xdf, d0, d0.
      clear d2 d1.
      destruct d. left. right. exact b.
      destruct d0. left. left. exact a.
      right. intro abs. destruct abs; contradiction.
    + intros.
      assert (Domain (@CharacFunc (RealT (ElemFunc IS)) _ A) x) as H.
      { destruct (CharacFunc A), (CharacFunc B); simpl; apply xD. }
      assert (Domain (@CharacFunc (RealT (ElemFunc IS)) _ B) x) as H0.
      { destruct (CharacFunc A), (CharacFunc B); simpl; apply xD. }
      rewrite (applyXmax _ _ _ H H0).
      destruct xG.
      (* In union *)
      destruct H, H0.
      rewrite CRmax_right. reflexivity. apply CRle_refl.
      rewrite CRmax_left. reflexivity. apply CRlt_asym, CRzero_lt_one.
      rewrite CRmax_right. reflexivity. apply CRlt_asym, CRzero_lt_one.
      exfalso. destruct o; contradiction.
      (* Not in union *)
      destruct H. exfalso. apply n. left. exact a.
      destruct H0. exfalso. apply n. right. exact b.
      rewrite CRmax_right. reflexivity. apply CRle_refl.
  - apply IntegrableMax; assumption.
Defined.

Lemma MeasureAdditive
  : forall {IS : IntegrationSpace}
      (A B : X (ElemFunc IS) -> Prop)
      (aInt : IntegrableSet A)
      (bInt : IntegrableSet B),
    MeasureSet aInt + MeasureSet bInt
    == MeasureSet (IntegrableSetUnion A B aInt bInt)
       + MeasureSet (IntegrableSetIntersect A B aInt bInt).
Proof.
  intros.
  setoid_replace (MeasureSet aInt + MeasureSet bInt)
    with (Integral (IntegrablePlus _ _ aInt bInt)).
  setoid_replace (MeasureSet (IntegrableSetUnion A B aInt bInt)
           + MeasureSet (IntegrableSetIntersect A B aInt bInt))
    with (Integral (IntegrablePlus _ _ (IntegrableSetUnion A B aInt bInt)
                                   (IntegrableSetIntersect A B aInt bInt))).
  - apply IntegralExtensional. intros.
    destruct xdf,xdg; simpl. destruct d.
    destruct d1. 2: exfalso; apply n; left; exact a.
    destruct d0.
    destruct d2. reflexivity. exfalso; apply n; split; assumption.
    destruct d2. exfalso. destruct a0. contradiction.
    reflexivity. destruct d0, d1, d2.
    exfalso. apply n, a. apply CRplus_comm. reflexivity.
    exfalso. apply n0. right. exact b.
    exfalso. apply n, a. exfalso. destruct o; contradiction.
    exfalso. apply n, a. reflexivity.
  - rewrite IntegralPlus. reflexivity.
  - rewrite IntegralPlus. reflexivity.
Qed.

Fixpoint UnionIterate {X : Set} (An : nat -> X -> Prop) (n : nat)
  : X -> Prop
  := match n with
     | O => An O
     | S p => fun x => UnionIterate An p x \/ An n x
     end.

Fixpoint IntersectIterate {X : Set} (An : nat -> X -> Prop) (n : nat)
  : X -> Prop
  := match n with
     | O => An O
     | S p => fun x => IntersectIterate An p x /\ An n x
     end.

Lemma applyUnionIterate
  : forall (X : Set) (An : nat -> X -> Prop)
      (n : nat)
      (x : X),
    UnionIterate An n x
    <-> exists (p:nat), le p n /\ An p x.
Proof.
  induction n.
  - split. intros. exists O. split. reflexivity. apply H.
    intros. simpl. destruct H as [p [pneg pxp]].
    inversion pneg. subst p. apply pxp.
  - split.
    + intros. simpl in H.
      destruct H.
      specialize (IHn x) as [H0 _].
      destruct (H0 H). exists x0. split. apply (le_trans _ n).
      apply H1. apply le_S, le_refl. apply H1.
      exists (S n). split. apply le_refl. apply H.
    + intros. destruct H as [p [pxp H]].
      apply Nat.le_succ_r in pxp. destruct pxp.
      (* p <= n *)
      left. specialize (IHn x) as [_ H3]. apply H3. exists p.
      split; assumption. subst p. right. exact H.
Qed.

Lemma applyIntersectIterate
  : forall (X : Set) (An : nat -> X -> Prop)
      (n : nat)
      (x : X),
    IntersectIterate An n x
    <-> forall (p:nat), le p n -> An p x.
Proof.
  induction n.
  - split. intros. simpl in H. inversion H0. subst p. exact H.
    intros. simpl. apply H. apply le_refl.
  - split.
    + intros. apply Nat.le_succ_r in H0. destruct H0.
      apply IHn. apply H. exact H0. subst p. apply H.
    + intros. split. apply IHn. intros. apply H.
      apply (le_trans _ _ _ H0). apply le_S, le_refl.
      apply H. apply le_refl.
Qed.

Definition IntegrableSetUnionIterate
           {IS : IntegrationSpace}
           (An : nat -> X (ElemFunc IS) -> Prop)
           (aInt : forall n:nat, IntegrableSet (An n))
  : forall n:nat, IntegrableSet (UnionIterate An n).
Proof.
  induction n.
  - apply aInt.
  - simpl. apply IntegrableSetUnion. apply IHn. apply aInt.
Defined.

Definition IntegrableSetIntersectIterate
           {IS : IntegrationSpace}
           (An : nat -> X (ElemFunc IS) -> Prop)
           (aInt : forall n:nat, IntegrableSet (An n))
  : forall n:nat, IntegrableSet (IntersectIterate An n).
Proof.
  induction n.
  - apply aInt.
  - simpl. apply IntegrableSetIntersect. apply IHn. apply aInt.
Defined.

Lemma MeasureIntersectSeqDecr
  : forall {IS : IntegrationSpace}
      (An : nat -> X (ElemFunc IS) -> Prop)
      (AnInt : forall n:nat, IntegrableSet (An n)),
    (forall (n : nat) (x : X (ElemFunc IS)),
       An (S n) x -> An n x)
    -> forall n : nat,
      MeasureSet (IntegrableSetIntersectIterate An AnInt n)
      == MeasureSet (AnInt n).
Proof.
  intros IS An AnInt H.
  (* The characteristic function of the decreasing intersection is
     equal to the last characteristic function. *)
  assert (forall (n : nat) (x : X (ElemFunc IS))
            (xIntersect : Domain (@CharacFunc (RealT (ElemFunc IS)) _ (IntersectIterate An n)) x)
            (xLast : Domain (CharacFunc (An n)) x),
             partialApply _ _ xIntersect = partialApply _ _ xLast).
  { induction n.
    - intros. simpl. destruct xIntersect, xLast.
      reflexivity. contradiction. contradiction. reflexivity.
    - intros. specialize (H n).
      (* Extract point in dAn *)
      destruct n.
      + clear IHn. simpl. destruct xIntersect, xLast.
        reflexivity. destruct i. contradiction.
        2: reflexivity. exfalso. apply n. split.
        apply H, a. exact a.
      + simpl. simpl in IHn, xIntersect.
        destruct xIntersect. destruct a.
        destruct xLast. reflexivity. contradiction.
        destruct xLast. 2: reflexivity.
        assert (~ (IntersectIterate An n x /\ An (S n) x)).
        intro abs. apply n0. split; assumption.
        specialize (H x a).
        specialize (IHn x (right H0) (left H)). exact IHn. }
  intros. apply IntegralExtensional. intros.
  rewrite (H0 _ _ _ xdg). reflexivity.
Qed.

Definition IntegrableSetDifference
           {IS : IntegrationSpace}
           (A B : X (ElemFunc IS) -> Prop)
           (aInt : IntegrableSet A)
           (bInt : IntegrableSet B)
  : IntegrableSet (fun x => A x /\ ~B x).
Proof.
  apply (IntegrableFunctionExtensional
           (Xminus (CharacFunc A) (CharacFunc (fun x => A x /\ B x)))).
  - split.
    + intros x xdf. destruct xdf. simpl.
      destruct d, d0. right. intro abs. destruct a0, abs; contradiction.
      left. split. exact a. intro abs. apply n. split; assumption.
      destruct a; contradiction.
      right. intro abs. destruct abs; contradiction.
    + intros. destruct xD.
      rewrite (applyXminus (CharacFunc A) (CharacFunc (fun x0 : X (ElemFunc IS) => A x0 /\ B x0))).
      destruct xG; simpl. destruct d0.
      destruct d. 2: destruct a0; contradiction.
      destruct a0, a; contradiction. destruct d. unfold CRminus.
      rewrite CRopp_0, CRplus_0_r. reflexivity.
      destruct a; contradiction. destruct d0.
      destruct d. unfold CRminus. rewrite CRplus_opp_r. reflexivity.
      destruct a; contradiction.
      destruct d. exfalso. apply n. split.
      exact a. intro abs. apply n0. split; assumption.
      unfold CRminus. rewrite CRplus_opp_r. reflexivity.
  - apply (IntegrableMinus aInt (IntegrableSetIntersect A B aInt bInt)).
Defined.

Lemma MeasureDifference
  : forall {IS : IntegrationSpace}
      (A B : X (ElemFunc IS) -> Prop)
      (aInt : IntegrableSet A)
      (bInt : IntegrableSet B),
    MeasureSet (IntegrableSetDifference A B aInt bInt)
    == MeasureSet aInt
       - MeasureSet (IntegrableSetIntersect A B aInt bInt).
Proof.
  intros. unfold MeasureSet.
  rewrite <- IntegralMinus. apply IntegralExtensional. intros.
  destruct xdg.
  rewrite (applyXminus (CharacFunc A) (CharacFunc (fun x0 : X (ElemFunc IS) => A x0 /\ B x0))).
  destruct xdf; simpl. destruct d0.
  destruct d. destruct a,a0; contradiction. destruct a0; contradiction.
  destruct d. unfold CRminus. rewrite CRopp_0, CRplus_0_r.
  reflexivity. destruct a; contradiction.
  destruct d0. destruct d. unfold CRminus. rewrite CRplus_opp_r.
  reflexivity. destruct a; contradiction.
  destruct d. 2: unfold CRminus; rewrite CRplus_opp_r; reflexivity.
  exfalso. apply n. split. exact a.
  intro abs. apply n0. split; assumption.
Qed.

Lemma MeasureDifferenceIncluded
  : forall {IS : IntegrationSpace}
      (A B : X (ElemFunc IS) -> Prop)
      (aInt : IntegrableSet A)
      (bInt : IntegrableSet B),
    (forall x:X (ElemFunc IS), B x -> A x)
    -> MeasureSet (IntegrableSetDifference A B aInt bInt)
      == MeasureSet aInt - MeasureSet bInt.
Proof.
  intros. rewrite MeasureDifference. apply CRplus_morph. reflexivity.
  apply CRopp_morph. apply IntegralExtensional. intros. simpl.
  destruct xdf, xdg. reflexivity. 3: reflexivity.
  destruct a. contradiction. exfalso. apply n. split.
  apply H, b. exact b.
Qed.

Lemma MeasureDifferenceInvolutive
  : forall {IS : IntegrationSpace}
      (A B : X (ElemFunc IS) -> Prop)
      (aInt : IntegrableSet A)
      (bInt : IntegrableSet B),
    MeasureSet (IntegrableSetDifference
                  A _ aInt (IntegrableSetDifference A B aInt bInt))
    == MeasureSet (IntegrableSetIntersect A B aInt bInt).
Proof.
  intros. apply IntegralExtensional. intros.
  destruct xdf,xdg; simpl.
  reflexivity. exfalso. destruct a. apply H0.
  split. exact H. intro abs. apply n. split; assumption.
  exfalso. apply n. split. apply a. intro abs.
  destruct a, abs; contradiction. reflexivity.
Qed.

Lemma CharacFuncStationary
  : forall {R : ConstructiveReals} (X : Set) (An : nat -> X -> Prop) (x : X)
      (xn : forall n:nat, Domain (CharacFunc (An n)) x),
    CR_cauchy R (fun n => partialApply (CharacFunc (An n)) x (xn n))
    -> { p : nat | forall n:nat, le p n ->
                                 partialApply (CharacFunc (An p)) x (xn p)
                                 = partialApply (CharacFunc (An n)) x (xn n) }.
Proof.
  intros. destruct (H 2%positive) as [p pcv]. auto. exists p.
  intros. simpl. simpl in pcv.
  specialize (pcv p n (le_refl _) H0).
  assert (CR_of_Q R (1 # 2) < 1).
  { apply CR_of_Q_lt. reflexivity. }
  destruct (xn p), (xn n). reflexivity. 3: reflexivity.
  - exfalso. unfold CRminus in pcv.
    rewrite CRopp_0, CRplus_0_r, CRabs_right in pcv.
    contradiction. apply CRlt_asym, CRzero_lt_one.
  - exfalso. unfold CRminus in pcv.
    rewrite CRplus_0_l, CRabs_opp, CRabs_right in pcv.
    contradiction. apply CRlt_asym, CRzero_lt_one.
Qed.

Definition IntegrableSetCountableUnion
           {IS : IntegrationSpace}
           (An : nat -> X (ElemFunc IS) -> Prop)
           (AnInt : forall n:nat, IntegrableSet (An n))
           (a : CRcarrier (RealT (ElemFunc IS)))
  : CR_cv _ (fun n => MeasureSet (IntegrableSetUnionIterate An AnInt n)) a
    -> { intUnion : IntegrableSet (fun x => exists n:nat, An n x)
      | MeasureSet intUnion == a }.
Proof.
  intros.
  destruct (IntegralMonotoneConvergence
              IS _ (IntegrableSetUnionIterate An AnInt) a)
    as [[i restr] cv].
  - intros n x xdf xdg. simpl. clear H.
    destruct xdf, xdg. apply CRle_refl. exfalso.
    apply n0. left. exact u.
    apply CRlt_asym, CRzero_lt_one. apply CRle_refl.
  - apply H.
  - assert (PartialRestriction (XinfiniteSumAbs (IntFn i))
                               (CharacFunc (fun x => exists n:nat, An n x))) as H0.
    apply (PartialRestriction_trans (X (ElemFunc IS))
             _ (XpointwiseLimit (fun n : nat => CharacFunc (UnionIterate An n)))).
    split. apply restr. apply restr. clear i restr cv. split.
    + intros x xdf. simpl.
      destruct xdf as [xn xncv].
      apply CharacFuncStationary in xncv. destruct xncv as [p pcv].
      simpl in pcv.
      destruct (xn p). left. apply applyUnionIterate in u.
      destruct u. exists x0. apply H0. right.
      intros [k abs]. destruct (le_lt_dec p k).
      specialize (pcv k l). destruct (xn k).
      pose proof CRzero_lt_one. specialize (X (RealT (ElemFunc IS))).
      rewrite pcv in X. exact (CRlt_asym _ _ X X).
      destruct k. contradiction. simpl in n0. apply n0.
      right. exact abs. apply n. apply applyUnionIterate.
      exists k. split. unfold lt in l. apply (le_trans _ (S k)).
      apply le_S, le_refl. exact l. exact abs.
    + intros. apply applyPointwiseLimit. simpl.
      destruct xD as [xn xcv]. destruct xG.
      simpl in xn.
      destruct (constructive_indefinite_ground_description_nat
                  (fun n => (if xn n then 1 else 0) == CR_of_Q (RealT (ElemFunc IS)) 1))
        as [n ncv].
      intro n. destruct (xn n). left. reflexivity. right.
      intros [abs _]. apply abs, CRzero_lt_one.
      destruct e as [n ncv]. exists n.
      destruct (xn n). reflexivity. exfalso.
      destruct n. contradiction. apply n0. right. exact ncv.
      exists n. intros. destruct (xn i).
      unfold CRminus. rewrite CRplus_opp_r, CRabs_right.
      2: apply CRle_refl. 
      apply CR_of_Q_le; discriminate.
      exfalso. apply n0. apply applyUnionIterate. exists n.
      split. exact H0. destruct (xn n).
      exfalso. apply n0. apply applyUnionIterate in u.
      destruct u. apply applyUnionIterate. exists x0. split.
      apply (le_trans _ n). apply H1. exact H0. apply H1.
      exfalso. destruct ncv. apply H1, CRzero_lt_one.
      exists O. intros n0 _. destruct (xn n0). exfalso.
      apply n. apply applyUnionIterate in u. destruct u. exists x0. apply H0.
      unfold CRminus. rewrite CRplus_opp_r, CRabs_right.
      apply CR_of_Q_le; discriminate. apply CRle_refl.
    + exists (existT _ i H0). exact cv.
Defined.

Definition IntegrableSetCountableIntersect
           {IS : IntegrationSpace}
           (An : nat -> X (ElemFunc IS) -> Prop)
           (AnInt : forall n:nat, IntegrableSet (An n))
           (a : CRcarrier (RealT (ElemFunc IS)))
  : CR_cv _ (fun n => MeasureSet (IntegrableSetIntersectIterate An AnInt n)) a
    -> { intIntersect : IntegrableSet (fun x => forall n:nat, An n x)
      | MeasureSet intIntersect == a }.
Proof.
  intros.
  destruct (IntegralMonotoneConvergenceDecr
              IS _ (IntegrableSetIntersectIterate An AnInt) a)
    as [[i restr] cv].
  - intros n x xdf xdg. simpl. clear H.
    destruct xdf, xdg. apply CRle_refl. exfalso.
    apply n0. apply i.
    apply CRlt_asym, CRzero_lt_one. apply CRle_refl.
  - apply H.
  - assert (PartialRestriction (XinfiniteSumAbs (IntFn i))
                               (CharacFunc (fun x => forall n:nat, An n x))) as H0.
    apply (PartialRestriction_trans (X (ElemFunc IS))
             _ (XpointwiseLimit (fun n : nat => CharacFunc (IntersectIterate An n)))).
    split. apply restr. apply restr. clear i restr cv. split.
    + intros x xdf. simpl.
      destruct xdf as [xn xncv].
      apply CharacFuncStationary in xncv. destruct xncv as [p pcv].
      simpl in pcv.
      destruct (xn p). left. intros.
      destruct (le_lt_dec p n). specialize (pcv n l).
      destruct (xn n). rewrite applyIntersectIterate in i0. apply i0, le_refl.
      exfalso. symmetry in pcv. pose proof CRzero_lt_one.
      specialize (X (RealT (ElemFunc IS))) as H0.
      rewrite pcv in H0. exact (CRlt_asym _ _ H0 H0).
      rewrite applyIntersectIterate in i. apply i.
      apply (le_trans _ (S n)).
      apply le_S, le_refl. exact l.
      right. intro abs. apply n. rewrite applyIntersectIterate. intros.
      apply abs.
    + intros. apply applyPointwiseLimit. simpl.
      destruct xD as [xn xcv].
      destruct xG. exists O. intros n H0.
      destruct (xn n).
      unfold CRminus. rewrite CRplus_opp_r, CRabs_right.
      apply CR_of_Q_le; discriminate. apply CRle_refl.
      exfalso. apply n0. rewrite applyIntersectIterate. intros. apply a0.

      apply CharacFuncStationary in xcv. destruct xcv as [p pcv].
      exists p. intros. simpl in pcv. destruct (xn p).
      exfalso. (* if in all An above p and intersect p, means all n *)
      apply n. intros n1.
      destruct (le_lt_dec p n1). specialize (pcv n1 l).
      destruct (xn n1). rewrite applyIntersectIterate in i1. apply i1, le_refl.
      exfalso. symmetry in pcv. pose proof CRzero_lt_one.
      specialize (X (RealT (ElemFunc IS))).
      rewrite pcv in X. exact (CRlt_asym _ _ X X).
      rewrite applyIntersectIterate in i0. apply i0.
      apply (le_trans _ (S n1)). apply le_S, le_refl. exact l.
      (* So it is not in the intersection at p *)
      specialize (pcv i H0). destruct (xn i).
      exfalso. pose proof CRzero_lt_one.
      specialize (X (RealT (ElemFunc IS))).
      rewrite pcv in X. exact (CRlt_asym _ _ X X).
      unfold CRminus. rewrite CRplus_opp_r, CRabs_right.
      apply CR_of_Q_le; discriminate. apply CRle_refl.
    + exists (existT _ i H0). exact cv.
Defined.

Lemma MeasureIntersectIncr
  : forall {IS : IntegrationSpace}
      (A B : X (ElemFunc IS) -> Prop)
      (aInt : IntegrableSet A)
      (bInt : IntegrableSet B),
    MeasureSet (IntegrableSetIntersect A B aInt bInt) <= MeasureSet bInt.
Proof.
  intros. apply MeasureNonDecreasing. intros. apply H.
Qed.


(* Integrable sets can serve as partial integration domains.
   Actually those domains can be enlarged to the measure sets,
   defined in a later file. This is proposition 4.2 of Bishop. *)

Lemma growing_infinite : forall un : nat -> nat,
    (forall n:nat, lt (un n) (un (S n)))
    -> forall n : nat, le n (un n).
Proof.
  induction n.
  - apply le_0_n.
  - specialize (H n). unfold lt in H.
    apply (le_trans _ (S (un n))). apply le_n_S, IHn. exact H.
Qed.

Lemma SliceBar
  : forall {R : ConstructiveReals} {X : Set}
      (x : CRcarrier R)
      (nk : nat -> nat),
    (forall n:nat, lt (nk n) (nk (S n)))
    -> nk O = O
    -> 0 <= x
    -> series_cv
         (fun n : nat =>
            CRmin (INR (nk (S n) - nk n))
                  (x - CRmin x (INR (nk n)))) x.
Proof.
  intros.
  assert (forall k:nat, CRsum (fun n : nat =>
            CRmin (INR (nk (S n) - nk n))
                  (x - CRmin x (INR (nk n)))) k
                 == CRmin x (INR (nk (S k)))).
  { induction k.
    - intros. simpl.
      rewrite (CRmin_right x (INR (nk 0%nat))).
      rewrite H0. rewrite CRmin_sym.
      rewrite Nat.sub_0_r.
      setoid_replace (x - INR 0) with x. reflexivity.
      unfold INR. simpl. unfold CRminus.
      rewrite CRopp_0, CRplus_0_r.
      reflexivity. rewrite H0. unfold INR. apply H1.
    - intros. simpl. rewrite IHk. clear IHk.
      rewrite CRmin_plus.
      setoid_replace (CRmin x (INR (nk (S k))) + (x - CRmin x (INR (nk (S k)))))
        with x.
      rewrite CRmin_sym, CRplus_comm, CRmin_plus.
      setoid_replace (@INR R (nk (S (S k)) - nk (S k)) + INR (nk (S k)))
        with (@INR R (nk (S (S k)))).
      rewrite CRmin_assoc.
      rewrite (CRmin_left x). reflexivity.
      apply (CRle_trans _ (0+x)). rewrite CRplus_0_l.
      apply CRle_refl. apply CRplus_le_compat. 
      apply CR_of_Q_le. unfold Qle; simpl. rewrite Z.mul_1_r.
      apply Nat2Z.is_nonneg. apply CRle_refl.
      unfold INR. rewrite <- CR_of_Q_plus. apply CR_of_Q_morph.
      rewrite Qinv_plus_distr. rewrite <- Nat2Z.inj_add.
      rewrite Nat.sub_add. reflexivity. specialize (H (S k)).
      apply (le_trans _ (S (nk (S k)))). apply le_S, le_refl.
      apply H. rewrite CRplus_comm. unfold CRminus.
      rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
      reflexivity. }
  destruct (CRup_nat x) as [n nmaj]. exists n.
  intros. rewrite H2. rewrite CRmin_left.
  unfold CRminus. rewrite CRplus_opp_r, CRabs_right.
  apply CR_of_Q_le. discriminate. apply CRle_refl.
  apply (CRle_trans _ (INR n)). apply CRlt_asym, nmaj.
  apply CR_of_Q_le. unfold Qle; simpl.
  do 2 rewrite Z.mul_1_r. apply Nat2Z.inj_le.
  apply (le_trans _ _ _ H3). apply (le_trans _ (S i)).
  apply le_S, le_refl. apply growing_infinite. exact H.
Qed.

Lemma SliceNonNegFunc
  : forall {R : ConstructiveReals} {X : Set}
      (f : @PartialFunction R X)
      (A : X -> Prop)
      (nk : nat -> nat),
    (forall n:nat, lt (nk n) (nk (S n)))
    -> nk O = O
    -> nonNegFunc f
    -> PartialRestriction
        (XinfiniteSumAbs (fun k : nat =>
                           Xmin (Xscale (INR (nk (S k) - nk k)) (CharacFunc A))
                                (Xminus f (XminConst f (INR (nk k))))))
        (Xmult (CharacFunc A) f).
Proof.
  split.
  - intros x [xn _]. specialize (xn O).
    destruct f, xn, d0, d0; split. exact d0. apply d.
  - intros. apply applyInfiniteSumAbs.
    assert (forall n:nat, Domain (Xscale (INR (nk (S n) - nk n)) (@CharacFunc R _ A)) x)
      as H2.
    { intro n. apply (domainInfiniteSumAbsIncReverse _ _ xD n). }
    assert (forall n:nat, Domain (Xminus f (XminConst f (INR (nk n)))) x) as H3.
    { intro n. apply (domainInfiniteSumAbsIncReverse _ _ xD n). }
    destruct xG. destruct d as [inA | notInA].
    + (* Inside of A, prove convergence towards f x *)
      assert (Domain f x) as H4.
      { specialize (H3 O). apply H3. }
      apply (series_cv_eq (fun n : nat =>
       CRmin (INR (nk (S n) - nk n))
                 (partialApply f x H4
                  - CRmin (partialApply f x H4) (INR (nk n))))).
      intro n. rewrite (applyXmin _ _ x (H2 n) (H3 n)).
      apply CRmin_morph. rewrite applyXscale.
      rewrite (DomainProp (CharacFunc A) x _ (left inA)).
      unfold CharacFunc, partialApply. rewrite CRmult_1_r. reflexivity.
      destruct (H3 n).
      rewrite (applyXminus f (XminConst f (INR (nk n)))). apply CRplus_morph.
      apply DomainProp. apply CRopp_morph. rewrite applyXminConst.
      apply CRmin_morph. apply DomainProp. reflexivity.
      setoid_replace (partialApply (Xmult (CharacFunc A) f) x (left inA, d0))
        with (partialApply f x H4).
      apply (@SliceBar R X). exact H. exact H0. apply H1.
      destruct f; simpl. rewrite CRmult_1_l.
      apply DomainProp.
    + (* Outside of A we have 0 == 0 *)
      apply (series_cv_eq (fun _ => 0)).
      intro n. rewrite (applyXmin _ _ x (H2 n) (H3 n)), CRmin_left.
      rewrite applyXscale.
      rewrite (DomainProp (CharacFunc A) x _ (right notInA)).
      unfold CharacFunc, partialApply. rewrite CRmult_0_r. reflexivity.
      rewrite applyXscale.
      rewrite (DomainProp (CharacFunc A) x _ (right notInA)).
      apply (CRle_trans _ 0).
      unfold CharacFunc, partialApply. rewrite CRmult_0_r.
      apply CRle_refl. destruct (H3 n).
      rewrite (applyXminus f (XminConst f (INR (nk n)))).
      apply CRle_minus.
      rewrite applyXminConst. rewrite (DomainProp f x d1 d).
      apply CRmin_l.
      setoid_replace (partialApply (Xmult (CharacFunc A) f) x (right notInA, d0))
        with (CR_of_Q R 0).
      intro p. exists O. intros. rewrite sum_const, CRmult_0_l.
      unfold CRminus. rewrite CRplus_opp_r, CRabs_right.
      apply CR_of_Q_le. discriminate. apply CRle_refl.
      clear xD. destruct f; simpl. apply CRmult_0_l.
Qed.

(* Add zero before sequence un, if it does not already start with zero. *)
Definition StartZero (un : nat -> nat) (n : nat)
  := match n with
     | O => O
     | S p => match un O with | O => un (S p) | S _ => un p end
     end.

Lemma StartZeroInc : forall (un : nat -> nat),
    (forall n:nat, lt (un n) (un (S n)))
    -> (forall n:nat, lt (StartZero un n) (StartZero un (S n))).
Proof.
  intros. destruct n.
  - simpl. destruct (un O) eqn:des.
    apply (le_lt_trans _ (un O)). apply le_0_n. apply H.
    apply le_n_S, le_0_n.
  - simpl. destruct (un O); apply H.
Qed.

Definition RestrictedIntegralNonneg
           {IS : IntegrationSpace}
           (f : PartialFunction (X (ElemFunc IS)))
           (A : (X (ElemFunc IS)) -> Prop)
  : IntegrableFunction f
    -> nonNegFunc f
    -> IntegrableSet A
    -> IntegrableFunction (Xmult (CharacFunc A) f).
Proof.
  intros fInt fNonNeg AInt.
  assert (forall k : nat, 0 < CRpow (CR_of_Q (RealT (ElemFunc IS)) (1 # 2)) k) as boundPos.
  { intro k. apply pow_lt. simpl.
    apply CR_of_Q_lt. reflexivity. }
  pose (StartZero (fun n => let (p,_) := ControlSubSeqCv _ _ (CRpow (CR_of_Q _ (1#2)))
             (IntegralTruncateLimit f fInt) boundPos n in p)) as nk.
  (* Cut f's non-negative graph horizontally, according to the nk *)
  pose (fun k:nat => Xmin (Xscale (INR (nk (S k) - nk k)) (CharacFunc A))
                     (Xminus f (XminConst f (INR (nk k))))) as fk.
  pose (fun k:nat => IntegrableMinus fInt (IntegrableMinInt _ (nk k) fInt))
    as fTopkInt.
  assert (forall k, IntegrableFunction (fk k)) as fkInt.
  { intro k. apply IntegrableMin. apply IntegrableScale, AInt.
    apply fTopkInt. }
  (* Majorate the series by the right-hand term of the minimum,
     which is itself lower than 2^k, a convergent series. *)
  destruct (series_cv_maj
              (fun n => Integral (IntegrableAbs (fkInt (S O + n)%nat)))
              (CRpow (CR_of_Q _ (1#2))) (CR_of_Q _ 2)) as [l llim].
  2: exact GeoHalfTwo.
  - intro n.
    rewrite CRabs_right.
    apply (CRle_trans _ (Integral (fTopkInt (S n)))).
    apply IntegralNonDecreasing. intros x xdf xdg.
    rewrite applyXabs.
    assert (Domain (Xscale (INR (nk (S (S n)) - nk (S n))) (@CharacFunc (RealT (ElemFunc IS)) _ A)) x)
      as H.
    { destruct xdf. apply d0. }
    rewrite CRabs_right. unfold fk.
    rewrite (applyXmin _ _ x H xdg). apply CRmin_r.
    unfold fk.
    rewrite (applyXmin _ _ x H xdg). apply CRmin_glb.
    rewrite applyXscale. rewrite <- (CRmult_0_r (INR (nk (S (S n)) - nk (S n)))).
    apply CRmult_le_compat_l. apply CR_of_Q_le.
    unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_r. apply Nat2Z.is_nonneg.
    simpl. destruct H. apply CRlt_asym, CRzero_lt_one. apply CRle_refl.
    destruct xdg.
    rewrite (applyXminus f (XminConst f (INR (nk (S n))))).
    apply CRle_minus. rewrite applyXminConst.
    rewrite (DomainProp f x d0 d).
    apply CRmin_l. unfold fTopkInt. rewrite IntegralMinus.
    unfold nk, StartZero.
    destruct (ControlSubSeqCv
                (fun n0 : nat => Integral (IntegrableMinInt f n0 fInt))
                (Integral fInt) (CRpow (CR_of_Q _ (1 # 2)))
                (IntegralTruncateLimit f fInt) boundPos 0), x.
    destruct (ControlSubSeqCv
              (fun n0 : nat => Integral (IntegrableMinInt f n0 fInt))
              (Integral fInt) (CRpow (CR_of_Q _ (1 # 2)))
              (IntegralTruncateLimit f fInt) boundPos (S n)).
    rewrite CRabs_minus_sym in c0.
    apply (CRle_trans _ _ _ (CRle_abs _)).
    apply (CRle_trans _ (CRpow (CR_of_Q _ (1 # 2)) (S n))).
    apply CRlt_asym, c0.
    apply (CRmult_le_reg_l (CRpow (CR_of_Q _ 2) (S n))).
    apply pow_lt. apply CR_of_Q_lt. reflexivity.
    rewrite pow_mult. rewrite (pow_proper _ 1), pow_one.
    replace (CRpow (CR_of_Q _ 2) (S n))
      with (CR_of_Q (RealT (ElemFunc IS)) 2 * CRpow (CR_of_Q _ 2) n). 2: reflexivity.
    rewrite CRmult_assoc, pow_mult.
    rewrite (pow_proper _ 1), pow_one. rewrite CRmult_1_r.
    apply CR_of_Q_le. discriminate. rewrite <- CR_of_Q_mult.
    setoid_replace (2 * (1 # 2))%Q with 1%Q. reflexivity. reflexivity.
    rewrite <- CR_of_Q_mult.
    setoid_replace (2 * (1 # 2))%Q with 1%Q. reflexivity. reflexivity.
    destruct (ControlSubSeqCv
              (fun n0 : nat => Integral (IntegrableMinInt f n0 fInt))
              (Integral fInt) (CRpow (CR_of_Q _ (1 # 2)))
              (IntegralTruncateLimit f fInt) boundPos n).
    rewrite CRabs_minus_sym in c0.
    apply (CRle_trans _ _ _ (CRle_abs _)).
    apply CRlt_asym, c0.
    apply IntegralNonNeg. intros x xdf. rewrite applyXabs.
    apply CRabs_pos.
  - destruct (IntegrableFunctionsComplete
                IS fk fkInt (l+Integral (IntegrableAbs (fkInt O)))).
    destruct llim.
    apply (series_cv_shift (fun n : nat =>
         Integral (IntegrableAbs (fkInt n))) O) in s.
    exact s. exists x.
    apply (PartialRestriction_trans _ _ (XinfiniteSumAbs fk)).
    apply p. clear p x llim l.
    apply (SliceNonNegFunc f A nk). apply StartZeroInc.
    apply ControlSubSeqCvInc. reflexivity. exact fNonNeg.
Qed.

Definition RestrictedIntegrable
           {IS : IntegrationSpace}
           {f : PartialFunction (X (ElemFunc IS))}
           {A : (X (ElemFunc IS)) -> Prop}
  : IntegrableFunction f
    -> IntegrableSet A
    -> IntegrableFunction (Xmult (CharacFunc A) f).
Proof.
  intros.
  apply (IntegrableFunctionExtensional
           (Xminus (Xmult (CharacFunc A) (XposPart f))
                   (Xmult (CharacFunc A) (XnegPart f)))).
  split.
  - intros x xdf. destruct f; split; apply xdf.
  - intros. destruct xG, xD.
    rewrite (applyXmult (CharacFunc A) f).
    rewrite (applyXminus (Xmult (CharacFunc A) (XposPart f))
                         (Xmult (CharacFunc A) (XnegPart f))).
    unfold CRminus.
    destruct d1, d2.
    rewrite (applyXmult (CharacFunc A) (XposPart f)).
    rewrite (applyXmult (CharacFunc A) (XnegPart f)).
    rewrite (DomainProp _ x d2 d1), (DomainProp _ x d4 d3).
    rewrite CRopp_mult_distr_r, <- CRmult_plus_distr_l.
    apply CRmult_morph. apply DomainProp. apply SplitPosNegParts.
  - apply IntegrableMinus.
    apply RestrictedIntegralNonneg. apply IntegrablePosPart, X.
    apply applyXposPartNonNeg. exact X0.
    apply RestrictedIntegralNonneg. apply IntegrableNegPart, X.
    apply XnegPartNonNeg. exact X0.
Qed.

Definition RestrictedIntegral
           {IS : IntegrationSpace}
           {f : PartialFunction (X (ElemFunc IS))}
           {A : (X (ElemFunc IS)) -> Prop}
           (fInt : IntegrableFunction f)
           (aInt : IntegrableSet A)
  := Integral (RestrictedIntegrable fInt aInt).
           


(* A variant for the countable union, that allows redundancies in the sum. *)
Definition IntegrableSetCountableUnionLe
           {IS : IntegrationSpace}
           (An : nat -> X (ElemFunc IS) -> Prop)
           (AnInt : forall n:nat, IntegrableSet (An n))
           (a : CRcarrier (RealT (ElemFunc IS)))
  : series_cv (fun n => MeasureSet (AnInt n)) a
    -> { intUnion : IntegrableSet (fun x => exists n:nat, An n x)
      | MeasureSet intUnion <= a }.
Proof.
  intros.
  pose (fun n:nat => match n with
                | O => MeasureSet (AnInt O)
                | S p => MeasureSet (IntegrableSetUnionIterate An AnInt n)
                        - MeasureSet (IntegrableSetUnionIterate An AnInt p)
                end)
    as incrMes.
  destruct (series_cv_maj incrMes (fun n => MeasureSet (AnInt n)) a) as [l [lcv lle]].
  2: exact H.
  - intro n. unfold incrMes. destruct n.
    + rewrite CRabs_right. apply CRle_refl. apply MeasureNonNeg.
    + rewrite <- MeasureDifferenceIncluded. rewrite CRabs_right.
      2: apply MeasureNonNeg. apply IntegralNonDecreasing.
      intros x xdf xdg. simpl. destruct xdf, xdg. apply CRle_refl.
      3: apply CRle_refl. 2: apply CRlt_asym, CRzero_lt_one. exfalso.
      destruct a0. destruct H0; contradiction.
      intros. left. exact H0.
  - destruct (IntegrableSetCountableUnion An AnInt l).
    + apply (CR_cv_eq _ (CRsum incrMes)). 2: exact lcv.
      induction n. reflexivity. simpl. rewrite IHn. clear IHn.
      rewrite CRplus_comm. unfold CRminus.
      rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r. reflexivity.
    + exists x. rewrite c. exact lle.
Qed.
