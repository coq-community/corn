(*
Copyright © 2020 Vincent Semeria

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*)


(** Proof that CoRN's faster reals implement the standard library's
    interface ConstructiveReals. *)

Require Import Coq.Reals.Abstract.ConstructiveReals.
Require Import CoRN.reals.faster.ARArith.
Require Import CoRN.reals.faster.ARabs.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.Complete.
Require Import CoRN.metric2.MetricMorphisms.
Require Import CoRN.model.metric2.Qmetric.
Require Import CoRN.model.totalorder.QposMinMax.
Require Import CoRN.reals.fast.CRArith.
Require Import CoRN.reals.fast.CRabs.
Require Import ConstructiveFastReals.

Section ConstructiveFaster.

Context {AQ : Set} `{AppRationals AQ}.

(* Redefine ARltT in sort Set *)
Definition AQPosS : Set := sig (lt zero).
Definition ARposS (x : AR) : Set := sig (λ y : AQPosS, 'y ≤ x).
Definition ARltS: AR → AR → Set := λ x y, ARposS (ARplus y (ARopp x)). 

Lemma ARltS_correct : eq ARltT ARltS.
Proof. reflexivity. Qed.

Lemma ARltS_linear : @isLinearOrder (RegularFunction (Eball (cast AQ Q))) ARltS.
Proof.
  destruct ARfpsro, full_pseudo_srorder_pso.
  destruct pseudo_srorder_strict.
  split. split.
  - intros x y J J0.
    pose proof (AR_lt_ltT x y) as [_ J1].
    pose proof (AR_lt_ltT y x) as [_ J2].
    exact (pseudo_order_antisym x y (conj (J1 J) (J2 J0))).
  - intros.
    destruct (ARtoCR_preserves_ltT x z) as [_ a].
    apply a. clear a.
    destruct (ARtoCR_preserves_ltT x y) as [a _].
    apply a in H5. clear a.
    destruct (ARtoCR_preserves_ltT y z) as [a _].
    apply a in H6.
    apply (CRlt_trans _ _ _ H5 H6). 
  - intros x y z J.
    destruct (CRlt_linear (cast AR CR x) (cast AR CR y) (cast AR CR z)).
    apply (ARtoCR_preserves_ltT x z), J.
    left. destruct (ARtoCR_preserves_ltT x y). apply a, c.
    right. destruct (ARtoCR_preserves_ltT y z). apply a, c.
Qed.

Lemma ARlt_or_epsilon : forall a b c d : AR,
       ARlt a b \/ ARlt c d -> ARltS a b + ARltS c d.
Proof.
  intros. destruct (CRlt_or_epsilon (cast AR CR a) (cast AR CR b)
                                    (cast AR CR c) (cast AR CR d)).
  - destruct H5. left.
    apply CR_lt_ltT, (ARtoCR_preserves_ltT a b), AR_lt_ltT. exact H5.
    right.
    apply CR_lt_ltT, (ARtoCR_preserves_ltT c d), AR_lt_ltT. exact H5.
  - left.
    apply (ARtoCR_preserves_ltT a b). exact c0.
  - right.
    apply (ARtoCR_preserves_ltT c d). exact c0. 
Qed.

Lemma AReq_nlt : forall a b : AR,
    st_eq a b
    <-> (fun x y : AR =>
         (fun x0 y0 : AR => (ARltS y0 x0) -> False) y x /\
         (fun x0 y0 : AR => (ARltS y0 x0) -> False) x y) a b.
Proof.
  split.
  - split.
    pose proof (ARle_not_lt b a) as [H6 _]. apply H6.
    rewrite H5. apply PreOrder_Reflexive.
    pose proof (ARle_not_lt a b) as [H6 _]. apply H6.
    rewrite H5. apply PreOrder_Reflexive.
  - intros [J J0]. apply po_antisym.
    pose proof (ARle_not_lt a b) as [_ H6].
    apply (H6 J0).
    pose proof (ARle_not_lt b a) as [_ H6].
    apply (H6 J).
Qed. 

Lemma inject_Q_AR_plus_nlt : ∀ q r : Q,
    (ARltS (inject_Q_AR (q + r)) (ARplus (inject_Q_AR q) (inject_Q_AR r)) → False)
    ∧ (ARltS (ARplus (inject_Q_AR q) (inject_Q_AR r)) (inject_Q_AR (q + r)) → False).
Proof.
  intros. rewrite <- AReq_nlt.
  apply inject_Q_AR_plus.
Qed.

Lemma inject_Q_AR_mult_nlt : ∀ q r : Q,
    (ARltS (inject_Q_AR (q * r)) (ARmult (inject_Q_AR q) (inject_Q_AR r)) → False)
    ∧ (ARltS (ARmult (inject_Q_AR q) (inject_Q_AR r)) (inject_Q_AR (q * r)) → False).
Proof.
  intros. rewrite <- AReq_nlt.
  apply inject_Q_AR_mult.
Qed.

Lemma AR_zero : st_eq (inject_Q_AR 0) (cast AQ AR zero0).
Proof.
  pose proof (ARtoCR_inject zero0) as H5.
  unfold cast in H5. unfold cast.
  rewrite inject_Q_AR_CR.
  apply (injective ARtoCR).
  rewrite H5.
  pose proof CRAR_id as H6.
  unfold cast in H6. rewrite (H6 (0%CR)).
  apply inject_Q_CR_wd.
  symmetry. apply rings.preserves_0.
Qed.

Lemma AR_one : st_eq (inject_Q_AR 1) (cast AQ AR one0).
Proof.
  pose proof (ARtoCR_inject one0) as H5.
  unfold cast in H5. unfold cast.
  rewrite inject_Q_AR_CR.
  apply (injective ARtoCR).
  rewrite H5.
  pose proof CRAR_id.
  unfold cast in H6. rewrite (H6 (1%CR)).
  apply inject_Q_CR_wd.
  symmetry. apply rings.preserves_1.
Qed. 

Lemma AR_ring : ring_theory (inject_Q_AR 0) (inject_Q_AR 1) ARplus ARmult
        (λ x y : AR, ARplus x (ARopp y)) ARopp
        (λ x y : AR,
           (λ x0 y0 : AR, ARltS y0 x0 → False) y x
           ∧ (λ x0 y0 : AR, ARltS y0 x0 → False) x y).
Proof.
  destruct (rings.stdlib_ring_theory AR).
  split.
  - intros. apply AReq_nlt. rewrite AR_zero. apply (Radd_0_l x).
  - intros. apply AReq_nlt. apply (Radd_comm x y).
  - intros. apply AReq_nlt. apply (Radd_assoc x y z).
  - intros. apply AReq_nlt. rewrite AR_one. apply (Rmul_1_l x).
  - intros. apply AReq_nlt. apply (Rmul_comm x y).
  - intros. apply AReq_nlt. apply (Rmul_assoc x y z).
  - intros. apply AReq_nlt. apply (Rdistr_l x y z).
  - intros. apply AReq_nlt. reflexivity.
  - intros. apply AReq_nlt. rewrite AR_zero. apply (Ropp_def x).
Qed.

Lemma AR_ring_ext : ring_eq_ext ARplus ARmult ARopp
        (λ x y : AR,
           (λ x0 y0 : AR, ARltS y0 x0 → False) y x
           ∧ (λ x0 y0 : AR, ARltS y0 x0 → False) x y).
Proof.
  split.
  - intros x y J z t J0.
    apply AReq_nlt. apply AReq_nlt in J.
    apply AReq_nlt in J0. rewrite J, J0. reflexivity.
  - intros x y J z t J0.
    apply AReq_nlt. apply AReq_nlt in J.
    apply AReq_nlt in J0. rewrite J, J0. reflexivity.
  - intros x y J.
    apply AReq_nlt. apply AReq_nlt in J.
    rewrite J. reflexivity.
Qed.

Lemma AR_lt_0_1 : ARltT (inject_Q_AR 0) (inject_Q_AR 1).
Proof.
  pose proof (inject_Q_AR_CR 0).
  pose proof (inject_Q_AR_CR 1).
  symmetry in H5.
  symmetry in H6.
  apply (ARltT_wd _ _ H5 _ _ H6).
  destruct (CRtoAR_preserves_ltT 0%CR 1%CR).
  exact (a (CRlt_Qlt 0 1 eq_refl)).
Qed.

Lemma AR_plus_lt : ∀ r r1 r2 : AR,
    ARltS r1 r2 → ARltS (ARplus r r1) (ARplus r r2).
Proof.
  intros.
  destruct (ARtoCR_preserves_ltT (ARplus r r1) (ARplus r r2)) as [_ a].
  apply a. clear a. 
  pose proof (ARtoCR_preserves_plus r r1).
  pose proof (ARtoCR_preserves_plus r r2).
  symmetry in H6. symmetry in H7.
  apply (CRltT_wd H6 H7).
  apply CRplus_lt_l.
  apply (ARtoCR_preserves_ltT r1 r2).
  exact H5.
Qed.

Lemma AR_plus_lt_rev : ∀ r r1 r2 : AR,
    ARltS (ARplus r r1) (ARplus r r2) → ARltS r1 r2.
Proof.
  intros.
  destruct (ARtoCR_preserves_ltT r1 r2) as [_ a].
  apply a. clear a.
  pose proof (ARtoCR_preserves_plus r r1).
  pose proof (ARtoCR_preserves_plus r r2).
  destruct (ARtoCR_preserves_ltT (ARplus r r1) (ARplus r r2)) as [a _].
  apply a in H5. clear a.
  apply (CRltT_wd H6 H7) in H5.
  pose proof (CRplus_lt_l ('r1) ('r2) ('r)) as [_ H8].
  apply H8, H5.
Qed.

Definition ARinvS (x : AR)
  : ARltS x (inject_Q_AR 0) + ARltS (inject_Q_AR 0) x → AR
  := fun H => ARinvT x (ARapartT_wd _ _ _ _ (reflexivity _) (AR_zero) H).

Lemma ARmult_inv_r
  : (∀ (r : AR)
       (rnz : (ARltS r (inject_Q_AR 0) + ARltS (inject_Q_AR 0) r)%type),
         (λ x y : AR,
            (λ x0 y0 : AR, ARltS y0 x0 → False) y x
            ∧ (λ x0 y0 : AR, ARltS y0 x0 → False) x
                y) (ARmult (ARinvS r rnz) r) (inject_Q_AR 1)).
Proof.
  intros. rewrite <- AReq_nlt.
  rewrite (commutativity _ r).
  unfold ARinvS.
  pose proof (AR_inverseT r (ARapartT_wd r r (inject_Q_AR 0) (' zero0)
                                         (reflexivity r) AR_zero rnz)).
  rewrite H5.
  symmetry. apply AR_one.
Qed.

Lemma ARinv_0_lt_compat
  : ∀ (r : AR)
      (rnz : (ARltS r (inject_Q_AR 0) + ARltS (inject_Q_AR 0) r)%type),
    ARltS (inject_Q_AR 0) r
    → ARltS (inject_Q_AR 0) (ARinvS r rnz).
Proof.
  intros r rnz H5. 
  destruct (ARtoCR_preserves_ltT (inject_Q_AR 0) (ARinvS r rnz)) as [_ a].
  apply a. clear a.
  assert (0 = ARtoCR (inject_Q_AR 0))%CR as H7.
  { rewrite <- (CRAR_id 0%CR).
    unfold cast.
    rewrite (inject_Q_AR_CR 0). reflexivity. }
  pose proof (ARtoCR_preserves_apartT_0 r ) as [ap _]. 
  pose proof (ARtoCR_preserves_invT
                r (ARapartT_wd r r (inject_Q_AR 0) (' zero0) (reflexivity r)
                               AR_zero rnz)
             (ap (ARapartT_wd r r (inject_Q_AR 0) (' zero0) (reflexivity r)
                               AR_zero rnz))) as H6.
  symmetry in H6.
  apply (CRltT_wd H7 H6). clear H6.
  apply CRinv_0_lt_compat.
  destruct (ARtoCR_preserves_ltT (inject_Q_AR 0) r) as [a _].
  apply a in H5. clear a. symmetry in H7.
  apply (CRltT_wd H7 (reflexivity _)). exact H5.
Qed.

Definition AR_Q_dense (x y : AR)
  : ARltS x y
    → sigT (fun q : Q => prod (ARltS x (inject_Q_AR q)) (ARltS (inject_Q_AR q) y)).
Proof.
  intro J.
  destruct (ARtoCR_preserves_ltT x y) as [a _].
  apply a in J. clear a.
  destruct (CRlt_Qmid (cast AR CR x) (cast AR CR y) J) as [q [J0 J1]].
  exists q. split.
  destruct (ARtoCR_preserves_ltT x (inject_Q_AR q)) as [_ a].
  apply a; clear a. 
  pose proof (CRAR_id ('q)%CR). symmetry in H5.
  rewrite <- (inject_Q_AR_CR q) in H5.
  apply (CRltT_wd (reflexivity _) H5), J0.
  destruct (ARtoCR_preserves_ltT (inject_Q_AR q) y) as [_ a].
  apply a; clear a. 
  pose proof (CRAR_id ('q)%CR).
  rewrite <- (inject_Q_AR_CR q) in H5.
  symmetry in H5.
  apply (CRltT_wd H5 (reflexivity _)), J1.
Qed.

Definition ARup (x : AR)
  : sigT (fun n : positive => ARltS x (inject_Q_AR (Z.pos n # 1))).
Proof.
  destruct (CRup (cast AR CR x)) as [n J].
  exists n.
  destruct (ARtoCR_preserves_ltT x (inject_Q_AR (Z.pos n # 1))) as [_ a].
  apply a; clear a.
  pose proof (CRAR_id ('(Z.pos n#1))%CR).
  rewrite <- inject_Q_AR_CR in H5.
  symmetry in H5.
  apply (CRltT_wd (reflexivity _) H5), J.
Qed.

Lemma ARabs_spec : ∀ x y : AR,
    (ARltS y x → False) ∧ (ARltS y (ARopp x) → False) ↔ (ARltS y (ARabs x) → False).
Proof.
  intros x y.
  split.
  - intros [H6 H7]. 
    apply (ARle_not_lt (ARabs x) y).
    apply (ARle_not_lt x y) in H6.
    apply (ARle_not_lt (ARopp x) y) in H7.
    pose proof (ARabs_AbsSmall y x) as [_ H5].
    apply H5. split. 2: exact H6.
    rewrite <- (rings.negate_involutive x). 
    apply rings.flip_le_negate. exact H7.
  - intro H6.
    apply (ARle_not_lt (ARabs x) y) in H6.
    pose proof (ARabs_AbsSmall y x) as [H5 _]. 
    split.
    + apply (ARle_not_lt x y).
      apply H5. exact H6.
    + apply (ARle_not_lt (ARopp x) y).
      rewrite <- (rings.negate_involutive y). 
      apply rings.flip_le_negate.
      apply H5, H6.
Qed.

Definition ARcauchy_sequence (xn : nat -> AR) : Set
  := ∀ p : positive,
       {n : nat
       | ∀ i j : nat,
           (n <= i)%nat
           → (n <= j)%nat
             → ARltT (inject_Q_AR (1 # p)) (ARabs (ARplus (xn i) (ARopp (xn j))))
               → False}.

Lemma ARtoCR_preserves_cauchy
  : forall xn : nat → AR,
    ARcauchy_sequence xn
    -> CRcauchy_sequence (fun n => cast AR CR (xn n)).
Proof.
  intros xn xncau p.
  specialize (xncau p) as [n J].
  exists n. intros.
  apply (J i j H5 H6); clear J.
  destruct (CRtoAR_preserves_ltT (' (1 # p))%CR
                                 (CRabs (' ARplus (xn i) (ARopp (xn j))))) as [c _].
  apply (ARltT_wd _ _ (reflexivity _) (' CRabs (' ARplus (xn i) (ARopp (xn j))))).
  - rewrite <- ARtoCR_preserves_abs.
    apply CRAR_id.
  - pose proof (inject_Q_AR_CR (1#p)).
    symmetry in H8.
    apply (ARltT_wd _ _ H8 _ _ (reflexivity _)). clear H8.
    apply c; clear c.
    apply (CRlt_le_trans _ _ _ H7); clear H7.
    setoid_replace ((' xn i)%mc - (' xn j)%mc)%CR
      with (cast AR CR (ARplus (xn i) (ARopp (xn j)))).
    apply CRle_refl.
    pose proof (ARtoCR_preserves_plus (xn i) (ARopp (xn j))).
    rewrite H7.
    apply ucFun2_wd. reflexivity.
    pose proof (ARtoCR_preserves_opp (xn j)).
    rewrite H8. apply Cmap_wd. apply uc_setoid.
    reflexivity.
Qed.

Lemma ARcauchy_complete
  : ∀ xn : nat → AR,
    ARcauchy_sequence xn 
    → sigT (fun l : AR =>
      ∀ p : positive,
        {n : nat
        | ∀ i : nat,
            (n <= i)%nat
            → ARltT (inject_Q_AR (1 # p)) (ARabs (ARplus (xn i) (ARopp l))) → False}).
Proof.
  intros. 
  destruct (CRcauchy_complete _ (ARtoCR_preserves_cauchy xn H5)) as [l J].
  exists (cast CR AR l).
  intro p. specialize (J p) as [n J]. exists n.
  intros i H6 H7. specialize (J i H6). apply J.
  unfold ARabs in H7.
  destruct (CRtoAR_preserves_ltT (' (1 # p))%CR
                                 (CRabs (' ARplus (xn i) (ARopp (' l))))) as [_ c].
  apply (ARltT_wd _ _ (reflexivity _)
                  _ (' CRabs (' ARplus (xn i) (ARopp ('l))))) in H7.
  - pose proof (inject_Q_AR_CR (1#p)).
    apply (ARltT_wd _ _ H8 _ _ (reflexivity _)) in H7. clear H8. 
    apply c in H7; clear c.
    apply (CRlt_le_trans _ _ _ H7).
    setoid_replace ((' xn i)%mc - l)%CR
      with (cast AR CR (ARplus (xn i) (ARopp (' l)))).
    apply CRle_refl.
    pose proof (ARtoCR_preserves_plus (xn i) (ARopp ('l))).
    rewrite H8.
    apply ucFun2_wd. reflexivity.
    pose proof (ARtoCR_preserves_opp ('l)).
    rewrite H9. apply Cmap_wd. apply uc_setoid.
    symmetry. apply CRAR_id. 
  - rewrite <- ARtoCR_preserves_abs.
    symmetry. apply CRAR_id.
Qed.

Definition FasterRealsConstructive : ConstructiveReals
  := Build_ConstructiveReals
       (RegularFunction (Eball (cast AQ Q)))
       ARltS ARltS_linear ARlt
       (fun x y H => fst (AR_lt_ltT x y) H) 
       (fun x y H => snd (AR_lt_ltT x y) H)
       ARlt_or_epsilon
       inject_Q_AR inject_Q_AR_lt inject_Q_AR_lt_rev
       ARplus ARopp ARmult
       inject_Q_AR_plus_nlt inject_Q_AR_mult_nlt
       AR_ring AR_ring_ext
       AR_lt_0_1 AR_plus_lt AR_plus_lt_rev
       AR_mult_0_lt_compat
       ARinvS ARmult_inv_r ARinv_0_lt_compat
       AR_Q_dense ARup ARabs ARabs_spec
       ARcauchy_complete.

End ConstructiveFaster.
