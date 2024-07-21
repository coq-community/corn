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

From Coq Require Import ArithRing.
From Coq Require Import Bool.
From Coq Require Import Qpower Qabs.
Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Export CoRN.reals.fast.CRArith.
Require Export CoRN.model.metric2.Qmetric.
Require Import CoRN.reals.fast.LazyNat.
Require Import CoRN.reals.fast.CRstreams.
Require Export CoRN.metric2.Limit.
Require Import CoRN.model.totalorder.QposMinMax.
Require Import CoRN.classes.Qclasses.
Require Import MathClasses.interfaces.abstract_algebra.

Opaque CR.

(**
** Computing Alternating Series.
Alternating series are particularly nice to sum because each term is also
a bound on the error of the partial sum.
*)

Section RationalStreamSum.
  Variable X : Type.

  (* The current rational value is part of the state. For example a^k/k! is
     used to produce a^(k+1)/(k+1)! by multiplying by a and dividing
     by k+1. *)
  Variable f : X*Q -> X*Q.

  Definition Str_pth (p : positive) (x:X*Q) : Q
    := snd (CRstreams.iterate _ f p x).

  (* Decreasing and alternating stream. *)
  Definition Str_alt_decr (x:X*Q) : Prop
    := forall p : positive,
      Qabs (Str_pth (Pos.succ p) x) <= Qabs (Str_pth p x)
      /\ (Str_pth (Pos.succ p) x)*(Str_pth p x) <= 0.

  Lemma Str_alt_decr_tl : forall x p,
      Str_alt_decr x -> Str_alt_decr (CRstreams.iterate _ f p x).
  Proof.
    assert (forall x, Str_alt_decr x -> Str_alt_decr (f x)).
    { intros x H p.
      specialize (H (Pos.succ p)).
      unfold Str_pth.
      unfold Str_pth in H. 
      rewrite <- iterate_shift, <- iterate_succ.
      rewrite <- iterate_shift, <- iterate_succ.
      apply H. }
    intros x p. revert p x.
    apply (Pos.peano_ind (fun p => forall (x : X * Q),
                              Str_alt_decr x → Str_alt_decr (CRstreams.iterate (X * Q) f p x))).
    - intros. simpl. apply H, H0.
    - intros. rewrite iterate_succ. apply H, H0, H1. 
  Qed.

  Lemma Str_alt_even_step : forall p x,
      Str_alt_decr x ->
      0 <= Str_pth p x * Str_pth (p+2) x.
  Proof.
    intros. pose proof (H p). pose proof (H (Pos.succ p)).
    destruct H0, H1.
    replace (p+2)%positive with (Pos.succ (Pos.succ p)).
    destruct (Str_pth p x).
    destruct (Str_pth (Pos.succ p) x).
    destruct (Str_pth (Pos.succ (Pos.succ p)) x).
    unfold Qmult, Qle; simpl. rewrite Z.mul_1_r.
    unfold Qmult, Qle in H2; simpl in H2. rewrite Z.mul_1_r in H2.
    unfold Qmult, Qle in H3; simpl in H3. rewrite Z.mul_1_r in H3.
    destruct Qnum, Qnum1; try discriminate.
    destruct Qnum0. 
    exfalso; apply H1; reflexivity.
    exfalso; apply H2; reflexivity.
    exfalso; apply H3; reflexivity.
    destruct Qnum0. 
    exfalso; apply H1; reflexivity.
    exfalso; apply H3; reflexivity.
    exfalso; apply H2; reflexivity.
    rewrite <- Pos.add_1_r, <- Pos.add_1_r.
    rewrite <- Pos.add_assoc. reflexivity.
  Qed.

  Lemma Str_alt_zero : forall p x,
      Str_alt_decr x ->
      Str_pth p x == 0 -> Str_pth (Pos.succ p) x == 0.
  Proof.
    intros. pose proof (H p) as [H1 _].
    rewrite H0 in H1.
    apply Qabs_Qle_condition in H1. destruct H1.
    apply (Qle_antisym _ _ H2) in H1. exact H1.
  Qed. 

  Lemma Str_alt_neg : forall p x,
      Str_alt_decr x -> 0 <= snd (f x) -> Str_pth (p~0) x <= 0.
  Proof.
    apply (Pos.peano_ind (fun p => forall (x : X * Q),
                              Str_alt_decr x → 0 <= snd (f x) →
                              Str_pth (p~0) x <= 0)).
    - intros. simpl. specialize (H xH).
      unfold Str_pth in H. simpl in H. destruct H.
      destruct (Q_dec (snd (f x)) 0).
      destruct s.
      exfalso; exact (Qlt_not_le _ _ q H0).
      rewrite <- (Qmult_0_l (snd (f x))) in H1.
      apply Qmult_le_r in H1. exact H1. exact q. 
      rewrite q in H.
      exact (Qle_trans _ _ _ (Qle_Qabs _) H).
    - intros. pose proof (Str_alt_even_step (p~0) x H0).
      specialize (H x H0 H1).
      replace (p~0+2)%positive with ((Pos.succ p)~0)%positive in H2.
      apply Qnot_lt_le. intro abs.
      rewrite <- (Qmult_0_l (Str_pth ((Pos.succ p)~0) x)) in H2.
      apply Qmult_le_r in H2. 2: exact abs.
      apply (Qle_antisym _ _ H) in H2. clear H.
      apply (Str_alt_zero _ _ H0) in H2.
      apply (Str_alt_zero _ _ H0) in H2.
      rewrite <- Pos.double_succ in H2.
      rewrite H2 in abs. exact (Qlt_irrefl 0 abs).
      rewrite Pos.double_succ.
      rewrite <- Pos.add_1_r, <- Pos.add_1_r, <- Pos.add_assoc. reflexivity.
  Qed.

  Lemma Str_alt_pos : forall p x,
      Str_alt_decr x ->
      0 <= snd (f x) ->
      0 <= snd (CRstreams.iterate (X * Q) f p~1 x).
  Proof.
    intros. 
    rewrite Pos.xI_succ_xO.
    pose proof (Str_alt_neg p x H H0).
    specialize (H (p~0))%positive.
    unfold Str_pth in H. destruct H.
    destruct (Q_dec 0 (snd (CRstreams.iterate (X * Q) f p~0 x))).
    destruct s.
    exfalso; exact (Qlt_not_le _ _ q H1).
    apply Qopp_le_compat in H2.
    change (-0)%Q with 0%Q in H2.
    setoid_replace (- (snd (CRstreams.iterate (X * Q) f (Pos.succ p~0) x) *
                       snd (CRstreams.iterate (X * Q) f p~0 x)))%Q
      with ( (snd (CRstreams.iterate (X * Q) f (Pos.succ p~0) x) *
              -snd (CRstreams.iterate (X * Q) f p~0 x)))%Q in H2
      by (unfold equiv, Q_eq; ring).
    rewrite <- (Qmult_0_l (-snd (CRstreams.iterate (X * Q) f p~0 x))) in H2.
    apply Qmult_le_r in H2. exact H2.
    rewrite <- (Qplus_0_l (- snd (CRstreams.iterate (X * Q) f p~0 x))).
    rewrite <- Qlt_minus_iff. exact q. 
    rewrite <- q in H.
    apply Qabs_Qle_condition in H. apply H.
  Qed.

  Definition Limit_zero x (cvmod : Qpos -> positive) : Prop
    := forall q:Qpos, Qabs (Str_pth (cvmod q) x) <= proj1_sig q.

  Lemma Limit_zero_tl : forall x (cvmod : Qpos -> positive) (p : positive),
      Str_alt_decr x ->
      Limit_zero x cvmod -> Limit_zero (CRstreams.iterate _ f p x)
                                      (fun e => cvmod e - p)%positive.
  Proof.
    intros. intro e. 
    unfold Str_pth.
    rewrite <- iterate_add.
    assert (forall q:positive,
               Qabs (snd (CRstreams.iterate (X * Q) f (q+cvmod e) x)) <= ` e).
    { apply Pos.peano_ind.
      - intros. rewrite Pos.add_1_l.
        apply (Qle_trans _ (Qabs (snd (CRstreams.iterate (X * Q) f (cvmod e) x)))).
        apply H. apply H0.
      - intros.
        rewrite <- Pos.add_1_l, <- Pos.add_assoc, Pos.add_1_l.
        refine (Qle_trans _ _ _ _ H1).
        apply H. }
    destruct (Pos.lt_total p (cvmod e)).
    2: destruct H2.
    - rewrite Pos.sub_add. apply H0. exact H2.
    - subst p. rewrite Pos.sub_diag. apply H1.
    - rewrite Pos.sub_lt. 2: exact H2.
      replace (1+p)%positive with (1+(p-cvmod e)+cvmod e)%positive.
      apply H1. rewrite <- Pos.add_assoc.
      apply f_equal. rewrite Pos.sub_add. reflexivity. exact H2.
  Qed.

  Definition SumStream x (p : positive) (e : Qpos) : Q
    := snd (iterate_stop
              _ 
              (fun y:X*Q*Q =>
                 let (z,r) := f (fst y) in
                 (z, r, Qred (r + snd y)))
              (fun y:X*Q*Q => Qle_bool (Qabs (snd (fst y))) (proj1_sig e))
              p (x, 0)).

  Lemma SumStream_fst : forall p z,
      fst (CRstreams.iterate _ 
             (fun y:X*Q*Q =>
                let (z,r) := f (fst y) in
                (z, r, r + snd y)) 
             p z)
      ≡ CRstreams.iterate _ f p (fst z).
  Proof.
    apply (Pos.peano_ind (fun p => forall z : X * Q * Q,
    fst
      (CRstreams.iterate (X * Q * Q)
         (fun y : X * Q * Q => let (z0, r) := f (fst y) in (z0, r, r + snd y)) p z)
    ≡ CRstreams.iterate (X * Q) f p (fst z))).
    - intro z. simpl. destruct (f (fst z)); reflexivity.
    - intros. rewrite iterate_succ, H.
      rewrite iterate_succ.
      destruct (f (CRstreams.iterate (X * Q) f p (fst z))). reflexivity.
  Qed. 

  Lemma SumStream_fst_red : forall p z,
      fst (CRstreams.iterate _ 
             (fun y:X*Q*Q =>
                let (z,r) := f (fst y) in
                (z, r, Qred (r + snd y))) 
             p z)
      ≡ CRstreams.iterate _ f p (fst z).
  Proof.
    apply (Pos.peano_ind (fun p => forall z : X * Q * Q,
    fst
      (CRstreams.iterate (X * Q * Q)
         (fun y : X * Q * Q => let (z0, r) := f (fst y) in (z0, r, Qred (r + snd y))) p z)
    ≡ CRstreams.iterate (X * Q) f p (fst z))).
    - intro z. simpl. destruct (f (fst z)); reflexivity.
    - intros. rewrite iterate_succ, H.
      rewrite iterate_succ.
      destruct (f (CRstreams.iterate (X * Q) f p (fst z))). reflexivity.
  Qed. 

  Lemma SumStream_red : forall (p:positive) z,
      snd (CRstreams.iterate _
             (fun y : X * Q * Q => let (z0, r1) := f (fst y) in (z0, r1, Qred (r1 + snd y)))
             p z)
      == snd (CRstreams.iterate _
       (fun y : X * Q * Q => let (z0, r1) := f (fst y) in (z0, r1, r1 + snd y)) p z).
  Proof.
    apply (Pos.peano_ind
             (fun p => forall z, snd (CRstreams.iterate _
             (fun y : X * Q * Q => let (z0, r1) := f (fst y) in (z0, r1, Qred (r1 + snd y)))
             p z) == snd (CRstreams.iterate _
       (fun y : X * Q * Q => let (z0, r1) := f (fst y) in (z0, r1, r1 + snd y)) p z))).
    - intros. rewrite iterate_one, iterate_one.
      destruct (f (fst z)). apply Qred_correct.
    - intros. rewrite iterate_succ, SumStream_fst_red.
      rewrite iterate_succ, SumStream_fst.
      destruct (f (CRstreams.iterate (X * Q) f p (fst z))).
      unfold snd at 1 4.
      rewrite Qred_correct.
      rewrite H. reflexivity.
  Qed.

  Lemma SumStream_init : forall (p:positive) z (r:Q),
      snd (CRstreams.iterate _
       (fun y : X * Q * Q => let (z0, r1) := f (fst y) in (z0, r1, r1 + snd y)) p
       (z, r)) ==
      r +
      snd (CRstreams.iterate _
       (fun y : X * Q * Q => let (z0, r1) := f (fst y) in (z0, r1, r1 + snd y)) p
       (z, 0)).
  Proof.
    apply (Pos.peano_ind (fun p => forall (z : X * Q) (r : Q),
    snd (CRstreams.iterate (X * Q * Q)
         (fun y : X * Q * Q => let (z0, r1) := f (fst y) in (z0, r1, r1 + snd y)) p
         (z, r)) == r + snd
      (CRstreams.iterate (X * Q * Q)
         (fun y : X * Q * Q => let (z0, r1) := f (fst y) in (z0, r1, r1 + snd y)) p
         (z, 0)))).
    - intros. rewrite iterate_one, iterate_one.
      unfold fst. destruct (f z). unfold snd. 
      rewrite Qplus_0_r. apply Qplus_comm.
    - intros. rewrite iterate_succ, SumStream_fst.
      rewrite iterate_succ, SumStream_fst.
      change (fst (z,r)) with z.
      change (fst (z,0)) with z.
      destruct (f (CRstreams.iterate (X * Q) f p z)).
      unfold snd at 1 4.
      rewrite H.
      rewrite (Qplus_comm q), <- Qplus_assoc.
      rewrite <- (Qplus_comm q). reflexivity.
  Qed.

  Lemma SumStream_assoc : forall x (p q : positive),
      snd (CRstreams.iterate _
                (fun y : X * Q * Q =>
                       let (z, r0) := f (fst y) in (z, r0, r0 + snd y))
                (p+q) (x,0))
      == snd (CRstreams.iterate _
                      (fun y : X * Q * Q =>
                             let (z, r0) := f (fst y) in (z, r0, r0 + snd y))
                      p (x,0))
         + snd (CRstreams.iterate _
                        (fun y : X * Q * Q =>
                               let (z, r0) := f (fst y) in (z, r0, r0 + snd y))
                q (CRstreams.iterate _ f p x, 0)).
  Proof.
    intros x p. revert p x.
    apply (Pos.peano_ind (fun p => forall x q,
    snd (CRstreams.iterate (X * Q * Q)
         (fun y : X * Q * Q => let (z, r0) := f (fst y) in (z, r0, r0 + snd y)) 
         (p + q) (x, 0)) ==
    snd (CRstreams.iterate (X * Q * Q)
         (fun y : X * Q * Q => let (z, r0) := f (fst y) in (z, r0, r0 + snd y)) p 
         (x, 0)) +
     snd
       (CRstreams.iterate (X * Q * Q)
          (fun y : X * Q * Q => let (z, r0) := f (fst y) in (z, r0, r0 + snd y)) q
          (CRstreams.iterate _ f p x, 0)))).
    - intros x q.
      rewrite Pos.add_comm, iterate_add.
      simpl.
      destruct (f x) as [z r0]. 
      rewrite SumStream_init. reflexivity.
    - intros.
      rewrite <- Pos.add_1_r, <- Pos.add_assoc, Pos.add_1_l.
      rewrite H, H. simpl.
      rewrite <- Qplus_assoc.
      apply Qplus_comp. reflexivity. clear H.
      rewrite iterate_add. simpl.
      rewrite <- iterate_shift.
      rewrite <- Pos.add_1_r, iterate_add. simpl.
      destruct (f (CRstreams.iterate (X * Q) f p x)).
      simpl. rewrite SumStream_init. reflexivity.
  Qed.
        

  (* Using AltSumF_stop is faster than AltSumF. *)
  Definition AltSeries_raw x (cvmod : Qpos -> positive) (e : QposInf) : Q
    := match e with 
       | Qpos2QposInf d => SumStream x (cvmod d) d
       | QposInfinity => 0
       end.

  Lemma AltSeries_small_pos_even : forall p x,
      Str_alt_decr x ->
      0 <= snd (f x) ->
  0 <= snd
    (CRstreams.iterate (X * Q * Q)
       (fun y : X * Q * Q => let (z, r0) := f (fst y) in (z, r0, r0 + snd y))
       (p~0) (x, 0)).
  Proof.
    (* Sum of positive terms. *)
    assert (forall x, Str_alt_decr x -> 0 <= snd (f x) ->
                 0 <= snd (CRstreams.iterate (X * Q * Q)
       (fun y : X * Q * Q => let (z, r0) := f (fst y) in (z, r0, r0 + snd y)) 
       (1 + 1) (x, 0))).
    { intros.
      pose proof (Str_alt_neg 1 x H H0) as H1.
      unfold Str_pth in H1. simpl in H1.
      specialize (H xH).
      simpl. unfold Str_pth in H. simpl in H.
      destruct (f x); simpl. simpl in H. unfold snd in H0.
      destruct (f (x0,q)); simpl. rewrite Qplus_0_r.
      simpl in H. unfold snd in H1.
      destruct H.
      rewrite Qabs_neg in H. 2: exact H1.
      rewrite Qabs_pos in H. 2: exact H0.
      apply Qle_minus_iff in H.
      rewrite Qopp_involutive, Qplus_comm in H. exact H. }
    apply (Pos.peano_ind (fun p => forall x, Str_alt_decr x -> 0 <= snd (f x) ->
  0 <= snd (CRstreams.iterate (X * Q * Q)
       (fun y : X * Q * Q => let (z, r0) := f (fst y) in (z, r0, r0 + snd y))
       (p~0) (x, 0)))).
    - intros. exact (H x H0 H1).
    - intros.
      rewrite <- Qplus_0_r.
      rewrite Pos.double_succ, <- Pos.add_1_l, <- Pos.add_1_l.
      rewrite Pos.add_assoc, SumStream_assoc.
      apply Qplus_le_compat. exact (H x H1 H2).
      apply H0. exact (Str_alt_decr_tl x 2 H1).
      rewrite <- iterate_succ.
      exact (Str_alt_pos _ x H1 H2).
  Qed.

  Lemma AltSeries_small_neg_even : forall p x,
      Str_alt_decr x ->
      snd (f x) <= 0 ->
      snd (CRstreams.iterate (X * Q * Q)
       (fun y : X * Q * Q => let (z, r0) := f (fst y) in (z, r0, r0 + snd y))
       (p~0) (x, 0)) <= 0.
  Proof.
    (* Sum of negative terms. *)
    assert (forall x, Str_alt_decr x -> snd (f x) <= 0 ->
                 snd (CRstreams.iterate (X * Q * Q)
       (fun y : X * Q * Q => let (z, r0) := f (fst y) in (z, r0, r0 + snd y)) 
       (1 + 1) (x, 0)) <= 0).
    { intros.
      specialize (H xH). 
      simpl. unfold Str_pth in H. simpl in H.
      destruct (f x); simpl. simpl in H. unfold snd in H0.
      destruct (f (x0,q)); simpl. rewrite Qplus_0_r.
      simpl in H. destruct H.
      apply (Qplus_le_l _ _ (-q)).
      rewrite <- Qplus_assoc, Qplus_opp_r, Qplus_0_r.
      apply (Qle_trans _ _ _ (Qle_Qabs _)).
      apply (Qle_trans _ _ _ H).
      rewrite Qplus_0_l, Qabs_neg.
      apply Qle_refl. exact H0. }
    apply (Pos.peano_ind (fun p => forall x, Str_alt_decr x -> snd (f x) <= 0 ->
       snd (CRstreams.iterate (X * Q * Q)
       (fun y : X * Q * Q => let (z, r0) := f (fst y) in (z, r0, r0 + snd y))
       (p~0) (x, 0)) <= 0)).
    - intros. exact (H x H0 H1).
    - intros.
      rewrite <- (Qplus_0_r 0).
      rewrite Pos.double_succ, <- Pos.add_1_l, <- Pos.add_1_l.
      rewrite Pos.add_assoc, SumStream_assoc.
      apply Qplus_le_compat. exact (H x H1 H2).
      apply H0. exact (Str_alt_decr_tl x 2 H1).
      simpl. pose proof (Str_alt_even_step 1 x H1).
      unfold Str_pth in H3. simpl in H3.
      apply Qnot_lt_le. intro abs.
      rewrite <- (Qmult_0_l (snd (f (f (f x))))) in H3.
      apply Qmult_le_r in H3. 2: exact abs.
      apply (Qle_antisym _ _ H2) in H3. clear H2.
      apply (Str_alt_zero 1 _ H1) in H3.
      apply (Str_alt_zero 2 _ H1) in H3.
      unfold Str_pth in H3. simpl in H3.
      rewrite H3 in abs. exact (Qlt_irrefl 0 abs). 
  Qed.

  Lemma AltSeries_small_pos : forall x (p : positive),
      Str_alt_decr x ->
      0 <= snd (f x) ->
      0 <= snd (CRstreams.iterate (X * Q * Q)
          (fun y : X * Q * Q => let (z, r0) := f (fst y) in (z, r0, r0 + snd y)) 
          p (x, 0)) <= snd (f x).
  Proof.
    (* This truncated sum starts at 0, and oscillates around 0
       while staying in [-e,e]. *)
    (* TODO remove induction. *)
    intros x p. revert p x.
    apply (Pos.peano_ind (fun p => forall x,
      Str_alt_decr x ->
      0 <= snd (f x) ->
      0 <= snd (CRstreams.iterate (X * Q * Q)
          (fun y : X * Q * Q => let (z, r0) := f (fst y) in (z, r0, r0 + snd y)) 
          p (x, 0)) <= snd (f x))).
    - intros. simpl. destruct (f x). simpl.
      rewrite Qplus_0_r. split. exact H0. apply Qle_refl.
    - intros. destruct p.
      + split. rewrite Pos.xI_succ_xO, <- Pos.double_succ.
        exact (AltSeries_small_pos_even _ x H0 H1).
        rewrite <- Pos.add_1_r.
        rewrite SumStream_assoc, iterate_one.
        specialize (H x H0 H1) as [_ H].
        apply (Qle_trans _ (snd (CRstreams.iterate _
       (fun y : X * Q * Q => let (z, r0) := f (fst y) in (z, r0, r0 + snd y)) p~1 
       (x, 0)) + 0)).
        2: rewrite Qplus_0_r; exact H.
        apply Qplus_le_r. unfold fst.
        apply (Qle_trans _ (snd (f (CRstreams.iterate (X * Q) f p~1 x)))).
        destruct (f (CRstreams.iterate (X * Q) f p~1 x)).
        simpl. rewrite Qplus_0_r. apply Qle_refl.
        rewrite <- iterate_succ.
        pose proof (Str_alt_neg (Pos.succ p) x H0 H1). 
        specialize (H0 (p~1)%positive) as [_ H0].
        unfold Str_pth in H0.
        exact H2.
      + split. 
        rewrite <- Pos.add_1_r.
        rewrite SumStream_assoc, iterate_one.
        rewrite <- (Qplus_0_r 0).
        apply Qplus_le_compat.
        exact (AltSeries_small_pos_even _ x H0 H1).
        apply (Qle_trans _ (snd (f (CRstreams.iterate (X * Q) f p~0 x)))).
        rewrite <- iterate_succ, <- Pos.xI_succ_xO.
        exact (Str_alt_pos _ x H0 H1).
        unfold fst.
        destruct (f (CRstreams.iterate (X * Q) f p~0 x)).
        simpl. rewrite Qplus_0_r. apply Qle_refl.
        rewrite <- Pos.add_1_l, SumStream_assoc, iterate_one.
        simpl (fst (x,0)).
        rewrite <- (Qplus_0_r (snd (f x))).
        setoid_replace (snd (let (z, r0) := f x in (z, r0, r0 + snd (x, 0))))
          with (snd (f x))
          by (destruct (f x); apply Qplus_0_r).
        apply Qplus_le_r.
        apply AltSeries_small_neg_even.
        apply (Str_alt_decr_tl x _ H0).
        rewrite <- iterate_succ.
        apply (Str_alt_neg _ x H0 H1).
      + pose proof (Str_alt_neg 1 x H0 H1) as sndNeg.
        unfold Str_pth in sndNeg. simpl in sndNeg.
        specialize (H0 xH).
        unfold Str_pth in H0. simpl in H0.
        simpl. destruct (f x). simpl. simpl in H0.
        unfold snd in H1.
        destruct (f (x0,q)). simpl. simpl in H0.
        rewrite Qplus_0_r.
        destruct H0. rewrite (Qabs_pos q) in H0.
        2: exact H1. unfold snd in sndNeg.
        split.
        rewrite Qabs_neg in H0. 2: exact sndNeg.
        rewrite Qle_minus_iff, Qopp_involutive, Qplus_comm in H0.
        exact H0.
        apply (Qle_trans _ (0 + q)).
        apply Qplus_le_l. exact sndNeg.
        rewrite Qplus_0_l. apply Qle_refl.
  Qed.

  Lemma AltSeries_small : forall x (p : positive),
      Str_alt_decr x ->
    Qabs (snd
       (CRstreams.iterate (X * Q * Q)
          (fun y : X * Q * Q => let (z, r0) := f (fst y) in (z, r0, r0 + snd y)) 
          p (x, 0))) <= Qabs (snd (f x)).
  Proof.
    intros. destruct (Qlt_le_dec (snd (f x)) 0).
    - apply (Pos.peano_case (fun p => Qabs (snd
       (CRstreams.iterate (X * Q * Q)
          (fun y : X * Q * Q => let (z, r0) := f (fst y) in (z, r0, r0 + snd y)) p 
          (x, 0))) <= Qabs (snd (f x)))).
      + simpl. destruct (f x). unfold snd.
        rewrite Qplus_0_r. apply Qle_refl.
      + assert (0 <= snd (f (f x))) as sndPos.
        { specialize (H xH) as [_ H].
          unfold Str_pth in H. simpl in H.
          rewrite <- (Qmult_0_l (-snd (f x))) in H.
          setoid_replace (snd (f (f x)) * snd (f x))%Q
            with (-snd (f (f x)) * -snd (f x))%Q in H.
          apply Qmult_le_r in H. apply (Qopp_le_compat _ 0) in H.
          rewrite Qopp_involutive in H. exact H.
          apply (Qplus_lt_l _ _ (snd (f x))).
          ring_simplify. exact q.
          unfold equiv, Q_eq. simpl. ring. }
        intro n. rewrite <- Pos.add_1_l, SumStream_assoc, iterate_one.
        setoid_replace (snd (let (z, r0) := f (fst (x, 0)) in (z, r0, r0 + snd (x, 0))))
          with (snd (f x))
          by (simpl; destruct (f x); apply Qplus_0_r).
        rewrite Qabs_neg, Qabs_neg.
        apply Qopp_le_compat.
        rewrite <- (Qplus_0_r (snd (f x))) at 1.
        apply Qplus_le_r.
        apply AltSeries_small_pos.
        exact (Str_alt_decr_tl x _ H).
        exact sndPos.
        apply Qlt_le_weak, q.
        apply (Qle_trans _ (snd (f x) + snd (f (f x)))).
        apply Qplus_le_r.
        apply AltSeries_small_pos.
        exact (Str_alt_decr_tl x 1 H).
        exact sndPos.
        specialize (H xH) as [H _].
        unfold Str_pth in H. simpl in H.
        rewrite (Qabs_pos _ sndPos) in H.
        rewrite Qabs_neg in H.
        apply (Qplus_le_r _ _ (snd (f x))) in H.
        rewrite Qplus_opp_r in H. exact H.
        apply Qlt_le_weak, q.
    - pose proof (AltSeries_small_pos x p H q).
      rewrite (Qabs_pos (snd (f x)) q).
      rewrite Qabs_pos. apply H0. apply H0.
  Qed.

  Lemma AltSeries_further : forall x (p q : positive) (d1 d2 ε1 ε2 : Qpos),
      Str_alt_decr x
      -> Qabs (Str_pth p x) <= proj1_sig ε1
      -> Qabs (Str_pth q x) <= proj1_sig ε2
      -> proj1_sig d1 <= proj1_sig ε1
      -> proj1_sig d2 <= proj1_sig ε2
      -> Qball (proj1_sig ε1 + proj1_sig ε2) (SumStream x p d1) (SumStream x q d2).
  Proof.
  (* Because the stopping conditions are satisfied at p and q,
     those positive bounds are useless and the sums will stop at
     prior indices where the terms are less than ε1 and ε2. *)
    intros.
    unfold SumStream.
    (* Replace p by its stopping index r. *)
    pose proof (iterate_stop_correct
                  _
                  (fun y : X * Q * Q => let (z, r) := f (fst y) in (z, r, Qred (r + snd y)))
                  (fun y : X * Q * Q => Qle_bool (Qabs (snd (fst y))) (` d1))
                  p (x,0)) as [r [req [_ H4]]].
    rewrite req. clear req.
    assert (Qabs (Str_pth r x) <= proj1_sig ε1) as rstop.
    { destruct H4. rewrite <- H4. exact H0.
      destruct H4.
      rewrite SumStream_fst_red in H5.
      unfold fst in H5.
      apply Qle_bool_iff in H5.
      exact (Qle_trans _ _ _ H5 H2). }
    clear H4 H2 d1 H0 p.
    rewrite SumStream_red.
    (* Replace q by its stopping index s. *)
    pose proof (iterate_stop_correct
                  _
                  (fun y : X * Q * Q => let (z, r) := f (fst y) in (z, r, Qred (r + snd y)))
                  (fun y : X * Q * Q => Qle_bool (Qabs (snd (fst y))) (` d2))
                  q (x,0)) as [s [seq [_ H2]]].
    rewrite seq. clear seq.
    assert (Qabs (Str_pth s x) <= proj1_sig ε2) as sstop.
    { destruct H2. rewrite <- H0. exact H1.
      destruct H0.
      rewrite SumStream_fst_red in H2.
      unfold fst in H2.
      apply Qle_bool_iff in H2.
      exact (Qle_trans _ _ _ H2 H3). }
    clear H2 H3 d2 H1 q.
    rewrite SumStream_red.
    destruct (Pos.lt_total r s).
    - (* r < s *)
      unfold Qball.
      rewrite <- (Pplus_minus s r).
      2: apply Pos.lt_gt, H0.
      apply AbsSmall_Qabs.
      rewrite (SumStream_assoc x r (s-r)).
      unfold Qminus.
      assert (forall a b : Q, -(a+b) == -a+-b).
      { intros. ring. }
      rewrite H1, Qplus_assoc, Qplus_opp_r, Qplus_0_l.
      clear H1. rewrite Qabs_opp.
      refine (Qle_trans _ _ _ (AltSeries_small _ _ _) _).
      apply Str_alt_decr_tl, H.
      rewrite <- iterate_succ.
      destruct (H r).
      apply (Qle_trans _ _ _ H1).
      apply (Qle_trans _ (` ε1 + 0)).
      rewrite Qplus_0_r. exact rstop.
      apply Qplus_le_r, Qpos_nonneg.
    - destruct H0. rewrite H0. apply ball_refl, (Qpos_nonneg (ε1 + ε2)).
      (* Now s < r. *)
      unfold Qball.
      rewrite <- (Pplus_minus r s).
      2: apply Pos.lt_gt, H0.
      apply AbsSmall_Qabs.
      rewrite (SumStream_assoc x s (r-s)).
      rewrite Qplus_comm.
      unfold Qminus.
      rewrite <- Qplus_assoc, Qplus_opp_r, Qplus_0_r.
      refine (Qle_trans _ _ _ (AltSeries_small _ _ _) _).
      apply Str_alt_decr_tl, H.
      rewrite <- iterate_succ.
      destruct (H s).
      apply (Qle_trans _ _ _ H1).
      apply (Qle_trans _ (0 + ` ε2)).
      rewrite Qplus_0_l. exact sstop.
      apply Qplus_le_l, Qpos_nonneg.
  Qed.

  Lemma AltSeries_raw_prf : forall x cvmod,
    Str_alt_decr x -> Limit_zero x cvmod -> 
    is_RegularFunction Qball (AltSeries_raw x cvmod).
  Proof.
    intros x cvmod decr lz ε1 ε2.
    apply AltSeries_further. exact decr.
    apply lz. apply lz. apply Qle_refl. apply Qle_refl.
  Qed.

  Definition AltSeries (x:X*Q) cvmod (decr : Str_alt_decr x) lz : CR
    := Build_RegularFunction (AltSeries_raw_prf x cvmod decr lz).

  Lemma SumStream_shift : forall p x e,
      ` e < Qabs (snd (f x))
      -> snd (f x) + SumStream (f x) p e == SumStream x (Pos.succ p) e.
  Proof.
    intros. unfold SumStream.
    pose proof (iterate_stop_correct
                  _
                  (fun y : X * Q * Q => let (z, r) := f (fst y) in (z, r, Qred (r + snd y)))
                  (fun y : X * Q * Q => Qle_bool (Qabs (snd (fst y))) (` e))
                  p (f x,0)) as [s [seq [H0 H1]]].
    rewrite seq, SumStream_red.
    pose proof (SumStream_assoc x 1 s) as H2.
    rewrite iterate_one, iterate_one in H2. 
    setoid_replace (snd (f x))
      with (snd (let (z, r0) := f (fst (x, 0)) in (z, r0, r0 + snd (x, 0))))
           by (simpl; destruct (f x); simpl; rewrite Qplus_0_r; reflexivity).
    rewrite <- H2. clear H2.
    rewrite Pos.add_1_l.
    pose proof (iterate_stop_correct
                  _
                  (fun y : X * Q * Q => let (z, r) := f (fst y) in (z, r, Qred (r + snd y)))
                  (fun y : X * Q * Q => Qle_bool (Qabs (snd (fst y))) (` e))
                  (Pos.succ p) (x,0)) as [r [req [H2 H3]]].
    rewrite req, SumStream_red. 
    clear req seq.
    assert (r ≢ 1%positive) as rone.
    { intro abs. clear H2 H0 H1. subst r. 
      destruct H3.
      pose proof (Pos.lt_1_succ p).
      rewrite H0 in H1. inversion H1. destruct H0.
      rewrite SumStream_fst_red in H1.
      simpl in H1. apply Qle_bool_iff in H1.
      exact (Qlt_not_le _ _ H H1). } 
    destruct H1 as [finish|stop].
    - subst s. destruct H3. subst r. reflexivity.
      exfalso. destruct H1.
      apply Qle_bool_iff in H3. (* 1 < r by hypothesis. *)
      rewrite SumStream_fst_red in H3.
      unfold fst in H3.
      rewrite <- (Pos.succ_pred r) in H1. 2: exact rone.
      apply Pos.succ_lt_mono in H1.
      specialize (H0 (Pos.pred r) H1).
      rewrite SumStream_fst_red in H0.
      unfold fst in H0.
      rewrite <- iterate_shift, <- iterate_succ, Pos.succ_pred in H0.
      apply Qle_bool_iff in H3.
      rewrite H0 in H3. discriminate. exact rone.
    - destruct stop.
      rewrite SumStream_fst_red in H4. unfold fst in H4.
      rewrite <- iterate_shift, <- iterate_succ in H4.
      destruct H3. exfalso. subst r.
      apply Pos.succ_lt_mono in H1.
      specialize (H2 (Pos.succ s) H1).
      rewrite SumStream_fst_red in H2.
      unfold fst in H2. 
      rewrite H4 in H2. discriminate.
      destruct (Pos.lt_total r (Pos.succ s)).
      exfalso.
      destruct H3.
      rewrite SumStream_fst_red in H6. unfold fst in H6.
      rewrite <- (Pos.succ_pred r) in H5. 2: exact rone.
      apply Pos.succ_lt_mono in H5.
      specialize (H0 _ H5).
      rewrite SumStream_fst_red in H0.
      unfold fst in H0.
      rewrite <- iterate_shift, <- iterate_succ, Pos.succ_pred in H0.
      rewrite H0 in H6. discriminate. exact rone. 
      destruct H5.
      rewrite H5. reflexivity. exfalso.
      specialize (H2 (Pos.succ s) H5). 
      rewrite SumStream_fst_red in H2.
      unfold fst in H2. rewrite H4 in H2. discriminate.
  Qed. 

  (* AltSeries makes an infinite sum in the real numbers. *)
  Lemma AltSeries_shift : forall x cvmod decr lz,
      (AltSeries x cvmod decr lz
       == '(snd (f x))
          + AltSeries (f x) _ (Str_alt_decr_tl x 1 decr)
                      (Limit_zero_tl x cvmod 1 decr lz))%CR.
  Proof.
    intros. 
    rewrite -> CRplus_translate.
    apply regFunEq_equiv, regFunEq_e.
    intros e.
    simpl.
    rewrite <- Pos.pred_sub.
    destruct (Qlt_le_dec (proj1_sig e) (Qabs (snd (f x)))).
    - (* The sum recombines after f x. *)
      rewrite SumStream_shift. 2: exact q.
      specialize (lz e). revert lz.
      generalize (cvmod e).
      apply (Pos.peano_case (fun p => Qabs (Str_pth p x) <= ` e
    → Qball (` e + ` e) (SumStream x p e) (SumStream x (Pos.succ (Pos.pred p)) e))).
      + intros. exfalso. unfold Str_pth in H.
        simpl in H. exact (Qlt_not_le _ _ q H).
      + intros. rewrite Pos.pred_succ. apply ball_refl.
        apply (Qpos_nonneg (e+e)).
    - (* The sum stops at f x. *)
      unfold SumStream.
      rewrite (iterate_stop_indep _ _ _ (cvmod e) 1).
      rewrite (iterate_stop_indep _ _ _ (Pos.pred (cvmod e)) 1).
      + rewrite iterate_stop_one, iterate_stop_one.
        unfold fst.
        setoid_replace (snd (let (z, r) := f x in (z, r, Qred (r + snd (x, 0)))))
          with (snd (f x))
          by (destruct (f x); unfold snd; rewrite Qred_correct; apply Qplus_0_r).
        setoid_replace (snd (let (z, r) := f (f x) in (z, r, Qred (r + snd (x, 0)))))
          with (snd (f (f x)))
          by (destruct (f (f x)); unfold snd; rewrite Qred_correct; apply Qplus_0_r).
        apply AbsSmall_Qabs.
        rewrite Qabs_Qminus. unfold Qminus.
        rewrite (Qplus_comm (snd (f x))), <- Qplus_assoc.
        rewrite Qplus_opp_r, Qplus_0_r.
        specialize (decr xH) as [decr _].
        apply (Qle_trans _ _ _ decr).
        apply (Qle_trans _ (proj1_sig e + 0)).
        rewrite Qplus_0_r. exact q.
        apply Qplus_le_r, Qpos_nonneg.
      + rewrite SumStream_fst_red. unfold fst.
        apply Qle_bool_iff.
        rewrite <- iterate_shift, <- iterate_succ.
        specialize (lz e). revert lz.
        generalize (cvmod e).
        apply (Pos.peano_case (fun p => Qabs (Str_pth p x) <= ` e
     → Qabs (snd (CRstreams.iterate (X * Q) f (Pos.succ (Pos.pred p)) x)) <= ` e)).
        intros _.
        simpl. specialize (decr xH) as [decr _].
        unfold Str_pth in decr. simpl in decr.
        apply (Qle_trans _ _ _ decr q).
        intros. rewrite Pos.pred_succ. apply H.
      + rewrite SumStream_fst_red. unfold fst.
        simpl. apply Qle_bool_iff.
        specialize (decr xH) as [decr _].
        apply (Qle_trans _ _ _ decr).
        exact q.
      + rewrite SumStream_fst_red. unfold fst.
        apply Qle_bool_iff. apply lz.
      + rewrite SumStream_fst_red. unfold fst.
        apply Qle_bool_iff. exact q.
  Qed.

End RationalStreamSum.

Lemma Str_alt_decr_pos
  : forall (X:Type) (f : X*Q->X*Q) x 
      (fdecr : Str_alt_decr X f x) (n:nat),
    0 <= Str_pth _ f 1 x ->
    0 <= (-1)^Z.of_nat n * Str_pth X f (Pos.of_nat (S n)) x.
Proof.
  intros X f x fdecr.
  induction n.
  - intros. simpl. rewrite Qmult_1_l. exact H.
  - intro H. specialize (IHn H).
    specialize (fdecr (Pos.of_nat (S n))).
    rewrite Nat2Pos.inj_succ. 2: discriminate.
    destruct (Str_pth X f (Pos.of_nat (S n)) x) as [p q].
    destruct p as [|p|p].
    + destruct fdecr.
      setoid_replace (Qabs (0#q)) with 0%Q in H0 by reflexivity.
      apply Qabs_Qle_condition in H0. change (-0) with 0 in H0.
      setoid_replace (Str_pth X f (Pos.succ (Pos.of_nat (S n))) x) with 0%Q.
      rewrite Qmult_0_r. apply Qle_refl.
      apply Qle_antisym; apply H0.
    + destruct fdecr. clear H0.
      rewrite <- (Qmult_0_l (Z.pos p # q)) in H1.
      rewrite Qmult_le_r in H1. 2: reflexivity.
      rewrite <- (Qmult_0_l (Z.pos p # q)) in IHn.
      rewrite Qmult_le_r in IHn. 2: reflexivity.
      change (S n) with (1+n)%nat.
      rewrite (Nat2Z.inj_add 1 n).
      rewrite Qpower_plus. simpl ((-1)^Z.of_nat 1). rewrite (Qmult_comm (-1)).
      rewrite <- Qmult_assoc.
      rewrite Qmult_comm, <- (Qmult_0_l ((-1)^Z.of_nat n)).
      apply Qmult_le_compat_r. 2: exact IHn.
      change (S n) with (1+n)%nat in H1.
      destruct (Str_pth X f (Pos.succ (Pos.of_nat (1+ n))) x).
      destruct Qnum. apply Z.le_refl.
      unfold Qle, Z.le in H1. simpl in H1.
      exfalso; apply H1; reflexivity. 
      discriminate. intro abs. discriminate.
    + destruct fdecr. clear H0.
      assert ((Z.neg p # q) == (-1) * (Z.pos p#q)) by reflexivity.
      rewrite H0, Qmult_assoc in H1. rewrite H0, Qmult_assoc in IHn.
      rewrite <- (Qmult_0_l (Z.pos p # q)) in H1.
      rewrite Qmult_le_r in H1. 2: reflexivity.
      rewrite <- (Qmult_0_l (Z.pos p # q)) in IHn.
      rewrite Qmult_le_r in IHn. 2: reflexivity.
      change (S n) with (1+n)%nat.
      rewrite (Nat2Z.inj_add 1 n).
      rewrite Qpower_plus. simpl ((-1)^Z.of_nat 1%nat). rewrite (Qmult_comm (-1)).
      rewrite (Qmult_comm ((-1) ^ Z.of_nat n * -1)).
      rewrite <- (Qmult_0_l ((-1) ^ Z.of_nat n * -1)).
      apply Qmult_le_compat_r. 2: exact IHn.
      change (S n) with (1+n)%nat in H1.
      destruct (Str_pth X f (Pos.succ (Pos.of_nat (1+ n))) x).
      destruct Qnum. apply Z.le_refl. discriminate.
      unfold Qle, Z.le in H1. simpl in H1.
      exfalso; apply H1; reflexivity. 
      discriminate.
Qed.

Lemma CRstream_opp_decr : forall (X:Type) (f : X*Q->X*Q) x,
    Str_alt_decr X f x
    -> Str_alt_decr X (CRstreams.CRstream_opp X f) (let (y, r) := x in (y, - r)).
Proof.
  intros X f x H p. specialize (H p).
  pose proof (CRstreams.CRstream_opp_pth X f x p).
  pose proof (CRstreams.CRstream_opp_pth X f x (Pos.succ p)). 
  unfold Str_pth. unfold Str_pth in H.
  destruct x as [x q].
  unfold negate, Q_opp.
  destruct (CRstreams.iterate _ f p (x,q)).
  destruct (CRstreams.iterate _ f (Pos.succ p) (x,q)).
  unfold snd in H.
  destruct (CRstreams.iterate _ (CRstreams.CRstream_opp X f) 
                              (Pos.succ p) (x, (-q)%Q)).
  destruct (CRstreams.iterate _ (CRstreams.CRstream_opp X f) p (x, (-q)%Q)).
  unfold snd.
  destruct H1. subst q2. subst x2.
  destruct H0. subst q3. subst x3.
  destruct H. split.
  - rewrite Qabs_opp, Qabs_opp. exact H.
  - setoid_replace (- q1 * - q0)%Q with (q1*q0)%Q.
    exact H0. unfold equiv, Q_eq. ring.
Qed.

Lemma CRstream_opp_limit_zero : forall (X:Type) (f : X*Q->X*Q) x cvmod,
  Limit_zero X f x cvmod
  -> Limit_zero X (CRstreams.CRstream_opp X f) (let (y, r) := x in (y, - r)) cvmod.
Proof.
  intros. intro e.
  specialize (H e).
  pose proof (CRstreams.CRstream_opp_pth X f x (cvmod e)).
  unfold Str_pth. unfold Str_pth in H.
  destruct (CRstreams.iterate (X * Q) f (cvmod e) x) as [y r].
  destruct x as [x q].
  unfold negate, Q_opp.
  destruct (CRstreams.iterate (X * Q) (CRstream_opp X f) (cvmod e) (x, (- q)%Q)).
  unfold snd. unfold snd in H. destruct H0.
  subst q0. rewrite Qabs_opp. exact H.
Qed. 

Lemma SumStream_wd : forall (p:positive)
                       (X Y:Type) (f : X*Q -> X*Q) (g : Y*Q -> Y*Q)
                       (x : X*Q) (y : Y*Q),
    (forall p:positive, Str_pth _ f p x == Str_pth _ g p y)
    -> snd (CRstreams.iterate _
       (fun y : X * Q * Q => let (z0, r1) := f (fst y) in (z0, r1, r1 + snd y)) p
       (x,0))
      == snd (CRstreams.iterate _
       (fun y : Y * Q * Q => let (z0, r1) := g (fst y) in (z0, r1, r1 + snd y)) p
       (y,0)).
Proof.
  apply (Pos.peano_ind (fun p => forall (X Y:Type) (f : X*Q -> X*Q) (g : Y*Q -> Y*Q)
                       (x : X*Q) (y : Y*Q),
    (forall p:positive, Str_pth _ f p x == Str_pth _ g p y)
    -> snd (CRstreams.iterate _
       (fun y : X * Q * Q => let (z0, r1) := f (fst y) in (z0, r1, r1 + snd y)) p
       (x,0))
      == snd (CRstreams.iterate _
       (fun y : Y * Q * Q => let (z0, r1) := g (fst y) in (z0, r1, r1 + snd y)) p
       (y,0)))).
  - intros. simpl. specialize (H xH).
    unfold Str_pth in H. simpl in H.
    destruct (f x), (g y). simpl. simpl in H.
    rewrite H. reflexivity.
  - intros.
    pose proof (H0 (Pos.succ p)).
    unfold Str_pth in H1.
    rewrite iterate_succ, iterate_succ in H1.
    rewrite iterate_succ, iterate_succ, SumStream_fst, SumStream_fst.
    unfold fst.
    destruct (f (CRstreams.iterate (X * Q) f p x)).
    unfold snd at 1.
    destruct (g (CRstreams.iterate (Y * Q) g p y)).
    unfold snd at 3.
    specialize (H X Y f g x y H0).
    rewrite H. simpl in H1.
    rewrite H1. reflexivity.
Qed.

Lemma AltSeries_wd : forall (X Y:Type) (f : X*Q -> X*Q) (g : Y*Q -> Y*Q)
                       (x : X*Q) (y : Y*Q) cvmod ccvmod
                       (fdecr : Str_alt_decr X f x) (gdecr : Str_alt_decr Y g y)
                       (flz : Limit_zero X f x cvmod) (glz : Limit_zero Y g y ccvmod),
    (forall p:positive, Str_pth _ f p x == Str_pth _ g p y)
    -> (forall e, cvmod e ≡ ccvmod e)
    -> (AltSeries X f x cvmod fdecr flz
       == AltSeries Y g y ccvmod gdecr glz)%CR.
Proof.
  intros. 
  apply regFunEq_equiv, regFunEq_e. intros e.
  simpl.
  setoid_replace (SumStream X f x (cvmod e) e)
    with (SumStream Y g y (cvmod e) e).
  rewrite H0.
  apply ball_refl. apply (Qpos_nonneg (e+e)).
  unfold SumStream.
  destruct (iterate_stop_correct
              _
              (fun y0 : X * Q * Q => let (z, r) := f (fst y0) in (z, r, Qred (r + snd y0)))
              (fun y0 : X * Q * Q => Qle_bool (Qabs (snd (fst y0))) (` e))
              (cvmod e) (x,0)) as [q [qeq [H1 H2]]].
  rewrite qeq, SumStream_red. clear qeq.
  destruct (iterate_stop_correct
              _
              (fun y0 : Y * Q * Q => let (z, r) := g (fst y0) in (z, r, Qred (r + snd y0)))
              (fun y0 : Y * Q * Q => Qle_bool (Qabs (snd (fst y0))) (` e))
              (cvmod e) (y,0)) as [r [req [H3 H4]]].
  rewrite req, SumStream_red. clear req.
  destruct H4 as [fuel|predicate].
  - subst r. destruct H2.
    + subst q. apply (SumStream_wd _ _ _ _ _ _ _ H).
    + exfalso. destruct H2.
      specialize (H3 q H2).
      rewrite SumStream_fst_red in H3.
      unfold fst in H3.
      rewrite SumStream_fst_red in H4.
      unfold fst in H4.
      specialize (H q). unfold Str_pth in H.
      rewrite H in H4.
      rewrite H4 in H3. discriminate.
  - destruct predicate.
    rewrite SumStream_fst_red in H5.
    unfold fst in H5. 
    destruct H2.
    + exfalso. subst q.
      specialize (H1 r H4).
      rewrite SumStream_fst_red in H1.
      unfold fst in H1.
      specialize (H r). unfold Str_pth in H.
      rewrite <- H in H5.
      rewrite H5 in H1. discriminate.
    + destruct H2.
      rewrite SumStream_fst_red in H6. unfold fst in H6.
      destruct (Pos.lt_total q r).
      exfalso. specialize (H3 q H7).
      rewrite SumStream_fst_red in H3; unfold fst in H3.
      specialize (H q). unfold Str_pth in H.
      rewrite H in H6. rewrite H6 in H3. discriminate.
      destruct H7. rewrite H7.
      exact (SumStream_wd _ _ _ _ _ _ _ H).
      exfalso. specialize (H1 r H7).
      rewrite SumStream_fst_red in H1; unfold fst in H1.
      specialize (H r). unfold Str_pth in H.
      rewrite H in H1. rewrite H1 in H5. discriminate.
Qed.

Lemma sym_sub_add_distr (p q r:positive) : (p-(q+r) ≡ p-q-r)%positive.
Proof.
  destruct (Pos.lt_total (q+r) p).
  - apply Pos.sub_add_distr, H.
  - destruct H. subst p.
    rewrite Pos.sub_diag.
    rewrite Pos.add_comm, Pos.add_sub.
    rewrite Pos.sub_diag. reflexivity.
    rewrite Pos.sub_lt. 2: exact H.
    rewrite Pos.sub_le. reflexivity.
    destruct (Pos.lt_total p q).
    + rewrite Pos.sub_lt. apply Pos.le_1_l. exact H0.
    + destruct H0. subst q. rewrite Pos.sub_diag. apply Pos.le_1_l.
      change (Zpos (p-q) <= Zpos r)%Z.
      rewrite Pos2Z.inj_sub. 2: exact H0.
      apply (Z.add_le_mono_r _ _ (Zpos q)).
      ring_simplify.
      rewrite <- Pos2Z.inj_add.
      apply Z.lt_le_incl, H.
Qed.

Lemma AltSeries_shift_pth : forall (p:positive) (X : Type) f x cvmod decr lz,
    (AltSeries X f x cvmod decr lz
     == inject_Q_CR (snd (CRstreams.iterate _
            (fun y : (X * Q) * Q =>
               let (z0, r1) := f (fst y) in (z0, r1, Qred (r1 + snd y)))
            p (x, 0%Q)))
        + AltSeries X f (CRstreams.iterate _ f p x)
                    _ (Str_alt_decr_tl X f x p decr)
                    (Limit_zero_tl X f x cvmod p decr lz))%CR.
Proof.
  apply (Pos.peano_ind (fun p => forall X f x cvmod decr lz,
      (AltSeries X f x cvmod decr lz
       == inject_Q_CR (snd (CRstreams.iterate _
            (fun y : (X * Q) * Q =>
               let (z0, r1) := f (fst y) in (z0, r1, Qred (r1 + snd y)))
            p (x, 0%Q)))
          + AltSeries X f _ _ (Str_alt_decr_tl X f x p decr)
                      (Limit_zero_tl X f x cvmod p decr lz))%CR)).
  - intros. rewrite AltSeries_shift.
    apply CRplus_eq_l. rewrite SumStream_red.
    rewrite iterate_one. simpl.
    destruct (f x). simpl. rewrite Qplus_0_r. reflexivity.
  - intros.
    setoid_replace (AltSeries X f (CRstreams.iterate (X * Q) f (Pos.succ p) x)
                              (fun e : Qpos => (cvmod e - Pos.succ p)%positive)
                              (Str_alt_decr_tl X f x (Pos.succ p) decr)
                              (Limit_zero_tl X f x cvmod (Pos.succ p) decr lz))
      with (AltSeries X f (CRstreams.iterate (X * Q) f p (f x))
                      _
                      (Str_alt_decr_tl X f (f x) p (Str_alt_decr_tl X f x 1 decr))
                      (Limit_zero_tl X f (f x) _ p (Str_alt_decr_tl X f x 1 decr)
                                     (Limit_zero_tl X f x _ 1 decr lz))).
    + setoid_replace (inject_Q_CR (snd
       (CRstreams.iterate (X * Q * Q)
          (fun y : X * Q * Q => let (z0, r1) := f (fst y) in (z0, r1, Qred (r1 + snd y)))
          (Pos.succ p) (x, 0))))
          with (inject_Q_CR (snd (f x)) + inject_Q_CR (snd
              (CRstreams.iterate (X * Q * Q)
                 (fun y : X * Q * Q =>
                    let (z0, r1) := f (fst y) in (z0, r1, Qred (r1 + snd y))) p
                 (f x, 0%Q))))%CR.
      rewrite <- CRplus_assoc, <- (H X f (f x)).
      rewrite <- AltSeries_shift. reflexivity.
      clear H. rewrite SumStream_red, SumStream_red.
      rewrite iterate_succ. rewrite SumStream_fst.
      simpl.
      rewrite CRplus_Qplus.
      apply inject_Q_CR_wd.
      transitivity (snd (f (CRstreams.iterate (X * Q) f p x) )
                    + snd (CRstreams.iterate (X * Q * Q)
              (fun y : X * Q * Q => let (z1, r0) := f (fst y) in (z1, r0, r0 + snd y)) p
              (x, 0))).
      destruct (f (CRstreams.iterate (X * Q) f p x)); reflexivity.
      pose proof (SumStream_assoc X f x 1 p).
      rewrite iterate_one, iterate_one in H.
      setoid_replace (snd (let (z, r0) := f (fst (x, 0)) in (z, r0, r0 + snd (x, 0)))%Q)
        with (snd (f x))%Q in H.
      rewrite <- H. clear H.
      rewrite Pos.add_1_l, iterate_succ, SumStream_fst.
      unfold fst.
      destruct (f (CRstreams.iterate (X * Q) f p x)). simpl.
      reflexivity.
      simpl. destruct (f x). simpl.
      rewrite Qplus_0_r. reflexivity.
    + apply AltSeries_wd.
      intros. rewrite iterate_succ, iterate_shift.
      reflexivity.
      intro e. rewrite <- Pos.add_1_l.
      rewrite sym_sub_add_distr. reflexivity.
Qed.
