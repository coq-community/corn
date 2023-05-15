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

Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import CoRN.reals.iso_CReals.
Require Import CoRN.reals.Q_in_CReals.
Require Import Coq.setoid_ring.ArithRing.
Require Export CoRN.reals.fast.CRArith.
Require Import CoRN.reals.fast.CRIR.
Require Import CoRN.reals.fast.CRabs.
Require Import Coq.Bool.Bool.
Require Import CoRN.algebra.COrdAbs.
Require Import CoRN.model.ordfields.Qordfield.
Require Export CoRN.model.metric2.Qmetric.
Require Import CoRN.reals.fast.LazyNat.
Require Export CoRN.metric2.Limit.
Require Import CoRN.model.totalorder.QposMinMax.
Require Import Coq.QArith.Qpower.
Require Import Coq.QArith.Qabs.
Require Export MathClasses.theory.CoqStreams.
Require Import CoRN.transc.PowerSeries.
Require Import CoRN.tactics.CornTac.
Require Import CoRN.classes.Qclasses.
Require Import MathClasses.interfaces.abstract_algebra MathClasses.interfaces.orders MathClasses.theory.series MathClasses.theory.streams.
Require Import CoRN.reals.fast.CRAlternatingSum.

Opaque CR.

Local Open Scope Q_scope.

Lemma abs_power_neg_one : forall n:nat, Qabs ((-1)^n) == 1.
Proof.
  induction n. reflexivity.
  change (S n) with (1+n)%nat. rewrite Nat2Z.inj_add, Qpower_plus.
  rewrite Qabs_Qmult, IHn. reflexivity.
  intro abs. discriminate.
Qed.

Lemma Str_alt_decr_decr
  : forall (X:Type) (f : X*Q->X*Q) x
      (fdecr : Str_alt_decr X f x) (n : nat),
    0 <= Str_pth _ f 1 x ->
    (-1) ^ S n * Str_pth X f (Pos.of_nat (S (S n))) x
    <= (-1) ^ n [*] Str_pth X f (Pos.of_nat (S n)) x.
Proof.
  intros.
  pose proof (Str_alt_decr_pos X f x fdecr).
  specialize (fdecr (Pos.of_nat (S n))) as [fdecr _].
  rewrite <- Qmult_1_l in fdecr.
  rewrite <- (abs_power_neg_one (S n)) in fdecr.
  rewrite <- (Qmult_1_l (Qabs (Str_pth X f (Pos.of_nat (S n)) x))) in fdecr.
  rewrite <- (abs_power_neg_one n) in fdecr.
  rewrite <- Qabs_Qmult, <- Qabs_Qmult in fdecr.
  rewrite Qabs_pos, Qabs_pos in fdecr.
  rewrite Nat2Pos.inj_succ. 2: discriminate.
  exact fdecr. apply H0, H. apply H0, H. 
Qed.

Lemma AltSeries_convergent_pos
  : forall (X:Type) (f : X*Q->X*Q) x cvmod
      (fdecr : Str_alt_decr X f x)
      (flz : Limit_zero X f x cvmod),
    0 <= Str_pth _ f 1 x ->
    convergent (fun n:nat => inj_Q IR (Str_pth _ f (Pos.of_nat (S n)) x)).
Proof.
  intros.
  assert (forall n:nat, [--] [1] [^] n [=] (inj_Q IR ((-1)^n))) as power_neg_one.
  { intro n.
    rewrite inj_Q_power. apply nexp_wd.
    rewrite (inj_Q_inv IR 1), inj_Q_One. reflexivity. }
  apply (convergent_wd (fun n : nat => [--][1][^]n[*]([--][1][^]n[*]inj_Q IR (Str_pth _ f (Pos.of_nat (S n)) x)))).
  - intro n.
    rewrite power_neg_one.
    rewrite <- inj_Q_mult, <- inj_Q_mult. apply inj_Q_wd.
    rewrite Qmult_assoc. rewrite <- Qpower_plus.
    replace (n+n)%Z with (2* Z.of_nat n)%Z.
    rewrite Qpower_mult. replace ((-1)^2) with 1%Q by reflexivity.
    rewrite Qpower_1, Qmult_1_l. reflexivity. ring.
    intro abs. discriminate.
  - apply alternate_series_conv.
    + (* positivity *)
      clear flz. intro n.
      pose proof (Str_alt_decr_pos X f x fdecr n).
      rewrite power_neg_one.
      rewrite <- inj_Q_mult, <- inj_Q_Zero.
      apply inj_Q_leEq, H0, H.
    + (* f tends to zero. *)
      intros e epos.
      destruct (Q_dense_in_CReals IR e epos) as [q qpos qmaj].
      apply (less_wdl IR [0] _ (inj_Q IR 0)) in qpos.
      apply less_inj_Q in qpos.
      specialize (flz (exist _ _ qpos)).
      exists (Pos.to_nat (cvmod (exist _ _ qpos))). intros m H1.
      apply (AbsSmall_wdr _ _ (inj_Q IR ((-1)^m * Str_pth X f (Pos.of_nat (S m)) x))).
      2: rewrite inj_Q_mult, power_neg_one; rational.
      apply (AbsSmall_trans _ (inj_Q IR q) _ _ qmaj).
      apply inj_Q_AbsSmall.
      apply AbsSmall_Qabs.
      refine (Qle_trans _ _ _ _ flz). clear flz.
      rewrite Qabs_pos. 2: apply (Str_alt_decr_pos X f x fdecr), H.
      rewrite <- (Pos2Nat.id (cvmod (q ↾ qpos))).
      pose proof (Pos2Nat.is_pos (cvmod (q ↾ qpos))).
      destruct (Pos.to_nat (cvmod (q ↾ qpos))). exfalso; inversion H0.
      clear H0.
      rewrite <- (Qmult_1_l (Qabs (Str_pth X f (Pos.of_nat (S n)) x))).
      rewrite <- (abs_power_neg_one n).
      rewrite <- Qabs_Qmult, Qabs_pos.
      2: apply (Str_alt_decr_pos X f x fdecr), H.
      revert m n H1. induction m.
      intros. exfalso; inversion H1.
      intros. apply Nat.le_succ_r in H1. destruct H1.
      specialize (IHm n H0).
      apply (Qle_trans _ _ _ (Str_alt_decr_decr X f x fdecr m H) IHm).
      inversion H0. subst n. apply Str_alt_decr_decr.
      exact fdecr. exact H.
      rewrite inj_Q_Zero. reflexivity.
    + (* Decreasing *)
      intro n. rewrite power_neg_one, power_neg_one.
      rewrite <- inj_Q_mult, <- inj_Q_mult.
      apply inj_Q_leEq.
      apply Str_alt_decr_decr; assumption.
Qed.

Lemma AltSeries_convergent
  : forall (X:Type) (f : X*Q->X*Q) x cvmod
      (fdecr : Str_alt_decr X f x)
      (flz : Limit_zero X f x cvmod),
    convergent (fun n:nat => inj_Q IR (Str_pth _ f (Pos.of_nat (S n)) x)).
Proof.
  (* Test whether the first term is positive or negative. *)
  intros. 
  destruct (Qlt_le_dec (Str_pth _ f 1 x) 0).
  2: exact (AltSeries_convergent_pos X f x cvmod fdecr flz q).
  apply (convergent_wd
           (fun n : nat => [--][1][*]inj_Q IR (Str_pth _ (CRstreams.CRstream_opp X f) (Pos.of_nat (S n))
                                                  (let (y,r):=x in (y,-r))))).
  - (* the sequences are pointwise equal *)
    intro n.
    pose proof (CRstreams.CRstream_opp_pth X f x (Pos.of_nat (S n))).
    unfold Str_pth.
    destruct (CRstreams.iterate
                _ (CRstreams.CRstream_opp X f) 
                (Pos.of_nat (S n)) (let (y, r) := x in (y, - r))),
    (CRstreams.iterate (X and Q) f (Pos.of_nat (S n)) x).
    unfold snd. destruct H as [_ H]. subst q0.
    rewrite (inj_Q_inv IR q1), inv_mult_invol.
    rewrite <- inj_Q_One, <- inj_Q_mult.
    apply inj_Q_wd, Qmult_1_l.
  - apply conv_series_mult_scal.
    apply (AltSeries_convergent_pos X (CRstreams.CRstream_opp X f)
                                   (let (y, r) := x in (y, - r)) cvmod).
    apply CRstream_opp_decr, fdecr.
    apply CRstream_opp_limit_zero, flz.
    unfold CRstreams.CRstream_opp, Str_pth; simpl.
    destruct x. unfold Str_pth in q; simpl in q.
    replace (--q0) with q0.
    destruct (f (x,q0)). unfold snd. unfold snd in q.
    apply (Qopp_le_compat q1 0), Qlt_le_weak, q.
    destruct q0. unfold Qopp; simpl.
    rewrite Z.opp_involutive. reflexivity. 
Qed.

Lemma AltSeries_convergent_0
  : forall (X:Type) (f : X*Q->X*Q) x cvmod q
      (fdecr : Str_alt_decr X f x)
      (flz : Limit_zero X f x cvmod),
    convergent (fun n:nat => match n with
                        | O => q
                        | S _ => inj_Q IR (Str_pth _ f (Pos.of_nat n) x) end).
Proof.
  intros.
  (* Get rid of the initial zero. *)
  apply (join_series (fun n : nat => inj_Q IR (Str_pth _ f (Pos.of_nat (S n)) x))).
  - exact (AltSeries_convergent X f x cvmod fdecr flz). 
  - exists 1%nat. exists O. intros n _.
    rewrite Nat.add_comm. reflexivity.
Qed.

Lemma AltSeries_small_inf : forall (X : Type) (f : X * Q → X * Q)
                          (x : X * Q)
                          (cvmod : Qpos → positive)
                          (fdecr : Str_alt_decr X f x)
                          (flz : Limit_zero X f x cvmod)
                          (e : CRasCReals),
    AbsSmall e (' snd (f x))%CR
    -> AbsSmall e (AltSeries X f x cvmod fdecr flz)%CR.
Proof.
  intros.
  apply CRabs_AbsSmall.
  apply CRabs_AbsSmall in H.
  rewrite inject_Q_CR_abs in H.
  refine (CRle_trans _ H).
  clear H e. intro e. simpl.
  unfold Cap_raw; simpl.
  apply (Qle_trans _ 0%Q).
  apply (Qopp_le_compat 0), Qpos_nonneg.
  unfold Qminus. rewrite <- Qle_minus_iff.
  generalize (Qpos_mult
                (@exist Q (Qlt {| Qnum := Z0; Qden := xH |})
                   {| Qnum := Zpos xH; Qden := xO xH |}
                   (@eq_refl Datatypes.comparison Datatypes.Lt)) e).
  clear e. intro e.
  unfold SumStream.
  pose proof (CRstreams.iterate_stop_correct
                _
                (λ y : X * Q * Q, let (z, r) := f (fst y) in (z, r, Qred (r + snd y)))
                (λ y : X * Q * Q, Qle_bool (Qabs (snd (fst y))) (proj1_sig e))
                (cvmod e) (x,0%Q)) as [s [seq [_ H4]]].
  unfold zero, Q_0.
  rewrite seq. clear seq.
  rewrite SumStream_red.
  apply (AltSeries_small X f x s). 
  exact fdecr.
Qed.

Lemma AltSeries_remainder : forall (X : Type) (f : X * Q → X * Q)
                              (x : X * Q)
                              (cvmod : Qpos → positive)
                              (fdecr : Str_alt_decr X f x)
                              (flz : Limit_zero X f x cvmod)
                              (e : CRasCReals) (p : positive),
    AbsSmall e (' Str_pth X f p x)%CR
    -> AbsSmall e (inject_Q_CR (snd
         (CRstreams.iterate ((X and Q) and Q)
            (λ y : (X and Q) and Q,
               let (z0, r1) := f (fst y) in (z0, r1, Qred (r1 + snd y)))
            p (x, 0%Q))) - AltSeries X f x cvmod fdecr flz)%CR.
Proof.
  intros.
  rewrite (AltSeries_shift_pth p).
  rewrite CRopp_plus_distr, CRplus_assoc.
  rewrite CRplus_opp.
  apply (AbsSmall_minus CRasCOrdField e _ 0%CR).
  unfold cg_minus. simpl.
  rewrite CRopp_0, CRplus_0_r.
  apply AltSeries_small_inf. 
  specialize (fdecr p) as [fdecr _].
  unfold Str_pth in fdecr.
  rewrite <- CRstreams.iterate_succ.
  apply CRabs_AbsSmall.
  rewrite inject_Q_CR_abs.
  apply (@CRle_trans _ (inject_Q_CR (Qabs (snd (CRstreams.iterate (X and Q) f p x))))).
  apply (order_embedding_preserving inject_Q_CR), fdecr. 
  rewrite <- inject_Q_CR_abs.
  apply CRabs_AbsSmall.
  apply H. 
Qed. 

Lemma AltSeries_correct : forall (X:Type) (f : X*Q->X*Q) x cvmod
                            (fdecr : Str_alt_decr X f x)
                            (flz : Limit_zero X f x cvmod)
                            (g:nat -> IR) (H : convergent g),
    (forall n:positive, inj_Q IR (Str_pth _ f n x)%Q [=] g (Pos.to_nat n))
    -> (IRasCR (g O) + AltSeries _ f x cvmod fdecr flz == IRasCR (series_sum g H))%CR.
Proof.
  (* z equals to limit, means the sequence converges towards z. *)
  intros.
  unfold series_sum.
  rewrite -> IR_Lim_as_CR.
  apply (SeqLimit_unique CRasCReals).
  (* then prove convergence. Apply the Cauchy proof as C at e/2 to get an index n. *)
  intros e He.
  generalize (IR_Cauchy_prop_as_CR (Build_CauchySeq IR (seq_part_sum g) H)).
  intro C.
  destruct (C _ (pos_div_two CRasCOrdField _ He)) as [n Hn].
  exists (S (S n)).
  (* prove that the partial sum of g until m >= 2+n minus the infinite sum of f
     is less than e. It is equal to the remaining infinite sum of g after m. *)
  intros m Hm.
  unfold CS_seq in *.
  clear C.
  unfold seq_part_sum in *.
  destruct m. exfalso; inversion Hm.
  apply le_S_n in Hm.
  (* Replace g by f. *)
  assert (forall k:positive, le n (Pos.to_nat k)
                        -> AbsSmall e (inject_Q_CR (Str_pth _ f k x)))
    as kSmall.
  { intros.
    stepr (IRasCR (g (Pos.to_nat k))).
    setoid_replace (IRasCR (g (Pos.to_nat k)))
      with (@Sum CRasCAbGroup (Pos.to_nat k) (Pos.to_nat k) (fun n => IRasCR (g n)))
      by (rewrite Sum_one; reflexivity).
    unfold Sum, Sum1.
    rewrite <- IR_Sum0_as_CR, <- IR_Sum0_as_CR.
    (* Triangle inequality with the sum until n. *)
    stepr ((IRasCR (Sum0 (G:=IR) (S (Pos.to_nat k)) g) - (IRasCR (Sum0 (G:=IR) n g))) + 
            (IRasCR (Sum0 (G:=IR) n g) - IRasCR (Sum0 (G:=IR) (Pos.to_nat k) g)))%CR
      by (unfold cg_minus; simpl; unfold msp_Equiv; ring).
    apply (AbsSmall_eps_div_two CRasCOrdField e
                                (IRasCR (Sum0 (S (Pos.to_nat k)) g) - IRasCR (Sum0 n g))
                                (IRasCR (Sum0 n g) - IRasCR (Sum0 (Pos.to_nat k) g)))%CR.
    apply (Hn (S (Pos.to_nat k))).
    apply le_S, H1.
    apply (AbsSmall_minus CRasCOrdField (e [/]TwoNZ)
                          (IRasCR (Sum0 (Pos.to_nat k) g)) (IRasCR (Sum0 n g))). 
    apply Hn.
    exact H1.
    rewrite <- IR_inj_Q_as_CR.
    apply IRasCR_wd.
    symmetry.
    apply H0. }
  stepr (IRasCR (Sum0 (S m) g) - IRasCR (g 0%nat) - AltSeries X f x cvmod fdecr flz)%CR
    by (unfold cg_minus; simpl; unfold msp_Equiv; ring).
  setoid_replace (IRasCR (Sum0 (S m) g) - IRasCR (g 0%nat))%CR
    with (inject_Q_CR
            (snd (CRstreams.iterate
                    _ (λ y : X * Q * Q, let (z0, r1) := f (fst y) in (z0, r1, Qred (r1 + snd y)))
             (Pos.of_nat m) (x,0%Q)))).
  - apply AltSeries_remainder.
    apply kSmall.
    rewrite Nat2Pos.id. apply (Nat.le_trans _ (S n)).
    apply le_S, Nat.le_refl. exact Hm.
    destruct m. inversion Hm. discriminate.
  - clear kSmall.
    replace (S m) with (S (Pos.to_nat (Pos.of_nat m))).
    generalize (Pos.of_nat m).
    clear Hm m.
    apply Pos.peano_ind.
    + rewrite SumStream_red.
      rewrite CRstreams.iterate_one.
      specialize (H0 xH).
      unfold Str_pth, Pos.to_nat in H0. simpl in H0.
      simpl.
      destruct (f x). 
      simpl. simpl in H0.
      rewrite <- IR_minus_as_CR, <- IR_inj_Q_as_CR.
      apply IRasCR_wd.
      rewrite cm_lft_unit, cag_commutes.
      unfold cg_minus.
      rewrite <- CSemiGroups.plus_assoc.
      rewrite cg_rht_inv_unfolded, cm_rht_unit.
      rewrite <- H0.
      apply inj_Q_wd. rewrite Qplus_0_r. reflexivity.
    + intros p IHp.
      simpl (Sum0 (S (Pos.to_nat (Pos.succ p))) g).
      rewrite IR_plus_as_CR.
      rewrite (CRplus_comm (IRasCR (Sum0 (Pos.to_nat (Pos.succ p)) g))).
      rewrite Pos2Nat.inj_succ.
      rewrite <- CRplus_assoc, IHp. clear IHp.
      rewrite SumStream_red.
      rewrite SumStream_red.
      rewrite CRstreams.iterate_succ.
      rewrite SumStream_fst.
      simpl.
      rewrite <- CRstreams.iterate_succ.
      specialize (H0 (Pos.succ p)).
      unfold Str_pth in H0.
      destruct (CRstreams.iterate (X and Q) f (Pos.succ p) x).
      simpl.
      simpl in H0.
      rewrite Pos2Nat.inj_succ in H0.
      rewrite <- CRplus_Qplus.
      apply CRplus_eq_l.
      rewrite <- IR_inj_Q_as_CR.
      apply IRasCR_wd.
      symmetry. exact H0.
    + rewrite Nat2Pos.id. reflexivity.
      destruct m. inversion Hm. discriminate.
Qed.

