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
From Coq Require Import ZArith.
Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import CoRN.model.totalorder.QposMinMax.
Require Export CoRN.metric2.Compact.
Require Export CoRN.metric2.LocatedSubset.
Require Export CoRN.reals.fast.CRArith.
Require Import CoRN.reals.fast.CRabs.
Require Export CoRN.model.metric2.Qmetric.
From Coq Require Import Qround.
From Coq Require Import Qabs.
Require Import CoRN.model.totalorder.QMinMax.
Require Import CoRN.logic.Classic.

Local Open Scope Q_scope.

Opaque Qabs.

Set Implicit Arguments.

Section Interval.
(**
* Intervals as a Compact Set.
We want to make an efficent implementation of intervals as compact sets.
We want to minimize the number of sample points in the approximations of

a compact interval.
*)
Variable (l r:Q).
Hypothesis Hlr : l <= r.

Let f (n:positive) (i:Z) := l + ((r-l)*(2*i+1#1))/(2*Zpos n#1).

Fixpoint iterateN_succ (z:Z) (n:positive) : list Z :=
  match n with
  | xI p => z :: app (iterateN_succ (Z.succ z) p)
                   (iterateN_succ (Z.succ z + Zpos p) p)
  | xO p => app (iterateN_succ z p) (iterateN_succ (z + Zpos p) p)
  | xH => z :: nil
  end.

Lemma iterateN_succ_example : iterateN_succ 4 3 = (4 :: 5 :: 6 :: nil)%Z.
Proof. reflexivity. Qed.

Lemma iterateN_succ_length
  : forall n z,
    length (iterateN_succ z n) = Pos.to_nat n.
Proof.
  induction n.
  - intro z. simpl.
    rewrite Pos2Nat.inj_xI. apply f_equal.
    rewrite app_length, IHn, IHn.
    simpl.
    rewrite Nat.add_0_r. reflexivity.
  - intro z. simpl.
    rewrite app_length, IHn, IHn.
    rewrite Pos2Nat.inj_xO. simpl.
    rewrite Nat.add_0_r. reflexivity.
  - reflexivity.
Qed.

Lemma iterateN_succ_nth
  : forall n (j:nat) s z,
    (j < Pos.to_nat n)%nat -> nth j (iterateN_succ s n) z = (s + Z.of_nat j)%Z.
Proof.
  induction n.
  - intros. simpl.
    destruct j. simpl. rewrite Z.add_0_r. reflexivity.
    destruct (le_lt_dec (Pos.to_nat n) j) as [l0|l0].
    + rewrite <- (iterateN_succ_length n (Z.succ s)) in l0.
      rewrite (app_nth2 _ _ z l0).
      pose proof (Nat.le_exists_sub _ _ l0) as [k [H0 _]].
      subst j.
      rewrite Nat.add_sub.
      rewrite IHn.
      rewrite iterateN_succ_length.
      rewrite Nat2Z.inj_succ, Nat2Z.inj_add, <- positive_nat_Z.
      ring.
      rewrite (iterateN_succ_length n (Z.succ s)), Pos2Nat.inj_xI in H.
      simpl in H. rewrite Nat.add_0_r in H.
      apply le_S_n in H.
      apply (Nat.add_le_mono_r _ _ (Pos.to_nat n)).
      exact H.
    + rewrite <- (iterateN_succ_length n (Z.succ s)) in l0.
      rewrite (app_nth1 _ _ z l0).
      rewrite IHn.
      rewrite Nat2Z.inj_succ. ring.
      rewrite <- (iterateN_succ_length n (Z.succ s)).
      exact l0. 
  - intros. simpl.
    destruct (le_lt_dec (Pos.to_nat n) j) as [l0|l0].
    + rewrite <- (iterateN_succ_length n s) in l0.
      rewrite (app_nth2 (iterateN_succ s n)
                        (iterateN_succ (s + Z.pos n) n) z l0).
      pose proof (Nat.le_exists_sub _ _ l0) as [k [H0 _]].
      subst j.
      rewrite Nat.add_sub.
      rewrite IHn.
      rewrite (iterateN_succ_length n s).
      rewrite Nat2Z.inj_add, <- positive_nat_Z.
      ring.
      rewrite (iterateN_succ_length n s), Pos2Nat.inj_xO in H.
      simpl in H. rewrite Nat.add_0_r in H.
      apply (Nat.add_le_mono_r _ _ (Pos.to_nat n)).
      exact H.
    + rewrite <- (iterateN_succ_length n s) in l0.
      rewrite (app_nth1 (iterateN_succ s n)
                        (iterateN_succ (s + Z.pos n) n) z l0).
      apply IHn.
      rewrite <- (iterateN_succ_length n s).
      exact l0.
  - intros. simpl.
    destruct j. simpl. rewrite Z.add_0_r. reflexivity.
    exfalso. inversion H. inversion H1.
Qed.


(** [UniformPartition] produces a set of n points uniformly distributed
    inside the interval [[l, r]]. We use binary positive instead of
    unary nat for faster computations. *)
Definition UniformPartition (n:positive) : list Q :=
  map (f n) (iterateN_succ 0%Z n).

Lemma UniformPartitionZ : forall n a z,
    In z (iterateN_succ a n) <-> (a <= z < a + Zpos n)%Z.
Proof.
  split.
  - intro H. apply (In_nth _ _ 0%Z) in H.
    destruct H as [p [H H0]].
    subst z. rewrite iterateN_succ_length in H.
    rewrite iterateN_succ_nth.
    2: exact H. split.
    rewrite <- (Z.add_0_r a) at 1.
    apply Z.add_le_mono_l. apply Nat2Z.is_nonneg.
    apply Z.add_lt_mono_l.
    destruct p. reflexivity.
    rewrite <- (Nat2Pos.id (S p)) in H.
    2: discriminate.
    apply Pos2Nat.inj_lt in H. 
    simpl.
    rewrite Pos.of_nat_succ. exact H.
  - revert n z a. 
    induction n; intros.
    + simpl. destruct (Z.le_gt_cases z a).
      left. apply Z.le_antisymm. apply H. exact H0.
      right. destruct (Z.le_gt_cases (Z.succ a + Z.pos n) z).
      apply in_app_iff. right. apply IHn.
      split. apply H1.
      rewrite <- Z.add_assoc, Z.add_diag.
      apply (Z.lt_le_trans _ _ _ (proj2 H)).
      rewrite <- Z.add_1_l, (Z.add_comm 1).
      rewrite <- Z.add_assoc.
      apply Z.le_refl.
      apply in_app_iff. left. apply IHn.
      split. apply Zlt_le_succ, H0. exact H1.
    + simpl. destruct (Z.le_gt_cases (a + Z.pos n) z).
      apply in_app_iff. right. apply IHn.
      split. apply H0.
      rewrite <- Z.add_assoc, Z.add_diag. apply H.
      apply in_app_iff. left. apply IHn.
      split. apply H. exact H0.
    + left. destruct H. apply Z.le_antisymm. exact H.
      rewrite Z.add_comm, Z.add_1_l in H0.
      apply Zlt_succ_le, H0.
Qed.

Lemma UniformPartition_inside : forall n x, In x (UniformPartition n) -> l <= x <= r.
Proof.
 intros n x.
 unfold UniformPartition.
 assert (forall z, In z (iterateN_succ 0%Z n) -> (0 <= z < Zpos n)%Z) as H.
 { intros. apply UniformPartitionZ in H. exact H. }
 revert H.
  generalize (iterateN_succ 0%Z n).
  intros s Hs H.
  induction s.
   contradiction.
  destruct H as [H | H];auto with *.
  rewrite <- H.
  destruct (Hs a) as [Hz0 Hz1]; auto with *.
  clear - Hz0 Hz1 Hlr.
  split.
   unfold f, Qdiv.
   rewrite <- (Qplus_0_r l) at 1.
   apply Qplus_le_r.
   apply Qle_shift_div_l. reflexivity.
   rewrite Qmult_0_l.
   apply Qmult_le_0_compat.
  unfold Qminus. rewrite <- Qle_minus_iff. exact Hlr.
   unfold Qle, Qnum, Qden.
   rewrite Z.mul_1_r, Z.mul_1_r.
   apply (Z.le_trans _ (1*a+0)%Z).
   rewrite Z.add_0_r, Z.mul_1_l. exact Hz0.
   apply Z.add_le_mono. apply Z.mul_le_mono_nonneg_r.
   exact Hz0.
   discriminate. discriminate.
  unfold f.
  apply (Qplus_le_r _ _ (-l)).
  rewrite Qplus_assoc.
  rewrite (Qplus_comm (-l)), Qplus_opp_r, Qplus_0_l.
  apply Qle_shift_div_r. reflexivity.
  rewrite (Qplus_comm (-l)), Qmult_comm, (Qmult_comm (r+-l)).
  apply Qmult_le_compat_r.
  unfold Qle, Qnum, Qden. rewrite Z.mul_1_r, Z.mul_1_r.
  rewrite Z.add_comm, Z.add_1_l.
  apply Zlt_le_succ.
  apply Z.mul_lt_mono_pos_l. 
  reflexivity. exact Hz1.
  rewrite <- Qle_minus_iff. exact Hlr.
Qed.

(** Given a point [x] in the interval [[l, r]], one can find a
nearby point in our [UniformPartition]. n is the number of points in
the partition, ie the step is (r-l)/n. This function computes the
maximum index k such that l+k(r-l)/n <= x. *)
Definition rasterize1 (n:positive) (x:Q) : Z
  := Qfloor (inject_Z (Zpos n)*(x-l)/(r-l)).

Lemma rasterize1_close : l < r -> forall (n:positive) (x:Q),
      Qabs (x - f n (rasterize1 n x))
      <= ((r-l)/((2#1) * inject_Z (Zpos n))).
Proof.
 clear Hlr.
 intros Hlr' n x.
 rewrite -> Qlt_minus_iff in Hlr'.
 assert (A:~ r - l == 0 /\ ~ inject_Z (Zpos n) == 0)
   by (split;auto with *;discriminate).
 setoid_replace ((r - l) / ((2#1) * inject_Z (Zpos n)))
   with ((1#2)/(inject_Z (Zpos n)/(r - l)))
   by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; field; auto).
 apply Qle_shift_div_l.
  apply Qlt_shift_div_l; auto with *.
 rewrite <- (Qabs_pos (inject_Z (Zpos n)/(r-l))); [|apply Qle_shift_div_l; auto with *].
 rewrite <- Qabs_Qmult.
 unfold f.
 change (2*Zpos n # 1) with ((2#1)*inject_Z (Zpos n)).
 setoid_replace ((x - (l + (r - l) * (2 * rasterize1 n x + 1 # 1) / ((2#1) * inject_Z (Zpos n)))) * (inject_Z (Zpos n) / (r - l)))
   with (inject_Z (Zpos n)*(x-l)/(r-l) - (2*rasterize1 n x + 1 # 1)/(2#1))
   by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; field; auto).
 rewrite -> Qmake_Qdiv.
 rewrite Q.Zplus_Qplus.
 unfold Qdiv.
 change (inject_Z 1) with 1%Q.
 rewrite Qmult_1_r.
 rewrite Q.Zmult_Qmult. 
 change (inject_Z 2) with (2#1).
 setoid_replace (((2#1) * inject_Z (rasterize1 n x) + 1) / (2#1))
   with (inject_Z (rasterize1 n x) + (1#2))
   by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; field; auto).
 unfold rasterize1.
 unfold Qdiv.
 generalize (inject_Z (Zpos n) * (x - l) * / (r - l)).
 intros q.
 clear - q.
 apply Qabs_case; intros H; rewrite -> Qle_minus_iff.
 setoid_replace ((1 # 2) + - (q - (inject_Z (Qfloor q) + (1 # 2))))
   with (inject_Z (Qfloor q) + 1 + - q)
   by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; ring).
  rewrite <- Qle_minus_iff.
  apply Qlt_le_weak.
  change 1 with (inject_Z 1).
  rewrite <- (Q.Zplus_Qplus (Qfloor q) 1).
  apply Qlt_floor.
  setoid_replace ((1 # 2) + - - (q - (inject_Z (Qfloor q) + (1 # 2))))
    with (q + -inject_Z (Qfloor q))
    by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; ring).
 rewrite <- Qle_minus_iff.
 apply Qfloor_le.
Qed.

Definition rasterize1_boundL : forall n (x:Q), l <= x -> (0 <= rasterize1 n x)%Z.
Proof.
 intros n x Hx.
 change 0%Z with (Qfloor 0).
 apply Qfloor_resp_le.
 destruct (Qle_lt_or_eq _ _ Hlr) as [Hlr' | Hlr'].
  rewrite -> Qlt_minus_iff in Hlr'.
  rewrite -> Qle_minus_iff in Hx.
  apply Qle_shift_div_l; auto with *.
  rewrite Qmult_0_l.
  apply Qmult_le_0_compat; simpl; auto with *.
 rewrite -> Hlr'.
 unfold Qminus.
 rewrite Qplus_opp_r.
 unfold Qdiv.
 change (/0) with 0.
 ring_simplify.
 auto with *.
Qed.

Definition rasterize1_boundR : forall n (x:Q), x < r -> (rasterize1 n x < Zpos n)%Z.
Proof.
 intros n x Hx.
 rewrite Zlt_Qlt.
 unfold rasterize1.
 apply (Qle_lt_trans _ _ _ (Qfloor_le _)).
 destruct (Qle_lt_or_eq _ _ Hlr) as [Hlr' | Hlr'].
  rewrite -> Qlt_minus_iff in Hlr'.
  apply Qlt_shift_div_r.
   auto with *.
  apply Qmult_lt_l;simpl; auto with *.
  rewrite -> Qlt_minus_iff.
  setoid_replace (r - l + - (x - l))
    with (r + - x)
    by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; ring).
  rewrite <- Qlt_minus_iff; auto.
 rewrite -> Hlr'.
 unfold Qminus.
 rewrite Qplus_opp_r.
 unfold Qdiv.
 change (/0) with 0.
 rewrite Qmult_0_r.
 auto with *.
Qed.

(* Index of x = r in the partition. *)
Lemma UniformPartition_fine_aux
  : forall (n : positive) (x : Q) (Hx : l <= x <= r) (q : r <= x),
  In (f n (Zpos n - 1)) (UniformPartition n) /\
  Qabs (x - f n (Zpos n - 1)) <= (r - l) / ((2#1) * inject_Z (Zpos n)).
Proof.
  intros. 
  split.
  - apply in_map; rewrite -> UniformPartitionZ.
    split. apply Z.le_0_sub, Pos.le_1_l.
    rewrite Z.add_comm.
   apply Z.add_lt_mono_l. reflexivity.
  - destruct Hx as [_ Hx].
    setoid_replace x with r by (apply Qle_antisym; assumption).
    unfold f.
    replace (2 * (Z.pos n - 1) + 1)%Z with (2 * Z.pos n - 1)%Z by ring.
    change (2*Zpos n #1) with ((2#1)*inject_Z (Zpos n)).
    change (2*Zpos n - 1#1) with (inject_Z (2*Zpos n + - 1)).
    rewrite Q.Zplus_Qplus.
    rewrite Q.Zmult_Qmult.
    change (inject_Z 2) with (2#1).
    change (inject_Z (-1)) with (-1#1).
    setoid_replace (r - (l + (r - l) * ((2#1) * inject_Z (Zpos n) + (-1#1))
                                         / ((2#1) * (inject_Z (Zpos n)))))
      with (((r-l) / ((2#1) * (inject_Z (Zpos n)))))
      by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; field; auto).
    rewrite -> Qabs_pos.
    apply Qle_refl.
    apply Qle_shift_div_l. reflexivity.
    rewrite Qmult_0_l; rewrite -> Qle_minus_iff in Hlr; auto.
Qed.

(* For any point x in [[l,r]], there is a point y in the uniform partition
   that is close to x within half the partition's step. *)
Lemma UniformPartition_fine : forall (n:positive) (x:Q),
    l <= x <= r
    -> {y | In y (UniformPartition n)
           /\ Qabs (x - y) <= ((r-l)/((2#1)*inject_Z (Zpos n)))}.
Proof.
 intros n x Hx.
 destruct (Qlt_le_dec_fast x r).
 - (* x < r *)
   exists (f n (rasterize1 n x)).
 abstract ( destruct Hx as [Hlx Hxr]; split;
            [apply in_map; rewrite -> UniformPartitionZ; split;
             [apply rasterize1_boundL; auto |apply rasterize1_boundR; auto]
            |apply rasterize1_close; apply Qle_lt_trans with x; auto]).
 - (* x = r *)
   exists (f n (Zpos n - 1)).
   apply UniformPartition_fine_aux; assumption.
Defined.

(** Construct the compact set. *)
Lemma CompactIntervalQ_nat : forall (e:Qpos),
    (0 <= Qceiling ((r-l)/(inject_Z 2*proj1_sig e)))%Z.
Proof.
 intros e.
 change (0%Z) with (Qceiling 0).
 apply Qceiling_resp_le.
 apply Qle_shift_div_l.
  auto with *.
  rewrite Qmult_0_l.
  unfold Qminus.
  rewrite <- Qle_minus_iff.
  exact Hlr.
Qed.

(* The finite approximation of real interval [l,r] by rational numbers,
   at precision e. *)
Definition CompactIntervalQ_raw (e:QposInf) : list Q :=
match e with
| QposInfinity => nil
| Qpos2QposInf e' =>
  UniformPartition (Z.to_pos (Qceiling ((r - l) / (inject_Z 2 * proj1_sig e'))))
end.

Lemma CompactIntervalQ_prf
  : is_RegularFunction (@ball (FinEnum Q_as_MetricSpace)) CompactIntervalQ_raw.
Proof.
 cut (forall (e1 e2:Qpos), hemiMetric Q_as_MetricSpace (proj1_sig e1 + proj1_sig e2) (fun a : Q_as_MetricSpace =>
   InFinEnumC a (CompactIntervalQ_raw e1)) (fun a : Q_as_MetricSpace =>
     InFinEnumC a (CompactIntervalQ_raw e2))).
  { intros Z e1 e2.
  split. apply (Qpos_nonneg (e1+e2)). split.
   apply Z.
  eapply hemiMetric_wd1;[|apply Z].
  unfold QposEq; simpl; ring. }
 intros e1 e2 a Ha.
 assert (l <= a <= r).
 { unfold CompactIntervalQ_raw in Ha.
  set (e1':=Z.to_pos (Qceiling ((r - l) / (inject_Z 2 * proj1_sig e1)))) in *.
  assert (L:=UniformPartition_inside e1').
  induction (UniformPartition e1').
  exfalso; exact (FinSubset_ball_nil Ha).
  destruct (Qeq_dec a a0) as [A|A].
   rewrite -> A.
   auto with *.
  apply IHl0; auto with *.
  apply FinSubset_ball_orC in Ha.
  destruct Ha as [G | Ha | Ha] using orC_ind.
  intro abs. contradict G; intro G. contradiction.
   elim A.
   apply Qball_0 in Ha. exact Ha.
  assumption. }
 unfold CompactIntervalQ_raw.
 set (e2':=Z.to_pos (Qceiling ((r - l) / (inject_Z 2 * proj1_sig e2)))).
 pose proof (UniformPartition_fine e2' H) as [y [Hy0 Hy1]].
 apply existsWeaken.
 exists y.
 split.
 - apply InFinEnumC_weaken, Hy0.
 - simpl.
   rewrite -> Qball_Qabs.
   eapply Qle_trans;[apply Hy1|].
   apply Qle_trans with (proj1_sig e2).
   apply Qle_shift_div_r.
   destruct e2'; auto with *.
   rewrite Qmult_comm, (Qmult_comm (2#1)), <- Qmult_assoc.
   rewrite <- (Qinv_involutive (inject_Z 2*proj1_sig e2)).
   apply Qle_shift_div_l.
   + apply Qinv_lt_0_compat.
     exact (Qpos_ispos ((2#1)*e2)).
   + unfold e2'.
     generalize (CompactIntervalQ_nat e2).
     unfold Qdiv.
     generalize ((r - l) * / (inject_Z 2 * proj1_sig e2)).
     intros q He.
     apply Qle_trans with (inject_Z (Qceiling q)).
     apply Qle_ceiling.
     destruct (Qceiling q). discriminate.
     rewrite Z2Pos.id.
     apply Z.le_refl.
     reflexivity. discriminate.
   + rewrite <- Qplus_0_l at 1.
     apply Qplus_le_l.
     apply Qpos_nonneg.
Qed.

Definition CompactIntervalQ : Compact Q_as_MetricSpace :=
Build_RegularFunction CompactIntervalQ_prf.

Local Open Scope CR_scope.

Opaque max.

(** The compact set indeed represents the interval [[l, r]]. *)
Lemma CompactIntervalQ_correct1 : forall (x:CR),
 inCompact x CompactIntervalQ -> ('l <= x /\ x <= 'r).
Proof.
 intros x Hx.
 split.
  unfold CRle.
  assert (x - 'l == '(-l)%Q + x)%CR. ring. rewrite -> H. clear H.
  rewrite -> CRplus_translate.
  intros e.
  simpl.
  rewrite -> Qle_minus_iff.
  setoid_replace (- l + approximate x e + - - proj1_sig e)%Q
    with (proj1_sig e + - (l - approximate x e))%Q
    by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; ring).
  rewrite <- Qle_minus_iff.
  apply Qle_closed.
  intros e2.
  assert (L:=Hx e e2).
  simpl in L.
  set (a:=Z.to_pos (Qceiling ((r - l) / (inject_Z 2 * proj1_sig e2)))) in *.
  assert (L0:=UniformPartition_inside a).
  induction (UniformPartition a).
  exfalso; exact (FinSubset_ball_nil L).
  apply FinSubset_ball_orC in L.
  destruct L as [ G | L | L] using orC_ind.
    auto with *.
   rewrite -> Qball_Qabs in L.
   eapply Qle_trans;[|apply L].
   rewrite <- Qabs_opp.
   eapply Qle_trans;[|apply Qle_Qabs].
   rewrite -> Qle_minus_iff.
   setoid_replace (- (approximate x e - a0) + - (l - approximate x e))%Q
     with (a0 + - l)%Q
     by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; ring).
   rewrite <- Qle_minus_iff.
   destruct (L0 a0); auto with *.
  apply IHl0; auto with *.
 unfold CRle.
 rewrite -> CRplus_translate.
 intros e.
 simpl.
 rewrite -> Qle_minus_iff.
 setoid_replace (r + - approximate x e + - - proj1_sig e)%Q
   with (proj1_sig e + - (approximate x e - r))%Q
   by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; ring).
 rewrite <- Qle_minus_iff.
 apply Qle_closed.
 intros e2.
 assert (L:=Hx e e2).
 simpl in L.
 set (a:=Z.to_pos (Qceiling ((r - l) / (inject_Z 2 * proj1_sig e2)))) in *.
 assert (L0:=UniformPartition_inside a).
 induction (UniformPartition a).
  exfalso; exact (FinSubset_ball_nil L).
  apply FinSubset_ball_orC in L.
 destruct L as [ G | L | L] using orC_ind.
   auto with *.
  rewrite -> Qball_Qabs in L.
  eapply Qle_trans;[|apply L].
  eapply Qle_trans;[|apply Qle_Qabs].
  rewrite -> Qle_minus_iff.
  setoid_replace (approximate x e - a0 + - (approximate x e - r))%Q
    with (r + - a0)%Q
    by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; ring).
  rewrite <- Qle_minus_iff.
  destruct (L0 a0); auto with *.
 apply IHl0; auto with *.
Qed.

Lemma CompactIntervalQ_correct2 : forall (x:CR),
 ('l <= x /\ x <= 'r) -> inCompact x CompactIntervalQ.
Proof.
 intros x [Hlx Hxr] e1 e2.
 simpl.
 set (y:= (Qmax (Qmin (approximate x e1) r) l)).
 apply (@FinSubset_ball_triangle_l _ (proj1_sig e1) (proj1_sig e2) (approximate x e1) y).
 - unfold y.
  apply Qmin_case.
   apply Qmax_case.
    auto with *.
   intros H _.
   split; simpl.
    unfold CRle in Hlx.
    assert (x - 'l == '(-l)%Q + x). ring. rewrite -> H0 in Hlx. clear H0.
    rewrite -> CRplus_translate in Hlx.
    assert (H0:=Hlx e1).
    simpl in H0.
    clear - H0.
    unfold Qminus. rewrite Qplus_comm.
    exact H0.
   apply Qle_trans with 0%Q; auto with *.
   clear - H.
   rewrite Qle_minus_iff in *. 
   setoid_replace (0 + - (approximate x e1 - l))%Q
     with (l + - approximate x e1)%Q
     by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; ring).
   exact H.
  intros H.
  rewrite -> Qle_max_l in Hlr.
  simpl.
  rewrite -> Hlr.
  split; simpl.
   clear - H.
   apply Qle_trans with 0%Q.
   apply (Qopp_le_compat 0), Qpos_nonneg.
   rewrite -> Qle_minus_iff in *.
   rewrite Qplus_0_r.
   auto.
  unfold CRle in Hxr.
  rewrite -> CRplus_translate in Hxr.
  assert (H0:=Hxr e1).
  simpl in H0.
  clear - H0.
  rewrite -> Qle_minus_iff in *.
  setoid_replace (proj1_sig e1 + - (approximate x e1 - r))%Q
    with ( r + - approximate x e1 + - - proj1_sig e1)%Q
    by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; ring). 
  exact H0.
 - assert (L: l <= y <= r).
   { unfold y. auto with *. }
 set (n:=Z.to_pos (Qceiling ((r - l) / (inject_Z 2 * proj1_sig e2)))).
 destruct (UniformPartition_fine n L) as [z Hz].
  clear - Hz.
  destruct Hz as [Hz0 Hz1].
  induction (UniformPartition n).
   contradiction.
  destruct Hz0 as [Hz0 | Hz0].
   + intro abs; contradict abs. exists a.
     split. left. reflexivity.
   rewrite Hz0.
   simpl.
   rewrite -> Qball_Qabs.
   eapply Qle_trans;[apply Hz1|].
   clear Hz1.
   apply Qle_shift_div_r.
   reflexivity.
   unfold Qdiv in n.
   unfold n. clear n.
   rewrite (Qmult_comm (r-l)).
   apply (Qmult_le_l _ _ (/(inject_Z 2 * proj1_sig e2))).
   apply Qinv_lt_0_compat. apply (Qpos_ispos ((2#1)*e2)).
   generalize (/ (inject_Z 2 * proj1_sig e2) * (r-l))%Q.
   intro q. 
   rewrite Qmult_assoc, Qmult_assoc.
   setoid_replace (/ (inject_Z 2 * proj1_sig e2) * proj1_sig e2 * (2#1))%Q with 1%Q
     by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; field). 
   rewrite Qmult_1_l.
   apply (Qle_trans _ (inject_Z (Qceiling q)) _ (Qle_ceiling _)).
   rewrite <- Zle_Qle.
   destruct (Qceiling q).
   discriminate.
   apply Z.le_refl.
   discriminate. apply Qpos_nonzero.
   + apply FinSubset_ball_cons.
     apply IHl0, Hz0.
Qed.

Lemma CompactIntervalQ_bonus_correct : forall e x,
 In x (approximate CompactIntervalQ e) -> (l <= x <= r).
Proof.
 intros [e|] x H.
  simpl in H.
  eapply UniformPartition_inside.
  apply H.
 elim H.
Qed.

End Interval.

(* Located subsets are more general than compact subsets. *)
Lemma InfiniteIntervalLocated
  : forall a : CR, LocatedSubset CR (fun x => a <= x)%CR.
Proof.
  intros a d e x ltde.
  (* The distance between x and [a,+\infty[ is CRmax 0 (a-x). *)
  destruct (CRlt_linear _ (CRmax 0%CR (a-x)%CR) _ (CRlt_Qlt d e ltde))
    as [far|close].
  - left. intros y H abs.
    clear ltde e.
    destruct (Qlt_le_dec d 0).
    apply (msp_nonneg (msp CR)) in abs.
    exact (Qlt_not_le _ _ q abs).
    assert (~(('d < a - x)%CR -> False)).
    { intros H0. apply CRle_not_lt in H0.
      revert far. apply CRle_not_lt, CRmax_lub.
      apply CRle_Qle, q. exact H0. }
    clear far.
    contradict H0. apply CRle_not_lt.
    apply CRabs_ball, CRabs_AbsSmall in abs.
    destruct abs as [abs _].
    rewrite (CRplus_le_r _ _ (y+('d)))%CR in abs.
    ring_simplify in abs.
    apply (CRle_trans H) in abs.
    clear H y.
    rewrite (CRplus_le_r _ _ x).
    ring_simplify.
    rewrite CRplus_comm. exact abs.
  - destruct (Qlt_le_dec d 0).
    left. intros y H abs.
    apply (msp_nonneg (msp CR)) in abs.
    exact (Qlt_not_le _ _ q abs). 
    right. exists (CRmax a x).
    split. apply CRmax_ub_l.
    apply CRabs_ball, CRabs_AbsSmall.
    split.
    + rewrite (CRplus_le_r _ _ (CRmax a x + 'e))%CR.
      ring_simplify.
      apply CRmax_lub.
      rewrite (CRplus_le_r _ _ (-x))%CR.
      rewrite <- CRplus_assoc.
      rewrite CRplus_opp, CRplus_0_r.
      apply CRle_not_lt. intro abs.
      apply (CRlt_trans _ _ _ close) in abs.
      clear close. revert abs.
      apply CRle_not_lt.
      apply CRmax_ub_r.
      apply (@CRle_trans _ (0+x)%CR).
      rewrite CRplus_0_l. apply CRle_refl.
      apply CRplus_le_r.
      apply CRle_Qle, (Qle_trans _ _ _ q).
      apply Qlt_le_weak, ltde.
    + rewrite (CRplus_le_r _ _ (CRmax a x)).
      ring_simplify.
      apply (@CRle_trans _ (CRmax a x + 0)%CR).
      rewrite CRplus_0_r. apply CRmax_ub_r.
      apply CRplus_le_l, CRle_Qle.
      apply (Qle_trans _ _ _ q).
      apply Qlt_le_weak, ltde.
Qed.
