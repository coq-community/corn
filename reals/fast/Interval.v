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
Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import CoRN.model.totalorder.QposMinMax.
Require Export CoRN.metric2.Compact.
Require Export CoRN.reals.fast.CRArith.
Require Export CoRN.model.metric2.Qmetric.
Require Import Coq.QArith.Qround.
Require Import Coq.QArith.Qabs.
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

Let f n (i:Z) := l + ((r-l)*(2*i+1#1))/(2*Z_of_nat n#1).

Fixpoint iterateN A (f:A -> A) (z:A) (n:nat) : list A :=
match n with
 O => nil
|S m => z :: (iterateN f (f z) m)
end.

(** [UniformPartition] produces a set of n points uniformly distributed
inside the interval [[l, r]]. *)
Definition UniformPartition (n:nat) :=
map (f n) (iterateN Z.succ 0%Z n).

Lemma UniformPartitionZ : forall n z, In z (iterateN Z.succ 0%Z n) <-> (0 <= z < Z.of_nat n)%Z.
Proof.
 intros n z.
 change (0 <= z < Z.of_nat n)%Z with (0 <= z < 0 + Z.of_nat n)%Z.
 generalize 0%Z.
 induction n; intros a.
  split; intros H.
   contradiction.
  apply (Zle_not_lt a a). auto with *.
  rewrite Zplus_comm in H.
  simpl in H.
  apply Z.le_lt_trans with z; auto with *.
 split.
  intros [H | H].
   rewrite H.
   rewrite inj_S.
   auto with *.
  change (In z (iterateN Z.succ (Z.succ a) n)) in H.
  rewrite -> IHn in H.
  rewrite inj_S.
  auto with *.
 intros [H0 H1].
 destruct (Zle_lt_or_eq _ _ H0) as [H2 | H2].
  simpl.
  right.
  rewrite -> IHn.
  rewrite inj_S in H1.
  auto with *.
 rewrite H2.
 left.
 reflexivity.
Qed.

Lemma UniformPartition_inside : forall n x, In x (UniformPartition n) -> l <= x <= r.
Proof.
 intros n x.
 unfold UniformPartition.
 cut (forall z, In z (iterateN Z.succ 0%Z n) -> (0 <= z < Z.of_nat n)%Z).
 { destruct n.
   contradiction.
  generalize (iterateN Z.succ 0%Z (S n)).
  intros s Hs H.
  induction s.
   contradiction.
  destruct H as [H | H];auto with *.
  rewrite <- H.
  destruct (Hs a) as [Hz0 Hz1]; auto with *.
  clear - Hz0 Hz1 Hlr.
  split.
   rewrite -> Qle_minus_iff.
   unfold f, Qdiv.
   setoid_replace (l + (r - l) * (2 * a + 1 # 1) * / (2 * Z.of_nat (S n) # 1) + - l)
     with ((r + - l) * ((2 * a + 1 # 1) * / (2 * Z.of_nat (S n) # 1)))
     by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; ring).
   apply Qmult_le_0_compat.
    rewrite ->Qle_minus_iff in Hlr; auto.
   apply Qle_shift_div_l; auto with *.
   rewrite Qmult_0_l.
   change (0 <= (2*a + 1)*1)%Z.
   auto with *.
  rewrite -> Qle_minus_iff.
  unfold f.
  setoid_replace (r + - (l + (r - l) * (2 * a + 1 # 1) / (2 * Z.of_nat (S n) # 1)))
    with (((r-l)*((2*Z.of_nat (S n)#1) + - (2 * a + 1 # 1))) / (2 * Z.of_nat (S n) # 1))
    by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; field; discriminate).
  apply Qle_shift_div_l; auto with *.
  rewrite Qmult_0_l.
  apply Qmult_le_0_compat.
   rewrite -> Qle_minus_iff in Hlr; auto.
  change (0 <= ((2*Z.of_nat (S n))*1 + - (2*a + 1)*1)*1)%Z.
  auto with *. }
 clear - n.
 intros z.
 change (0 <= z < Z.of_nat n)%Z with (0 <= z < 0 + Z.of_nat n)%Z.
 revert z.
 generalize 0%Z.
 induction n.
  contradiction.
 intros z x Hx.
 destruct Hx as [Hx | Hx].
 - rewrite <- Hx; split; simpl.
  apply Z.le_refl.
  apply (Z.le_lt_trans _ (z+0)).
  rewrite Z.add_0_r. apply Z.le_refl.
  apply Z.add_lt_mono_l. reflexivity.
 - destruct (IHn (Z.succ z) x Hx).
   rewrite inj_S.
   split.
   exact (Z.le_trans _ _ _ (Z.le_succ_diag_r _) H).
   apply (Z.lt_le_trans _ _ _ H0).
   rewrite <- Z.add_1_r, <- Z.add_1_r.
   rewrite <- Z.add_assoc.
   apply Z.add_le_mono_l.
   rewrite Z.add_comm.
   apply Z.le_refl.
Qed.

(** Given a point [x] in the interval [[l, r]], one can find a
nearby point in our [UniformPartition]. *)
Definition rasterize1 n (x:Q) : Z
  := Qfloor (inject_Z (Z.of_nat n)*(x-l)/(r-l)).

Lemma rasterize1_close : l < r -> forall n (x:Q),
      Qabs (x - f (S n) (rasterize1 (S n) x))
      <= ((r-l)/((2#1) * inject_Z (Z.of_nat (S n)))).
Proof.
 clear Hlr.
 intros Hlr' n x.
 rewrite -> Qlt_minus_iff in Hlr'.
 assert (A:~ r - l == 0 /\ ~ inject_Z (Z.of_nat (S n)) == 0)
   by (split;auto with *;discriminate).
 setoid_replace ((r - l) / ((2#1) * inject_Z (Z.of_nat (S n))))
   with ((1#2)/(inject_Z (Z.of_nat (S n))/(r - l)))
   by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; field; auto).
 apply Qle_shift_div_l.
  apply Qlt_shift_div_l; auto with *.
 rewrite <- (Qabs_pos (inject_Z (Z.of_nat (S n))/(r-l))); [|apply Qle_shift_div_l; auto with *].
 rewrite <- Qabs_Qmult.
 unfold f.
 change (2*Z.of_nat (S n) # 1) with ((2#1)*inject_Z (Z.of_nat (S n))).
 setoid_replace ((x - (l + (r - l) * (2 * rasterize1 (S n) x + 1 # 1) / ((2#1) * inject_Z (Z.of_nat (S n))))) * (inject_Z (Z.of_nat (S n)) / (r - l)))
   with (inject_Z (Z.of_nat (S n))*(x-l)/(r-l) - (2*rasterize1 (S n) x + 1 # 1)/(2#1))
   by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; field; auto).
 rewrite -> Qmake_Qdiv.
 rewrite Q.Zplus_Qplus.
 unfold Qdiv.
 change (inject_Z 1) with 1%Q.
 rewrite Qmult_1_r.
 rewrite Q.Zmult_Qmult. 
 change (inject_Z 2) with (2#1).
 setoid_replace (((2#1) * inject_Z (rasterize1 (S n) x) + 1) / (2#1))
   with (inject_Z (rasterize1 (S n) x) + (1#2))
   by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; field; auto).
 unfold rasterize1.
 unfold Qdiv.
 generalize (inject_Z (Z.of_nat (S n)) * (x - l) * / (r - l)).
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

Definition rasterize1_boundR : forall n (x:Q), x < r -> (rasterize1 (S n) x < Z.of_nat (S n))%Z.
Proof.
 intros n x Hx.
 cut (inject_Z (rasterize1 (S n) x) < inject_Z (Z.of_nat (S n)))%Q.
  generalize (S n).
  intros m.
  unfold Qlt.
  simpl.
  auto with *.
 unfold rasterize1.
 eapply Qle_lt_trans.
  apply Qfloor_le.
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

Lemma UniformPartition_fine_aux
  : forall (n : nat) (x : Q) (Hx : l <= x <= r) (q : r <= x),
  In (f (S n) (Z.of_nat n)) (UniformPartition (S n)) /\
  Qabs (x - f (S n) (Z.of_nat n)) <= (r - l) / ((2#1) * inject_Z (Z.of_nat (S n))).
Proof.
  intros. 
  split.
  - apply in_map; rewrite -> UniformPartitionZ; rewrite inj_S; auto with *.
  - destruct Hx as [_ Hx].
    setoid_replace x with r by (apply Qle_antisym; assumption).
    unfold f.
    change (2*Z.of_nat (S n) #1) with ((2#1)*inject_Z (Z.of_nat (S n))).
    change (2*Z.of_nat n + 1#1) with (inject_Z (2*Z.of_nat n + 1)).
    rewrite (inj_S n).
    unfold Z.succ.
    do 2 rewrite Q.Zplus_Qplus.
    rewrite Q.Zmult_Qmult.
    change (inject_Z 2) with (2#1).
    change (inject_Z 1) with (1#1).
    setoid_replace (r - (l + (r - l) * ((2#1) * inject_Z (Z.of_nat n) + 1)
                                         / ((2#1) * (inject_Z (Z.of_nat n) + 1))))
      with (((r-l) / ((2#1) * (inject_Z (Z.of_nat n) + 1))))
      by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; field; auto).
    rewrite -> Qabs_pos.
    apply Qle_refl.
    apply Qle_shift_div_l.
    rewrite <- (Qmult_0_r (2#1)).
    apply Qmult_lt_l. reflexivity.
    unfold Qlt; simpl; auto with *.
    rewrite Qmult_0_l; rewrite -> Qle_minus_iff in Hlr; auto.
    change 1 with (inject_Z 1).
    rewrite <- Q.Zplus_Qplus, Z.add_1_r.
    rewrite <- Zpos_P_of_succ_nat.
    apply Q.positive_nonzero_in_Q.
Qed.

Lemma UniformPartition_fine : forall n x,
    l <= x <= r -> {y | In y (UniformPartition (S n))
                     /\ Qabs (x - y) <= ((r-l)/((2#1)*inject_Z (Z.of_nat (S n))))}.
Proof.
 intros n x Hx.
 destruct (Qlt_le_dec_fast x r).
  exists (f (S n) (rasterize1 (S n) x)).
  abstract ( destruct Hx as [Hlx Hxr]; split; [apply in_map; rewrite -> UniformPartitionZ; split;
    [apply rasterize1_boundL; auto |apply rasterize1_boundR; auto] |apply rasterize1_close;
      apply Qle_lt_trans with x; auto]).
 exists (f (S n) (Z.of_nat n)).
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

Definition CompactIntervalQ_raw (e:QposInf) : FinEnum stableQ :=
match e with
| QposInfinity => nil
| Qpos2QposInf e' =>
  UniformPartition (max 1 (Z.to_nat (Qceiling ((r - l) / (inject_Z 2 * proj1_sig e')))))
end.

Lemma CompactIntervalQ_prf : is_RegularFunction (@ball (FinEnum stableQ)) CompactIntervalQ_raw.
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
  set (e1':=(max 1 (Z.to_nat (Qceiling ((r - l) / (inject_Z 2 * proj1_sig e1)))))) in *.
  assert (L:=UniformPartition_inside e1').
  induction (UniformPartition e1').
   contradiction.
  destruct (Qeq_dec a a0) as [A|A].
   rewrite -> A.
   auto with *.
  apply IHl0; auto with *.
  destruct Ha as [G | Ha | Ha] using orC_ind.
    auto using InFinEnumC_stable.
   elim A.
   assumption.
  assumption. }
 unfold CompactIntervalQ_raw.
 set (e2':=(max 1 (Z.to_nat (Qceiling ((r - l) / (inject_Z 2 * proj1_sig e2)))))).
 assert (L:=UniformPartition_fine (pred e2') H).
 rewrite <- (S_pred _ O) in L.
 destruct L as [y [Hy0 Hy1]].
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
     rewrite inj_max.
     unfold Qle.
     simpl.
     ring_simplify.
     eapply Z.le_trans;[|apply Z.le_max_r].
     rewrite Z2Nat.id. apply Z.le_refl.
     exact He.
   + rewrite <- Qplus_0_l at 1.
     apply Qplus_le_l.
     apply Qpos_nonneg.
 - apply (lt_le_trans _ 1). auto.
   apply Nat.le_max_l.
Qed.

Definition CompactIntervalQ : Compact stableQ :=
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
  set (a:=(max 1 (Z.to_nat (Qceiling ((r - l) / (inject_Z 2 * proj1_sig e2)))))) in *.
  assert (L0:=UniformPartition_inside a).
  induction (UniformPartition a).
   contradiction.
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
 set (a:=(max 1 (Z.to_nat (Qceiling ((r - l) / (inject_Z 2 * proj1_sig e2)))))) in *.
 assert (L0:=UniformPartition_inside a).
 induction (UniformPartition a).
  contradiction.
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
 apply (@almostIn_triangle_l _ stableQ (proj1_sig e1) (proj1_sig e2) (approximate x e1) y).
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
   apply Qle_trans with 0%Q; auto with *.
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
 set (n:=(max 1 (Z.to_nat (Qceiling ((r - l) / (inject_Z 2 * proj1_sig e2)))))).
 destruct (UniformPartition_fine (pred n) L) as [z Hz].
 assert (L0:(0 < n)%nat).
 { unfold n.
   apply (Nat.lt_le_trans _ 1).
   apply le_refl.
   apply Nat.le_max_l. }
 rewrite <- (S_pred _ O L0) in Hz.
  clear - Hz.
  destruct Hz as [Hz0 Hz1].
  induction (UniformPartition n).
   contradiction.
  destruct Hz0 as [Hz0 | Hz0]; apply orWeaken.
   + left.
   rewrite Hz0.
   simpl.
   rewrite -> Qball_Qabs.
   eapply Qle_trans;[apply Hz1|].
   clear Hz1.
   apply Qle_shift_div_r.
   rewrite <- (Qmult_0_r (2#1)).
   apply Qmult_lt_l. reflexivity.
   change 0%Q with (inject_Z 0).
   rewrite <- Zlt_Qlt.
   apply (Z.lt_le_trans _ 1).
   reflexivity.
   apply (inj_le 1).
   apply Nat.le_max_l.
   rewrite Qmult_comm, (Qmult_comm (2#1)), <- Qmult_assoc.
   rewrite <- (Qinv_involutive (inject_Z 2*proj1_sig e2)).
   apply Qle_shift_div_l.
   apply Qinv_lt_0_compat.
   apply (Qpos_ispos ((2#1)*e2)).
   unfold Qdiv in n.
   unfold n. clear n.
   generalize ((r - l) * / (inject_Z 2 * proj1_sig e2))%Q.
   intro q. 
   apply (Qle_trans _ (inject_Z (Qceiling q)) _ (Qle_ceiling _)).
   rewrite inj_max.
   unfold Qle.
   simpl.
   ring_simplify.
   destruct (Qceiling q).
   discriminate.
   rewrite Z2Nat.id. apply Z.le_max_r.
   discriminate. discriminate.
   + right.
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
