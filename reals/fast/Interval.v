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
Require Export CoRN.metric2.Compact.
Require Export CoRN.reals.fast.CRArith.
Require Export CoRN.model.metric2.Qmetric.
Require Import CoRN.model.ordfields.Qordfield.
Require Import CoRN.algebra.COrdFields2.
Require Import Coq.QArith.Qround.
Require Import CoRN.tactics.Qauto.
Require Import Coq.QArith.Qabs.
Require Import CoRN.model.totalorder.QMinMax.
Require Import CoRN.logic.Classic.
Require Import CoRN.tactics.CornTac.

Open Local Scope Q_scope.

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

(** [UniformPartition] produces a set of n points uniformly distributed
inside the interval [[l, r]]. *)
Definition UniformPartition (n:nat) :=
map (f n) (iterateN Zsucc 0%Z n).

Lemma UniformPartitionZ : forall n z, In z (iterateN Zsucc 0%Z n) <-> (0 <= z < n)%Z.
Proof.
 intros n z.
 change (0 <= z < n)%Z with (0 <= z < 0 + n)%Z.
 generalize 0%Z.
 induction n; intros a.
  split; intros H.
   contradiction.
  apply (Zle_not_lt a a); auto with *.
  rewrite Zplus_comm in H.
  simpl in H.
  apply Zle_lt_trans with z; auto with *.
 split.
  intros [H | H].
   rewrite H.
   rewrite inj_S.
   auto with *.
  change (In z (iterateN Zsucc (Zsucc a) n)) in H.
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
 cut (forall z, In z (iterateN Zsucc 0%Z n) -> (0 <= z < n)%Z).
  destruct n.
   contradiction.
  generalize (iterateN Zsucc 0%Z (S n)).
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
   replace RHS with ((r + - l) * ((2 * a + 1 # 1) * / (2 * (S n) # 1))) by simpl; ring.
   apply: mult_resp_nonneg.
    rewrite ->Qle_minus_iff in Hlr; auto.
   apply Qle_shift_div_l; auto with *.
   replace LHS with 0 by (simpl; ring).
   change (0 <= (2*a + 1)*1)%Z.
   auto with *.
  rewrite -> Qle_minus_iff.
  unfold f.
  replace RHS with (((r-l)*((2*S n#1) + - (2 * a + 1 # 1))) / (2 * S n # 1)) by (simpl; field; discriminate).
  apply Qle_shift_div_l; auto with *.
  replace LHS with 0 by simpl; ring.
  apply: mult_resp_nonneg.
   rewrite -> Qle_minus_iff in Hlr; auto.
  change (0 <= ((2*S n)*1 + - (2*a + 1)*1)*1)%Z.
  auto with *.
 clear - n.
 intros z.
 change (0 <= z < n)%Z with (0 <= z < 0 + n)%Z.
 revert z.
 generalize 0%Z.
 induction n.
  contradiction.
 intros z x Hx.
 destruct Hx as [Hx | Hx].
  rewrite <- Hx; split; simpl; auto with *.
 destruct (IHn (Zsucc z) x Hx).
 rewrite inj_S.
 auto with *.
Qed.

(** Given a point [x] in the interval [[l, r]], one can find a
nearby point in our [UniformPartition]. *)
Definition rasterize1 n (x:Q) := Qfloor ((Z_of_nat n)*(x-l)/(r-l)).

Lemma rasterize1_close : l < r -> forall n (x:Q), Qabs (x - f (S n) (rasterize1 (S n) x)) <= ((r-l)/(2*(S n))).
Proof.
 clear Hlr.
 intros Hlr' n x.
 rewrite -> Qlt_minus_iff in Hlr'.
 assert (A:~ r - l == 0 /\ ~ S n == 0) by (split;auto with *;discriminate).
 replace RHS with ((1#2)/((S n)/(r - l))) by (simpl; field;auto).
 apply Qle_shift_div_l.
  apply Qlt_shift_div_l; auto with *.
 rewrite <- (Qabs_pos (S n/(r-l))); [|apply Qle_shift_div_l; auto with *].
 rewrite <- Qabs_Qmult.
 unfold f.
 change (2*S n # 1) with (2*S n).
 setoid_replace ((x - (l + (r - l) * (2 * rasterize1 (S n) x + 1 # 1) / (2 * S n))) * (S n / (r - l)))
   with ((S n)*(x-l)/(r-l) - (2*rasterize1 (S n) x + 1 # 1)/2); [| now (simpl; field; auto)].
 rewrite -> Qmake_Qdiv.
 rewrite -> injz_plus.
 setoid_replace ((2 * rasterize1 (S n) x + 1%positive) / 1%positive / 2)
   with (rasterize1 (S n) x + (1#2)).
  2:simpl; field.
 unfold rasterize1.
 generalize (S n * (x - l) / (r - l)).
 intros q.
 clear - q.
 apply Qabs_case; intros H; rewrite -> Qle_minus_iff.
  replace RHS with (Qfloor q + 1 + - q) by simpl; ring.
  rewrite <- Qle_minus_iff.
  apply Qlt_le_weak.
  rewrite <- (injz_plus (Qfloor q) 1).
  apply Qlt_floor.
 replace RHS with (q + -Qfloor q) by simpl; ring.
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
  replace LHS with 0 by simpl; ring.
  apply: mult_resp_nonneg; simpl; auto with *.
 rewrite -> Hlr'.
 setoid_replace (r-r) with 0; [| now simpl; ring].
 unfold Qdiv.
 change (/0) with 0.
 ring_simplify.
 auto with *.
Qed.

Definition rasterize1_boundR : forall n (x:Q), x < r -> (rasterize1 (S n) x < (S n))%Z.
Proof.
 intros n x Hx.
 cut (rasterize1 (S n) x < (S n)).
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
  apply: mult_resp_less_lft;simpl; auto with *.
  rewrite -> Qlt_minus_iff.
  replace RHS with (r + - x) by simpl; ring.
  rewrite <- Qlt_minus_iff; auto.
 rewrite -> Hlr'.
 setoid_replace (r-r) with 0; [| now simpl; ring].
 unfold Qdiv.
 change (/0) with 0.
 replace LHS with 0 by simpl; ring.
 auto with *.
Qed.

Lemma UniformPartition_fine : forall n x,
 l <= x <= r -> {y | In y (UniformPartition (S n)) /\ Qabs (x - y) <= ((r-l)/(2*(S n)))}.
Proof.
 intros n x Hx.
 destruct (Qlt_le_dec_fast x r).
  exists (f (S n) (rasterize1 (S n) x)).
  abstract ( destruct Hx as [Hlx Hxr]; split; [apply in_map; rewrite -> UniformPartitionZ; split;
    [apply rasterize1_boundL; auto |apply rasterize1_boundR; auto] |apply rasterize1_close;
      apply Qle_lt_trans with x; auto]).
 exists (f (S n) n).
 abstract ( split; [apply: in_map; rewrite -> UniformPartitionZ; rewrite inj_S; auto with *|];
   destruct Hx as [_ Hx]; (setoid_replace x with r; [| now apply Qle_antisym; auto with *]); unfold f;
     change (2*S n #1) with (2*S n); change (2*n + 1#1) with ((2*n + 1)%Z:Q); rewrite (inj_S n);
       unfold Zsucc; do 2 rewrite -> injz_plus; (setoid_replace ((2%positive * n)%Z:Q) with (2*n)
         ; [| now unfold Qeq; simpl; auto with *]);
           (setoid_replace (r - (l + (r - l) * (2 * n + 1%positive) / (2 * (n + 1%positive))))
             with (((r-l) / (2 * (n + 1%positive)))); [| now simpl; field; unfold Qeq; simpl; auto with *]);
               rewrite -> Qabs_pos;[apply Qle_refl|]; apply Qle_shift_div_l;
                 [apply: mult_resp_pos; simpl;auto with *; unfold Qlt; simpl; auto with *|];
                   (replace LHS with 0 by simpl; ring); rewrite -> Qle_minus_iff in Hlr; auto).
Defined.

(** Construct the compact set. *)
Lemma CompactIntervalQ_nat : forall (e:Qpos), (0 <= Qceiling ((r-l)/(2*e)))%Z.
Proof.
 intros e.
 change (0%Z) with (Qceiling 0).
 apply Qceiling_resp_le.
 apply Qle_shift_div_l.
  auto with *.
 rewrite -> Qle_minus_iff in Hlr.
 Qauto_le.
Qed.

Definition CompactIntervalQ_raw (e:QposInf) : FinEnum stableQ :=
match e with
| QposInfinity => nil
| Qpos2QposInf e' =>
  UniformPartition (max 1 (Z_to_nat (CompactIntervalQ_nat e')))
end.

Lemma CompactIntervalQ_prf : is_RegularFunction CompactIntervalQ_raw.
Proof.
 cut (forall e1 e2, hemiMetric Q_as_MetricSpace (e1 + e2) (fun a : Q_as_MetricSpace =>
   InFinEnumC a (CompactIntervalQ_raw e1)) (fun a : Q_as_MetricSpace =>
     InFinEnumC a (CompactIntervalQ_raw e2))).
  intros Z e1 e2.
  split.
   apply Z.
  eapply hemiMetric_wd1;[|apply Z].
  QposRing.
 intros e1 e2 a Ha.
 assert (l <= a <= r).
  unfold CompactIntervalQ_raw in Ha.
  set (e1':=(max 1 (Z_to_nat (z:=Qceiling ((r - l) / (2%positive * e1)))
    (CompactIntervalQ_nat e1)))) in *.
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
  assumption.
 unfold CompactIntervalQ_raw.
 set (e2':=(max 1 (Z_to_nat (z:=Qceiling ((r - l) / (2%positive * e2))) (CompactIntervalQ_nat e2)))).
 assert (L:=UniformPartition_fine (pred e2') H).
 rewrite S_predn in L; [|intros Z; symmetry in Z;revert Z; apply lt_O_neq; unfold e2';
   apply lt_le_trans with 1%nat; auto with *].
 destruct L as [y [Hy0 Hy1]].
 apply existsWeaken.
 exists y.
 split.
  auto using InFinEnumC_weaken.
 simpl.
 rewrite -> Qball_Qabs.
 eapply Qle_trans;[apply Hy1|].
 apply Qle_trans with e2.
  apply Qle_shift_div_r.
   destruct e2'; auto with *.
  replace RHS with (e2'*(2%positive*e2)) by simpl; ring.
  rewrite <- (Qinv_involutive (2%positive*e2)).
  apply Qle_shift_div_l.
   apply Qinv_lt_0_compat.
   auto with *.
  change ( (r - l) / (2%positive * e2) <= e2').
  unfold e2'.
  generalize (CompactIntervalQ_nat e2).
  generalize ((r - l) / (2%positive * e2)).
  intros q He.
  apply Qle_trans with (Qceiling q); auto with *.
  rewrite inj_max.
  unfold Qle.
  simpl.
  ring_simplify.
  eapply Zle_trans;[|apply Zle_max_r].
  rewrite <- Z_to_nat_correct.
  auto with *.
 autorewrite with QposElim.
 Qauto_le.
Qed.

Definition CompactIntervalQ : Compact stableQ :=
Build_RegularFunction CompactIntervalQ_prf.

Open Local Scope CR_scope.

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
  replace RHS with (e + - (l - approximate x e))%Q by simpl; ring.
  rewrite <- Qle_minus_iff.
  apply Qle_closed.
  intros e2.
  assert (L:=Hx e e2).
  simpl in L.
  set (a:=(max 1 (Z_to_nat (z:=Qceiling ((r - l) / (2%positive * e2)))
    (CompactIntervalQ_nat e2)))) in *.
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
   replace RHS with (a0 + - l)%Q by simpl; ring.
   rewrite <- Qle_minus_iff.
   destruct (L0 a0); auto with *.
  apply IHl0; auto with *.
 unfold CRle.
 rewrite -> CRplus_translate.
 intros e.
 simpl.
 rewrite -> Qle_minus_iff.
 replace RHS with (e + - (approximate x e - r))%Q by simpl; ring.
 rewrite <- Qle_minus_iff.
 apply Qle_closed.
 intros e2.
 assert (L:=Hx e e2).
 simpl in L.
 set (a:=(max 1 (Z_to_nat (z:=Qceiling ((r - l) / (2%positive * e2)))
   (CompactIntervalQ_nat e2)))) in *.
 assert (L0:=UniformPartition_inside a).
 induction (UniformPartition a).
  contradiction.
 destruct L as [ G | L | L] using orC_ind.
   auto with *.
  rewrite -> Qball_Qabs in L.
  eapply Qle_trans;[|apply L].
  eapply Qle_trans;[|apply Qle_Qabs].
  rewrite -> Qle_minus_iff.
  replace RHS with (r + - a0)%Q by simpl; ring.
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
 apply (@almostIn_triangle_l _ stableQ e1 e2 (approximate x e1) y).
  unfold y.
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
    rewrite ->  Qle_minus_iff in *.
    replace RHS with (-l + approximate x e1 + - - e1)%Q by simpl; ring.
    auto.
   apply Qle_trans with 0%Q; auto with *.
   clear - H.
   rewrite -> Qle_minus_iff in *.
   replace RHS with (l + - approximate x e1)%Q by simpl; ring.
   auto.
  intros H.
  rewrite -> Qle_max_l in Hlr.
  simpl.
  rewrite -> Hlr.
  split; simpl.
   clear - H.
   apply Qle_trans with 0%Q; auto with *.
   rewrite -> Qle_minus_iff in *.
   replace RHS with (approximate x e1 + - r)%Q by simpl; ring.
   auto.
  unfold CRle in Hxr.
  rewrite -> CRplus_translate in Hxr.
  assert (H0:=Hxr e1).
  simpl in H0.
  clear - H0.
  rewrite -> Qle_minus_iff in *.
  replace RHS with ( r + - approximate x e1 + - - e1)%Q by simpl; ring.
  auto.
 assert (L: l <= y <= r).
  unfold y.
  auto with *.
 set (n:=(max 1 (Z_to_nat (z:=Qceiling ((r - l) / (2%positive * e2))) (CompactIntervalQ_nat e2)))).
 destruct (UniformPartition_fine (pred n) L) as [z Hz].
 assert (L0:(0 < 2*n)%Q).
  Transparent max.
  simpl.
  destruct ( Z_to_nat (z:=Qceiling ((r - l) / (2%positive * e2)))
    (CompactIntervalQ_nat e2)); auto with *.
 rewrite S_predn in Hz.
  clear - Hz L0.
  destruct Hz as [Hz0 Hz1].
  induction (UniformPartition n).
   contradiction.
  destruct Hz0 as [Hz0 | Hz0]; apply orWeaken.
   left.
   rewrite Hz0.
   simpl.
   rewrite -> Qball_Qabs.
   eapply Qle_trans;[apply Hz1|].
   apply Qle_shift_div_r;auto.
   replace RHS with (n*(2%positive*e2))%Q by simpl; ring.
   rewrite <- (Qinv_involutive (2%positive*e2)).
   apply Qle_shift_div_l.
    apply Qinv_lt_0_compat. auto with *.
   unfold n.
   fold ((r - l) / (2%positive * e2)).
   generalize (CompactIntervalQ_nat e2).
   generalize ((r - l) / (2%positive * e2)).
   intros q He.
   apply Qle_trans with (Qceiling q); auto with *.
   rewrite inj_max.
   unfold Qle.
   simpl.
   ring_simplify.
   eapply Zle_trans;[|apply Zle_max_r].
   rewrite <- Z_to_nat_correct.
   auto with *.
  right.
  apply IHl0.
  auto.
 clear - L0.
 intros H.
 rewrite H in L0.
 discriminate L0.
Qed.

Lemma CompactIntervalQ_bonus_correct : forall e x,
 In x (approximate CompactIntervalQ e) -> (l <= x <= r).
Proof.
 intros [e|] x H.
  simpl in H.
  apply: UniformPartition_inside.
  apply H.
 elim H.
Qed.

End Interval.
