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
Require Import CoRN.model.totalorder.QposMinMax.
Require Export CoRN.metric2.Hausdorff.
Require Import CoRN.logic.Classic.
Require Export CoRN.stdlib_omissions.List.
Require Export CoRN.metric2.Classification.
Require Import CoRN.metric2.Complete.
Require Import CoRN.metric2.Prelength.

Set Implicit Arguments.

Local Open Scope Q_scope.

Section Finite.

Variable X:MetricSpace.

(**
* Finite Enumerations
Here we define a classical in predicate for lists.  Being classically
in a list doesn't tell you which element in the list you are.
*)
Fixpoint InFinEnumC (x:X) (l:list X) : Prop :=
match l with
| nil => False
| y::ys => orC (st_eq x y) (InFinEnumC x ys)
end.

Lemma InFinEnumC_weaken : forall x l, (In x l) -> InFinEnumC x l.
Proof.
 induction l.
  contradiction.
 intros [H0|H0]; apply orWeaken.
  left.
  rewrite H0.
  reflexivity.
 right.
 apply IHl.
 assumption.
Qed.

Lemma InFinEnumC_wd1 : forall x y l, (st_eq x y) -> (InFinEnumC x l <-> InFinEnumC y l).
Proof.
 induction l.
  simpl; tauto.
 intros H.
 simpl.
 cut ((st_eq x a)<->(st_eq y a)).
  unfold orC; tauto.
 rewrite -> H.
 reflexivity.
Qed.

Lemma InFinEnumC_stable : forall x l, ~~(InFinEnumC x l) -> InFinEnumC x l.
Proof.
 induction l.
  simpl; auto.
 intros H H0.
 apply H.
 clear H.
 intros H.
 destruct H as [HG | H | H] using orC_ind; tauto.
Qed.

Lemma InFinEnumC_app_l : forall x l1 l2, InFinEnumC x l1 -> InFinEnumC x (l1 ++ l2).
Proof.
 intros x l1 l2 H.
 induction l1.
  contradiction.
 destruct H as [ G | H | H] using orC_ind.
   auto using InFinEnumC_stable.
  apply orWeaken.
  left.
  auto.
 apply orWeaken.
 right.
 apply IHl1.
 assumption.
Qed.

Lemma InFinEnumC_app_r : forall x l1 l2, InFinEnumC x l2 -> InFinEnumC x (l1 ++ l2).
Proof.
 intros x l1 l2 H.
 induction l1.
  assumption.
 apply orWeaken.
 right.
 apply IHl1.
Qed.
(* begin hide *)
Hint Resolve InFinEnumC_app_l InFinEnumC_app_r.
(* end hide *)
Lemma InFinEnumC_app_orC : forall x l1 l2, InFinEnumC x (l1 ++ l2) -> orC (InFinEnumC x l1)  (InFinEnumC x l2).
Proof.
 intros x l1 l2 H.
 induction l1.
  apply orWeaken.
  right.
  assumption.
 destruct H as [ G | H | H] using orC_ind.
   auto using orC_stable.
  apply orWeaken.
  left.
  apply orWeaken.
  left.
  assumption.
 destruct (IHl1 H) as [ G | IH | IH] using orC_ind.
   auto using orC_stable.
  apply orWeaken.
  left.
  apply orWeaken.
  right.
  assumption.
 apply orWeaken.
 right.
 assumption.
Qed.

(**
** Equivalence
Two finite enumerations, represented as lists, are equivalent
if they (classically) have the same elements.
*)
Definition FinEnum_eq (a b:list X) : Prop :=
 forall x, InFinEnumC x a <-> InFinEnumC x b.

Lemma FinEnum_eq_refl : forall a, FinEnum_eq a a.
Proof.
 unfold FinEnum_eq.
 reflexivity.
Qed.

Lemma FinEnum_eq_sym : forall a b, FinEnum_eq a b -> FinEnum_eq b a.
Proof.
 unfold FinEnum_eq.
 symmetry.
 auto.
Qed.

Lemma FinEnum_eq_trans : forall a b c, FinEnum_eq a b -> FinEnum_eq b c -> FinEnum_eq a c.
Proof.
 unfold FinEnum_eq.
 intros a b c H0 H1 x.
 transitivity (InFinEnumC x b); auto.
Qed.
(* begin hide *)
Hint Resolve FinEnum_eq_refl FinEnum_eq_sym FinEnum_eq_trans : FinEnum.
(* end hide *)

Lemma FinEnum_is_Setoid : Setoid_Theory _ FinEnum_eq.
Proof.
 split; unfold Reflexive, Symmetric, Transitive; auto with *.
 apply FinEnum_eq_trans.
Qed.

Definition FinEnumS : RSetoid := Build_RSetoid FinEnum_is_Setoid.

(**
** Metric Space
Finite enumerations form a metric space under the Hausdorff metric for
any stable metric space X.
*)
Definition FinEnum_ball (e:Q) (x y:list X) :=
 hausdorffBall X e (fun a => InFinEnumC a x) (fun a => InFinEnumC a y).

Lemma FinEnum_ball_wd : forall (e1 e2:Q), (e1 == e2) ->
 forall (a1 a2 : FinEnumS), st_eq a1 a2 ->
 forall (b1 b2 : FinEnumS), st_eq b1 b2 ->
 (FinEnum_ball e1 a1 b1 <-> FinEnum_ball e2 a2 b2).
Proof.
 intros e1 e2 He a1 a2 Ha b1 b2 Hb.
 apply hausdorffBall_wd; auto with *.
Qed.

Lemma hemiMetric_closed : forall e A b,
 (forall d, 0 < d -> hemiMetric X (e+d) A (fun a => InFinEnumC a b)) ->
  hemiMetric X e A (fun a => InFinEnumC a b).
Proof.
 intros e A b H x Hx.
 set (P:=fun n y => ball (e + (1#(P_of_succ_nat n))%Q) x y).
 assert (HP:(forall n, existsC X (fun x => ~~In x b /\ P n x))).
 { intros n.
  unfold P.
  destruct (H (1#(P_of_succ_nat n))%Q eq_refl x Hx)
    as [HG | y [Hy0 Hy1]] using existsC_ind.
   apply existsC_stable; auto.
  clear - Hy0 Hy1.
  induction b.
   contradiction.
  destruct (Hy0) as [HG | Hy2 | Hy2] using orC_ind.
    apply existsC_stable; auto.
   apply existsWeaken.
   exists a.
   split; auto 7 with *.
   apply (ball_wd _ eq_refl _ _ (reflexivity _) _ _ Hy2).
   assumption.
  destruct (IHb Hy2) as [HG | z [Hz0 Hz1]] using existsC_ind.
   apply existsC_stable; auto.
  apply existsWeaken.
  exists z.
  split; auto 7 with *. }
 destruct (infinitePidgeonHolePrinicple _ _ P HP) as [HG | y [Hy0 Hy1]] using existsC_ind.
  apply existsC_stable; auto.
 apply existsWeaken.
 exists y.
 split; auto using InFinEnumC_weaken.
 apply ball_closed.
 intros [n d] dpos.
 destruct n. inversion dpos. 2: inversion dpos.
 destruct (Hy1 (nat_of_P d)) as [HG | m [Hmd Hm]] using existsC_ind.
  apply (msp_stable (msp X) (e + (Zpos p#d))%Q); assumption.
 eapply ball_weak_le;[|apply Hm].
 simpl.
 rewrite -> Qle_minus_iff.
 ring_simplify.
 rewrite <- Qle_minus_iff.
 apply Zmult_le_compat.
 apply Pos.le_1_l.
 simpl. apply Pos2Nat.inj_le.
 apply (le_trans _ _ _ Hmd).
 rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
 apply le_S, le_refl.
 discriminate. discriminate.
Qed.

Lemma FinEnum_ball_closed : forall e a b,
 (forall d, 0 < d -> FinEnum_ball (e+d) a b) ->
 FinEnum_ball e a b.
Proof.
 unfold FinEnum_ball, hausdorffBall.
 intros e a b Hab.
 split.
 - apply Qnot_lt_le. intro abs.
   specialize (Hab (-e * (1#2))). destruct Hab.
   rewrite <- (Qmult_0_l (1#2)). apply Qmult_lt_r.
   reflexivity. apply (Qplus_lt_l _ _ e). ring_simplify.
   exact abs.
   ring_simplify in H.
   rewrite <- (Qmult_0_r (1#2)) in H.
   apply Qmult_le_l in H. exact (Qlt_not_le _ _ abs H). reflexivity.
 - split; apply hemiMetric_closed; firstorder. 
Qed.

Lemma FinEnum_ball_eq :
 forall a b : list X, (forall e : Qpos, FinEnum_ball (proj1_sig e) a b) -> FinEnum_eq a b.
Proof.
 unfold FinEnum_ball, FinEnum_eq.
 cut (forall a b : list X, (forall e : Qpos, hemiMetric X (proj1_sig e) (fun a0 : X => InFinEnumC a0 a)
   (fun a0 : X => InFinEnumC a0 b)) -> forall x : X, InFinEnumC x a -> InFinEnumC x b).
  unfold hausdorffBall.
  split; apply H; firstorder.
 induction a.
  contradiction.
 intros b H x Hx.
 destruct Hx as [HG | Hx | Hx] using orC_ind.
   auto using InFinEnumC_stable.
  assert (H':forall n :nat ,
             existsC X (fun y : X => InFinEnumC y b
                                  /\ ball (m:=X) (1#(P_of_succ_nat n)) x y)).
   intros e.
   apply (H (exist (Qlt 0) (1#(P_of_succ_nat e)) eq_refl)).
   apply orWeaken.
   left;  assumption.
  assert (H'':forall n :nat ,
             existsC X (fun y : X => ~~In y b
                                  /\ ball (m:=X) (1#(P_of_succ_nat n)) x y)).
  { intros n.
   destruct (H' n) as [HG | z [Hz0 Hz1]] using existsC_ind.
    auto using existsC_stable.
   clear - Hz1 Hz0.
   induction b.
    contradiction.
   destruct (Hz0) as [Hg | Hz2 | Hz2] using orC_ind.
     auto using existsC_stable.
    apply existsWeaken.
    exists a.
    split; auto with *.
    apply (ball_wd _ eq_refl _ _ (reflexivity _) _ _ Hz2).
    assumption.
   destruct (IHb Hz2) as [HG | y [Hy0 Hy1]] using existsC_ind.
    auto using existsC_stable.
   apply existsWeaken.
   exists y.
   split; auto 7 with *. }
   destruct (infinitePidgeonHolePrinicple _ _ _ H'')
     as [HG | y [Hy0 Hy1]] using existsC_ind.
   auto using InFinEnumC_stable.
  rewrite -> (InFinEnumC_wd1 x y).
   auto using InFinEnumC_weaken.
  apply ball_eq.
  intros [n d] dpos.
  destruct n. inversion dpos. 2: inversion dpos.
  replace d with (Pos.of_succ_nat (Init.Nat.pred (Pos.to_nat d))).
  destruct (Hy1 (pred (nat_of_P d))) as [HG | z [Hz0 Hz1]] using existsC_ind.
  apply (msp_stable (msp X) (Zpos p # Pos.of_succ_nat (Init.Nat.pred (Pos.to_nat d)))). auto.
  apply ball_weak_le with (1 # P_of_succ_nat z); auto.
  simpl.
  apply Zmult_le_compat; auto with *.
  apply Pos.le_1_l. simpl.
  assert (forall i j:nat, le i j -> Pos.of_succ_nat i <= Pos.of_succ_nat j)%positive.
  { intros.
    rewrite Pos.of_nat_succ, Pos.of_nat_succ.
    apply Pos2Nat.inj_le.
    rewrite Nat2Pos.id, Nat2Pos.id.
    apply le_n_S, H0. discriminate. discriminate. }
  apply H0, Hz0.
  discriminate.
  rewrite Pos.of_nat_succ.
  rewrite <- (Pos2Nat.id d) at 2.
  apply f_equal.
  symmetry. apply (S_pred _ O).
  apply Pos2Nat.is_pos.
 apply IHa; auto.
 intros e y Hy.
 apply H.
 apply orWeaken.
 right.
 assumption.
Qed.

Lemma FinEnum_is_MetricSpace : is_MetricSpace FinEnumS FinEnum_ball.
Proof.
 split.
 - intros e epos x. apply hausdorffBall_refl, epos.
 - intros e x y. apply hausdorffBall_sym.
 - intros e d x y z. apply hausdorffBall_triangle.
 - intros e x y. unfold FinEnum_ball.
   apply FinEnum_ball_closed.
 - intros. apply FinEnum_ball_eq.
   intros [e epos]. apply H, epos.
 - intros. apply H.
 - intros e x y.
   apply hausdorffBall_stable.
Qed.

Definition FinEnum : MetricSpace :=
Build_MetricSpace FinEnum_ball_wd FinEnum_is_MetricSpace.

Lemma FinEum_map_ball : forall (f:X -> X) (e:Qpos) (s:FinEnum),
 (forall x, ball (proj1_sig e) x (f x)) -> ball (proj1_sig e) s (map f s).
Proof.
 intros f e s H.
 induction s. split. apply Qpos_nonneg.
  split; intros a b; contradiction.
 destruct IHs as [IHs0 IHs1].
 split. apply Qpos_nonneg.
 split; intros x y; (destruct y as [G | y | y] using orC_ind; [auto using existsC_stable
   |apply existsWeaken |]).
    exists (f a);split.
     apply orWeaken; left; reflexivity.
     apply (ball_wd _ eq_refl _ _ y _ _ (reflexivity _)); apply H.
   destruct ((proj1 IHs1) x y) as [G | z [Hz0 Hz1]] using existsC_ind.
    auto using existsC_stable.
   apply existsWeaken.
   exists z.
   split; auto.
   apply orWeaken.
   right; assumption.
  exists a.
  split.
   apply orWeaken; left; reflexivity.
  apply ball_sym.
  apply (ball_wd _ eq_refl _ _ (reflexivity _) _ _ y); apply H.
 destruct ((proj2 IHs1) x y) as [G | z [Hz0 Hz1]] using existsC_ind.
  auto using existsC_stable.
 apply existsWeaken.
 exists z.
 split; auto.
 apply orWeaken.
 right; assumption.
Qed.

Section Strong.
(**
** Strong Hausdroff Metric
This section shows that the strong version of the Hausdroff metric
is equivalen to the weak version when X is a located metric.
*)
Hypothesis almostDecideX : locatedMetric X.

Lemma HemiMetricHemiMetricStrong : forall (e:Q) A b,
    hemiMetric X e A (fun a => InFinEnumC a b)
    -> hemiMetricStrong X e A (fun a => InFinEnumC a b).
Proof.
 intros e A b H x Hx.
 generalize (H x Hx).
 clear H.
 revert x Hx.
 induction b; intros x Hx H d.
  elimtype False.
  clear -H.
  abstract ( generalize H; apply existsC_ind;[tauto|]; intros y [Hy0 Hy1]; apply Hy0).
 destruct (@almostDecideX e (e + proj1_sig d) x a).
   clear - e d.
   abstract ( simpl; rewrite -> Qlt_minus_iff; ring_simplify; auto with * ).
  exists a.
  clear - b0.
  abstract (auto using InFinEnumC_weaken with * ).
 assert (Z:existsC X (fun y : X => InFinEnumC y b /\ ball (m:=X) e x y)).
 { clear - H n.
   destruct (H) as [HG | y [Hy0 Hy1]] using existsC_ind.
   auto using existsC_stable.
   apply existsWeaken. exists y.
   split. 2: exact Hy1. destruct Hy0 as [HG | Hy | Hy] using orC_ind.
   auto using InFinEnumC_stable. 2: assumption.
   apply (ball_wd _ eq_refl _ _ (reflexivity _) _ _ Hy) in Hy1. 
   contradiction. }
 exists (let (y,_) := (IHb x Hx Z d) in y).
 clear - IHb.
 abstract ( destruct (IHb x Hx Z d) as [y [Hy0 Hy1]]; split; auto; apply orWeaken; auto).
Defined.

Lemma HausdorffBallHausdorffBallStrong : forall (e:Q) (a b:FinEnum),
 ball e a b ->
 hausdorffBallStrong X e (fun x => InFinEnumC x a) (fun x => InFinEnumC x b).
Proof.
 intros e a b [H0 H1].
 split; apply HemiMetricHemiMetricStrong; apply H1.
Defined.

Lemma HemiMetricStrongAlmostDecidableBody :
 forall (e d:Q) a (b : FinEnum),
 e < d ->
 {hemiMetric X d (fun x => st_eq x a) (fun x => InFinEnumC x b)} +
 {~hemiMetric X e (fun x => st_eq x a) (fun x => InFinEnumC x b)}.
Proof.
 intros e d a b.
 induction b.
  intros Hed.
  right.
  abstract ( intros H; apply (H a); try reflexivity; intros x [Hx0 Hx1];
    auto using InFinEnumC_weaken with * ).
 intros Hed.
 destruct (IHb Hed) as [H|H].
  left.
  abstract ( intros x Hx; destruct (H x Hx) as [HG | z [Hz0 Hz1]] using existsC_ind;
    [apply existsC_stable; auto|]; apply existsWeaken; exists z; split; try assumption; apply orWeaken;
      auto).
 destruct (@almostDecideX _ _ a a0 Hed).
 - left.
  intros x Hx; apply existsWeaken; exists a0.
  split. auto using InFinEnumC_weaken with *.
  apply (ball_wd _ eq_refl _ _ Hx _ _ (reflexivity _)).
  auto using InFinEnumC_weaken with *.
 - right.
 intros H0; assert (Haa:st_eq a a) by reflexivity;
   destruct (H0 a Haa) as [HG | z [Hz0 Hz1]] using existsC_ind; [tauto|];
     destruct (Hz0) as [HG | Hz2 | Hz2] using orC_ind.
 tauto.
 apply (ball_wd _ eq_refl _ _ (reflexivity _) _ _ Hz2) in Hz1. 
 contradiction.
 apply H; intros x Hx; apply existsWeaken; exists z.
 split. exact Hz2.
 apply (ball_wd _ eq_refl _ _ Hx _ _ (reflexivity _)). auto.
Defined.

Lemma HemiMetricStrongAlmostDecidable :
 forall (e d:Q) (a b : FinEnum),
 e < d ->
 {hemiMetric X d (fun x => InFinEnumC x a) (fun x => InFinEnumC x b)} +
 {~hemiMetric X e (fun x => InFinEnumC x a) (fun x => InFinEnumC x b)}.
Proof.
 induction a.
  intros a _.
  left.
  intros x Hx _.
  apply Hx.
 intros b Hed.
 destruct (IHa b Hed) as [I|I].
  destruct (@HemiMetricStrongAlmostDecidableBody _ _ a b Hed) as [J|J].
   left.
   abstract ( intros x Hx; destruct (Hx) as [HG | ? | ?] using orC_ind; [auto using existsC_stable
     |apply J; assumption |apply I; assumption]).
  right.
  abstract ( intros H; apply J; intros x Hx; apply H; apply orWeaken; left; assumption).
 right.
 abstract ( intros H; apply I; intros x Hx; apply H; apply orWeaken; right; assumption).
Defined.

(** Finite Enumerations preserve the locatedness property. *)
Lemma FinEnum_located : locatedMetric FinEnum.
Proof.
 intros e d a b Hed.
 destruct (Q.Qle_dec 0 e).
 - destruct (@HemiMetricStrongAlmostDecidable _ _ a b Hed).
   destruct (@HemiMetricStrongAlmostDecidable _ _ b a Hed).
   left. split. apply (Qle_trans _ _ _ q). apply Qlt_le_weak, Hed.
   split; assumption.
   right. intro abs. destruct abs, H0. contradiction.
   right. intro abs. destruct abs, H0. contradiction.
 - right. intro abs. destruct abs. contradiction.
Defined.

(** Finite Enumerations preserve the prelength property assuming X
is a located metric space.

If we change the definition of prelenght space to use a classical
existential, then we could drop the located assumption of X.  I
believe there would be no harm in changing the definition this way,
but it has not been done yet. *)
Hypothesis preLengthX : PrelengthSpace X.

Lemma FinEnum_prelength : PrelengthSpace FinEnum.
Proof.
 intros a b e.
 revert a b.
 cut (forall d1 d2 : Qpos, proj1_sig e < proj1_sig (d1 + d2)%Qpos ->
   forall (a b:FinEnum), hemiMetricStrong X (proj1_sig e) (fun x : X => InFinEnumC x a)
     (fun x : X => InFinEnumC x b) ->
       exists2 c : FinEnum, ball (proj1_sig d1) a c &  hemiMetric X (proj1_sig d2) (fun x : X => InFinEnumC x c) (fun x : X => InFinEnumC x b)).
  intros Z a b d1 d2 He H.
  destruct (HausdorffBallHausdorffBallStrong H) as [Hl Hr].
  clear H.
  destruct (Z _ _ He _ _ Hl) as [c0 Hc0 Hc0c].
  assert (He0: proj1_sig e < proj1_sig (d2 + d1)%Qpos).
   clear - He.
   abstract (simpl; rewrite -> Qplus_comm; assumption).
  destruct (Z _ _ He0 _ _ Hr) as [c1 Hc1 Hc1c].
  clear Z Hl Hr.
  exists (c0 ++ c1).
  split. apply Qpos_nonneg. destruct Hc0 as [_ Hc0].
   abstract ( destruct Hc0 as [Hc0a Hc0b]; destruct Hc1 as [Hc1a Hc1b]; split; intros x Hx;
     [destruct (Hc0a x Hx) as [ G | y [Hya Hyb]] using existsC_ind;
       [auto using existsC_stable | apply existsWeaken; exists y; auto]
         |destruct (InFinEnumC_app_orC _ _ _ Hx) as [G | Hxl | Hxr] using orC_ind;
           [auto using existsC_stable |destruct (Hc0b x Hxl) as [ G | y [Hya Hyb]] using existsC_ind;
             [auto using existsC_stable | apply existsWeaken; exists y; auto]
               |destruct (Hc1c x Hxr) as [ G | y [Hya Hyb]] using existsC_ind;
                 [auto using existsC_stable | apply existsWeaken; exists y; auto]]]).
   split. apply Qpos_nonneg.
   destruct Hc0 as [_ Hc0]. destruct Hc1 as [_ Hc1].
  abstract ( destruct Hc0 as [Hc0a Hc0b]; destruct Hc1 as [Hc1a Hc1b]; split; intros x Hx;
    [destruct (InFinEnumC_app_orC _ _ _ Hx) as [G | Hxl | Hxr] using orC_ind;
      [auto using existsC_stable |destruct (Hc0c x Hxl) as [ G | y [Hya Hyb]] using existsC_ind;
        [auto using existsC_stable | apply existsWeaken; exists y; auto]
          |destruct (Hc1b x Hxr) as [ G | y [Hya Hyb]] using existsC_ind;
            [auto using existsC_stable | apply existsWeaken; exists y; auto]]
              |destruct (Hc1a x Hx) as [ G | y [Hya Hyb]] using existsC_ind;
                [auto using existsC_stable | apply existsWeaken; exists y; auto]]).
 intros d1 d2 He a b H.
 induction a.
  exists nil.
   apply ball_refl. apply Qpos_nonneg.
  intros x Hx; elim Hx.
 destruct IHa as [c1 Hc1a Hc1b].
  abstract ( intros x Hx d; apply (H x); apply orWeaken; right; auto).
 destruct (Qpos_sub _ _ He) as [g Hg].
 pose (exist (Qlt 0) (1#2) eq_refl) as half.
 destruct (fun z => H a z (half*g)%Qpos) as [b0 Hb0].
  abstract (apply orWeaken; left; reflexivity).
 clear H.
 destruct (@preLengthX a b0 (e + half * g)%Qpos d1 d2) as [c Hc0 Hc1].
   abstract ( clear - Hg; unfold QposEq in Hg; rewrite -> Hg; simpl; rewrite -> Qlt_minus_iff; ring_simplify;
     apply (Qpos_ispos ((1#2)*g))).
  abstract (clear - Hb0; destruct Hb0; auto).
 exists (c :: c1).
 - split. apply Qpos_nonneg. split; intros x Hx.
   + destruct Hx as [ G | Hx | Hx ] using orC_ind.
 auto using existsC_stable.
 apply existsWeaken. exists c. split. apply orWeaken. left. reflexivity.
 apply (ball_wd _ eq_refl _ _ Hx _ _ (reflexivity _)). assumption.
 destruct Hc1a as [_ Hc1a].
 destruct Hc1a as [Hc1a _].
 destruct (Hc1a x Hx) as [ G | y [Hy0 Hy1]] using existsC_ind; [auto using existsC_stable|].
 apply existsWeaken; exists y; split; auto; apply orWeaken; right; auto.
   + destruct Hx as [ G | Hx | Hx ] using orC_ind.
     auto using existsC_stable.
     apply existsWeaken; exists a; split. apply orWeaken;left; reflexivity.
     apply (ball_wd _ eq_refl _ _ Hx _ _ (reflexivity _)); auto with *.
     destruct Hc1a as [_ Hc1a].
     destruct Hc1a as [_ Hc1a];
       destruct (Hc1a x Hx) as [ G | y [Hy0 Hy1]] using existsC_ind;
       [auto using existsC_stable|]; apply existsWeaken; exists y; split; auto;
         apply orWeaken; right; auto.
 - destruct Hb0 as [Hb0a Hb0b]; intros x Hx.
   destruct Hx as [ G | Hx | Hx ] using orC_ind.
   auto using existsC_stable.
   apply existsWeaken; exists b0; split; auto.
   apply (ball_wd _ eq_refl _ _ Hx _ _ (reflexivity _)); auto.
   apply Hc1b; auto.
Defined.


End Strong.

End Finite.
(* begin hide *)
Arguments InFinEnumC [X].
(* end hide *)
(** A list is equivalent to it's reverse as finite enumerations *)
Lemma FinEnum_eq_rev : forall X (f:FinEnum X), st_eq f (rev f).
Proof.
 induction f.
  change (st_eq (nil:FinEnum X) (nil:FinEnum X)).
  reflexivity.
 intros x.
 destruct (IHf x) as [H0 H1].
 split; simpl; intros H.
  destruct H as [G|H|H] using orC_ind.
    auto using InFinEnumC_stable.
   apply InFinEnumC_app_r.
   apply orWeaken.
   left; auto.
  apply InFinEnumC_app_l.
  auto.
 destruct (InFinEnumC_app_orC _ _ _ _ H) as [G |A | A] using orC_ind.
   auto using orC_stable.
  apply orWeaken.
  right.
  auto.
 destruct A as [G | A| A] using orC_ind.
   auto using orC_stable.
  apply orWeaken.
  left; auto.
 contradiction.
Qed.

Local Open Scope uc_scope.

(** [map] is compatable with classical in *)
Lemma InFinEnumC_map : forall (X Y:MetricSpace) (f:X --> Y) a l, InFinEnumC a l -> InFinEnumC (f a) (map f l).
Proof.
 induction l.
  auto.
 intros Ha.
 destruct Ha as [G | Ha | Ha] using orC_ind.
   auto using InFinEnumC_stable.
  apply orWeaken.
  left.
  rewrite -> Ha; reflexivity.
 apply orWeaken.
 right.
 apply IHl.
 auto.
Qed.

(** The map function for finite enumerations is uniformly continuous *)
Definition FinEnum_map_modulus (z:Qpos) (muf : Qpos -> QposInf) (e:Qpos) :=
match (muf e) with
| QposInfinity => z
| Qpos2QposInf d => d
end.

(* if a is empty and b is not, then (map f a) and (map f b) are not equivalent,
 even if f is the constant function *)
Lemma FinEnum_map_uc : forall z X Y (f:X --> Y),
    is_UniformlyContinuousFunction (map f:FinEnum X -> FinEnum Y)
                                   (FinEnum_map_modulus z (mu f)).
Proof.
 intros z X Y f e.
 cut (forall (a b : FinEnum X) (d:Qpos),
         (QposInf_le d (mu f e)) ->
         ball (proj1_sig d) a b
         -> ball (m:=FinEnum Y) (proj1_sig e) (map f a) (map f b)).
 { intros Z a b.
  unfold FinEnum_map_modulus.
  case_eq (mu f e).
   intros d Hd H.
   apply Z with d; auto.
   rewrite Hd.
   simpl; auto with *.
  intros He H.
  apply Z with z; auto.
  rewrite He.
  constructor. }
 revert e.
 cut (forall (e d:Qpos), (QposInf_le d (mu f e)) -> forall (s1 s2 : FinEnum X),
   hemiMetric X (proj1_sig d) (fun a => InFinEnumC a s1) (fun a => InFinEnumC a s2) ->
     hemiMetric Y (proj1_sig e) (fun a => InFinEnumC a (map f s1:FinEnum Y)) (fun a => InFinEnumC a (map f s2))).
  intros Z e s1 s2 d Hd [H0 H1].
  split. apply Qpos_nonneg.
  split; apply (Z e d Hd); apply H1.
 intros e d Hd s1 s2.
 intros H a Ha.
 induction s1.
  contradiction.
 destruct Ha as [G | Ha | Ha] using orC_ind.
   auto using existsC_stable.
  assert (Ha0:InFinEnumC a0 (a0::s1)).
   apply orWeaken.
   left; reflexivity.
  destruct (H a0 Ha0) as [G | y [Hy0 Hy1]] using existsC_ind.
   auto using existsC_stable.
  apply existsWeaken.
  exists (f y).
  split.
   apply InFinEnumC_map; assumption.
   apply (ball_wd _ eq_refl _ _ Ha _ _ (reflexivity _)).
  apply (uc_prf f).
  apply ball_ex_weak_le with d; auto.
 apply IHs1; auto.
 intros b Hb.
 apply H.
 apply orWeaken.
 right; assumption.
Qed.
(* begin hide *)
Arguments FinEnum_map_uc z [X Y].
(* end hide *)
Definition FinEnum_map z X Y (f:X --> Y) :=
 Build_UniformlyContinuousFunction (FinEnum_map_uc z f).

(** maping [Cunit] is an injection from FinEnum X to FinEnum Complete X that
preserves the metric *)
Lemma FinEnum_map_Cunit : forall X (s1 s2:FinEnum X) (e:Qpos),
    ball (proj1_sig e) s1 s2 <-> ball (proj1_sig e) (map Cunit s1:FinEnum (Complete X)) (map Cunit s2).
Proof.
 intros X s1 s2 e.
 split.
 - intros H.
   exact (@FinEnum_map_uc (1 # 1) _ _ Cunit e s1 s2 H).
 - revert s1 s2.
 cut (forall (s1 s2 : FinEnum X) ,
   hemiMetric (Complete X) (proj1_sig e) (fun a => InFinEnumC a (map Cunit s1:FinEnum (Complete X)))
     (fun a => InFinEnumC a (map Cunit s2)) ->
       hemiMetric X (proj1_sig e) (fun a => InFinEnumC a s1) (fun a => InFinEnumC a s2)).
  intros Z s1 s2.
  intros [epos [H0 H1]].
  split. exact epos.
  split; apply Z; assumption.
 intros s1 s2 H a Ha.
 induction s1.
  contradiction.
 destruct Ha as [G | Ha | Ha] using orC_ind.
   auto using existsC_stable.
  clear IHs1.
  assert (Ha0:InFinEnumC (Cunit a0) (map Cunit (a0::s1))).
   apply orWeaken.
   left; reflexivity.
  destruct (H _ Ha0) as [G | y [Hy0 Hy1]] using existsC_ind.
   auto using existsC_stable.
  clear - Ha Hy0 Hy1.
  induction s2.
   contradiction.
  destruct Hy0 as [G | Hy0 | Hy0] using orC_ind.
    auto using existsC_stable.
   apply existsWeaken.
   exists a1.
   split.
    apply orWeaken.
    left; reflexivity.
    apply (ball_wd _ eq_refl _ _ Ha _ _ (reflexivity _)). 
   rewrite <- ball_Cunit.
   apply (ball_wd _ eq_refl _ _ (reflexivity _) _ _ Hy0). 
   assumption.
  destruct (IHs2 Hy0) as [G | z [Hz0 Hz1]] using existsC_ind.
   auto using existsC_stable.
  apply existsWeaken.
  exists z.
  split; auto.
  apply orWeaken.
  right; assumption.
 apply IHs1; auto.
 intros b Hb.
 apply H.
 apply orWeaken.
 right; assumption.
Qed.
