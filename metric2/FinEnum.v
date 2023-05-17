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

(** [FinSubset_ball] says that the distance between x and l is <= e.
    It is stated as a negation, to remind that a <= b means
    ~(b < a) in the real numbers.
    As shown by lemma AlmostInExists, the double negation can
    be removed, at the cost of slightly increasing e. *)
Definition FinSubset_ball (e:Q) (x:X) (l:list X) : Prop :=
  ~~ exists y:X, In y l /\ ball e x y.

Definition InFinEnumC (x:X) (l:list X) : Prop
  := FinSubset_ball 0 x l.

Lemma InFinEnumC_weaken : forall x l, In x l -> InFinEnumC x l.
Proof.
  intros. intro abs.
  contradict abs.
  exists x. split. exact H. apply ball_refl.
  apply Qle_refl.
Qed.

Lemma FinSubset_ball_nil : forall e x, ~FinSubset_ball e x nil.
Proof.
 intros e x H.
 unfold FinSubset_ball in H.
 contradict H; intros [y [H _]].
 contradiction.
Qed.

Lemma FinSubset_ball_cons : forall x e a l,
    FinSubset_ball e x l -> FinSubset_ball e x (a :: l).
Proof.
  intros. intro abs. unfold FinSubset_ball in H.
  contradict H; intros [z [H0 H1]].
  contradict abs. exists z. split.
  right. exact H0. exact H1.
Qed.

Lemma FinSubset_ball_orC : forall e x a l,
    FinSubset_ball e x (a :: l) -> orC (ball e x a) (FinSubset_ball e x l).
Proof.
  intros. intro abs.
  unfold FinSubset_ball in H.
  contradict H; intros [y [H H0]].
  destruct H.
  - subst y. destruct abs. contradiction.
  - destruct abs. contradict H2.
    intro abs; contradict abs.
    exists y. split; assumption.
Qed.

Lemma FinSubset_ball_wd : forall x y d e l,
    d == e -> msp_eq x y -> (FinSubset_ball d x l <-> FinSubset_ball e y l).
Proof.
  split.
  - intros H1 abs.
    unfold FinSubset_ball in H1.
    contradict H1; intros [z [H1 H2]].
    contradict abs. exists z. split.
    exact H1. rewrite <- H, <- H0. exact H2.
  - intros H1 abs. 
    unfold FinSubset_ball in H1.
    contradict H1; intros [z [H1 H2]].
    contradict abs. exists z. split.
    exact H1. rewrite H, H0. exact H2.
Qed.

Lemma FinSubset_ball_weak_le : forall (e1 e2:Q) x l,
    e1 <= e2 -> FinSubset_ball e1 x l
    -> FinSubset_ball e2 x l.
Proof.
  intros. intro abs.
  unfold FinSubset_ball in H0.
  contradict H0; intros [y [iny H0]].
  contradict abs. exists y. split.
  exact iny. 
  apply (ball_weak_le X x y H), H0.
Qed.

Lemma FinSubset_ball_nonneg : forall (e:Q) x l,
    FinSubset_ball e x l -> 0 <= e.
Proof.
  intros. apply Qnot_lt_le. intro abs.
  unfold FinSubset_ball in H.
  contradict H; intros [y [_ H]].
  apply (Qlt_not_le _ _ abs).
  apply (msp_nonneg (msp X) e x y H).
Qed.

Lemma FinSubset_ball_closed : forall (e:Q) x l,
    (forall d:Q, 0 < d -> FinSubset_ball (e+d) x l) -> FinSubset_ball e x l.
Proof.
 induction l.
 - intros H. exfalso. exact (FinSubset_ball_nil (H (1#1) eq_refl)).
 - intros H abs.
   assert (~ball e x a) as A.
   { intro H0. contradict abs. exists a.
     split. left. reflexivity. exact H0. }
   assert (~ (exists y : X, In y l /\ ball e x y)) as B.
   { intros [y H1]. contradict abs. exists y.
     split. right. apply H1. apply H1. }
   clear abs.
   revert B.
   apply IHl. clear IHl.
   intros d dpos.
   (* Improve A *)
   assert (existsC Qpos (fun d => ~ball (e+proj1_sig d) x a)) as Aprime.
   { intros Y.
     apply A.
     apply ball_closed.
     intros d0 d0pos.
     apply (msp_stable (msp X)).
     apply (Y (exist _ _ d0pos)). }
   clear A.
   destruct Aprime as [G | d0 Hd0] using existsC_ind.
   intro abs; contradict G; intro G; contradiction.
 intros Z.
 destruct (Qlt_le_dec (proj1_sig d0) d).
 + revert Z.
  apply (@FinSubset_ball_weak_le (e + proj1_sig d0)).
   apply Qlt_le_weak.
   rewrite -> Qlt_minus_iff in *.
   setoid_replace (e + d + - (e + proj1_sig d0))
     with (d + - proj1_sig d0) by (simpl; ring).
   assumption.
  intros Y.
  destruct d0 as [d0 d0pos].
  apply (H d0 d0pos).
  intros [y abs].
  contradict Y. exists y.
  simpl.
  split. 2: apply abs.
  destruct abs. destruct H0.
  2: exact H0. subst y. contradiction.
 + specialize (H d dpos).
   unfold FinSubset_ball in H.
   contradict H; intros [y [iny H]].
   destruct iny. subst y.
   contradict Hd0.
   apply (@ball_weak_le X (e + d)).
   rewrite -> Qle_minus_iff in *.
   setoid_replace (e + proj1_sig d0 + - (e + d))
     with (proj1_sig d0 + - d) by (simpl; ring).
   assumption. exact H.
   contradict Z. exists y.
   split. exact H0. exact H.
Qed.

(** Left and right triangle laws for balls and [FinSubset_ball]. *)
Lemma FinSubset_ball_triangle_l : forall e1 e2 x1 x2 l,
    (ball e1 x1 x2) -> FinSubset_ball e2 x2 l -> FinSubset_ball (e1 + e2) x1 l.
Proof.
  intros. intro abs.
  unfold FinSubset_ball in H0.
  contradict H0; intros [y H0].
  contradict abs. exists y. split.
  apply H0.
  eapply ball_triangle.
   apply H.
  apply H0.
Qed.

Lemma FinSubset_ball_app_l : forall e x l1 l2,
    FinSubset_ball e x l1 -> FinSubset_ball e x (l1 ++ l2).
Proof.
 intros e x l1 l2 H abs.
 unfold FinSubset_ball in H.
 contradict H; intros [y H].
 contradict abs. exists y. split.
 apply in_app_iff. left.
 apply H. apply H.
Qed.

Lemma FinSubset_ball_app_r : forall e x l1 l2,
    FinSubset_ball e x l2 -> FinSubset_ball e x (l1 ++ l2).
Proof.
 intros e x l1 l2 H abs.
 unfold FinSubset_ball in H.
 contradict H; intros [y H].
 contradict abs. exists y. split.
 apply in_app_iff. right.
 apply H. apply H.
Qed.
(* begin hide *)
Hint Resolve FinSubset_ball_app_l FinSubset_ball_app_r.
(* end hide *)
Lemma FinSubset_ball_app_orC : forall e x l1 l2,
    FinSubset_ball e x (l1 ++ l2)
    -> orC (FinSubset_ball e x l1) (FinSubset_ball e x l2).
Proof.
 intros e x l1 l2 H [H0 H1].
 unfold FinSubset_ball in H.
 contradict H; intros [y [H H2]].
 apply in_app_iff in H. destruct H.
 contradict H0. intro abs.
 contradict abs. exists y.
 split; assumption.
 contradict H1. intro abs.
 contradict abs. exists y.
 split; assumption.
Qed.

(**
** Equivalence
Two finite enumerations, represented as lists, are equivalent
if they (classically) have the same elements.
*)
Definition FinEnum_eq (a b:list X) : Prop :=
 forall x, InFinEnumC x a <-> InFinEnumC x b.

(**
** Metric Space
Finite enumerations form a metric space under the Hausdorff metric for
any stable metric space X.
*)
Definition FinEnum_ball (e:Q) (x y:list X) :=
 hausdorffBall X e (fun a => InFinEnumC a x) (fun a => InFinEnumC a y).

Lemma FinEnum_ball_e_wd : forall (e1 e2:Q) (a b : list X), (e1 == e2) ->
 (FinEnum_ball e1 a b <-> FinEnum_ball e2 a b).
Proof.
 intros e1 e2 a b He.
 apply hausdorffBall_wd; auto with *.
Qed.

Lemma hemiMetric_closed : forall e A b,
 (forall d, 0 < d -> hemiMetric X (e+d) A (fun a => InFinEnumC a b)) ->
  hemiMetric X e A (fun a => InFinEnumC a b).
Proof.
 intros e A b H x Hx.
 pose (fun n y => ball (e + (1#(P_of_succ_nat n))%Q) x y) as P.
 assert (forall n, existsC X (fun x => ~~In x b /\ P n x)) as HP.
 { intros n.
   unfold P.
   destruct (H (1#(P_of_succ_nat n))%Q eq_refl x Hx)
     as [HG | y [Hy0 Hy1]] using existsC_ind.
   apply existsC_stable; auto.
   clear - Hy0 Hy1.
   intro abs.
   unfold InFinEnumC, FinSubset_ball in Hy0.
   contradict Hy0; intros [y0 [Hy0 yeq]].
   specialize (abs y0).
   contradict abs. split.
   intro abs. contradiction.
   rewrite <- yeq. exact Hy1. }
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
 apply (Nat.le_trans _ _ _ Hmd).
 rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
 apply le_S, Nat.le_refl.
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
 { unfold hausdorffBall.
  split; apply H; firstorder. }
 induction a.
 intros. exfalso.
 unfold InFinEnumC, FinSubset_ball in H0.
 contradict H0; intros [y [H0 _]].
 contradiction. 
 intros b H x Hx.

 intro abs. unfold InFinEnumC, FinSubset_ball in Hx.
 contradict Hx; intros [y [iny Hx]].
 destruct iny.
 - subst y.
  assert (H':forall n :nat ,
             existsC X (fun y : X => InFinEnumC y b
                                  /\ ball (m:=X) (1#(P_of_succ_nat n)) x y)).
  { intros e.
    apply (H (exist (Qlt 0) (1#(P_of_succ_nat e)) eq_refl)).
    intro H0. contradict H0.
    exists a. split. left. reflexivity. exact Hx. }
  assert (H'':forall n :nat ,
             existsC X (fun y : X => ~~In y b
                                  /\ ball (m:=X) (1#(P_of_succ_nat n)) x y)).
  { intros n.
   destruct (H' n) as [HG | z [Hz0 Hz1]] using existsC_ind.
    auto using existsC_stable.
   clear - Hz1 Hz0.
   intro abs. unfold InFinEnumC, FinSubset_ball in Hz0.
   contradict Hz0; intros [y [iny Hz0]].
   specialize (abs y).
   contradict abs. split.
   intro abs. contradiction.
   rewrite <- Hz0. exact Hz1. }
   destruct (infinitePidgeonHolePrinicple _ _ _ H'')
     as [HG | y [Hy0 Hy1]] using existsC_ind.
  contradict HG. intro HG. contradiction.
  revert abs. change (FinSubset_ball 0 x b).
  rewrite -> (FinSubset_ball_wd x y).
  2: reflexivity.
  apply InFinEnumC_weaken, Hy0.
  apply ball_eq.
  intros [n d] dpos.
  destruct n. inversion dpos. 2: inversion dpos.
  replace d with (Pos.of_succ_nat (Init.Nat.pred (Pos.to_nat d))).
  destruct (Hy1 (pred (nat_of_P d))) as [HG | z [Hz0 Hz1]] using existsC_ind.
  apply (msp_stable (msp X) (Zpos p # Pos.of_succ_nat (Init.Nat.pred (Pos.to_nat d)))). auto.
  apply ball_weak_le with (1 # P_of_succ_nat z); auto.
  simpl.
  apply Zmult_le_compat; [..|auto with *].
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
  apply (Nat.lt_succ_pred O _).
  apply Pos2Nat.is_pos.
 - revert abs. apply IHa.
   intros e y0 Hy.
   apply H. intro abs.
   unfold InFinEnumC, FinSubset_ball in Hy.
   contradict Hy; intros [y1 Hy].
   contradict abs.
   exists y1. split.
   right. apply Hy.
   apply Hy.
   intro abs; contradict abs.
   exists y. split; assumption.
Qed.

Lemma FinEnum_is_MetricSpace : is_MetricSpace FinEnum_ball.
Proof.
 split.
 - intros e epos x. apply hausdorffBall_refl, epos.
 - intros e x y. apply hausdorffBall_sym.
 - intros e d x y z. apply hausdorffBall_triangle.
 - intros e x y. unfold FinEnum_ball.
   apply FinEnum_ball_closed.
 - intros. apply H.
 - intros e x y.
   apply hausdorffBall_stable.
Qed.

Definition FinEnum : MetricSpace :=
Build_MetricSpace FinEnum_ball_e_wd FinEnum_is_MetricSpace.

Lemma FinEnum_eq_equiv : forall (x y : FinEnum),
    FinEnum_eq x y <-> msp_eq x y.
Proof.
  unfold FinEnum_eq, msp_eq. split.
  - intros. split. apply Qle_refl. split.
    intros z H0. rewrite H in H0.
    intro abs. apply (abs z).
    split. exact H0. reflexivity.
    intros z H0. rewrite <- H in H0.
    intro abs. apply (abs z).
    split. exact H0. reflexivity.
  - split. 
    + intros z H0. 
      destruct H as [_ [H1 _]].
      specialize (H1 x0 z). clear z.
      unfold existsC in H1.
      contradict H1; intros x1 [H1 H2]. 
      unfold InFinEnumC, FinSubset_ball in H1.
      contradict H1; intros [t H1].
      contradict H0. exists t. split.
      apply H1. rewrite H2. apply H1.
    + intros z H0. 
      destruct H as [_ [_ H1]].
      specialize (H1 x0 z). clear z.
      unfold existsC in H1.
      contradict H1; intros x1 [H1 H2]. 
      unfold InFinEnumC, FinSubset_ball in H1.
      contradict H1; intros [t H1].
      contradict H0. exists t. split.
      apply H1. rewrite H2. apply H1.
Qed.

Lemma FinSubset_ball_triangle_r : forall e1 e2 x (l1 l2 : FinEnum),
    FinSubset_ball e1 x l1 -> (ball e2 l1 l2) -> FinSubset_ball (e1 + e2) x l2.
Proof.
 intros e1 e2 x l1 l2 H1 [epos [H2 _]].
 revert l2 H1 H2.
 induction l1; intros l2 H1 H2.
 exfalso; exact (FinSubset_ball_nil H1).
 unfold hemiMetric in *.
 apply FinSubset_ball_orC in H1.
 destruct H1 as [G | H1 | H1] using orC_ind.
 intro abs; contradict G; intro G; contradiction.
  assert (Z:InFinEnumC a (a :: l1)).
  { intro abs; contradict abs.
    exists a. split. left; reflexivity. reflexivity. }
  destruct (H2 a Z) as [ G | z [Hz0 Hz1]] using existsC_ind.
 intro abs; contradict G; intro G; contradiction.
  clear - H1 Hz0 Hz1.
  apply FinSubset_ball_closed.
  intros d dpos.
  apply FinSubset_ball_triangle_l with z.
   apply ball_triangle with a; assumption.
   apply FinSubset_ball_weak_le with (e1:=0).
   apply Qlt_le_weak, dpos. exact Hz0.
 apply IHl1.
  assumption.
 intros y Hy.
 apply H2.
 apply FinSubset_ball_cons.
 exact Hy.
Qed.

Lemma FinEum_map_ball : forall (f:X -> X) (e:Qpos) (s:FinEnum),
 (forall x, ball (proj1_sig e) x (f x)) -> ball (proj1_sig e) s (map f s).
Proof.
 intros f e s H.
 induction s. split. apply Qpos_nonneg.
 - split; intros a b abs; apply (FinSubset_ball_nil b).
 - destruct IHs as [IHs0 IHs1].
   split. apply Qpos_nonneg.
   split; intros x y abs; unfold InFinEnumC, FinSubset_ball in y; contradict y
   ; intros [y [iny H0]].
   destruct iny.
   + subst y.
     specialize (abs (f a)). contradict abs.
     split.
     apply InFinEnumC_weaken.
     left. reflexivity.
     rewrite H0. apply H.
   + destruct IHs1 as [IHs1 _].
     pose proof (@FinSubset_ball_wd x y 0 0 s eq_refl H0) as [_ H2].
     specialize (IHs1 x (H2 (InFinEnumC_weaken y s H1))).
     unfold existsC in IHs1. contradict IHs1.
     intros z [H3 H4].
     specialize (abs z). contradict abs.
     split. 2: exact H4. simpl.
     apply FinSubset_ball_cons.
     exact H3.
   + destruct iny. subst y.
     specialize (abs a). contradict abs.
     split. apply InFinEnumC_weaken. left. reflexivity.
     rewrite H0. apply ball_sym, H. 
     destruct IHs1 as [_ IHs1]. 
     pose proof (@FinSubset_ball_wd x y 0 0 (map f s) eq_refl H0) as [_ H2].
     specialize (IHs1 x (H2 (InFinEnumC_weaken y _ H1))).
     unfold existsC in IHs1. contradict IHs1.
     intros z [H3 H4].
     specialize (abs z). contradict abs.
     split. 2: exact H4. simpl.
     apply FinSubset_ball_cons.
     exact H3.
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
 - abstract (unfold existsC in H; contradict H;
             intros y [H _]; exact (FinSubset_ball_nil H)).
 - destruct (@almostDecideX e (e + proj1_sig d) x a).
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
   split. 2: exact Hy1.
   apply FinSubset_ball_orC in Hy0.
   destruct Hy0 as [HG | Hy | Hy] using orC_ind.
   intro abs. contradict HG; intro HG; contradiction.
   2: assumption.
   apply (ball_wd _ eq_refl _ _ (reflexivity _) _ _ Hy) in Hy1. 
   contradiction. }
 exists (let (y,_) := (IHb x Hx Z d) in y).
 clear - IHb.
 abstract (destruct (IHb x Hx Z d) as [y [Hy0 Hy1]]; split; auto;
           apply FinSubset_ball_cons, Hy0).
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
 {hemiMetric X d (fun x => msp_eq x a) (fun x => InFinEnumC x b)} +
 {~hemiMetric X e (fun x => msp_eq x a) (fun x => InFinEnumC x b)}.
Proof.
  intros e d a b.
  induction b.
  - intros Hed.
    right.
    abstract (intros H; apply (H a); try reflexivity;
              intros x [Hx0 Hx1]; exact (FinSubset_ball_nil Hx0)).
  - intros Hed.
    destruct (IHb Hed) as [H|H].
    left.
    abstract (intros x Hx; destruct (H x Hx) as [HG | z [Hz0 Hz1]] using existsC_ind;
              [apply existsC_stable; auto|]; apply existsWeaken; exists z; split;
              try assumption;
              apply FinSubset_ball_cons, Hz0).
    destruct (@almostDecideX _ _ a a0 Hed).
    + left.
      intros x Hx; apply existsWeaken; exists a0.
      split. auto using InFinEnumC_weaken with *.
      apply (ball_wd _ eq_refl _ _ Hx _ _ (reflexivity _)).
      auto using InFinEnumC_weaken with *.
    + right.
      intros H0; assert (Haa:msp_eq a a) by reflexivity;
        destruct (H0 a Haa) as [HG | z [Hz0 Hz1]] using existsC_ind; [tauto|].
      apply FinSubset_ball_orC in Hz0.
      destruct Hz0 as [HG | Hz2 | Hz2] using orC_ind.
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
  exact (FinSubset_ball_nil Hx).
 intros b Hed.
 destruct (IHa b Hed) as [I|I].
  destruct (@HemiMetricStrongAlmostDecidableBody _ _ a b Hed) as [J|J].
   left.
   abstract ( intros x Hx; apply FinSubset_ball_orC in Hx;
              destruct Hx as [HG | ? | ?] using orC_ind;
              [auto using existsC_stable
     |apply J; assumption |apply I; assumption]).
  right.
  abstract (intros H; apply J; intros x Hx; apply H;
            intro abs; contradict abs; exists a; split; [left; reflexivity | apply Hx]).
 right.
  abstract (intros H; apply I; intros x Hx; apply H;
            apply FinSubset_ball_cons, Hx).
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
       [auto using existsC_stable | apply existsWeaken; exists y; unfold InFinEnumC; auto]
         |destruct (@FinSubset_ball_app_orC _ _ _ _ Hx) as [G | Hxl | Hxr] using orC_ind;
           [auto using existsC_stable |destruct (Hc0b x Hxl) as [ G | y [Hya Hyb]] using existsC_ind;
             [auto using existsC_stable | apply existsWeaken; exists y; auto]
               |destruct (Hc1c x Hxr) as [ G | y [Hya Hyb]] using existsC_ind;
                 [auto using existsC_stable | apply existsWeaken; exists y; auto]]]). 
   split. apply Qpos_nonneg.
   destruct Hc0 as [_ Hc0]. destruct Hc1 as [_ Hc1].
  abstract ( destruct Hc0 as [Hc0a Hc0b]; destruct Hc1 as [Hc1a Hc1b]; split; intros x Hx;
    [destruct (@FinSubset_ball_app_orC _ _ _ _ Hx) as [G | Hxl | Hxr] using orC_ind;
      [auto using existsC_stable |destruct (Hc0c x Hxl) as [ G | y [Hya Hyb]] using existsC_ind;
        [auto using existsC_stable | apply existsWeaken; exists y; auto]
          |destruct (Hc1b x Hxr) as [ G | y [Hya Hyb]] using existsC_ind;
            [auto using existsC_stable | apply existsWeaken; exists y; auto]]
              |destruct (Hc1a x Hx) as [ G | y [Hya Hyb]] using existsC_ind;
                [auto using existsC_stable | apply existsWeaken; exists y; unfold InFinEnumC; auto]]).
 intros d1 d2 He a b H.
 induction a.
  exists nil.
   apply ball_refl. apply Qpos_nonneg.
  intros x Hx; exfalso; exact (FinSubset_ball_nil Hx).
 destruct IHa as [c1 Hc1a Hc1b].
 abstract (intros x Hx d; apply (H x); apply FinSubset_ball_cons, Hx).
 destruct (Qpos_sub _ _ He) as [g Hg].
 pose (exist (Qlt 0) (1#2) eq_refl) as half.
 destruct (fun z => H a z (half*g)%Qpos) as [b0 Hb0].
 abstract (intro abs; contradict abs; exists a; split;
           [left; reflexivity | reflexivity]).
 clear H.
 destruct (@preLengthX a b0 (e + half * g)%Qpos d1 d2) as [c Hc0 Hc1].
   abstract ( clear - Hg; unfold QposEq in Hg; rewrite -> Hg; simpl; rewrite -> Qlt_minus_iff; ring_simplify;
     apply (Qpos_ispos ((1#2)*g))).
  abstract (clear - Hb0; destruct Hb0; auto).
 exists (c :: c1).
 - split. apply Qpos_nonneg. split; intros x Hx.
   + apply FinSubset_ball_orC in Hx.
     destruct Hx as [ G | Hx | Hx ] using orC_ind.
     auto using existsC_stable.
     apply existsWeaken. exists c. split.
     intro abs; contradict abs; exists c; split; [left; reflexivity | reflexivity].
     rewrite Hx. assumption.
     destruct Hc1a as [_ Hc1a].
     destruct Hc1a as [Hc1a _].
     destruct (Hc1a x Hx) as [ G | y [Hy0 Hy1]] using existsC_ind;
       [auto using existsC_stable|].
     apply existsWeaken; exists y; split; auto.
     apply FinSubset_ball_cons. exact Hy0.
   + apply FinSubset_ball_orC in Hx.
     destruct Hx as [ G | Hx | Hx ] using orC_ind.
     auto using existsC_stable.
     apply existsWeaken; exists a; split.
     intro abs; contradict abs; exists a; split; [left; reflexivity | reflexivity].
     apply (ball_wd _ eq_refl _ _ Hx _ _ (reflexivity _)); auto with *.
     destruct Hc1a as [_ Hc1a].
     destruct Hc1a as [_ Hc1a];
       destruct (Hc1a x Hx) as [ G | y [Hy0 Hy1]] using existsC_ind;
       [auto using existsC_stable|]; apply existsWeaken; exists y; split; auto.
     apply (@FinSubset_ball_cons y). exact Hy0.
 - destruct Hb0 as [Hb0a Hb0b]; intros x Hx.
   apply FinSubset_ball_orC in Hx.
   destruct Hx as [ G | Hx | Hx ] using orC_ind.
   auto using existsC_stable.
   apply existsWeaken; exists b0; split; auto.
   apply (ball_wd _ eq_refl _ _ Hx _ _ (reflexivity _)); auto.
   apply Hc1b; auto.
Defined.


End Strong.

End Finite.

(* begin hide *)
Add Parametric Morphism {X : MetricSpace} : (FinSubset_ball X)
    with signature Qeq ==> (@msp_eq _) ==> (@msp_eq (FinEnum X)) ==> iff
      as FinSubset_ball_wd_full.
Proof.
 unfold FinEnum_eq.
 assert (Y:forall x1 x2 : Q, x1 == x2 -> forall y1 y2 : X,
              msp_eq y1 y2 ->forall z : FinEnum X,
                (FinSubset_ball _ x1 y1 z
                 -> FinSubset_ball _ x2 y2 z)).
  { intros x1 x2 Hx y1 y2 Hy.
  induction z.
  intros. exfalso; exact (FinSubset_ball_nil H).
  intros H.
  apply FinSubset_ball_orC in H.
  destruct H as [G | H | H] using orC_ind.
  intro abs; contradict G; intro G; contradiction.
  intro abs; contradict abs.
  exists a. split. left. reflexivity.
   unfold QposEq in Hx. rewrite <- Hx, <- Hy.
   assumption.
   apply FinSubset_ball_cons.
  apply IHz; assumption. }
 intros x1 x2 Hx y1 y2 Hy.
 cut (forall z1 x3 : FinEnum X, (forall x : X, InFinEnumC _ x z1 -> InFinEnumC _ x x3) ->
   (FinSubset_ball _ x1 y1 z1 -> FinSubset_ball _ x2 y2 x3)).
  { intros Z z1 z2 Hz.
  split.
   apply Z.
   intros x H.
   simpl in Hz.
   apply FinEnum_eq_equiv in Hz.
   rewrite <- (Hz x).
   exact H.
  intros H.
  eapply Y.
    unfold QposEq.
    simpl; symmetry.
    apply Hx.
   symmetry.
   apply Hy.
  eapply Z.
   intros a Ha.
   apply FinEnum_eq_equiv in Hz.
   apply <- (Hz a).
   apply Ha.
  eapply Y.
    unfold QposEq.
    simpl; symmetry.
    apply Hx.
   symmetry.
   apply Hy.
  assumption. }
 induction z1; intros z2 Hz.
  intro abs; exfalso; exact (FinSubset_ball_nil abs).
 intros H.
 apply FinSubset_ball_orC in H.
 destruct H as [G | H | H] using orC_ind.
 intro abs; contradict G; intro G; contradiction.
  assert (Z:InFinEnumC _ a z2).
   apply Hz.
   intro abs; contradict abs.
   exists a. split. left; reflexivity. reflexivity.
  rewrite -> Hx, Hy in H.
  clear - H Z.
  induction z2.
  exfalso; exact (FinSubset_ball_nil Z).
  apply FinSubset_ball_orC in Z.
  destruct Z as [G | Z | Z] using orC_ind.
 intro abs; contradict G; intro G; contradiction.
   rewrite -> Z in H.
   intro abs; contradict abs.
   exists a0. split. left. reflexivity. exact H.
   apply FinSubset_ball_cons.
  apply IHz2; auto.
 apply IHz1.
  intros b Hb.
  apply Hz.
  apply FinSubset_ball_cons.
  exact Hb. exact H.
Qed.

(* begin hide *)
Arguments InFinEnumC [X].
Arguments FinSubset_ball [X].
(* end hide *)
(** A list is equivalent to it's reverse as finite enumerations *)
Lemma FinEnum_eq_rev : forall X (f:FinEnum X), msp_eq f (rev f).
Proof.
  intros. apply FinEnum_eq_equiv.
  split.
  - intros H abs. unfold InFinEnumC, FinSubset_ball in H.
    contradict H; intros [y H].
    contradict abs. exists y. split.
    rewrite <- in_rev. apply H. apply H.
  - intros H abs. unfold InFinEnumC, FinSubset_ball in H.
    contradict H; intros [y H].
    contradict abs. exists y. split.
    rewrite in_rev. apply H. apply H.
Qed.

Local Open Scope uc_scope.

(** [map] is comparable with classical in.
    A proper f with respect to the setoid equivalences would be enough. *)
Lemma InFinEnumC_map : forall (X Y:MetricSpace) (f:X --> Y) a l,
    InFinEnumC a l -> InFinEnumC (f a) (map f l).
Proof.
  intros. intro abs.
  unfold InFinEnumC, FinSubset_ball in H.
  contradict H; intros [y [H H0]].
  contradict abs. exists (f y). split.
  apply in_map. exact H.
  rewrite H0. reflexivity.
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
  { intros Z e s1 s2 d Hd [H0 H1].
  split. apply Qpos_nonneg.
  split; apply (Z e d Hd); apply H1. }
 intros e d Hd s1 s2.
 intros H a Ha.
 induction s1.
  exfalso; exact (FinSubset_ball_nil Ha).
  apply FinSubset_ball_orC in Ha.
 destruct Ha as [G | Ha | Ha] using orC_ind.
   auto using existsC_stable.
  assert (Ha0:InFinEnumC a0 (a0::s1)).
  intro abs; contradict abs. exists a0.
  split. left. reflexivity. reflexivity.
  destruct (H a0 Ha0) as [G | y [Hy0 Hy1]] using existsC_ind.
   auto using existsC_stable.
  apply existsWeaken.
  exists (f y).
  split.
   apply InFinEnumC_map; assumption.
   rewrite Ha.
  apply (uc_prf f).
  apply ball_ex_weak_le with d; auto.
 apply IHs1; auto.
 intros b Hb.
 apply H.
 apply (@FinSubset_ball_cons _ b).
 exact Hb.
Qed.
(* begin hide *)
Arguments FinEnum_map_uc z [X Y].
(* end hide *)

Definition FinEnum_map z (X Y : MetricSpace) (f:X --> Y) : FinEnum X --> FinEnum Y
  := Build_UniformlyContinuousFunction (FinEnum_map_uc z f).

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
  { intros Z s1 s2.
  intros [epos [H0 H1]].
  split. exact epos.
  split; apply Z; assumption. }
 intros s1 s2 H a Ha.
 induction s1.
 exfalso; exact (FinSubset_ball_nil Ha).
 apply FinSubset_ball_orC in Ha.
 destruct Ha as [G | Ha | Ha] using orC_ind.
   auto using existsC_stable.
  clear IHs1.
  assert (Ha0:InFinEnumC (Cunit a0) (map Cunit (a0::s1))).
  intro abs; contradict abs.
  exists (Cunit a0). split.
  left; reflexivity. reflexivity.
  destruct (H _ Ha0) as [G | y [Hy0 Hy1]] using existsC_ind.
   auto using existsC_stable.
  clear - Ha Hy0 Hy1.
  induction s2.
  exfalso; exact (FinSubset_ball_nil Hy0).
  apply FinSubset_ball_orC in Hy0.
  destruct Hy0 as [G | Hy0 | Hy0] using orC_ind.
    auto using existsC_stable.
   apply existsWeaken.
   exists a1.
   split.
  intro abs; contradict abs.
  exists a1. split.
  left; reflexivity. reflexivity.
  rewrite Ha.
  rewrite <- ball_Cunit.
  rewrite <- Hy0.
  assumption.
  destruct (IHs2 Hy0) as [G | z [Hz0 Hz1]] using existsC_ind.
   auto using existsC_stable.
  apply existsWeaken.
  exists z.
  split; auto.
  apply FinSubset_ball_cons.
  exact Hz0.
 apply IHs1; auto.
 intros b Hb.
 apply H.
 apply FinSubset_ball_cons.
 exact Hb.
Qed.
