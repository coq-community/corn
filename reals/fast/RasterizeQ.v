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
Require Export CoRN.reals.fast.RasterQ.
Require Import CoRN.reals.fast.Interval.
Require Import CoRN.logic.Classic.
Require Import CoRN.model.totalorder.QposMinMax.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qround.
Require Import Omega.

Local Open Scope Q_scope.

Set Implicit Arguments.

(**
** Rasterization
Rasterization takes finite enumeration of points in [Q2] and moves them
around a little so that they lie on a raster.  Thus rasterization produces
a raster object that when interpreted as a finite enumeration of [Q2] is
close to the original enumeration of points.  How close depends on how
fine a raster is chosen.

There is a choice as to how to treat points that lie outside of the bound
of a chosen rectangle for rasterization.  In this implemenation I choose
to push all points inside the raster.  In typical applications a rectangle
is chosen that contains all the points, so that this doesn't matter. *)

(* [Rasterize Point] adds a single point [p] into a raster.
The raster is inside the rectanle t l b r, meaning top, left, bottom and right.
It has n points horizontally and m points vertically. The indexes (0,0)
correspond to the point (l,t) ie the top left corner. That yields the correct
printing order of the raster, which is a vector of lines. *)
Definition rasterize2 (n m:positive) (t l b r:Q) (p:Q*Q) : prod Z Z
  := pair (Z.min (Zpos n -1) (Z.max 0 (rasterize1 l r n (fst p))))
          (Zpos m -1 - (Z.min (Zpos m -1) (Z.max 0 (rasterize1 b t m (snd p)))))%Z.
           
Definition RasterizePoint n m (bm:raster) (t l b r:Q) (p:Q*Q)
  : raster :=
  let (i,j) := rasterize2 n m t l b r p in
  setRaster bm true (Z.to_nat j) (Z.to_nat i).

Lemma rasterize2_bound :
  forall n z, (0 <= Z.min (Zpos n -1) (Z.max 0 z) < Zpos n)%Z.
Proof.
  split.
  - apply Z.min_case.
    apply Z.le_0_sub, Pos.le_1_l.
    apply Z.le_max_l.
  - apply (Z.le_lt_trans _ _ _ (Z.le_min_l _ _)).
    rewrite <- (Z.add_0_r (Z.pos n)) at 2.
    apply Z.add_lt_mono_l. reflexivity.
Qed. 

Lemma rasterize1_origin : forall l r n, rasterize1 l r n l = 0%Z.
Proof.
  intros.
  unfold rasterize1.
  unfold Qminus.
  rewrite Qplus_opp_r, Qmult_0_r.
  unfold Qdiv. rewrite Qmult_0_l.
  reflexivity.
Qed.

Lemma rasterize2_origin
  : forall n m (t l b r : Q),
    b < t -> rasterize2 n m t l b r (pair l t) = pair 0%Z 0%Z.
Proof.
  assert (forall n:positive, 0 <= Zpos n -1)%Z.
  { intro n.
    change 0%Z with (1-1)%Z.
    apply Z.add_le_mono_r.
    apply Pos.le_1_l. }
  intros. unfold rasterize2, fst, snd.
  rewrite rasterize1_origin.
  replace (rasterize1 b t m t) with (Zpos m)%Z.
  change (Z.max 0 0) with 0%Z.
  rewrite Z.min_r. 2: apply H.
  rewrite Z.max_r. 2: discriminate.
  rewrite Z.min_l.
  rewrite Z.sub_diag. reflexivity.
  rewrite <- (Z.add_0_r (Zpos m)) at 2.
  apply Z.add_le_mono_l. discriminate.
  unfold rasterize1.
  unfold Qdiv.
  rewrite <- Qmult_assoc, Qmult_inv_r, Qmult_1_r.
  rewrite Qfloor_Z. reflexivity.
  intro abs. apply Qlt_minus_iff in H0.
  unfold Qminus in abs. rewrite abs in H0.
  exact (Qlt_irrefl 0 H0).
Qed.

(* begin hide *)
Add Parametric Morphism n m bm : (@RasterizePoint n m bm)
    with signature Qeq ==> Qeq ==> Qeq ==> Qeq ==> (@eq _) ==> (@eq _)
      as RasterizePoint_wd.
Proof.
 intros x0 x1 H x2 x3 H0 x4 x5 H1 x6 x7 H2 x.
 unfold RasterizePoint, rasterize2.
 replace (rasterize1 x4 x0 m (snd x)) with (rasterize1 x5 x1 m (snd x)).
  replace (rasterize1 x2 x6 n (fst x)) with (rasterize1 x3 x7 n (fst x)).
   reflexivity.
  unfold rasterize1.
  rewrite -> H0.
  rewrite -> H2.
  reflexivity.
 unfold rasterize1.
 rewrite -> H.
 rewrite -> H1.
 reflexivity.
Qed.
(* end hide *)

(* Adding a point to a raster preserves all the points that were
   already in it. *)
Lemma RasterizePoint_carry : forall t l b r n m (bm:raster) p i j,
    raster_well_formed_nm n m bm
    -> Is_true (RasterIndex bm i j)
    -> Is_true (RasterIndex (RasterizePoint n m bm t l b r p) i j).
Proof.
 intros t l b r m n bm p i j rWf H.
 unfold RasterizePoint, rasterize2.
 set (j0:=(Z.to_nat (Z.min (Z.pos m - 1) (Z.max 0 (rasterize1 l r m (fst p)))))).
 set (i0:=(Z.to_nat (Z.pos n - 1 - Z.min (Z.pos n - 1) (Z.max 0 (rasterize1 b t n (snd p)))))%nat).
 destruct (le_lt_dec (Pos.to_nat n) i0).
 rewrite setRaster_overflow. exact H.
 apply (raster_well_formed_weaken rWf).
 left. destruct rWf. rewrite H0. exact l0.
 destruct (le_lt_dec (Pos.to_nat m) j0).
 rewrite setRaster_overflow. exact H.
 apply (raster_well_formed_weaken rWf).
 right. destruct rWf. unfold RasterLineLength.
 rewrite H1. exact l1. apply nth_In.
 rewrite H0. apply Pos2Nat.is_pos.
 destruct (eq_nat_dec i i0).
 - destruct (eq_nat_dec j j0).
   rewrite e, e0.
   rewrite setRaster_correct1. reflexivity.
   apply (raster_well_formed_weaken rWf).
   destruct rWf. rewrite H0. exact l0.
   destruct rWf. unfold RasterLineLength.
   rewrite H1. exact l1. apply nth_In.
   rewrite H0. apply Pos2Nat.is_pos.
   rewrite setRaster_correct2. exact H.
   exact (raster_well_formed_weaken rWf).
   right. exact n0. 
 - rewrite setRaster_correct2; auto.
   exact (raster_well_formed_weaken rWf).
Qed.

(** Rasterization is done by rasterizing each point, and composing
the resulting raster transfomers. A fold_left is done for efficency.
(It is translated to a fold_right when we reason about it). *)
(* This function could be a bit more efficent by sorting rast *)
Definition RasterizeQ2 (points:list Q2) (n m:positive) (t l b r:Q)
  : raster :=
  fold_left (fun (rast:raster) (p:Q*Q) => @RasterizePoint n m rast t l b r p)
            points (emptyRaster n m).

Lemma RasterizeQ2_wf : forall points n m t l b r,
    raster_well_formed_nm n m (RasterizeQ2 points n m t l b r).
Proof.
  intros. unfold RasterizeQ2.
  pose proof (emptyRaster_wf n m).
  revert H. generalize (emptyRaster n m).
  induction points.
  - intros. exact H.
  - intros. simpl. apply IHpoints.
    unfold RasterizePoint.
    apply setRaster_wf, H.
Qed.

Lemma RasterizeQ2_wf_r : forall points n m (bm:raster) t l b r,
    raster_well_formed_nm n m bm ->
    raster_well_formed_nm n m
      (fold_right (fun p (rast:raster) => @RasterizePoint n m rast t l b r p)
                  bm points).
Proof.
  induction points.
  - intros. exact H.
  - intros. simpl.
    apply setRaster_wf, IHpoints, H.
Qed.

(* begin hide *)
Add Parametric Morphism f n m : (@RasterizeQ2 f n m)
    with signature Qeq ==> Qeq ==> Qeq ==> Qeq ==> (@eq _) as RasterizeQ2_wd.
Proof.
 intros.
 unfold RasterizeQ2.
 do 2 rewrite <- fold_left_rev_right.
 induction (@rev (prod Q Q) f).
  reflexivity.
 simpl.
 rewrite IHl.
 apply RasterizePoint_wd; auto.
Qed.
(* end hide *)
Section RasterizeCorrect.

(* Middles of the horizontal subdivision of the segment [[l, r]].
Instead of l, l + (r-l)/n, ...
it is l + (r-l)/2n, l + (r-l)*3/2n, ... *)
Let C : Q -> Q -> positive -> Z -> Q
  := fun l r (n:positive) (i:Z) => l + (r - l) * (2 * i + 1 # 1) / (2 * Z.pos n # 1).

(* rasterize1 is used in both horizontally and vertically,
   so it will be called for left,width and also for bottom,height. *)
Lemma rasterize1_error : forall l (w:Qpos) n x,
(l <= x <= l + proj1_sig w) ->
Qball ((1 #2*n) * proj1_sig w)
      (C l (l + proj1_sig w) n (Z.min (Z.pos n -1)
                  (Z.max 0 (rasterize1 l (l+proj1_sig w) n x))))
      x.
Proof.
 clear - C.
 intros l w n x H0.
 destruct (Qlt_le_dec x (l+proj1_sig w)).
 - replace (Z.min (Z.pos n -1)
          (Z.max 0 (rasterize1 l (l + proj1_sig w) n x)))
    with (rasterize1 l (l + proj1_sig w) n x).
   + apply ball_sym.
   simpl.
   rewrite -> Qball_Qabs.
   assert (l < l + proj1_sig w).
   { rewrite -> Qlt_minus_iff.
    ring_simplify.
    exact (Qpos_ispos w). }
   eapply Qle_trans.
    unfold C.
    apply (rasterize1_close H).
    setoid_replace (l + proj1_sig w - l) with (proj1_sig w) 
     by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; ring).
    unfold Qdiv. rewrite Qmult_comm.
    apply Qmult_le_compat_r. apply Qle_refl.
    apply Qpos_nonneg.
   + rewrite Z.max_r.
   apply Z.min_case_strong.
    intros H.
    apply Zle_antisym; auto.
    apply Zlt_succ_le.
    rewrite <- Z.add_1_r.
    replace (Z.pos n - 1 + 1)%Z with (Z.pos n) by ring.
    apply rasterize1_boundR; auto.
    rewrite -> Qle_minus_iff.
    ring_simplify.
    exact (Qpos_nonneg w).
   reflexivity.
  destruct H0.
  apply rasterize1_boundL; auto.
  apply Qle_trans with x; auto.
 - rewrite Z.min_l.
  setoid_replace x with (l + proj1_sig w).
   apply ball_sym.
   rewrite ->  Qball_Qabs.
   unfold C.
   rewrite <- (Qmult_comm (proj1_sig w)).
   change (1 # 2*n) with (/((2#1)*inject_Z (Z.pos n))).
   change (2*Z.pos n #1) with ((2#1)*inject_Z (Z.pos n)).
   replace (2 * (Z.pos n - 1) + 1)%Z with (2*Z.pos n + - 1)%Z by ring.
   change (2*Z.pos n + -1#1) with (inject_Z (2*Z.pos n + - 1)).
   rewrite -> Q.Zplus_Qplus.
   rewrite -> Q.Zmult_Qmult.
   change (inject_Z 2) with (2#1).
   change (inject_Z (-1)) with (-1#1)%Q.
   setoid_replace (l + proj1_sig w - (l + (l + proj1_sig w - l) * ((2#1) * inject_Z (Z.pos n) + (-1#1)) / ((2#1) * (inject_Z (Z.pos n)))))
     with ((proj1_sig w / ((2#1) * (inject_Z (Z.pos n)))))
     by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; field; unfold Qeq; simpl; auto with *).
   rewrite -> Qabs_pos;[apply Qle_refl|].
   apply Qle_shift_div_l.
   rewrite <- (Qmult_0_r (2#1)). apply Qmult_lt_l. reflexivity.
   simpl; auto with *; unfold Qlt; simpl; auto with *.
   rewrite Qmult_0_l.
   exact (Qpos_nonneg w).
  destruct H0.
  apply Qle_antisym; auto.
 eapply Z.le_trans;[|apply Z.le_max_r].
 unfold rasterize1.
 rewrite <- (Qfloor_Z (Z.pos n -1)).
 apply Qfloor_resp_le.
 setoid_replace x with (l+proj1_sig w).
 setoid_replace (l + proj1_sig w - l) with (proj1_sig w)
   by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; ring).
 unfold Qdiv.
 rewrite <- Qmult_assoc, Qmult_inv_r, Qmult_1_r.
 2: apply Qpos_nonzero.
 rewrite <- Zle_Qle.
 rewrite <- (Z.add_0_r (Z.pos n)) at 2.
 apply Z.add_le_mono_l. discriminate.
  apply Qle_antisym.
  apply H0. exact q.
Qed.

(* Strange, we should always have b <= t in rasterize1. *)
Lemma switch_line_interp : forall (t b : Q) (m : positive) (j : Z),
     (j < Z.pos m)%Z
     -> C t b m (Z.pos m - 1- j) == C b t m j.
Proof.
 intros t b m j H.
 unfold C.
 replace (2 * (Z.pos m -1 - j) + 1)%Z with (2 * (Z.pos m - j) - 1)%Z by ring.
 change (2 * (Z.pos m - j) - 1 # 1)
   with (inject_Z (2 * (Z.pos m - j) + - 1)%Z).
 change (2*Z.pos m#1) with ((2#1)*inject_Z (Z.pos m)).
 change ((2*j +1)#1) with (inject_Z (2*j+1)%Z).
 do 2 rewrite -> Q.Zplus_Qplus.
 rewrite -> Q.Zmult_Qmult.
 change (inject_Z (-1)) with (-1#1).
 rewrite -> Q.Zmult_Qmult.
 change (inject_Z 2) with (2#1).
 unfold Zminus.
 rewrite -> Q.Zplus_Qplus.
 change (inject_Z (-j)) with (-inject_Z j).
 field.
 apply Q.positive_nonzero_in_Q.
Qed.

Variable b l:Q.
Variable w h:Qpos.

Let r:=l+proj1_sig w.
Let t:=b+proj1_sig h.

Variable f:FinEnum Q2.

Variable n m : positive.

Let errX : Qpos := ((1#2*n)*w)%Qpos.
Let errY : Qpos := ((1#2*m)*h)%Qpos.
Let err : Qpos := Qpos_max errX errY.

Hypothesis Hf : forall (x y : Q), InFinEnumC ((x,y):ProductMS _ _) f ->
 (l<= x <= r) /\ (b <= y <= t).

(** The Rasterization is close to the original enumeration,
ie each one is approximately included in the other,
within error err (Hausdorff distance).
To measure closeness, we use the product metric on Q2, which has
square balls aligned with the 2 axes. *)
Lemma RasterizeQ2_correct1 : forall (x y:Q),
 @InFinEnumC (ProductMS _ _) (x,y) f ->
 ~~exists p, In p (InterpRaster (RasterizeQ2 f n m t l b r) (l,t) (r,b))
        /\ ball (proj1_sig err) p (x,y).
Proof.
 intros x y.
 unfold RasterizeQ2.
 rewrite <- fold_left_rev_right.
 intros H abs.
 unfold InFinEnumC, FinSubset_ball in H.
 destruct (Hf H) as [Hfl Hfr].
 clear Hf.
 pose proof (FinEnum_eq_rev f) as L.
 apply FinEnum_eq_equiv in L.
 specialize (L (x,y)) as [L _].
 specialize (L H).
 contradict H; intro H.
 unfold InFinEnumC, FinSubset_ball in L.
 contradict L; intro L.
 revert abs.
 generalize L.
 clear L H.
 generalize (emptyRaster_wf n m).
 generalize (emptyRaster n m).
 simpl (rev f).
 induction (@rev (prod Q Q) f) as [|a l0].
 intros bm bmWf [z [H _]]; contradiction.
 intros bm bmWf H.
 destruct H as [yH [iny H]].
 destruct iny.
 - subst yH. destruct H as [Hl Hr]. simpl in Hl, Hr.
  simpl.
  unfold RasterizePoint, rasterize2 at 1.
  set (i:=Z.to_nat (Z.min (Z.pos n -1) (Z.max 0 (rasterize1 l r n (fst a))))).
  set (j:=Z.to_nat
            (Z.pos m - 1 -
             Z.min (Z.pos m -1) (Z.max 0 (rasterize1 b t m (snd a))))).
  intro abs; contradict abs.
  exists (C l r n (Z.of_nat i), C t b m (Z.of_nat j)).
  split.
  unfold C.
   apply InterpRaster_correct1.
   apply setRaster_wf.
   apply RasterizeQ2_wf_r, bmWf.
   rewrite setRaster_correct1; unfold i, j.
   reflexivity.
   apply RasterizeQ2_wf_r, bmWf.
   apply Nat2Z.inj_lt.
   rewrite positive_nat_Z, Z2Nat.id.
   rewrite <- Z.sub_add_distr, <- Z.lt_sub_pos.
   apply (Z.lt_le_trans _ (1+0)).
   reflexivity.
   apply Z.add_le_mono_l, rasterize2_bound.
   apply Z.le_0_sub, Z.le_min_l.
   apply Nat2Z.inj_lt.
   rewrite positive_nat_Z, Z2Nat.id; apply rasterize2_bound.
  split.
   + change (ball (proj1_sig err) (C l r n (Z.of_nat i)) x).
   apply Qball_0 in Hl.
   rewrite -> Hl.
   eapply ball_weak_le.
    unfold err.
    apply Qpos_max_ub_l.
    simpl.
    unfold i.
    rewrite Z2Nat.id.
    apply rasterize1_error.
   simpl in Hl.
   rewrite ->  Hl in Hfl.
   exact Hfl.
   apply rasterize2_bound.
   + change (ball (proj1_sig err) (C t b m (Z.of_nat j)) y).
  apply Qball_0 in Hr.
  rewrite -> Hr.
  eapply ball_weak_le.
   unfold err.
   apply Qpos_max_ub_r.
  simpl (ball (m:=Q_as_MetricSpace)).
  unfold j.
  rewrite Z2Nat.id.
  rewrite -> switch_line_interp.
  2: apply rasterize2_bound.
  apply rasterize1_error.
  simpl in Hr.
  rewrite -> Hr in Hfr.
  exact Hfr.
  apply Z.le_0_sub.
  apply Z.le_min_l.
 - simpl.
   specialize (IHl0 bm bmWf (ex_intro _ yH (conj H0 H))).
   intro abs.
   contradict IHl0; intros [z [Hz0 Hz1]].
   contradict abs.
   exists z.
   split. 2: exact Hz1.
   clear - Hz0 bmWf.
   destruct z as [zx zy].
   pose proof (RasterizeQ2_wf_r l0 bm t l b r bmWf).
   destruct (InterpRaster_correct2 _ _ _ _ _ _ _ H Hz0)
     as [[ax ay] [Ha1 [Ha2 Ha3]]].
   rewrite Ha2.
   rewrite Ha3.
   apply InterpRaster_correct1.
   apply setRaster_wf, RasterizeQ2_wf_r, bmWf.
   apply RasterizePoint_carry.
   apply RasterizeQ2_wf_r, bmWf.
   exact Ha1.
Qed.

Lemma RasterizeQ2_correct2 : forall (x y : Q),
    @InFinEnumC (ProductMS _ _) (x,y)
                (InterpRaster (RasterizeQ2 f n m t l b r) (l,t) (r,b))
    -> ~~ exists p, In p f /\ ball (proj1_sig err) p (x,y).
Proof.
 intros x y H.
 intro abs.
 unfold InFinEnumC, FinSubset_ball in H.
 contradict H; intro H.
 destruct H as [[x' y'] [H' Hxy]].
 destruct (InterpRaster_correct2
             _ _ _ _ _ _ _ (RasterizeQ2_wf f n m t l b r) H')
   as [[j i] [Hij [Hx' Hy']]].
 rewrite Hx' in Hxy.
 rewrite Hy' in Hxy.
 assert (Hf':forall x y : Q_as_MetricSpace,
   InFinEnumC ((x, y):ProductMS Q_as_MetricSpace Q_as_MetricSpace) (rev f)
   -> l <= x <= r /\ b <= y <= t).
 { intros c d Hcd.
  apply Hf.
  pose proof (FinEnum_eq_rev f).
  apply FinEnum_eq_equiv in H.
  destruct (H (c,d)). exact (H1 Hcd). }
 clear Hf.
 clear Hx' Hy' H'.
 destruct Hxy as [Hx' Hy'].
 cut (existsC (ProductMS Q_as_MetricSpace Q_as_MetricSpace)
   (fun p : ProductMS Q_as_MetricSpace Q_as_MetricSpace =>
     InFinEnumC (X:=ProductMS Q_as_MetricSpace Q_as_MetricSpace) p (rev f) /\
       ball (m:=ProductMS Q_as_MetricSpace Q_as_MetricSpace) (proj1_sig err) p (x, y))).
 - intros L.
   clear -L abs.
   unfold existsC in L.
   contradict L. intros x0 [H H0].
   unfold InFinEnumC, FinSubset_ball in H.
   contradict H; intros H.
   contradict abs.
   destruct H.
   exists x1. split.
   rewrite in_rev. apply H.
   destruct H.
   rewrite <- H1.
   exact H0.
 - unfold RasterizeQ2 in Hij.
 rewrite <- fold_left_rev_right in Hij.
 simpl (rev f). simpl (rev f) in Hf'.
 induction (@rev (prod Q Q) f).
  clear - Hij.
  simpl in Hij.
  pose proof (emptyRasterEmpty n m j i).
  simpl in H.
  rewrite H in Hij. clear H.
  contradiction.
  simpl in Hij.
 unfold RasterizePoint, rasterize2 at 1 in Hij.
  set (i0:=Z.to_nat (Z.min (Z.pos n -1) (Z.max 0 (rasterize1 l r n (fst a))))) in Hij.
  set (j0:=Z.to_nat
             (Z.pos m -1 -
              Z.min (Z.pos m -1) (Z.max 0 (rasterize1 b t m (snd a))))) in Hij.
 assert (L:((i=i0)/\(j=j0) \/ ((j<>(j0)) \/ (i<>i0)))%nat) by omega.
 destruct L as [[Hi Hj] | L].
   + clear IHl0.
  rewrite Hi, Hj in Hx'.
  rewrite Hi, Hj in Hy'.
  unfold fst, snd in *.
  apply existsWeaken.
  exists a.
  split.
  intro H; contradict H.
  exists a. split. left. reflexivity. reflexivity.
  destruct a as [ax ay].
  destruct (Hf' ax ay) as [Hax Hay].
  intro H; contradict H.
  exists (ax,ay). split. left. reflexivity. reflexivity.
  clear Hf'.
  split.
     * unfold fst.
   rewrite -> Hx'.
   apply ball_sym.
   eapply ball_weak_le.
    unfold err.
    apply Qpos_max_ub_l.
    unfold i0.
    rewrite Z2Nat.id. 
   apply rasterize1_error.
   auto.
   apply rasterize2_bound.
     * unfold snd.
  rewrite -> Hy'.
  apply ball_sym.
  eapply ball_weak_le.
   unfold err.
   apply Qpos_max_ub_r.
  change (Qball (proj1_sig errY) (C t b m (Z.of_nat j0)) ay).
  unfold j0.
  rewrite Z2Nat.id. 
  rewrite -> switch_line_interp.
  2: apply rasterize2_bound.
  apply rasterize1_error.
  exact Hay.
  apply Z.le_0_sub.
  apply Z.le_min_l. 
   + assert (L0:existsC (Q * Q) (fun p : Q * Q =>
   InFinEnumC (X:=ProductMS Q_as_MetricSpace Q_as_MetricSpace) p l0 /\
     ball (m:=ProductMS Q_as_MetricSpace Q_as_MetricSpace) (proj1_sig err) p (x, y))).
  apply IHl0.
   simpl in Hij.
   rewrite setRaster_correct2 in Hij.
   exact Hij.
   apply RasterizeQ2_wf_r, emptyRaster_wf.
   exact L.
  intros c d Hcd.
  apply Hf'.
  apply FinSubset_ball_cons.
  exact Hcd.
 destruct L0 as [G | z [Hz0 Hz1]] using existsC_ind.
  apply existsC_stable, G.
 apply existsWeaken.
 exists z.
 split.
  apply FinSubset_ball_cons.
  exact Hz0. exact Hz1.
Qed.

Lemma RasterizeQ2_correct :
 ball (proj1_sig err)
  (InterpRaster (RasterizeQ2 f n m t l b r) (l,t) (r,b))
  f.
Proof.
  split. apply Qpos_nonneg.
  split; intros [x y] Hx.
  - pose proof (RasterizeQ2_correct2 Hx).
    intro abs.
    contradict H; intros [z [Hz0 Hz1]].
    specialize (abs z). contradict abs.
    split.
    apply InFinEnumC_weaken, Hz0.
    apply ball_sym, Hz1.
  - intro abs.
    pose proof (RasterizeQ2_correct1 Hx).
    contradict H; intros [z [Hz0 Hz1]].
    specialize (abs z). contradict abs.
    split.
    apply InFinEnumC_weaken, Hz0.
    apply ball_sym, Hz1.
Qed.

End RasterizeCorrect.
