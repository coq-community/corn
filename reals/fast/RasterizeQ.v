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
Definition rasterize2 (n m:nat) (t l b r:Q) (p:Q*Q) : prod nat nat
  := pair (min (pred n) (Z.to_nat (Z.max 0 (rasterize1 l r n (fst p)))))
          (min (pred m) (Z.to_nat (Z.max 0 (rasterize1 b t m (snd p))))).
           
Definition RasterizePoint (n m:nat) (bm:raster n m) (t l b r:Q) (p:Q*Q) : raster n m :=
  let (i,j) := rasterize2 n m t l b r p in
  setRaster bm true (pred m - j) i.

Lemma rasterize1_origin : forall l r n, rasterize1 l r n l = 0%Z.
Proof.
  intros. unfold rasterize1.
  unfold Qminus.
  rewrite Qplus_opp_r, Qmult_0_r.
  unfold Qdiv. rewrite Qmult_0_l.
  reflexivity.
Qed.

(* The y-coordinate is flipped by (pred m - j) before
   calling setRaster, so the origin is the top left corner. *)
Lemma rasterize2_origin
  : forall n m t l b r,
    rasterize2 n m t l b r (pair l b) = pair O O.
Proof.
  intros. unfold rasterize2; simpl.
  rewrite rasterize1_origin, rasterize1_origin.
  simpl. 
  rewrite NPeano.Nat.min_0_r, NPeano.Nat.min_0_r.
  reflexivity.
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
Lemma RasterizePoint_carry : forall t l b r n m (bm:raster n m) p i j,
    Is_true (RasterIndex bm i j)
    -> Is_true (RasterIndex (RasterizePoint bm t l b r p) i j).
Proof.
 intros t l b r m n bm p i j H.
 unfold RasterizePoint, rasterize2.
 set (j0:=(min (pred m) (Z.to_nat (Z.max 0 (rasterize1 l r m (fst p)))))).
 set (i0:=(pred n - min (pred n)
   (Z.to_nat (Z.max 0 (rasterize1 b t n (snd p)))))%nat).
 destruct (le_lt_dec n i0).
  rewrite setRaster_overflow; auto.
 destruct (le_lt_dec m j0).
  rewrite setRaster_overflow; auto.
 destruct (eq_nat_dec i i0).
  destruct (eq_nat_dec j j0).
   rewrite e, e0.
   rewrite setRaster_correct1; try constructor; congruence.
  rewrite setRaster_correct2; auto.
 rewrite setRaster_correct2; auto.
Qed.

(** Rasterization is done by rasterizing each point, and composing
the resulting raster transfomers. A fold_left is done for efficency.
(It is translated to a fold_right when we reason about it). *)
(* This function could be a bit more efficent by sorting rast *)
Definition RasterizeQ2 (f:FinEnum Q2) (n m:nat) (t l b r:Q) : raster n m :=
  fold_left (fun (rast:raster n m) (p:Q*Q) => @RasterizePoint n m rast t l b r p)
            f (emptyRaster _ _).

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
Let C : Q -> Q -> nat -> Z -> Q
  := fun l r (n:nat) (i:Z) => l + (r - l) * (2 * i + 1 # 1) / (2 * Z.of_nat n # 1).

(* rasterize1 is used in both horizontally and vertically,
   so it will be called for left,width and also for bottom,height. *)
Lemma rasterize1_error : forall l (w:Qpos) n x,
(l <= x <= l + proj1_sig w) ->
Qball ((1 #2*P_of_succ_nat n) * proj1_sig w)
      (C l (l + proj1_sig w) (S n) (Z.of_nat (min n
             (Z.to_nat
                (Z.max 0 (rasterize1 l (l+proj1_sig w) (S n) x))))))
      x.
Proof.
 clear - C.
 intros l w n x H0.
 destruct (Qlt_le_dec x (l+proj1_sig w)).
 - replace (Z_of_nat (min n (Z.to_nat (Z.max 0 (rasterize1 l (l + proj1_sig w) (S n) x)) )))
    with (rasterize1 l (l + proj1_sig w) (S n) x).
   apply ball_sym.
   simpl.
   rewrite -> Qball_Qabs.
   assert (l < l + proj1_sig w).
    rewrite -> Qlt_minus_iff.
    ring_simplify.
    auto with *.
   eapply Qle_trans.
    unfold C.
    apply (rasterize1_close H).
    change ((l + proj1_sig w - l) / ((2#1) * inject_Z (Z.of_nat (S n)))
            <=(/ inject_Z 2) * (1# (P_of_succ_nat n)) * proj1_sig w).
   unfold Qdiv.
   rewrite -> Qinv_mult_distr.
   setoid_replace ( (l + proj1_sig w - l) * (/ (2#1) * / inject_Z (Z.of_nat (S n))))
     with (((/ (2#1)) * (/ inject_Z (Z.of_nat (S n))) * proj1_sig w))
     by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; ring).
   apply Qle_refl.
  rewrite inj_min.
  rewrite Z2Nat.id.
  rewrite Zmax_right.
   apply Z.min_case_strong.
    intros H.
    apply Zle_antisym; auto.
    apply Zlt_succ_le.
    rewrite <- inj_S.
    apply rasterize1_boundR; auto.
    rewrite -> Qle_minus_iff.
    ring_simplify.
    auto with *.
   reflexivity.
  destruct H0.
  apply rasterize1_boundL; auto.
  apply Qle_trans with x; auto.
  apply Z.le_max_l.
 - simpl.
 replace (min n (Z.to_nat (Z.max 0 (rasterize1 l (l + proj1_sig w) (S n) x)))) with n.
  setoid_replace x with (l + proj1_sig w).
   apply ball_sym.
   rewrite ->  Qball_Qabs.
   unfold C.
   setoid_replace ((1 # (Pos.of_succ_nat n)~0) * proj1_sig w) 
     with (proj1_sig w*(1#xO (P_of_succ_nat n)))
     by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; ring).
   change (1 # xO (P_of_succ_nat n)) with (/((2#1)*inject_Z (Z.of_nat (S n)))).
   change (2*Z.of_nat (S n) #1) with ((2#1)*inject_Z (Z.of_nat (S n))).
   change (2*Z.of_nat n + 1#1) with (inject_Z (2*Z.of_nat n + 1)).
   rewrite (inj_S n).
   unfold Z.succ.
   do 2 rewrite -> Q.Zplus_Qplus.
   rewrite -> Q.Zmult_Qmult.
   change (inject_Z 2) with (2#1).
   change (inject_Z 1) with 1%Q.
   setoid_replace (l + proj1_sig w - (l + (l + proj1_sig w - l) * ((2#1) * inject_Z (Z.of_nat n) + 1) / ((2#1) * (inject_Z (Z.of_nat n) + 1))))
     with ((proj1_sig w / ((2#1) * (inject_Z (Z.of_nat n) + 1))))
     by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; field; unfold Qeq; simpl; auto with *).
   rewrite -> Qabs_pos;[apply Qle_refl|].
   apply Qle_shift_div_l.
   rewrite <- (Qmult_0_r (2#1)). apply Qmult_lt_l. reflexivity.
   simpl; auto with *; unfold Qlt; simpl; auto with *.
   rewrite Qmult_0_l.
   auto with *.
  destruct H0.
  apply Qle_antisym; auto.
 symmetry.
 apply min_l.
 apply Nat2Z.inj_le.
 rewrite Z2Nat.id.
 eapply Z.le_trans;[|apply Z.le_max_r].
 unfold rasterize1.
 rewrite <- (Qfloor_Z (Z.of_nat n)).
 apply Qfloor_resp_le.
 setoid_replace x with (l+proj1_sig w).
 setoid_replace (l + proj1_sig w - l) with (proj1_sig w)
   by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; ring).
 unfold Qdiv.
 rewrite <- Qmult_assoc, Qmult_inv_r, Qmult_1_r.
  unfold Qle.
  simpl.
  rewrite Z.mul_1_r, Pos.mul_1_r, Zpos_P_of_succ_nat.
  apply Z.le_succ_diag_r.
  apply Qpos_nonzero.
  apply Qle_antisym.
  apply H0. exact q.
  apply Z.le_max_l.
Qed.

(* Strange, we should always have b <= t in rasterize1. *)
Lemma switch_line_interp : forall (t b : Q) (m j : nat),
             (j <= m)%nat -> C t b (S m) (Z.of_nat (m - j)%nat) == C b t (S m) (Z.of_nat j).
Proof.
 intros t b m j H.
 unfold C.
 rewrite inj_minus1;[|auto].
 change (2 * (Z.of_nat m - Z.of_nat j) + 1 # 1)
   with (inject_Z (2 * (Z.of_nat m - Z.of_nat j) + 1)%Z).
 change (2*Z.of_nat (S m)#1) with ((2#1)*inject_Z (Z.of_nat (S m))).
 change ((2*Z.of_nat j +1)#1) with (inject_Z (2*Z.of_nat j+1)%Z).
 do 2 rewrite -> Q.Zplus_Qplus.
 rewrite -> Q.Zmult_Qmult.
 change (inject_Z 1) with 1.
 rewrite -> Q.Zmult_Qmult.
 change (inject_Z 2) with (2#1).
 unfold Zminus.
 rewrite -> Q.Zplus_Qplus.
 rewrite (inj_S m).
 unfold Z.succ.
 rewrite -> Q.Zplus_Qplus.
 change (inject_Z (-Z.of_nat j)) with (-inject_Z (Z.of_nat j)).
 field.
 change 1 with (inject_Z 1).
 rewrite <- Q.Zplus_Qplus, Z.add_1_r.
 rewrite <- Zpos_P_of_succ_nat.
 apply Q.positive_nonzero_in_Q.
Qed.

Variable b l:Q.
Variable w h:Qpos.

Let r:=l+proj1_sig w.
Let t:=b+proj1_sig h.

Variable f:FinEnum Q2.

Variable n m : nat.

Let errX : Qpos := ((1#2*P_of_succ_nat n)*w)%Qpos.
Let errY : Qpos := ((1#2*P_of_succ_nat m)*h)%Qpos.
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
 ~~exists p, In p (InterpRaster (RasterizeQ2 f (S n) (S m) t l b r) (l,t) (r,b))
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
 generalize (emptyRaster (S n) (S m)).
 simpl (rev f).
 induction (@rev (prod Q Q) f).
 intros r0 [z [H _]]; contradiction.
 intros bm H.
 destruct H as [yH [iny H]].
 destruct iny.
 - subst yH. destruct H as [Hl Hr]. simpl in Hl, Hr.
  simpl (fold_right (fun (y0 : Q * Q) (x0 : raster (S n) (S m)) =>
    RasterizePoint x0 t l b r y0) bm (a :: l0)).
  unfold RasterizePoint, rasterize2 at 1.
  simpl (pred (S n)).
  simpl (pred (S m)).
  set (i:=min n (Z.to_nat (Z.max 0 (rasterize1 l r (S n) (fst a))))).
  set (j:=min m (Z.to_nat (Z.max 0 (rasterize1 b t (S m) (snd a))))).
  cbv zeta.
  intro abs; contradict abs.
  exists (C l r (S n) (Z.of_nat i), C t b (S m) (Z.of_nat (m -j)%nat)).
  split.
   apply InterpRaster_correct1.
   rewrite setRaster_correct1; unfold i, j; auto with *.
  split.
   change (ball (proj1_sig err) (C l r (S n) (Z.of_nat i)) x).
   apply Qball_0 in Hl.
   rewrite -> Hl.
   eapply ball_weak_le.
    unfold err.
    apply Qpos_max_ub_l.
   apply rasterize1_error.
   simpl in Hl.
   rewrite ->  Hl in Hfl.
   auto.
  change (ball (proj1_sig err) (C t b (S m) (Z.of_nat (m-j)%nat)) y).
  apply Qball_0 in Hr.
  rewrite -> Hr.
  eapply ball_weak_le.
   unfold err.
   apply Qpos_max_ub_r.
  simpl (ball (m:=Q_as_MetricSpace)).
  rewrite -> switch_line_interp;[|unfold j; auto with *].
  apply rasterize1_error.
  simpl in Hr.
  rewrite -> Hr in Hfr.
  auto.
 - simpl ((fold_right (fun (y : Q * Q) (x : raster (S n) (S m)) =>
   RasterizePoint x t l b r y) bm) (a :: l0)).
   specialize (IHl0 bm (ex_intro _ yH (conj H0 H))).
   intro abs.
   contradict IHl0; intros [z [Hz0 Hz1]].
   contradict abs.
   exists z.
   split; auto.
   clear - Hz0.
   destruct z as [zx zy].
   destruct (InterpRaster_correct2 _ _ _ _ _ _ _ Hz0) as [[ax ay] [Ha1 [Ha2 Ha3]]].
   rewrite Ha2.
   rewrite Ha3.
   apply InterpRaster_correct1.
   apply RasterizePoint_carry.
   auto.
Qed.

Lemma RasterizeQ2_correct2 : forall (x y : Q),
    @InFinEnumC (ProductMS _ _) (x,y)
                (InterpRaster (RasterizeQ2 f (S n) (S m) t l b r) (l,t) (r,b))
    -> ~~ exists p, In p f /\ ball (proj1_sig err) p (x,y).
Proof.
 intros x y H.
 intro abs.
 unfold InFinEnumC, FinSubset_ball in H.
 contradict H; intro H.
 destruct H as [[x' y'] [H' Hxy]].
 destruct (InterpRaster_correct2 _ _ _ _ _ _ _ H') as [[j i] [Hij [Hx' Hy']]].
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
  set (z:=emptyRaster (S n) (S m)) in Hij.
  simpl in Hij.
  unfold z in Hij.
  rewrite emptyRasterEmpty in Hij.
  contradiction.
 simpl (fold_right (fun (y : Q * Q) (x : raster (S n) (S m)) =>
   RasterizePoint x t l b r y) (emptyRaster (S n) (S m)) (a :: l0)) in Hij.
 unfold RasterizePoint at 1 in Hij.
 set (i0:=min (pred (S n)) (Z.to_nat (Z.max 0 (rasterize1 l r (S n) (fst a))))) in *.
 set (j0:=min (pred (S m)) (Z.to_nat (Z.max 0 (rasterize1 b t (S m) (snd a))))) in *.
 cbv zeta in Hij.
 assert (L:((i=i0)/\(j=m-j0) \/ ((j<>(m-j0)) \/ (i<>i0)))%nat) by omega.
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
   unfold fst.
   rewrite -> Hx'.
   apply ball_sym.
   eapply ball_weak_le.
    unfold err.
    apply Qpos_max_ub_l.
   apply rasterize1_error.
   auto.
  unfold snd.
  rewrite -> Hy'.
  apply ball_sym.
  eapply ball_weak_le.
   unfold err.
   apply Qpos_max_ub_r.
  fold (C t b (S m) (Z.of_nat (m - j0)%nat)).
  simpl (ball (m:=Q_as_MetricSpace)).
  rewrite -> switch_line_interp;[|unfold j0; auto with *].
  apply rasterize1_error.
  auto.
   + assert (L0:existsC (Q * Q) (fun p : Q * Q =>
   InFinEnumC (X:=ProductMS Q_as_MetricSpace Q_as_MetricSpace) p l0 /\
     ball (m:=ProductMS Q_as_MetricSpace Q_as_MetricSpace) (proj1_sig err) p (x, y))).
  apply IHl0.
   simpl in Hij.
   rewrite setRaster_correct2 in Hij; auto.
  intros c d Hcd.
  apply Hf'.
  apply FinSubset_ball_cons.
  exact Hcd.
 destruct L0 as [G | z [Hz0 Hz1]] using existsC_ind.
  auto using existsC_stable.
 apply existsWeaken.
 exists z.
 split; auto.
  apply FinSubset_ball_cons.
  exact Hz0.
Qed.

Lemma RasterizeQ2_correct :
 ball (proj1_sig err)
  (InterpRaster (RasterizeQ2 f (S n) (S m) t l b r) (l,t) (r,b))
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
    auto using ball_sym.
  - intro abs.
    pose proof (RasterizeQ2_correct1 Hx).
    contradict H; intros [z [Hz0 Hz1]].
    specialize (abs z). contradict abs.
    split.
    apply InFinEnumC_weaken, Hz0.
    auto using ball_sym.
Qed.

End RasterizeCorrect.
