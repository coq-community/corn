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
Require Export RasterQ.
Require Import Interval.
Require Import Classic.
Require Import QposMinMax.
Require Import Qabs.
Require Import Qauto.
Require Import Qround.
Require Import CornTac.

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
is chosen that contains all the points, so that this doesn't matter.

[Rasterize Point] adds a single point [p] into a raster. *)
Definition RasterizePoint n m (bm:raster n m) (t l b r:Q) (p:Q*Q) : raster n m :=
let i := min (pred n) (Z_to_nat (Zle_max_l 0 (rasterize1 l r n (fst p)))) in
let j := min (pred m) (Z_to_nat (Zle_max_l 0 (rasterize1 b t m (snd p)))) in
setRaster bm true (pred m - j) i.
(* begin hide *)
Add Parametric Morphism n m bm : (@RasterizePoint n m bm) with signature Qeq ==> Qeq ==> Qeq ==> Qeq ==> (@eq _) ==> (@eq _) as RasterizePoint_wd.
intros x0 x1 H x2 x3 H0 x4 x5 H1 x6 x7 H2 x.
unfold RasterizePoint.
replace (rasterize1 x4 x0 m (snd x))
 with (rasterize1 x5 x1 m (snd x)).
 replace (rasterize1 x2 x6 n (fst x))
  with (rasterize1 x3 x7 n (fst x)).
  reflexivity.
 unfold rasterize1.
 rewrite H0.
 rewrite H2.
 reflexivity.
unfold rasterize1.
rewrite H.
rewrite H1.
reflexivity.
Qed.
(* end hide *)
Lemma RasterizePoint_carry : forall t l b r n m (bm:raster n m) p i j,
 Is_true (RasterIndex bm i j) -> Is_true (RasterIndex (RasterizePoint bm t l b r p) i j).
Proof.
intros t l b r m n bm p i j H.
unfold RasterizePoint.
set (j0:=(min (pred m)
           (Z_to_nat (z:=Zmax 0 (rasterize1 l r m (fst p)))
              (Zle_max_l 0 (rasterize1 l r m (fst p)))))).
set (i0:=(pred n -
         min (pred n)
           (Z_to_nat (z:=Zmax 0 (rasterize1 b t n (snd p))) (Zle_max_l 0 (rasterize1 b t n (snd p)))))%nat).
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
the resulting raster transfomers.  A fold_left is done for efficency.
(It is translated to a fold_right when we reason about it). *)
(* This function could be a bit more efficent by sorting x *)
Definition RasterizeQ2 (f:FinEnum stableQ2) n m (t l b r:Q) : raster n m :=
fold_left (fun x y => @RasterizePoint n m x t l b r y) f (emptyRaster _ _).
(* begin hide *)
Add Parametric Morphism f n m : (@RasterizeQ2 f n m) with signature Qeq ==> Qeq ==> Qeq ==> Qeq ==> (@eq _) as RasterizeQ2_wd.
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

Let C := fun l r (n:nat) (i:Z) => l + (r - l) * (2 * i + 1 # 1) / (2 * n # 1).

Lemma rasterization_error : forall l (w:Qpos) n x,
(l <= x <= l + w) ->
ball (m:=Q_as_MetricSpace) ((1 #2*P_of_succ_nat n) * w) (C l (l + w) (S n) (min n
             (Z_to_nat 
                (Zle_max_l 0 (rasterize1 l (l+w) (S n) x))))) x.
Proof.
clear - C.
intros l w n x H0.
destruct (Qlt_le_dec x (l+w)).
 replace (Z_of_nat (min n
        (Z_to_nat (z:=Zmax 0 (rasterize1 l (l + w) (S n) x))
           (Zle_max_l 0 (rasterize1 l (l + w) (S n) x)))))
  with (rasterize1 l (l + w) (S n) x).
  apply ball_sym.
  simpl.
  rewrite Qball_Qabs.
  assert (l < l + w).
   rewrite Qlt_minus_iff.
   ring_simplify.
   auto with *.
  eapply Qle_trans.
   unfold C.
   apply (rasterize1_close H).
  change ((l + w - l) / (2 * S n) <=(/ 2%positive) * (/ P_of_succ_nat n) * w).
  unfold Qdiv.
  rewrite Qinv_mult_distr.
  replace LHS with (((/ 2) * (/ S n) * w)) by ring.
  apply Qle_refl.
 rewrite inj_min.
 rewrite <- Z_to_nat_correct.
 rewrite Zmax_right.
  apply Zmin_case_strong.
   intros H.
   apply Zle_antisym; auto.
   apply Zlt_succ_le.
   rewrite <- inj_S.
   apply rasterize1_boundR; auto.
   rewrite Qle_minus_iff.
   ring_simplify.
   auto with *.
  reflexivity.
 destruct H0.
 apply rasterize1_boundL; auto.
 apply Qle_trans with x; auto.
simpl.
replace (min n
        (Z_to_nat (z:=Zmax 0 (rasterize1 l (l + w) (S n) x))
           (Zle_max_l 0 (rasterize1 l (l + w) (S n) x))))
 with n.
 setoid_replace x with (l + w).
  rapply ball_sym.
  rewrite Qball_Qabs.
  unfold C.
  autorewrite with QposElim.
  replace RHS with (w*(1#xO (P_of_succ_nat n))) by ring.
  change (1 # xO (P_of_succ_nat n)) with (/(2*(S n))).
  change (2*S n #1) with (2*S n).
  change (2*n + 1#1) with ((2*n + 1)%Z:Q).
  rewrite (inj_S n).
  unfold Zsucc.
  do 2 rewrite injz_plus.
  setoid_replace ((2%positive * n)%Z:Q) with (2*n)
   by (unfold Qeq; simpl; auto with *).
  setoid_replace (l + w - (l + (l + w - l) * (2 * n + 1%positive) / (2 * (n + 1%positive))))
   with ((w / (2 * (n + 1%positive))))
   by (field; unfold Qeq; simpl; auto with *).
  rewrite Qabs_pos;[apply Qle_refl|].
  apply Qle_shift_div_l;
   [rsapply mult_resp_pos; auto with *;
    unfold Qlt; simpl; auto with *|].
  replace LHS with 0 by ring.
  auto with *.
 destruct H0.
 apply Qle_antisym; auto.
symmetry.
apply min_l.
apply surj_le.
rewrite <- Z_to_nat_correct.
eapply Zle_trans;[|apply Zle_max_r].
unfold rasterize1.
rewrite <- (Qfloor_Z n).
apply Qfloor_resp_le.
setoid_replace x with (l+w).
 setoid_replace (l + w - l) with (w:Q) by ring.
 field_simplify;[|apply Qpos_nonzero].
 unfold Qle.
 simpl.
 change (n * 1* 1 <= (S n)*1*1)%Z.
 ring_simplify.
 apply inj_le.
 auto with *.
destruct H0; auto with *.
Qed.

Lemma switch_line_interp : forall t b m j, (j <= m)%nat -> C t b (S m) (m - j)%nat == C b t (S m) j.
Proof.
intros t b m j H.
unfold C.
rewrite inj_minus1;[|auto].
change (2 * (m - j) + 1 # 1) with ((2 * (m - j) + 1)%Z:Q).
change (2*S m#1) with (2*(S m)).
change ((2*j +1)#1) with ((2*j+1)%Z:Q).
do 2 rewrite injz_plus.
change ((2%positive * (m - j))%Z:Q)
 with (2 * (m - j)%Z).
change ((2%positive * j)%Z:Q)
 with (2 * j).
change (1%Z:Q) with (1:Q).
unfold Zminus.
rewrite injz_plus.
rewrite (inj_S m).
unfold Zsucc.
rewrite injz_plus.
change ((-j)%Z:Q) with (-j).
field.
unfold Qeq.
simpl.
auto with *.
Qed.

Variable b l:Q.
Variable w h:Qpos.

Let r:=l+w.
Let t:=b+h.

Variable f:FinEnum stableQ2.

Variable n m : nat.

Let errX : Qpos := ((1#2*P_of_succ_nat n)*w)%Qpos.
Let errY : Qpos := ((1#2*P_of_succ_nat m)*h)%Qpos.
Let err : Qpos := Qpos_max errX errY.

Hypothesis Hf:forall x y, InFinEnumC ((x,y):ProductMS _ _) f -> 
 (l<= x <= r) /\ (b <= y <= t).

(** The Rasterization is close to the original enumeration. *)
Lemma RasterizeQ2_correct1 : forall x y,
 InFinEnumC ((x,y):ProductMS _ _) f -> 
 existsC (ProductMS _ _) 
  (fun p => InFinEnumC p (InterpRaster (RasterizeQ2 f (S n) (S m) t l b r) (l,t) (r,b))
            /\ ball err p (x,y)).
Proof.
intros x y.
unfold RasterizeQ2.
rewrite <- fold_left_rev_right.
intros H.
destruct (Hf _ _ H) as [Hfl Hfr].
clear Hf.
destruct (FinEnum_eq_rev f (x,y)) as [L _].
generalize (L H).
clear L H.
simpl (ms Q2).
generalize (emptyRaster (S n) (S m)).
induction (@rev (prod Q Q) f).
 contradiction.
intros bm H.
destruct H as [G | [Hl Hr] | H] using orC_ind.
  auto using existsC_stable.
 simpl in Hl, Hr.
 simpl (fold_right
           (fun (y0 : Q * Q) (x0 : raster (S n) (S m)) =>
            RasterizePoint x0 t l b r y0) bm (a :: l0)).
 unfold RasterizePoint at 1.
 simpl (pred (S n)).
 simpl (pred (S m)).
 set (i:=min n
             (Z_to_nat (Zle_max_l 0 (rasterize1 l r (S n) (fst a))))).
 set (j:=min m
             (Z_to_nat (Zle_max_l 0 (rasterize1 b t (S m) (snd a))))).
 cbv zeta.
 apply existsWeaken.
 exists (C l r (S n) i,C t b (S m) (m -j)%nat).
 split.
  apply InFinEnumC_weaken.
  rapply InterpRaster_correct1.
  rewrite setRaster_correct1; unfold i, j; auto with *.
 split.
  change (ball err (C l r (S n) i) x).
  change (ms_eq x (fst a)) in Hl.
  rewrite Hl.
  eapply ball_weak_le.
   unfold err.
   apply Qpos_max_ub_l.
  rapply rasterization_error.
  simpl in Hl.
  rewrite Hl in Hfl.
  auto.
 change (ball err (C t b (S m) (m-j)%nat) y).
 change (ms_eq y (snd a)) in Hr.
 rewrite Hr.
 eapply ball_weak_le.
  unfold err.
  apply Qpos_max_ub_r.
 simpl (ball (m:=Q_as_MetricSpace)).
 rewrite switch_line_interp;[|unfold j; auto with *].
 rapply rasterization_error.
 simpl in Hr.
 rewrite Hr in Hfr.
 auto.
simpl ((fold_right
        (fun (y : Q * Q) (x : raster (S n) (S m)) =>
         RasterizePoint x t l b r y) bm) (a :: l0)).
destruct (IHl0 bm H) as [G | z [Hz0 Hz1]] using existsC_ind.
 auto using existsC_stable.
apply existsWeaken.
exists z.
split; auto.
clear - Hz0.
destruct z as [zx zy].
destruct (InStrengthen _ _ Hz0) as [[zx' zy'] [Hz'0 Hz'1]].
rewrite (fun a => InFinEnumC_wd1 _ _ _ a Hz'1).
apply InFinEnumC_weaken.
destruct (InterpRaster_correct2 _ _ _ _ _ _ _ Hz'0) as [[ax ay] [Ha1 [Ha2 Ha3]]].
rewrite Ha2.
rewrite Ha3.
apply InterpRaster_correct1.
apply RasterizePoint_carry.
auto.
Qed.

Lemma RasterizeQ2_correct2 : forall x y,
 InFinEnumC ((x,y):ProductMS _ _) (InterpRaster (RasterizeQ2 f (S n) (S m) t l b r) (l,t) (r,b))
 -> (existsC (ProductMS _ _) 
  (fun p => InFinEnumC p f/\ ball err p (x,y))).
Proof.
intros x y H.
destruct (InStrengthen _ _ H) as [[x' y'] [H' Hxy]].
destruct (InterpRaster_correct2 _ _ _ _ _ _ _ H') as [[j i] [Hij [Hx' Hy']]].
rewrite Hx' in Hxy.
rewrite Hy' in Hxy.
assert (Hf':forall x y : Q_as_MetricSpace,
     InFinEnumC (X:=ProductMS Q_as_MetricSpace Q_as_MetricSpace)
       ((x, y):ProductMS Q_as_MetricSpace Q_as_MetricSpace) (rev f) ->
     l <= x <= r /\ b <= y <= t).
 intros c d Hcd.
 apply Hf.
 destruct (FinEnum_eq_rev f (c,d)); auto.
clear Hf.
clear Hx' Hy' H' H.
destruct Hxy as [Hx' Hy'].
cut (existsC (ProductMS Q_as_MetricSpace Q_as_MetricSpace)
  (fun p : ProductMS Q_as_MetricSpace Q_as_MetricSpace =>
   InFinEnumC (X:=ProductMS Q_as_MetricSpace Q_as_MetricSpace) p (rev f) /\
   ball (m:=ProductMS Q_as_MetricSpace Q_as_MetricSpace) err p (x, y))).
 intros L.
 clear -L.
 destruct L as [G | z [Hz0 Hz]] using existsC_ind.
  auto using existsC_stable.
 apply existsWeaken.
 exists z.
 split; auto.
 destruct (FinEnum_eq_rev f z); auto.
unfold RasterizeQ2 in Hij.
rewrite <- fold_left_rev_right in Hij.
simpl (ms Q2) in Hf'|-*.
induction (@rev (prod Q Q) f).
 clear - Hij.
 set (z:=emptyRaster (S n) (S m)) in Hij.
 simpl in Hij.
 unfold z in Hij.
 rewrite emptyRasterEmpty in Hij.
 contradiction.
simpl (fold_right (fun (y : Q * Q) (x : raster (S n) (S m)) =>
               RasterizePoint x t l b r y) (emptyRaster (S n) (S m))
              (a :: l0)) in Hij.
unfold RasterizePoint at 1 in Hij.
set (i0:=min (pred (S n))
                (Z_to_nat (z:=Zmax 0 (rasterize1 l r (S n) (fst a)))
                   (Zle_max_l 0 (rasterize1 l r (S n) (fst a))))) in *.
set (j0:=min (pred (S m))
                (Z_to_nat (z:=Zmax 0 (rasterize1 b t (S m) (snd a)))
                   (Zle_max_l 0 (rasterize1 b t (S m) (snd a))))) in *.
cbv zeta in Hij.
assert (L:((i=i0)/\(j=m-j0) \/ ((j<>(m-j0)) \/ (i<>i0)))%nat)
 by omega.
destruct L as [[Hi Hj] | L].
 clear IHl0.
 rewrite Hi, Hj in Hx'.
 rewrite Hi, Hj in Hy'.
 unfold fst, snd in *.
 apply existsWeaken.
 exists a.
 change (ms Q2) in a.
 split.
  rapply orWeaken.
  left.
  reflexivity.
 destruct a as [ax ay].
 destruct (Hf' ax ay) as [Hax Hay].
  rapply orWeaken;left;change (ax, ay) with ((ax,ay):Q2);reflexivity.
 clear Hf'.
 split.
  unfold fst.
  rewrite Hx'.
  apply ball_sym.
  eapply ball_weak_le.
   unfold err.
   apply Qpos_max_ub_l.
  rapply rasterization_error.
  auto.
 unfold snd.
 rewrite Hy'.
 apply ball_sym.
 eapply ball_weak_le.
  unfold err.
  apply Qpos_max_ub_r.
 fold (C t b (S m) (m - j0)%nat).
 simpl (ball (m:=Q_as_MetricSpace)).
 rewrite switch_line_interp;[|unfold j0; auto with *].
 rapply rasterization_error.
 auto.
assert (L0:existsC (Q * Q)
         (fun p : Q * Q =>
          InFinEnumC (X:=ProductMS Q_as_MetricSpace Q_as_MetricSpace) p l0 /\
          ball (m:=ProductMS Q_as_MetricSpace Q_as_MetricSpace) err p
            (x, y))).
 apply IHl0.
  simpl in Hij.
  rewrite setRaster_correct2 in Hij; auto.
 intros c d Hcd.
 apply Hf'.
 rapply orWeaken; right; auto.
destruct L0 as [G | z [Hz0 Hz1]] using existsC_ind.
 auto using existsC_stable.
apply existsWeaken.
exists z.
split; auto.
rapply orWeaken.
right; auto.
Qed.

Lemma RasterizeQ2_correct : 
 ball err
  (InterpRaster (RasterizeQ2 f (S n) (S m) t l b r) (l,t) (r,b))
  f.
Proof.
split; intros [x y] Hx.
 destruct (RasterizeQ2_correct2 Hx) as [ G | z [Hz0 Hz1]] using existsC_ind.
  auto using existsC_stable.
 apply existsWeaken.
 exists z.
 split; auto.
 auto using ball_sym.
destruct (RasterizeQ2_correct1 Hx) as [ G | z [Hz0 Hz1]] using existsC_ind.
 auto using existsC_stable.
apply existsWeaken.
exists z.
split; auto.
auto using ball_sym.
Qed.

End RasterizeCorrect.
