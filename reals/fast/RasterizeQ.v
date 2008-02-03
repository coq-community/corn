Require Export RasterQ.
Require Import Interval.
Require Import Classic.
Require Import QposMinMax.
Require Import Qabs.
Require Import Qauto.
Require Import Qround.
Require Import CornTac.

Set Implicit Arguments.

(** In this implemenation of Rasterization, I choose to push all points inside the raster *)

Definition RasterizePoint (t l b r:Q) n m (bm:raster n m) (p:Q*Q) : raster n m :=
let i := min (pred n) (Z_to_nat (Zle_max_l 0 (rasterize1 l r n (fst p)))) in
let j := min (pred m) (Z_to_nat (Zle_max_l 0 (rasterize1 b t m (snd p)))) in
setRaster bm true (pred m - j) i.

Lemma RasterizePoint_carry : forall t l b r n m (bm:raster n m) p i j,
 Is_true (RasterIndex bm i j) -> Is_true (RasterIndex (RasterizePoint t l b r bm p) i j).
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

(* This function could be a bit more efficent by sorting x *)
Definition RasterizeQ2 (f:FinEnum stableQ2) (t l b r:Q) n m : raster n m :=
fold_left (fun x y => @RasterizePoint t l b r n m x y) f (emptyRaster _ _).

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
  rewrite Qabs_pos;[|apply Qle_refl].
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

Lemma RasterizeQ2_correct1 : forall x y,
 InFinEnumC ((x,y):ProductMS _ _) f -> 
 existsC (ProductMS _ _) 
  (fun p => InFinEnumC p (InterpRaster (l,t) (r,b) (RasterizeQ2 f t l b r (S n) (S m)))
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
simpl ((ms (ProductMS Q_as_MetricSpace Q_as_MetricSpace))).
generalize (emptyRaster (S n) (S m)).
induction (@rev (prod Q Q) f).
 contradiction.
intros bm H.
destruct H as [G | [Hl Hr] | H] using orC_ind.
  auto using existsC_stable.
 simpl in Hl, Hr.
 simpl (fold_right
           (fun (y0 : Q * Q) (x0 : raster (S n) (S m)) =>
            RasterizePoint t l b r x0 y0) bm (a :: l0)).
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
 setoid_replace (C t b (S m) (m - j)%nat) with
  (C b t (S m) j).
  rapply rasterization_error.
  simpl in Hr.
  rewrite Hr in Hfr.
  auto.
 unfold C.
 rewrite inj_minus1;[|unfold j; auto with *].
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
simpl ((fold_right
        (fun (y : Q * Q) (x : raster (S n) (S m)) =>
         RasterizePoint t l b r x y) bm) (a :: l0)).
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

Definition foo := Pair (-58 # 60) (-5 # 21)
       :: Pair (-54 # 60) (-9 # 21)
          :: Pair (-50 # 60) (-12 # 21)
             :: Pair (-46 # 60) (-15 # 21)
                :: Pair (-42 # 60) (-18 # 21)
                   :: Pair (-38 # 60) (-19 # 21)
                      :: Pair (-34 # 60) (-20 # 21)
                         :: Pair (-30 # 60) (-20 # 21)
                            :: Pair (-26 # 60) (-20 # 21)
                               :: Pair (-22 # 60) (-18 # 21)
                                  :: Pair (-18 # 60) (-1557 # 2000)
                                     :: Pair (-14 # 60) (-7 # 10)
                                        :: Pair (-10 # 60) (-1 # 2)
                                           :: Pair (-6 # 60) (-3 # 10)
                                              :: Pair (-2 # 60) 0
                                                 :: Pair (2 # 60) 0
                                                    :: Pair (6 # 60) (3 # 10)
                                                       :: Pair (10 # 60)
                                                            (1 # 2)
                                                          :: Pair (14 # 60)
                                                               (7 # 10)
                                                             :: Pair
                                                                  (18 # 60)
                                                                  (1557
                                                                   # 2000)
                                                                :: Pair
                                                                    (22 # 60)
                                                                    (18 # 21)
                                                                   :: 
                                                                   Pair
                                                                    (26 # 60)
                                                                    (20 # 21)
                                                                   :: 
                                                                   Pair
                                                                    (30 # 60)
                                                                    (20 # 21)
                                                                   :: 
                                                                   Pair
                                                                    (34 # 60)
                                                                    (20 # 21)
                                                                   :: 
                                                                   Pair
                                                                    (38 # 60)
                                                                    (19 # 21)
                                                                   :: 
                                                                   Pair
                                                                    (42 # 60)
                                                                    (18 # 21)
                                                                   :: 
                                                                   Pair
                                                                    (46 # 60)
                                                                    (15 # 21)
                                                                   :: 
                                                                   Pair
                                                                    (50 # 60)
                                                                    (12 # 21)
                                                                   :: 
                                                                   Pair
                                                                    (54 # 60)
                                                                    (9 # 21)
                                                                   :: 
                                                                   Pair
                                                                    (58 # 60)
                                                                    (5 # 21)
                                                                   :: nil.

Open Local Scope raster.
Eval vm_compute in RasterizeQ2 foo 1 (-(1)) (-(1)) 1 10 10.
