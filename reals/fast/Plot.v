Require Export RasterizeQ.
Require Import Interval.
Require Import Graph.
Require Import QMinMax.
Require Export QposMinMax.
Require Import CornTac.

Section Plot.

Variable (l r:Q).
Hypothesis Hlr : l < r.

Variable (b t:Q).
Hypothesis Hbt : b < t.

Open Local Scope uc_scope.

Let clip := uc_compose (boundBelow b) (boundAbove t).

Variable f : Q_as_MetricSpace --> CR.

Lemma plFEQ : PrelengthSpace (FinEnum stableQ).
Proof.
apply FinEnum_prelength.
 apply locatedQ.
apply QPrelengthSpace.
Qed.

Definition graphQ f := CompactGraph_b f stableQ2 plFEQ (CompactIntervalQ (Qlt_le_weak _ _ Hlr)).

Lemma graphQ_bonus : forall e x y, 
 In (x, y) (approximate (graphQ (uc_compose clip f)) e) -> l <= x <= r /\ b <= y <= t.
Proof.
intros [e|] x y;[|intros; contradiction].
simpl.
unfold Cjoin_raw.
Opaque  CompactIntervalQ.
simpl.
unfold FinCompact_raw.
rewrite map_map.
rewrite in_map_iff.
unfold graphPoint_b_raw.
simpl.
unfold Strength_raw.
simpl.
intros [z [Hz0 Hz1]].
inversion Hz0.
rewrite <- H0.
clear Hz0 x y H0 H1.
split; auto with *.
eapply CompactIntervalQ_bonus_correct.
apply Hz1.
Qed.

Variable n m : nat.
Hypothesis Hn : eq_nat n 0 = false.
Hypothesis Hm : eq_nat m 0 = false.

Let w := proj1_sigT _ _ (Qpos_lt_plus Hlr).
Let h := proj1_sigT _ _ (Qpos_lt_plus Hbt).

(*
Variable err : Qpos.
*)
Let err := Qpos_max ((1 # 4 * P_of_succ_nat n) * w) 
 ((1 # 4 * P_of_succ_nat m) * h).
 
Definition PlotQ := RasterizeQ2 (approximate (graphQ (uc_compose clip f)) err) n m t l b r.  

Open Local Scope raster.

Theorem Plot_correct : 
ball (err + Qpos_max ((1 # 2 * P_of_succ_nat (pred n)) * w)
        ((1 # 2 * P_of_succ_nat (pred m)) * h))
 (graphQ (uc_compose clip f))
 (Cunit (InterpRaster PlotQ (l,t) (r,b))).
Proof.
assert (Hw:=(ProjT2 (Qpos_lt_plus Hlr))).
assert (Hh:=(ProjT2 (Qpos_lt_plus Hbt))).
fold w in Hw.
fold h in Hh.
simpl in Hw, Hh.
apply ball_triangle with (Cunit (approximate (graphQ (uc_compose clip f)) err)).
 rapply ball_approx_r.
unfold Compact.
rewrite ball_Cunit.
apply ball_sym.
assert (L:ms_eq ((l,t):Q2) (l,b + h)).
 split; simpl.
  reflexivity.
 auto.
set (Z0:=(Pair l t):Q2) in *.
set (Z1:=(Pair r b):Q2) in *.
set (Z:=(Pair l (b + h)):Q2) in *.
rewrite L.
setoid_replace Z1 with (l+w,b) using relation ms_eq.
 unfold Z, PlotQ.
 rewrite Hw, Hh.
 destruct n; try discriminate.
 destruct m; try discriminate.
 apply (RasterizeQ2_correct).
 intros.
 rewrite <- Hw.
 rewrite <- Hh.
 destruct (InStrengthen _ _ H) as [[zx xy] [Hz0 [Hz1 Hz2]]].
 simpl in Hz1, Hz2.
 rewrite Hz1, Hz2.
 eapply graphQ_bonus.
 apply Hz0.
split; simpl; auto with *.
Qed.

End Plot.

Notation "'graphCR' f [ l '..' r ]" := 
 (graphQ l r (refl_equal _) f) : raster.
