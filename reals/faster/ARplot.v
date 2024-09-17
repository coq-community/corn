From Coq Require Import Qround.
Require Import CoRN.reals.fast.Plot.
Require Import CoRN.reals.faster.ARArith.
Require Import CoRN.reals.faster.ARinterval.
Require Import CoRN.model.metric2.Qmetric.

Local Open Scope uc_scope.

Section PlotPath.
Context `{AppRationals AQ}.

Variable (from to:Q).
Hypothesis Hfromto:from<=to.

Variable (l r:Q).
Hypothesis Hlr : l < r.

Variable (b t:Q).
Hypothesis Hbt : b < t.

(* Number of pixels on the X-axis. *)
Variable n : positive.

Lemma wpos : 0 < r - l.
Proof.
  apply Qlt_minus_iff in Hlr. exact Hlr.
Qed.

Lemma hpos : 0 < t - b.
Proof.
  apply Qlt_minus_iff in Hbt. exact Hbt.
Qed.

(* Compute the number of pixels on the Y-axis to make square pixels. *)
Let m : positive := Z.to_pos (Qceiling ((t-b) * inject_Z (Z.pos n) / (r-l))).

(**
Half the error in the Plot example, since we need to approximate twice.
*)
Let err := Qpos_max ((1 # 8 * n) * (exist _ _ wpos))
                    ((1 # 8 * m) * (exist _ _ hpos)).

Variable path:AQ_as_MetricSpace --> Complete (ProductMS AQ_as_MetricSpace AQ_as_MetricSpace).

(** The actual plot function *)
Definition PlotPath : positive * positive * Q * sparse_raster n m
  := (n, m, 2,
      let num := (Z.to_pos
                    (Qceiling
                       ((to - from) /
                                    (inject_Z 2 *
                                     ((1 # 2) *
                                      ` (FinEnum_map_modulus 
                                           (1 # 1)%Qpos 
                                           (mu path) err)))))) in
    sparse_raster_data n m
      (map
         (λ x : Z,
            rasterize2 n m t l b r
              (let (a, b0) :=
                 approximate
                    (path
                      (AppInverse0
                         (from +
                          (to - from) * (2 * x + 1 # 1) /
                          (2 *
                           Z.pos num # 1))
                         ((1 # 2)%Qpos *
                          FinEnum_map_modulus (1#1)%Qpos (mu path) err)%Qpos))
               err in
               (AQtoQ a, AQtoQ b0))) (* TODO rasterize2AQ *)
         (Interval.iterateN_succ 0 num))).

Definition PlotPath_slow : positive * positive * Q * sparse_raster n m
  := (n, m, 2#1,
 sparse_raster_data n m
    (map
       (λ x : AQ_as_MetricSpace,
          rasterize2 n m t l b r
            (let (a, b0) := approximate (path x) err in (AQtoQ a, AQtoQ b0)))
       (approximate (IabCompact from to Hfromto)
          (FinEnum_map_modulus (1 # 1) (mu path) err)))).

Lemma PlotPath_correct : eq PlotPath PlotPath_slow.
Proof.
  unfold PlotPath_slow. unfold IabCompact, approximate.
  rewrite map_map.
  unfold Interval.UniformPartition.
  rewrite map_map.
  reflexivity.
Qed.

End PlotPath.
