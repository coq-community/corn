Require Import Coq.QArith.Qround.
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
Variable n : nat.

Lemma wpos : 0 < r - l.
Proof.
  apply Qlt_minus_iff in Hlr. exact Hlr.
Qed.

Lemma hpos : 0 < t - b.
Proof.
  apply Qlt_minus_iff in Hbt. exact Hbt.
Qed.

(* Compute the number of pixels on the Y-axis to make square pixels. *)
Let m : nat := Z.to_nat (Qceiling ((t-b) * inject_Z (Z.of_nat n) / (r-l))).

(**
Half the error in the Plot example, since we need to approximate twice.
*)
Let err := Qpos_max ((1 # 8 * P_of_succ_nat (pred n)) * (exist _ _ wpos))
                    ((1 # 8 * P_of_succ_nat (pred m)) * (exist _ _ hpos)).

Variable path:AQ_as_MetricSpace --> Complete (ProductMS AQ_as_MetricSpace AQ_as_MetricSpace).

(** The actual plot function *)
Definition PlotPath : nat * nat * Q * raster n m
  := (n, m, 2#1,
      RasterizeQ2 
        (map (fun x :Complete (ProductMS AQ_as_MetricSpace AQ_as_MetricSpace)
              => (let (a,b) := approximate x err in (AQtoQ a, AQtoQ b)))
             (map path (approximate (IabCompact _ _ Hfromto)
                                    (FinEnum_map_modulus (1 # 1) (mu path) err))))
        n m t l b r).

End PlotPath.
