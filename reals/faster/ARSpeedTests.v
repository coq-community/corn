Require Import
  CoRN.model.totalorder.QposMinMax
  CoRN.algebra.RSetoid
  CoRN.metric2.Metric
  CoRN.metric2.Complete
  CoRN.reals.faster.ARexp
  CoRN.reals.faster.ARbigD.

(* Resolve type classes *)
Definition AQexpBigD : bigD -> st_car (msp_is_setoid ARbigD)
  := AQexp.

(* Some time measures on a 5000 bogomips CPU *)

Time Eval vm_compute in (approximate (AQexpBigD (cast _ _ 300%Z)) (Qpos2QposInf (1#1))).
(* 0.1 secs *)
