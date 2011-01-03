Require Import 
  QMinMax
  abstract_algebra
  minmax.
Require Export 
  stdlib_rationals.

Lemma Qmin_coincides x y : Qmin x y = min x y.
Proof with auto.
  destruct (total_order x y).
   rewrite min_l... apply Qle_min_l...
  rewrite min_r... apply Qle_min_r...
Qed.

Lemma Qmax_coincides x y : Qmax x y = max x y.
Proof with auto.
  destruct (total_order x y).
   rewrite max_r... apply Qle_max_r...
  rewrite max_l... apply Qle_max_l...
Qed.

