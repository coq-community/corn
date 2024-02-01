Require Import 
  CoRN.model.totalorder.QMinMax
  MathClasses.interfaces.orders
  MathClasses.interfaces.abstract_algebra
  MathClasses.orders.minmax.
Require Export 
  MathClasses.implementations.stdlib_rationals.

Lemma Qmin_coincides x y : Qmin x y = x ⊓ y.
Proof.
  destruct (total (≤) x y).
   rewrite lattices.meet_l by easy. now apply Qle_min_l.
  rewrite lattices.meet_r by easy. now apply Qle_min_r.
Qed.

Lemma Qmax_coincides x y : Qmax x y = x ⊔ y.
Proof.
  destruct (total (≤) x y).
   rewrite lattices.join_r by easy. now apply Qle_max_r.
  rewrite lattices.join_l by easy. now apply Qle_max_l.
Qed.
