Require Export Qpossec.
Require Import abstract_algebra additional_operations stdlib_rationals.

Instance: Equiv Qpos := QposEq.
Instance: RingOne Qpos := Qpos_one.
Instance: RingPlus Qpos := Qpos_plus.
Instance: RingMult Qpos := Qpos_mult.

Instance: Pow Qpos Z := Qpos_power.

Instance inject_Qpos_Q: Coerce Qpos Q := QposAsQ.

Instance: ∀ x : Qpos, PropHolds (0 < (x:Q)).
Proof. intros x. red. auto. Qed.