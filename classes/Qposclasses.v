Require Import Qpossec.
Require Import canonical_names additional_operations.

Instance: Equiv Qpos := QposEq.
Instance: RingOne Qpos := Qpos_one.
Instance: RingPlus Qpos := Qpos_plus.
Instance: RingMult Qpos := Qpos_mult.

Instance: Pow Qpos Z := Qpos_power.
