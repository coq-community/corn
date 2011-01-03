Require Import Qpossec.
Require Import canonical_names.

Instance: RingOne Qpos := Qpos_one.
Instance: RingPlus Qpos := Qpos_plus.
Instance: RingMult Qpos := Qpos_mult.