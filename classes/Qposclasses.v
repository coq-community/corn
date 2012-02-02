(* todo: remove *)

Require Export Qpossec.
Require Import abstract_algebra additional_operations stdlib_rationals.

Instance: Equiv Qpos := QposEq.
Instance: One Qpos := Qpos_one.
Instance: Plus Qpos := Qpos_plus.
Instance: Mult Qpos := Qpos_mult.

Instance: Pow Qpos Z := Qpos_power.

Instance inject_Qpos_Q: Cast Qpos Q := QposAsQ.

Instance: ∀ x : Qpos, PropHolds (0 < (x:Q)).
Proof. intros x. now destruct x. Qed.