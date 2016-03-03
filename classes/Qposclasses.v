(* todo: remove *)

Require Export CoRN.model.structures.Qpossec.
Require Import MathClasses.interfaces.abstract_algebra MathClasses.interfaces.additional_operations MathClasses.implementations.stdlib_rationals.

Instance: Equiv Qpos := QposEq.
Instance: One Qpos := Qpos_one.
Instance: Plus Qpos := Qpos_plus.
Instance: Mult Qpos := Qpos_mult.

Instance: Pow Qpos Z := Qpos_power.

Instance inject_Qpos_Q: Cast Qpos Q := QposAsQ.

Instance: ∀ x : Qpos, PropHolds (0 < (x:Q)).
Proof. intros x. now destruct x. Qed.