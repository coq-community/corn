(* todo: remove *)

Require Export CoRN.model.structures.Qpossec.
Require Import MathClasses.interfaces.abstract_algebra MathClasses.interfaces.additional_operations MathClasses.implementations.stdlib_rationals.

#[global]
Instance: Equiv Qpos := QposEq.
#[global]
Instance: One Qpos := Qpos_one.
#[global]
Instance: Plus Qpos := Qpos_plus.
#[global]
Instance: Mult Qpos := Qpos_mult.

#[global]
Instance: Pow Qpos Z := Qpos_power.

#[global]
Instance inject_Qpos_Q: Cast Qpos Q := QposAsQ.

#[global]
Instance: ∀ x : Qpos, PropHolds (0 < (x:Q)).
Proof. intros x. now destruct x. Qed.
