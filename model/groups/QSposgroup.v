(* $Id$ *)

Require Export QSposmonoid.
Require Import CGroups.

(** **Example of a group: $\langle$#&lang;#[Qpos],$(x,y) \mapsto xy/2$ #(x,y) &#x21A6; xy/2#$\rangle$#&rang;#
The positive rationals form with the operation  $(x,y) \mapsto xy/2$ 
#(x,y) &#x21A6; xy/2# a CGroup.
*)

Lemma Qpos_multdiv2_is_CGroup : is_CGroup Qpos_multdiv2_as_CMonoid divmult4.
intro x; case x; simpl; apply multdiv2_is_inv.
Qed.

Definition Qpos_multdiv2_as_CGroup := Build_CGroup
 Qpos_multdiv2_as_CMonoid divmult4 Qpos_multdiv2_is_CGroup.
