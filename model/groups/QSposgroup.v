(* $Id$ *)

Require Export QSposmonoid.
Require Import CGroups.

(** *Example of a group: <$\mathbb{Q}^{+}$ #Q<SUP>+</SUP>#,$(x,y) \mapsto xy/2$ #(x,y) &#x21A6; xy/2#>
*)

(** The positive rationals form with the operation  $(x,y) \mapsto xy/2$ 
#(x,y) &#x21A6; xy/2# a CGroup.
*)

Lemma Qpos_multdiv2_is_CGroup : is_CGroup Qpos_multdiv2_as_CMonoid divmult4.
unfold is_CGroup in |- *.
unfold is_inverse in |- *.
intros x.
unfold divmult4 in |- *.
case x.
simpl in |- *.
apply multdiv2_is_inv.
Qed.

Definition Qpos_multdiv2_as_CGroup :=
  Build_CGroup Qpos_multdiv2_as_CMonoid divmult4 Qpos_multdiv2_is_CGroup.
