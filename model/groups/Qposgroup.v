(* $Id$ *)

Require Export Qposmonoid.
Require Export CGroups.

(** *Example of a group: <$\mathbb{Q}^{+}$ #Q<SUP>+</SUP>#,*>
*)

(** The positive rational numbers form a multiplicative group.
*)

Lemma Qpos_is_CGroup : is_CGroup Qpos_mult_as_CMonoid Qpos_Qpos_inv_op.
unfold is_CGroup in |- *.
unfold Qpos_Qpos_inv_op in |- *.
simpl in |- *.
intro x.
case x.
simpl in |- *.
unfold is_inverse in |- *.
simpl in |- *.
intros y H.
apply Qinv_is_inv.
Qed.


Definition Qpos_as_CGroup :=
  Build_CGroup Qpos_mult_as_CMonoid Qpos_Qpos_inv_op Qpos_is_CGroup.
