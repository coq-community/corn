(* $Id$ *)

Require Export Qpossetoid.
Require Export CSemiGroups.

(** *Example of a semi-group: <$\mathbb{Q}^{+}$ #Q<SUP>+</SUP>#,*>
*)

(** The positive rationals form with the multiplication a CSemiGroup.
*)

Definition Qpos_mult_as_CSemiGroup :=
  Build_CSemiGroup Qpos Qpos_mult associative_Qpos_mult.
