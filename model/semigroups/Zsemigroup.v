(* $Id$ *)

Require Export Zsetoid.
Require Import CSemiGroups.

(** *Examples of a semi-group: <Z,+> and <Z,*>
*)

(** **<Z,+>
*)

Definition Z_as_CSemiGroup :=
  Build_CSemiGroup Z_as_CSetoid Zplus_is_bin_fun Zplus_is_assoc.

(** The term [Z_as_CSemiGroup] is of type [CSemiGroup]. Hence we have proven that [Z] is a constructive semi-group. *)

(** **<Z,*>
*)

Definition Z_mul_as_CSemiGroup :=
  Build_CSemiGroup Z_as_CSetoid Zmult_is_bin_fun Zmult_is_assoc.
