(* $Id$ *)

Require Export Qsetoid.
Require Import CSemiGroups.

(** *Examples of a semi-group: <Q,+> and <Q,*>
*)

(** **<Q,+>
*)

Definition Q_as_CSemiGroup :=
  Build_CSemiGroup Q_as_CSetoid Qplus_is_bin_fun Qplus_is_assoc.

(** **<Q,*>
*)

Definition Q_mul_as_CSemiGroup :=
  Build_CSemiGroup Q_as_CSetoid Qmult_is_bin_fun Qmult_is_assoc.
