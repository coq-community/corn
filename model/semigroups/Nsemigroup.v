(* $Id$ *)

Require Export Nsetoid.
Require Import CSemiGroups.

(** *Example of a semi-group: <N,+>
*)

(** Because addition is associative, the natural numbers form a CSemiGroup.
*)

Definition nat_as_CSemiGroup :=
  Build_CSemiGroup nat_as_CSetoid plus_is_bin_fun plus_is_assoc.
