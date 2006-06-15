(* $Id$ *)

Require Export Zsetoid.
Require Export CSemiGroups.

(** **Examples of semi-groups: $\langle$#&lang;#[Z],[[+]]$\rangle$#&rang;# and $\langle$#&lang;#[Z],[[*]]$\rangle$#&rang;#
***$\langle$#&lang;#[Z],[[+]]$\rangle$#&rang;#
*)

Lemma Zplus_is_CSemiGroup: (is_CSemiGroup Z_as_CSetoid Zplus_is_bin_fun).
unfold is_CSemiGroup.
exact Zplus_is_assoc.
Qed.

Definition Z_as_CSemiGroup := Build_CSemiGroup _ Zplus_is_bin_fun Zplus_is_assoc.

(** The term [Z_as_CSemiGroup] is of type [CSemiGroup]. Hence we have proven that [Z] is a constructive semi-group. *)

(** ***$\langle$#&lang;#[Z],[[*]]$\rangle$#&rang;#
*)

Lemma Zmult_is_CSemiGroup: (is_CSemiGroup Z_as_CSetoid Zmult_is_bin_fun).
unfold is_CSemiGroup.
exact Zmult_is_assoc.
Qed.

Definition Z_mul_as_CSemiGroup := Build_CSemiGroup _ Zmult_is_bin_fun Zmult_is_assoc.




