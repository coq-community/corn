
Require Export Qsetoid.
Require Import CSemiGroups.

(** **Examples of semi-groups: $\langle$#&lang;#[Q],[[+]]$\rangle$#&rang;# and $\langle$#&lang;#[Q],[[*]]$\rangle$#&rang;#
***$\langle$#&lang;#[Q],[[+]]$\rangle$#&rang;#
*)

Definition Q_as_CSemiGroup := Build_CSemiGroup _ Qplus_is_bin_fun Qplus_is_assoc.

(** ***$\langle$#&lang;#[Q],[[*]]$\rangle$#&rang;#
*)

Definition Q_mul_as_CSemiGroup := Build_CSemiGroup _ Qmult_is_bin_fun Qmult_is_assoc.
