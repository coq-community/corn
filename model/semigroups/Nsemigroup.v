
Require Export Nsetoid.
Require Import CSemiGroups.

(** **Example of a semi-group: $\langle$#&lang;#[nat],[[+]]$\rangle$#&rang;#
*)

(** Because addition is associative, the natural numbers form a CSemiGroup.
*)

Definition nat_as_CSemiGroup := Build_CSemiGroup _ plus_is_bin_fun plus_is_assoc.

Lemma Nmult_is_CSemiGroup : is_CSemiGroup nat_as_CSetoid mult_as_bin_fun.
unfold is_CSemiGroup in |- *.
unfold associative in |- *.
unfold mult_as_bin_fun in |- *.
simpl in |- *.
auto with arith.
Qed.

Definition Nmult_as_CSemiGroup := Build_CSemiGroup
 nat_as_CSetoid mult_as_bin_fun Nmult_is_CSemiGroup.
