(* $Id$ *)

Require Export Qmonoid.
Require Import CGroups.

(** **Example of a group: $\langle$#&lang;#[Q],[[+]]$\rangle$#&rang;#
The rational numbers with addition form a group. The inverse function is taking the opposite.
*)

Lemma Q_is_CGroup : is_CGroup Q_as_CMonoid Qopp_is_fun.
Proof.
red in |- *.
split.
apply Qplus_inverse_r.
eapply eq_transitive_unfolded.
apply Qplus_is_commut0.
apply Qplus_inverse_r.
Qed.

Definition Q_as_CGroup := Build_CGroup Q_as_CMonoid Qopp_is_fun Q_is_CGroup.
