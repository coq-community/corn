

Require Export Zmonoid.
Require Import CGroups.

(** **Example of a group: $\langle$#&lang;#[Z],[[+]]$\rangle$#&rang;#
*)

Lemma Z_is_CGroup : is_CGroup Z_as_CMonoid Zopp_is_fun. 
Proof.
red in |- *.
simpl in |- *.
intro x.
split; simpl in |- *.
apply Zplus_opp_r.
apply Zplus_opp_l.
Qed.

Definition Z_as_CGroup := Build_CGroup Z_as_CMonoid Zopp_is_fun Z_is_CGroup.

(** The term [Z_as_CGroup] is of type [CGroup]. Hence we have proven that [Z] is a constructive group. *)
