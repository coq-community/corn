
(* $Id$ *)

Require Import CGroups.
Require Export Nposmonoid.

(** **Non-example of a group: $\langle$#&lang;#[Npos],[[+]]$\rangle$#&rang;#
There is no inverse for multiplication on the positive natural numbers.
*)

Lemma no_inverse_Nposmult : forall inv : CSetoid_un_op Npos,
 ~ is_inverse Npos_mult ONEpos TWOpos (inv TWOpos).
intro inv.
red in |- *.
unfold is_inverse in |- *.
intro H.
elim H.
clear H.
intros H1 H2.
clear H2.
set (H3 := no_inverse_Nposmult1) in *.
elim (H3 (inv TWOpos)).
exact H1.
Qed.

(** Hence the natural numbers with multiplication do not form a group.
*)

Lemma no_group_Nposmult : forall inv : CSetoid_un_op Nposmult_as_CMonoid,
 ~ is_CGroup Nposmult_as_CMonoid inv.
simpl in |- *.
intro inv.
red in |- *.
unfold is_CGroup in |- *.
intro H.
set
 (H0 :=
  H (Build_subcsetoid_crr nat_as_CSetoid (fun n : nat => n <> 0) 2 (S_O 1)))
 in *.
set (H1 := no_inverse_Nposmult inv) in *.
apply H1.
exact H0.
Qed.
