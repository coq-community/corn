(* $Id$ *)


Require Export Nmonoid.
Require Import CGroups.

(** **Non-example of a group: $\langle$#&lang;#[nat],[[+]]$\rangle$#&rang;#
There is no inverse function for the natural numbers with addition.
*)

Lemma no_inverse_nat_plus : forall inv : CSetoid_un_op nat_as_CSetoid,
 ~ is_inverse (csg_op (c:=nat_as_CSemiGroup)) 0 2 (inv 2).
simpl in |- *.
unfold plus_is_bin_fun in |- *.
intro inv.
case inv.
unfold is_inverse in |- *.
simpl in |- *.
intros a1 a2. 
generalize no_inverse0.
simpl in |- *.
intuition.
Qed.

(** Hence they do not form a CGroup.
*)

Lemma no_group_nat_plus : forall inv : CSetoid_un_op nat_as_CMonoid,
 ~ is_CGroup nat_as_CMonoid inv.
simpl in |- *.
intro inv.
red in |- *.
unfold is_CGroup in |- *.
intro H.
set (H0 := H 2) in *.
set (H1 := no_inverse_nat_plus inv) in *.
apply H1.
exact H0.
Qed.
