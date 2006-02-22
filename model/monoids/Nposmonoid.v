(* $Id: Nposmonoid.v,v 1.6 2004/04/08 08:20:33 lcf Exp $ *)

Require Export Npossemigroup.
Require Import CMonoids.

(** **Example of a monoid: $\langle$#&lang;#[Npos],[[*]]$\rangle$#&rang;#
One is the right unit as well as the left unit of the multiplication on the
positive natural numbers.
*)

Lemma rhtunitNpos : is_rht_unit Npos_mult ONEpos.
unfold is_rht_unit in |- *.
unfold Npos_mult in |- *.
intro x.
case x.
simpl in |- *.
intros scs_elem H.
auto with arith.
Qed.

Lemma lftunitNpos : is_lft_unit Npos_mult ONEpos.
unfold is_rht_unit in |- *.
unfold Npos_mult in |- *.
intro x.
case x.
simpl in |- *.
intros scs_elem H.
auto with arith.
Qed.

(** So, the positive natural numbers with multiplication form a CMonoid.
*)

Definition Nposmult_is_CMonoid := Build_is_CMonoid
 Nposmult_as_CSemiGroup ONEpos rhtunitNpos lftunitNpos.

Definition Nposmult_as_CMonoid := Build_CMonoid
 Nposmult_as_CSemiGroup ONEpos Nposmult_is_CMonoid.
