
(* $Id$ *)

Require Export Qpossemigroup.
Require Import CMonoids.

(** *Example of a monoid: <$\mathbb{Q}^{+}$ #Q<SUP>+</SUP>#,*>
*)

(** One is the unit for multiplication on positive integers. Therefore the positive rational numbers together with the multiplication are a CMonoid.
*)

Lemma QONEpos_is_rht_unit : is_rht_unit Qpos_mult QONEpos.
unfold is_rht_unit in |- *.
simpl in |- *.
intro x.
case x.
simpl in |- *.
intros e H.
apply Qmult_n_1.
Qed.

Lemma QONEpos_is_lft_unit : is_lft_unit Qpos_mult QONEpos.
unfold is_lft_unit in |- *.
simpl in |- *.
intro x.
case x.
simpl in |- *.
intros e H.
cut (Q.ONE{*Q}e{=Q}e{*Q}Q.ONE).
intro H0.
apply trans_Qeq with (e{*Q}Q.ONE).
exact H0.
apply Qmult_n_1.
apply Qmult_sym.
Qed.


Definition Qpos_mult_is_CMonoid :=
  Build_is_CMonoid Qpos_mult_as_CSemiGroup QONEpos QONEpos_is_rht_unit
    QONEpos_is_lft_unit.

Definition Qpos_mult_as_CMonoid :=
  Build_CMonoid Qpos_mult_as_CSemiGroup QONEpos Qpos_mult_is_CMonoid.
