

Require Export QSpossemigroup.
Require Import CMonoids.

(** **Example of a monoid: $\langle$#&lang;#[Qpos],$(x,y) \mapsto xy/2$ #(x,y) &#x21A6; xy/2#$\rangle$#&rang;#
Two is the unit of the operation  $(x,y) \mapsto xy/2$ #(x,y) 
  &#x21A6; xy/2# on the positive rationals. So we have another monoid structure on the positive rational numbers.
*)                              

Lemma QTWOpos_is_rht_unit : is_rht_unit multdiv2 QTWOpos.
unfold is_rht_unit in |- *.
intro x.
case x.
simpl in |- *.
apply QTWOpos_is_rht_unit0.
Qed.

Lemma QTWOpos_is_lft_unit : is_lft_unit multdiv2 QTWOpos.
unfold is_lft_unit in |- *.
intro x.
case x.
simpl in |- *.
apply QTWOpos_is_left_unit0.
Qed.

Definition Qpos_multdiv2_is_CMonoid := Build_is_CMonoid
 Qpos_multdiv2_as_CSemiGroup QTWOpos QTWOpos_is_rht_unit QTWOpos_is_lft_unit.

Definition Qpos_multdiv2_as_CMonoid := Build_CMonoid
 Qpos_multdiv2_as_CSemiGroup QTWOpos Qpos_multdiv2_is_CMonoid.
