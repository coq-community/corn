

Require Export Qposgroup.
Require Import CAbGroups.

(** **Example of an abelian group: $\langle$#&lang;#[Qpos],[[*]]$\rangle$#&rang;#
The positive rationals form with the multiplication a CAbgroup.
*)

Definition Qpos_mult_is_CAbGroup : is_CAbGroup Qpos_as_CGroup.
unfold is_CAbGroup in |- *.
unfold commutes in |- *.
intros x y.
case x.
case y.
simpl in |- *.
intros x0 Hx y1 Hy.
apply Qmult_sym.
Qed.

Definition Qpos_mult_as_CAbGroup := Build_CAbGroup
 Qpos_as_CGroup Qpos_mult_is_CAbGroup.
