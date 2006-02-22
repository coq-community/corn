(* $Id: Npossemigroup.v,v 1.6 2004/04/08 08:20:34 lcf Exp $ *)

Require Export CSemiGroups.
Require Import Nsemigroup.
Require Export Npossetoid.

(** **Examples of semi-groups:  $\langle$#&lang;#[Npos],[[+]]$\rangle$#&rang;# and $\langle$#&lang;#[Npos],[[*]]$\rangle$#&rang;#
***$\langle$#&lang;#[Npos],[[+]]$\rangle$#&rang;#
The positive natural numbers form together with addition a subsemigroup 
 of the semigroup of the natural numbers with addition.
*)

Definition Npos_as_CSemiGroup := Build_SubCSemiGroup
 nat_as_CSemiGroup NposP plus_resp_Npos.

(** ***$\langle$#&lang;#[Npos],[[*]]$\rangle$#&rang;#
Also together with multiplication, the positive numbers form a semigroup.
*)

Lemma Nposmult_is_CSemiGroup : is_CSemiGroup Npos Npos_mult.
unfold is_CSemiGroup in |- *.
unfold associative in |- *.
unfold Npos_mult in |- *.
simpl in |- *.
intros x y z.
case x.
case y.
case z.
simpl in |- *.
intros a pa b pb c pc.
auto with arith.
Qed.

Definition Nposmult_as_CSemiGroup := Build_CSemiGroup
 Npos Npos_mult Nposmult_is_CSemiGroup.
