(* $Id$ *)

Require Export Npossetoid.
Require Export CSemiGroups.
Require Import Nsemigroup.

(** *Examples of a semi-group:  <$\mathbb{N}^{+}$ #N<SUP>+</SUP>#,+> and <$\mathbb{N}^{+}$ #N<SUP>+</SUP>#,*>
*)

(** **<$\mathbb{N}^{+}$ #N<SUP>+</SUP>#,+>
*)

(** The positive natural numbers form together with addition a subsemigroup 
 of the semigroup of the natural numbers with addition.
*)

Definition Npos_as_CSemiGroup :=
  Build_SubCSemiGroup nat_as_CSemiGroup (fun n : nat => n <> 0)
    plus_resp_Npos.

(** **<$\mathbb{N}^{+}$ #N<SUP>+</SUP>#,*>
*)

(** Also together with multiplication, the positive numbers form a semigroup.
*)

Lemma Nposmult_is_CSemiGroup : is_CSemiGroup Npossetoid.Npos Npos_mult.
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

Definition Nposmult_as_CSemiGroup :=
  Build_CSemiGroup Npossetoid.Npos Npos_mult Nposmult_is_CSemiGroup.
