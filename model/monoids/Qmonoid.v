
(* $Id$ *)

Require Export Qsemigroup.
Require Import CMonoids.

(** *Examples of a monoid: <Q,+> and <Q,*>
*)

(** **<Q,+>
*)

(** The rational numbers form with addition a CMonoid. Zero is the unit.
*)

Lemma ZEROQ_as_rht_unit3 :
 is_rht_unit (S:=Q_as_CSetoid) Qplus_is_bin_fun Q.ZERO.
Proof.
red in |- *.
simpl in |- *.
apply ZEROQ_as_rht_unit0.
Qed.

Lemma ZEROQ_as_lft_unit3 :
 is_lft_unit (S:=Q_as_CSetoid) Qplus_is_bin_fun Q.ZERO.
Proof.
red in |- *.
simpl in |- *.
apply ZEROQ_as_lft_unit0.
Qed.

Definition Q_is_CMonoid :=
  Build_is_CMonoid Q_as_CSemiGroup _ ZEROQ_as_rht_unit3 ZEROQ_as_lft_unit3.

Definition Q_as_CMonoid := Build_CMonoid Q_as_CSemiGroup _ Q_is_CMonoid.

(** **<Q,*>
*)

(** Also with multiplication Q forms a CMonoid. Here, the unit is one.
*)

Lemma ONEQ_as_rht_unit : is_rht_unit (S:=Q_as_CSetoid) Qmult_is_bin_fun Q.ONE.
Proof.
red in |- *.
simpl in |- *.
exact Qmult_n_1.
Qed.

Lemma ONEQ_as_lft_unit : is_lft_unit (S:=Q_as_CSetoid) Qmult_is_bin_fun Q.ONE.
Proof.
red in |- *.
intro.
eapply eq_transitive_unfolded.
apply Qmult_is_commut.
apply ONEQ_as_rht_unit.
Qed.

Definition Q_mul_is_CMonoid :=
  Build_is_CMonoid Q_mul_as_CSemiGroup _ ONEQ_as_rht_unit ONEQ_as_lft_unit. 

Definition Q_mul_as_CMonoid :=
  Build_CMonoid Q_mul_as_CSemiGroup _ Q_mul_is_CMonoid.
