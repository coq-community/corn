(* $Id$ *)


Require Export Qsec.
Require Import CSetoidFun.

(** *Example of a setoid: Q
*)

(** **Q
*)
Lemma ap_Q_irreflexive1 : irreflexive (A:=Q.Q) Q.ap.
red in |- *.
apply ap_Q_irreflexive0.
Qed.

Lemma ap_Q_symmetric1 : Csymmetric Q.ap.
red in |- *.
apply ap_Q_symmetric0.
Qed.

Lemma ap_Q_cotransitive1 : cotransitive (A:=Q.Q) Q.ap.
red in |- *.
apply ap_Q_cotransitive0.
Qed.

Lemma ap_Q_tight1 : tight_apart (A:=Q.Q) Q.eq Q.ap.
red in |- *.
apply ap_Q_tight0.
Qed.

Definition ap_Q_is_apartness :=
  Build_is_CSetoid Q.Q Q.eq Q.ap ap_Q_irreflexive1 ap_Q_symmetric1
    ap_Q_cotransitive1 ap_Q_tight1.

Definition Q_as_CSetoid := Build_CSetoid Q.Q Q.eq Q.ap ap_Q_is_apartness.

(** **Addition
*)

Lemma Qplus_is_well_defined :
 bin_fun_well_def Q_as_CSetoid Q_as_CSetoid Q_as_CSetoid Q.plus.
Proof.
red in |- *.
simpl in |- *.
intros.
exact (Qplus_simpl x1 x2 y1 y2 H H0).
Qed.

Lemma Qplus_is_extensional1 :
 bin_fun_strong_ext Q_as_CSetoid Q_as_CSetoid Q_as_CSetoid Q.plus.
red in |- *.
simpl in |- *.
exact Qplus_is_extensional0.
Qed.

Definition Qplus_is_bin_fun :=
  Build_CSetoid_bin_fun Q_as_CSetoid Q_as_CSetoid Q_as_CSetoid Q.plus
    Qplus_is_extensional1.

(** It is associative and commutative.
*)

Lemma Qplus_is_assoc : associative Qplus_is_bin_fun.
Proof Qplus_assoc.


Lemma Qplus_is_commut1 : commutes Qplus_is_bin_fun.
Proof.
red in |- *.
simpl in |- *.
exact Qplus_is_commut0.
Qed.

(** **Opposite
*)

Lemma Qopp_is_well_defined :
 fun_well_def (S1:=Q_as_CSetoid) (S2:=Q_as_CSetoid) Q.opp.
Proof.
red in |- *.
simpl in |- *.
intros.
exact (Qopp_simpl x y H).
Qed.

Lemma Qopp_is_extensional :
 fun_strong_ext (S1:=Q_as_CSetoid) (S2:=Q_as_CSetoid) Q.opp.
Proof.
red in |- *.
simpl in |- *.
unfold Q.ap in |- *.
intros.
red in |- *.
intro H0.
apply X.
exact (Qopp_simpl x y H0).
Qed.

Definition Qopp_is_fun :=
  Build_CSetoid_fun Q_as_CSetoid Q_as_CSetoid Q.opp Qopp_is_extensional.

(** **Multiplication
*)

Lemma Qmult_is_well_defined :
 bin_fun_well_def Q_as_CSetoid Q_as_CSetoid Q_as_CSetoid Q.mult.
Proof.
red in |- *.
simpl in |- *.
intros.
apply Qmult_simpl.
assumption.
assumption.
Qed.

Lemma Qmult_is_extensional1 :
 bin_fun_strong_ext Q_as_CSetoid Q_as_CSetoid Q_as_CSetoid Q.mult.
Proof.
red in |- *.
simpl in |- *.
apply Qmult_is_extensional0.
Qed.

Definition Qmult_is_bin_fun :=
  Build_CSetoid_bin_fun Q_as_CSetoid Q_as_CSetoid Q_as_CSetoid Q.mult
    Qmult_is_extensional1.

(** It is associative and commutative.
*)

Lemma Qmult_is_assoc : associative Qmult_is_bin_fun.
Proof.
red in |- *.
intros x y z.
simpl in |- *.
apply Qmult_assoc.
Qed.

Lemma Qmult_is_commut : commutes Qmult_is_bin_fun.
Proof.
red in |- *.
simpl in |- *.
exact Qmult_sym.
Qed.

(** **Less-than
*)

Lemma Qlt_is_extensional : Crel_strong_ext Q_as_CSetoid Q.lt.
Proof.
red in |- *.
apply Qlt_is_extensional_unfolded.
Qed.

Definition Qlt_is_CSetoid_relation :=
  Build_CCSetoid_relation Q_as_CSetoid Q.lt Qlt_is_extensional.
