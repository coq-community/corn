

Require Export Qsec.
Require Import CSetoidFun.

(** **Example of a setoid: [Q]
***Setoid
*)
Lemma ap_Q_irreflexive1 : irreflexive (A:=Q) Qap.
red in |- *.
apply ap_Q_irreflexive0.
Qed.

Lemma ap_Q_symmetric1 : Csymmetric Qap.
red in |- *.
apply ap_Q_symmetric0.
Qed.

Lemma ap_Q_cotransitive1 : cotransitive (A:=Q) Qap.
red in |- *.
apply ap_Q_cotransitive0.
Qed.

Lemma ap_Q_tight1 : tight_apart (A:=Q) Qeq Qap.
red in |- *.
apply ap_Q_tight0.
Qed.

Definition ap_Q_is_apartness := Build_is_CSetoid Q Qeq Qap
 ap_Q_irreflexive1 ap_Q_symmetric1 ap_Q_cotransitive1 ap_Q_tight1.

Definition Q_as_CSetoid := Build_CSetoid _ _ _ ap_Q_is_apartness.

(** ***Addition
*)

Lemma Qplus_wd : bin_fun_wd Q_as_CSetoid Q_as_CSetoid Q_as_CSetoid Qplus.
Proof.
red in |- *.
simpl in |- *.
intros.
exact (Qplus_simpl x1 x2 y1 y2 H H0).
Qed.

Lemma Qplus_strext1 : bin_fun_strext Q_as_CSetoid Q_as_CSetoid Q_as_CSetoid Qplus.
red in |- *.
simpl in |- *.
exact Qplus_strext0.
Qed.

Definition Qplus_is_bin_fun := Build_CSetoid_bin_fun _ _ _ _ Qplus_strext1.

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

(** ***Opposite
*)

Lemma Qopp_wd : fun_wd (S1:=Q_as_CSetoid) (S2:=Q_as_CSetoid) Qopp.
Proof.
red in |- *.
simpl in |- *.
intros.
exact (Qopp_simpl x y H).
Qed.

Lemma Qopp_strext : fun_strext (S1:=Q_as_CSetoid) (S2:=Q_as_CSetoid) Qopp.
Proof.
red in |- *.
simpl in |- *.
unfold Qap in |- *.
intros.
red in |- *.
intro H0.
apply H.
exact (Qopp_simpl x y H0).
Qed.

Definition Qopp_is_fun := Build_CSetoid_fun _ _ _ Qopp_strext.

(** ***Multiplication
*)

Lemma Qmult_wd : bin_fun_wd Q_as_CSetoid Q_as_CSetoid Q_as_CSetoid Qmult.
Proof.
red in |- *.
simpl in |- *.
intros.
apply Qmult_simpl.
assumption.
assumption.
Qed.

Lemma Qmult_strext1 : bin_fun_strext Q_as_CSetoid Q_as_CSetoid Q_as_CSetoid Qmult.
Proof.
red in |- *.
simpl in |- *.
apply Qmult_strext0.
Qed.

Definition Qmult_is_bin_fun := Build_CSetoid_bin_fun _ _ _ _ Qmult_strext1.

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

(** ***Less-than
*)

Lemma Qlt_strext : Crel_strext Q_as_CSetoid Qlt.
Proof.
red in |- *.
apply Qlt_strext_unfolded.
Qed.

Definition Qlt_is_CSetoid_relation := Build_CCSetoid_relation _ _ Qlt_strext.
