(* $Id$ *)


Require Export Zsec.
Require Import CSetoidFun.

(** *Example of a setoid: Z
*)

(** **Z
*)

Lemma ap_Z_irreflexive : irreflexive (A:=Z) ap_Z.
Proof.
red in |- *.
apply ap_Z_irreflexive0.
Qed.

Lemma ap_Z_symmetric : Csymmetric ap_Z.
Proof.
red in |- *.
apply ap_Z_symmetric0.
Qed.

Lemma ap_Z_cotransitive : cotransitive (A:=Z) ap_Z.
Proof.
red in |- *.
apply ap_Z_cotransitive0.
Qed.

Lemma ap_Z_tight : tight_apart (A:=Z) (eq (A:=Z)) ap_Z.
Proof.
red in |- *.
apply ap_Z_tight0.
Qed.

Definition ap_Z_is_apartness :=
  Build_is_CSetoid Z (eq (A:=Z)) ap_Z ap_Z_irreflexive ap_Z_symmetric
    ap_Z_cotransitive ap_Z_tight.


Definition Z_as_CSetoid := Build_CSetoid _ _ _ ap_Z_is_apartness.

(** The term [Z_as_CSetoid] is of type [CSetoid]. Hence we have proven that [Z] is a constructive setoid. *)

(** **Addition
*)

(** We will prove now that the addition on the integers is a setoid function.
*)

Lemma Zplus_is_well_defined :
 bin_fun_well_def Z_as_CSetoid Z_as_CSetoid Z_as_CSetoid Zplus.
Proof.
red in |- *.
simpl in |- *.
apply Zplus_is_well_defined0.
Qed.

Lemma Zplus_is_extensional :
 bin_fun_strong_ext Z_as_CSetoid Z_as_CSetoid Z_as_CSetoid Zplus.
Proof.
red in |- *.
simpl in |- *.
apply Zplus_is_extensional0.
Qed.

Definition Zplus_is_bin_fun :=
  Build_CSetoid_bin_fun Z_as_CSetoid Z_as_CSetoid Z_as_CSetoid Zplus
    Zplus_is_extensional.

(** What's more: the addition is also associative and commutative.
*) 

Lemma Zplus_is_assoc : associative Zplus_is_bin_fun.
Proof.
red in |- *.
intros x y z.
simpl in |- *.
apply Zplus_assoc.
Qed.

Lemma Zplus_is_commut : commutes Zplus_is_bin_fun.
Proof.
red in |- *.
simpl in |- *.
intros x y.
apply Zplus_comm.
Qed.

(** **Opposite
*)

(** Taking the opposite of an integer is a setoid function.
*)

Lemma Zopp_is_well_defined :
 fun_well_def (S1:=Z_as_CSetoid) (S2:=Z_as_CSetoid) Zopp.
Proof.
red in |- *.
simpl in |- *.
intros x y H.
apply (f_equal Zopp H).
Qed.

Lemma Zopp_is_extensional :
 fun_strong_ext (S1:=Z_as_CSetoid) (S2:=Z_as_CSetoid) Zopp.
Proof.
red in |- *.
simpl in |- *.
unfold ap_Z in |- *.
intros x y H.
intro H0.
apply H.
exact (f_equal Zopp H0).
Qed.

Definition Zopp_is_fun :=
  Build_CSetoid_fun Z_as_CSetoid Z_as_CSetoid Zopp Zopp_is_extensional.

(** **Multiplication
*)

(** Finally the multiplication is a setoid function and is associative and commutative.
*)

Lemma Zmult_is_well_defined :
 bin_fun_well_def Z_as_CSetoid Z_as_CSetoid Z_as_CSetoid Zmult.
Proof.
red in |- *.
simpl in |- *.
intros x1 x2 y1 y2 H H0.
apply (f_equal2 Zmult (x1:=x1) (y1:=x2) (x2:=y1) (y2:=y2)).
assumption.
assumption.
Qed.

Lemma Zmult_is_extensional :
 bin_fun_strong_ext Z_as_CSetoid Z_as_CSetoid Z_as_CSetoid Zmult.
Proof.
red in |- *.
simpl in |- *.
apply Zmult_is_extensional0.
Qed.

Definition Zmult_is_bin_fun :=
  Build_CSetoid_bin_fun Z_as_CSetoid Z_as_CSetoid Z_as_CSetoid Zmult
    Zmult_is_extensional.

Lemma Zmult_is_assoc : associative Zmult_is_bin_fun.
Proof.
red in |- *.
intros x y z.
simpl in |- *.
apply Zmult_assoc.
Qed.


Lemma Zmult_is_commut : commutes Zmult_is_bin_fun.
Proof.
red in |- *.
simpl in |- *.
intros x y.
apply Zmult_comm.
Qed.
