
(* $Id$ *)

Require Export Nsec.
Require Import CSetoidFun.

(** *Example of a setoid: N
*)

(** **N
*)

(** We will show that the natural numbers form a CSetoid. 
*)

  Lemma ap_nat_irreflexive : irreflexive (A:=nat) ap_nat.
Proof.
red in |- *.
apply ap_nat_irreflexive0.
Qed.


  Lemma ap_nat_symmetric : Csymmetric ap_nat.
Proof.
red in |- *.
apply ap_nat_symmetric0.
Qed.

  Lemma ap_nat_cotransitive : cotransitive (A:=nat) ap_nat.
Proof.
red in |- *.
apply ap_nat_cotransitive0.
Qed.

  Lemma ap_nat_tight : tight_apart (A:=nat) (eq (A:=nat)) ap_nat.
red in |- *.
apply ap_nat_tight0.
Qed.

  Definition ap_nat_is_apartness :=
    Build_is_CSetoid nat (eq (A:=nat)) ap_nat ap_nat_irreflexive
      ap_nat_symmetric ap_nat_cotransitive ap_nat_tight.


  Definition nat_as_CSetoid := Build_CSetoid _ _ _ ap_nat_is_apartness.

(** **Addition
*)

  Lemma plus_is_well_defined :
   bin_fun_well_def nat_as_CSetoid nat_as_CSetoid nat_as_CSetoid plus.
Proof.
red in |- *.
simpl in |- *.
auto.
Qed.

  Lemma plus_is_extensional :
   bin_fun_strong_ext nat_as_CSetoid nat_as_CSetoid nat_as_CSetoid plus.
Proof.
red in |- *.
simpl in |- *.
apply plus_is_extensional0.
Qed.

  Definition plus_is_bin_fun :=
    Build_CSetoid_bin_fun nat_as_CSetoid nat_as_CSetoid nat_as_CSetoid plus
      plus_is_extensional.

(** It is associative and commutative.
*)

  Lemma plus_is_assoc : associative plus_is_bin_fun.
Proof.
red in |- *.
intros x y z.
simpl in |- *.
apply plus_assoc.
Qed.

  Lemma plus_is_commut : commutes plus_is_bin_fun. 
Proof.
red in |- *.
simpl in |- *.
intros x y.
exact (plus_comm x y). 
Qed.

(** **Multiplication
*)

Lemma mult_is_extensional :
 bin_fun_strong_ext nat_as_CSetoid nat_as_CSetoid nat_as_CSetoid mult. 
red in |- *.
simpl in |- *.
apply mult_is_extensional0.
Qed.

Definition mult_as_bin_fun :=
  Build_CSetoid_bin_fun nat_as_CSetoid nat_as_CSetoid nat_as_CSetoid mult
    mult_is_extensional. 
