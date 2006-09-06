
Require Export Qgroup.
Require Import CAbGroups.

(** **Example of an abelian group: $\langle$#&lang;#[Q],[[+]]$\rangle$#&rang;#
*)

(** Addition is commutative, so the rationals form with the addition a 
CAbGroup.
*)

Lemma Q_is_CAbGroup : is_CAbGroup Q_as_CGroup.
Proof.
red in |- *.
exact Qplus_is_commut1.
Qed.

Definition Q_as_CAbGroup := Build_CAbGroup Q_as_CGroup Q_is_CAbGroup.
