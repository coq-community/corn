(* $Id$ *)

Require Export Qring.
Require Import CFields.

(** *Example of a field: <Q,+,*>
*)

(** As we have seen, there is a inverse for the multiplication for non-zeroes.
So, [Q] not only forms a ring, but even a field.
*)

Lemma Q_is_CField : is_CField Q_as_CRing Q.inv.
Proof.
red in |- *.
intro.
unfold is_inverse in |- *.
apply Qinv_is_inv.
Qed.

Definition Q_as_CField :=
  Build_CField Q_as_CRing Q.inv Q_is_CField Qinv_is_extensional.

