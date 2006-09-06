
Require Export Qring.
Require Import CFields.

(** **Example of a field: $\langle$#&lang;#[Q],[[+]],[[*]]$\rangle$#&rang;#
As we have seen, there is a inverse for the multiplication for non-zeroes.
So, [Q] not only forms a ring, but even a field.
*)

Lemma Q_is_CField : is_CField Q_as_CRing Qinv.
Proof.
red in |- *.
intro.
unfold is_inverse in |- *.
apply Qinv_is_inv.
Qed.

Definition Q_as_CField := Build_CField _ _ Q_is_CField Qinv_strext.

