
Require Export Zabgroup.
Require Import CRings.

(** **Example of a ring: $\langle$#&lang;#[Z],[[+]],[[*]]$\rangle$#&rang;#

The multiplication and the addition are distributive.
*)

Lemma Z_mult_plus_is_dist : distributive Zmult_is_bin_fun Zplus_is_bin_fun. 
Proof.
red in |- *.
simpl in |- *.
intros x y z.
apply Zmult_plus_distr_r.
Qed.

Definition Z_is_CRing := Build_is_CRing Z_as_CAbGroup _ _ Zmult_is_assoc
    Z_mul_is_CMonoid Zmult_is_commut Z_mult_plus_is_dist ONE_neq_O.

Definition Z_as_CRing := Build_CRing _ _ _ Z_is_CRing.

(** The term [Z_as_CRing] is of type [CRing]. Hence we have proven that [Z] is a constructive ring. *)
