(* $Id: Zmonoid.v,v 1.7 2004/09/22 11:06:12 loeb Exp $ *)


Require Export Zsemigroup.
Require Export CMonoids.

(** **Examples of monoids: $\langle$#&lang;#[Z],[[+]]$\rangle$#&rang;# and $\langle$#&lang;#[Z],[[*]]$\rangle$#&rang;#
***$\langle$#&lang;#[Z],[[+]]$\rangle$#&rang;#
We use the addition [ZERO] (defined in the standard library) as the
unit of monoid:
*)


Lemma ZERO_as_rht_unit : is_rht_unit (S:=Z_as_CSetoid) Zplus_is_bin_fun 0%Z.
Proof.
red in |- *.
simpl in |- *.
intro x.
apply Zplus_0_r.
Qed.

Lemma ZERO_as_lft_unit : is_lft_unit (S:=Z_as_CSetoid) Zplus_is_bin_fun 0%Z.
Proof.
red in |- *.
simpl in |- *.
reflexivity.
Qed.

Lemma is_unit_Z_0 :(is_unit Z_as_CSemiGroup 0%Z).
unfold is_unit.
intro a.
simpl.
split.
reflexivity.
intuition.
Qed.

Definition Z_is_CMonoid := Build_is_CMonoid
 Z_as_CSemiGroup _ ZERO_as_rht_unit ZERO_as_lft_unit.

Definition Z_as_CMonoid := Build_CMonoid Z_as_CSemiGroup _ Z_is_CMonoid.

(** The term [Z_as_CMonoid] is of type [CMonoid]. Hence we have proven that [Z] is a constructive monoid.

***$\langle$#&lang;#[Z],[[*]]$\rangle$#&rang;#
As the multiplicative unit we should use [`1`], which is [(POS xH)] in
the representation we have for integers.
*)

Lemma ONE_as_rht_unit : is_rht_unit (S:=Z_as_CSetoid) Zmult_is_bin_fun 1%Z.
Proof.
red in |- *.
simpl in |- *.
intro.
apply Zmult_1_r.
Qed.

Lemma ONE_as_lft_unit : is_lft_unit (S:=Z_as_CSetoid) Zmult_is_bin_fun 1%Z.
Proof.
red in |- *.
intro.
eapply eq_transitive_unfolded.
apply Zmult_is_commut.
apply ONE_as_rht_unit.
Qed.

Definition Z_mul_is_CMonoid := Build_is_CMonoid
 Z_mul_as_CSemiGroup _ ONE_as_rht_unit ONE_as_lft_unit. 

Definition Z_mul_as_CMonoid := Build_CMonoid
 Z_mul_as_CSemiGroup _ Z_mul_is_CMonoid.


(** The term [Z_mul_as_CMonoid] is another term of type [CMonoid]. *)
