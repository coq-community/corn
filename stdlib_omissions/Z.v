
Require Import ZArith NPeano stdlib_omissions.P.

Open Scope Z_scope.

(* Injection from nat preserves various operations: *)

Lemma div_Zdiv (n m: nat): m <> 0%nat -> Z_of_nat (n / m) = Z_of_nat n / Z_of_nat m.
Proof.
 intros.
 apply (Zdiv_unique (Z_of_nat n) (Z_of_nat m) (Z_of_nat (n/m)%nat) (Z_of_nat (n mod m))).
  split.
   auto with *.
  apply inj_lt.
  apply Nat.mod_upper_bound.
  assumption.
 rewrite <- inj_mult.
 rewrite <- inj_plus.
 apply inj_eq.
 apply Nat.div_mod.
 assumption.
Qed.

Lemma mod_Zmod (n m: nat): m <> 0%nat -> Z_of_nat (n mod m) = (Z_of_nat n) mod (Z_of_nat m).
Proof with auto with *.
 intros.
 apply (Zmod_unique (Z_of_nat n) (Z_of_nat m) (Z_of_nat n / Z_of_nat m)).
  split...
  apply inj_lt.
  apply Nat.mod_upper_bound...
 rewrite <- div_Zdiv...
 rewrite <- inj_mult, <- inj_plus.
 apply inj_eq, Nat.div_mod...
Qed.

Lemma Ple_Zle (p q: positive): Ple p q <-> Zle (Zpos p) (Zpos q).
Proof.
 intros.
 rewrite Ple_le, inj_le_iff.
 do 2 rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
 reflexivity.
Qed.
