
Require Import ZArith NPeano stdlib_omissions.P.

Open Scope Z_scope.

Definition nat_of_Z (x : Z) : nat :=
  match x with
  | Z0 => O
  | Zpos p => nat_of_P p
  | Zneg p => O
  end.

Lemma nat_of_Z_nonpos (x : Z) : x <= 0 -> nat_of_Z x = 0%nat.
Proof.
  destruct x; simpl; try reflexivity.
  now intros [].
Qed.

Lemma nat_of_Z_nonneg (x : Z) : 0 <= x -> Z_of_nat (nat_of_Z x) = x.
Proof.
  destruct x; simpl.
    reflexivity.
   intros. apply Z_of_nat_of_P.
  now intros [].
Qed.

Definition N_of_Z (x : Z) : N :=
  match x with
  | Z0 => 0%N
  | Zpos p => Npos p
  | Zneg p => 0%N
  end.

Lemma N_of_Z_nonpos (x : Z) : x <= 0 -> N_of_Z x = 0%N.
Proof.
  destruct x; simpl; try reflexivity.
  now intros [].
Qed.

Lemma N_of_Z_nonneg (x : Z) : 0 <= x -> Z_of_N (N_of_Z x) = x.
Proof.
  destruct x; simpl; try reflexivity.
  now intros [].
Qed.

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
 apply div_mod.
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
 apply inj_eq, div_mod...
Qed.

Lemma P_of_succ_nat_Zplus (m: nat): Zpos (P_of_succ_nat m) = Z_of_nat m + 1.
Proof with intuition.
 induction m...
 simpl.
 destruct (P_of_succ_nat m)...
Qed.

Lemma S_Zplus (n: nat): (Z_of_nat (S n) = Z_of_nat n + 1)%Z.
Proof.
 simpl Z_of_nat.
 rewrite  P_of_succ_nat_Zplus.
 reflexivity.
Qed.

Lemma Ple_Zle (p q: positive): Ple p q <-> (Zpos p <= Zpos q).
Proof.
 rewrite Ple_le, inj_le_iff.
 do 2 rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
 reflexivity.
Qed.

Lemma Ple_Zle_to_pos_l (z : Z) (p : positive) : (Z.to_pos z <= p)%positive <-> (z <= p)%Z.
Proof.
  destruct z as [| q | q]; simpl.
  + split; intros _; [apply Zle_0_pos | apply Pos.le_1_l].
  + apply Ple_Zle.
  + split; intros _; [apply Zle_neg_pos | apply Pos.le_1_l].
Qed.

Lemma add_pos_nonneg (a b: Z): 0 < a -> 0 <= b -> 0 < a+b.
Proof. intros. omega. Qed.
