
From Coq Require Import ZArith.
Require Import CoRN.stdlib_omissions.P.
From Coq Require Import Lia.

(*Require Import NSigNAxioms.  was added in the trunk branch*)

Open Scope Z_scope.

Lemma iff_not (P Q : Prop) : (P <-> Q) -> (not P <-> not Q).
Proof. tauto. Qed.

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

Lemma P_of_succ_nat_Zplus (m: nat): Zpos (P_of_succ_nat m) = Z_of_nat m + 1.
Proof.
 destruct m. reflexivity.
 simpl.
 destruct (P_of_succ_nat m); reflexivity.
Qed.

Lemma S_Zplus (n: nat): (Z_of_nat (S n) = Z_of_nat n + 1)%Z.
Proof.
 simpl Z_of_nat.
 rewrite  P_of_succ_nat_Zplus.
 reflexivity.
Qed.

Lemma Zto_nat_nonpos (z : Z) : z <= 0 -> Z.to_nat z = 0%nat.
Proof.
intro A; destruct z as [| p | p]; trivial.
unfold Z.le in A; now contradict A.
Qed.

Lemma Ple_Zle (p q: positive): Pos.le p q <-> (Zpos p <= Zpos q).
Proof.
 rewrite Ple_le, inj_le_iff.
 do 2 rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
 reflexivity.
Qed.

Lemma Ple_Zle_to_pos (z : Z) (p : positive) : (Z.to_pos z <= p)%positive <-> z <= Zpos p.
Proof.
  destruct z as [| q | q]; simpl.
  + split; intros _; [apply Zle_0_pos | apply Pos.le_1_l].
  + apply Ple_Zle.
  + split; intros _; [apply Zle_neg_pos | apply Pos.le_1_l].
Qed.

Lemma le_Zle_to_nat (n : nat) (z : Z) : (Z.to_nat z <= n)%nat <-> z <= Z.of_nat n.
Proof.
pose proof (Nat.le_0_l n). pose proof (Zle_0_nat n).
destruct (Z.neg_nonneg_cases z).
+ rewrite Zto_nat_nonpos by now apply Z.lt_le_incl. split; auto with zarith.
+ split; intro A.
  - apply inj_le in A. rewrite Z2Nat.id in A; trivial.
  - apply Z2Nat.inj_le in A; trivial. rewrite Nat2Z.id in A; trivial.
Qed.

Lemma lt_Zlt_to_nat (n : nat) (z : Z) : Z.of_nat n < z <-> (n < Z.to_nat z)%nat.
Proof.
assert (A : forall (m n : nat), not (m <= n)%nat <-> (n < m)%nat).
+ intros; split; [apply not_le | apply Nat.lt_nge].
+ assert (A1 := le_Zle_to_nat n z). apply iff_not in A1.
  now rewrite A, Z.nle_gt in A1.
Qed.

Lemma add_pos_nonneg (a b: Z): 0 < a -> 0 <= b -> 0 < a+b.
Proof. intros. lia. Qed.

