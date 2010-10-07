
Require Import
  QArith ZArith NArith
  Qround Qabs.

Set Automatic Introduction.

Open Scope Q_scope.

(* Proofs that the various injections into Q are homomorphisms w.r.t. the various operations: *)

Lemma Zplus_Qplus (m n: Z): inject_Z (m + n) = inject_Z m + inject_Z n.
Proof.
 unfold Qplus. simpl. unfold inject_Z.
 do 2 rewrite Zmult_1_r. reflexivity.
Qed.

Lemma Zsucc_Qplus (z: Z): inject_Z (Zsucc z) = inject_Z z + 1.
Proof. apply Zplus_Qplus. Qed.

Lemma Zmult_Qmult (x y: Z): inject_Z (x * y) = inject_Z x * inject_Z y.
Proof. reflexivity. Qed.

Lemma S_Qplus (n: nat): inject_Z (Z_of_nat (S n)) = inject_Z (Z_of_nat n) + 1.
Proof. rewrite inj_S. apply Zplus_Qplus. Qed.

Lemma Pmult_Qmult (x y: positive): inject_Z (' (Pmult x y)) = inject_Z (' x) * inject_Z (' y).
Proof. rewrite Zpos_mult_morphism. apply Zmult_Qmult. Qed.

Lemma Zle_Qle (x y: Z): (x <= y)%Z = (inject_Z x <= inject_Z y).
Proof.
 unfold Qle. intros. simpl.
 do 2 rewrite Zmult_1_r. reflexivity.
Qed.

Lemma Zlt_Qlt (x y: Z): (x < y)%Z = (inject_Z x < inject_Z y).
Proof.
 unfold Qlt. intros. simpl.
 do 2 rewrite Zmult_1_r. reflexivity.
Qed.

Lemma Zdiv_Qdiv (n m: Z): (n / m)%Z = Qfloor (inject_Z n / inject_Z m).
Proof with simpl; try reflexivity.
 unfold Qfloor. intros. simpl.
 destruct m...
   rewrite Zdiv_0_r.
   rewrite Zmult_0_r...
  rewrite Zmult_1_r...
 rewrite <- Zopp_eq_mult_neg_1.
 rewrite <- (Zopp_involutive (Zpos p)).
 rewrite Zdiv_opp_opp...
Qed.

Lemma Qle_nat (n: nat): 0 <= inject_Z (Z_of_nat n).
Proof. rewrite <- (Zle_Qle 0). apply Zle_0_nat. Qed.

Lemma inject_Z_injective (a b: Z): inject_Z a = inject_Z b <-> a = b.
Proof. unfold inject_Z. split; congruence. Qed.

(* Properties of arithmetic: *)

Lemma Qmult_injective_l (z: Q) (Znz: ~ z == 0): forall x y, (x * z == y * z <-> x == y).
Proof.
 split; intro E.
  rewrite <- (Qmult_1_r x).
  rewrite <- (Qmult_1_r y).
  rewrite <- (Qmult_inv_r _ Znz).
  do 2 rewrite Qmult_assoc.
  rewrite E. reflexivity.
 rewrite E. reflexivity.
Qed.

Lemma Qmult_injective_r (z: Q) (Znz: ~ z == 0): forall x y, (z * x == z * y <-> x == y).
Proof.
 intros. do 2 rewrite (Qmult_comm z).
 apply Qmult_injective_l. assumption.
Qed.

Lemma Qinv_char x q: (x * q == 1) <-> (x == / q /\ ~ q == 0).
Proof with auto.
 split.
  intros A.
  assert (~ q == 0).
   intro B. apply Q_apart_0_1. rewrite <- A, B. ring.
  intuition.
  apply (Qmult_injective_l q)...
  rewrite A. field...
 intros [A ?]. rewrite A. field...
Qed.

Lemma show_is_Qinv x q: x * q == 1 -> x == / q.
Proof. intros. apply Qinv_char. assumption. Qed.

Lemma Qabs_Qminus x y: Qabs (x - y) == Qabs (y - x).
Proof.
 unfold Qminus.
 intros.
 rewrite <- (Qopp_opp x) at 1.
 rewrite <- Qopp_plus.
 rewrite Qplus_comm.
 apply Qabs_opp.
Qed.

(* Properties of arithmetic w.r.t. order: *)

Lemma Qplus_le_l (z x y : Q): x + z <= y + z <-> x <= y.
Proof with auto with *.
 split; intros.
  setoid_replace x with (x + z + -z) by (simpl; ring).
  setoid_replace y with (y + z + -z) by (simpl; ring).
  apply Qplus_le_compat...
 apply Qplus_le_compat...
Qed.

Lemma Qplus_le_r (z x y : Q): z + x <= z + y <-> x <= y.
Proof. do 2 rewrite (Qplus_comm z). apply Qplus_le_l. Qed.

Lemma Qopp_Qlt_0_l (x: Q): 0 < -x <-> x < 0.
Proof.
 split.
  rewrite <- (Qopp_opp x) at 2.
  apply (Qopp_lt_compat 0 (-x)).
 apply (Qopp_lt_compat x 0).
Qed.
 
Lemma Qopp_Qlt_0_r (x: Q): -x < 0 <-> 0 < x.
Proof. rewrite <- Qopp_Qlt_0_l, Qopp_opp. reflexivity. Qed.

Lemma Qmult_lt_0_compat (x y: Q): 0 < x -> 0 < y -> 0 < x * y.
Proof.
 destruct x, y. unfold Qlt. simpl.
 repeat rewrite Zmult_1_r.
 apply Zmult_lt_0_compat.
Qed.

Hint Resolve Qmult_lt_0_compat.

Lemma Qplus_lt_le_0_compat x y: 0 < x -> 0 <= y -> 0 < x + y.
Proof with auto.
 unfold Qlt, Qle. simpl.
 repeat rewrite Zmult_1_r. intros.
 apply Zdiv.Z.add_pos_nonneg.
  apply Zmult_lt_0_compat...
  reflexivity.
 apply Zmult_le_0_compat...
 discriminate.
Qed.

Lemma Qplus_le_lt_0_compat x y: 0 <= x -> 0 < y -> 0 < x + y.
Proof.
 rewrite Qplus_comm. intros.
 apply (Qplus_lt_le_0_compat y x); assumption.
Qed.

Lemma Qabs_Qle x y: (Qabs x <= y) <-> (-y <= x <= y).
Proof with intuition.
 split.
  split.
   rewrite <- (Qopp_opp x).
   apply Qopp_le_compat.
   apply Qle_trans with (Qabs (-x)).
    apply Qle_Qabs.
   rewrite Qabs_opp...
  apply Qle_trans with (Qabs x)...
  apply Qle_Qabs.
 intros.
 apply Qabs_case...
 rewrite <- (Qopp_opp y).
 apply Qopp_le_compat...
Qed.

Lemma Qabs_diff_Qle x y r: (Qabs (x - y) <= r) <-> (x - r <= y <= x + r).
Proof with try ring.
 intros.
 rewrite Qabs_Qle.
 rewrite <- (Qplus_le_r (r + y) (-r) (x- y)).
 rewrite <- (Qplus_le_r (y - r) (x-y) r).
 setoid_replace (r + y + -r) with y...
 setoid_replace (r + y + (x - y)) with (x + r)...
 setoid_replace (y - r + (x - y)) with (x - r)...
 setoid_replace (y - r + r) with y...
 intuition.
Qed.
 