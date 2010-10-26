Require Import
  List NPeano
  QArith Qabs Qpossec Qmetric
  Program
  stdlib_omissions.N
  stdlib_omissions.Z
  stdlib_omissions.Q.

Set Automatic Introduction.

Open Scope Q_scope.

Coercion nat_of_P: positive >-> nat.

Definition Qsum := fold_right Qplus 0.

Definition Σ (n: nat) (f: nat -> Q) := Qsum (map f (enum n)).

(** Properties of Σ: *)

Lemma Σ_sub f g n: Σ n f - Σ n g == Σ n (fun x => f x - g x).
Proof.
 unfold Σ. induction n. reflexivity.
 simpl. rewrite <- IHn. ring.
Qed.

Lemma Σ_mult n f k: Σ n f * k == Σ n (Qmult k ∘ f).
Proof.
 unfold Σ, Basics.compose.
 induction n. reflexivity.
 intros. simpl. rewrite <- IHn. ring.
Qed.

Lemma Σ_constant x n f: (forall i, (i < n)%nat -> f i == x) -> Σ n f == n * x.
Proof with auto.
 unfold Σ. induction n. reflexivity.
 simpl. intro E.
 rewrite IHn...
 rewrite E...
 rewrite P_of_succ_nat_Zplus.
 rewrite Q.Zplus_Qplus.
 ring.
Qed.

Lemma Σ_const x n: Σ n (fun _ => x) == n * x.
Proof. apply Σ_constant. reflexivity. Qed.

Lemma Σ_S_bound_back f n: Σ (S n) f == Σ n f + f n.
Proof. unfold Σ. simpl. ring. Qed.

Lemma Σ_S_bound_front n f: Σ (S n) f == Σ n (f ∘ S) + f O.
Proof.
 unfold Σ, Basics.compose.
 induction n; intros; simpl in *. ring.
 rewrite IHn. ring.
Qed.

Lemma Σ_S_bound_rev n f: Σ n (f ∘ S) == Σ (S n) f - f O.
Proof. rewrite Σ_S_bound_front. ring. Qed.

Lemma Σ_le f n (b: Q):
  (forall x, (x < n)%nat -> f x <= b) -> Σ n f <= n * b.
Proof.
 induction n. discriminate.
 intro.
 rewrite Q.S_Qplus.
 change (f n + Σ n f <= (n + 1) * b)%Q.
 assert ((n + 1) * b == b + n * b)%Q as E. ring.
 rewrite E.
 apply Qplus_le_compat; auto.
Qed.

Lemma Σ_abs_le f n (b: Q):
  (forall x, (x < n)%nat -> Qabs (f x) <= b) -> Qabs (Σ n f) <= n * b.
Proof.
 induction n.
  discriminate.
 intros.
 rewrite S_Zplus.
 rewrite Q.Zplus_Qplus.
 change (Qabs (f n + Σ n f) <= (n + 1) * b)%Q.
 assert ((n + 1) * b == b + n * b)%Q. ring.
 rewrite H0. clear H0.
 apply Qle_trans with (Qabs (f n) + Qabs (Σ n f))%Q.
  apply Qabs_triangle.
 apply Qplus_le_compat; auto.
Qed. 

Lemma Σ_wd f g n (H: forall x, (x < n)%nat -> f x == g x):
  Σ n f == Σ n g.
Proof with auto with *.
 unfold Σ. induction n; simpl...
 rewrite IHn... rewrite H...
Qed.

Lemma Σ_plus_bound m n f: Σ (m + n) f == Σ n f + Σ m (f ∘ plus n).
Proof with try reflexivity.
 induction m; simpl; intros.
  unfold Σ. simpl. ring.
 do 2 rewrite Σ_S_bound_back.
 rewrite Qplus_assoc.
 rewrite <- IHm.
 unfold Basics.compose.
 replace (f (m + n)%nat) with (f (n + m)%nat)...
 rewrite plus_comm...
Qed.

Lemma Σ_mult_bound n m f:
  Σ (n * m) f == Σ n (fun i => Σ m (fun j => f (i * m + j)%nat)).
Proof.
 induction n; intros.
  reflexivity.
 unfold Σ in *.
 simpl.
 rewrite <- IHn.
 change (Σ (m + n * m) f == Σ m (fun j => f (n * m + j)%nat) + Σ (n * m) f).
 rewrite Σ_plus_bound.
 unfold Basics.compose.
 ring.
Qed.

Lemma Σ_Qball (f g: nat -> Q) (e: Qpos) (n: nat):
  (forall i: nat, (i < n)%nat -> Qabs (f i - g i) <= e / n) ->
  Qball e (Σ n f) (Σ n g).
Proof with auto.
 intro H.
 apply Qball_Qabs.
 destruct n. simpl. auto.
 rewrite Σ_sub.
 setoid_replace (QposAsQ e) with (S n * (/S n*e)).
  apply Σ_abs_le.
  intros ? E.
  specialize (H x E).
  simpl QposAsQ in *.
  rewrite Qmult_comm.
  assumption.
 change (e == S n * (/ S n * e)).
 field. discriminate.
Qed.

Lemma Σ_Qball_pos_bounds (f g: nat -> Q) (e: Qpos) (n: positive):
  (forall i: nat, (i < n)%nat -> Qball (e / n) (f i) (g i)) ->
  Qball e (Σ n f) (Σ n g).
Proof with intuition.
 intros. apply Σ_Qball. intros.
 setoid_replace (e / nat_of_P n) with (e / n)%Qpos.
  apply Qball_Qabs...
 rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P...
Qed.

Lemma Qmult_Σ (f: nat -> Q) n (k: nat):
  Σ n f * k == Σ (k * n) (f ∘ flip div k).
Proof with auto with *.
 unfold Basics.compose.
 rewrite mult_comm.
 rewrite Σ_mult_bound.
 unfold Qdiv.
 rewrite Σ_mult.
 apply Σ_wd.
 intros.
 unfold Basics.compose.
 rewrite (Σ_constant (f x))...
 intros.
 unfold flip.
 replace ((x * k + i) / k)%nat with x...
 apply (div_unique (x * k + i)%nat k x i)...
Qed.

Lemma Σ_multiply_bound n (k: positive) (f: nat -> Q):
  Σ n f == Σ (k * n) (f ∘ flip div k) / k.
Proof.
 rewrite <- Qmult_Σ.
 rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
 field. discriminate.
Qed.

Lemma Qball_hetero_Σ (n m: positive) f g e:
 (forall i: nat, (i < (n * m)%positive)%nat ->
   Qball (e / (n * m)%positive)
     (/ m * f (i / m)%nat)
     (/ n * g (i / n)%nat)) ->
   Qball e (Σ n f) (Σ m g).
Proof.
 intros.
 rewrite (Σ_multiply_bound (nat_of_P n) m).
 rewrite (Σ_multiply_bound (nat_of_P m) n).
 rewrite mult_comm.
 rewrite <- nat_of_P_mult_morphism.
 unfold Qdiv.
 rewrite Σ_mult.
 rewrite Σ_mult.
 apply Σ_Qball_pos_bounds.
 intros.
 unfold Basics.compose.
 unfold flip.
 auto.
Qed.

(** Σ was defined above straightforwardly in terms of ordinary lists and without
 any efficiency consideration. In practice, building up a list with enum only to
 break it down immediately with Qsum is wasteful, and I strongly doubt Coq
 does list deforestation/fusion. Also, summing many Q's quickly yields large
 numerators and denominators. Hence, we now define a faster version
 which avoids the intermediate lists and uses Qred. The idea is to use
 fastΣ in the actual definition of operations, and to immediately rewrite it to Σ
 (using the correctness property) when doing proofs about said operations. *)

Section fastΣ.

  Fixpoint fast (f: nat -> Q) (left: nat) (sofar: Q): Q :=
    match left with
    | O => sofar
    | S n => fast f n (Qred (sofar + f n))
    end.

  Definition fastΣ (n: nat) (f: nat -> Q): Q := fast f n 0.

  Lemma fastΣ_correct n f: fastΣ n f == Σ n f.
  Proof.
   intros.
   rewrite <- (Qplus_0_r (Σ n f)).
   unfold Σ, fastΣ.
   generalize 0.
   induction n; intros.
    simpl. ring.
   change (fast f n (Qred (q + f n)) == Qsum (map f (enum (S n))) + q).
   rewrite IHn.
   rewrite Qred_correct.
   simpl.
   ring.
  Qed.

End fastΣ.
