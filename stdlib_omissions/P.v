
Require Import Coq.Setoids.Setoid Coq.PArith.BinPos Coq.PArith.Pnat.

Set Automatic Introduction.

Section P_of_nat.

  Variables (n: nat) (E: n <> O).

  Lemma P_of_nat: positive.
   apply P_of_succ_nat.
   destruct n as [|p].
    exfalso. apply E. reflexivity.
   exact p.
  Defined.

  Lemma P_of_nat_correct: nat_of_P P_of_nat = n.
   unfold P_of_nat.
   destruct n. exfalso. intuition.
   apply nat_of_P_o_P_of_succ_nat_eq_succ.
  Qed.

End P_of_nat.

Lemma nat_of_P_inj_iff (p q : positive): nat_of_P p = nat_of_P q <-> p = q.
Proof with auto.
 split; intro. apply nat_of_P_inj... subst...
Qed.

Lemma nat_of_P_nonzero (p: positive): nat_of_P p <> 0.
Proof.
 intro H.
 apply Lt.lt_irrefl with 0.
 rewrite <- H at 2.
 apply lt_O_nat_of_P.
Qed.

#[global]
Hint Immediate nat_of_P_nonzero.

Lemma Plt_lt (p q: positive): Pos.lt p q <-> (nat_of_P p < nat_of_P q).
Proof.
 split. apply nat_of_P_lt_Lt_compare_morphism.
 apply nat_of_P_lt_Lt_compare_complement_morphism.
Qed.

Lemma Ple_le (p q: positive): Pos.le p q <-> le (nat_of_P p) (nat_of_P q).
Proof.
 rewrite Pos.le_lteq, Plt_lt, Lt.le_lt_or_eq_iff, nat_of_P_inj_iff.
 reflexivity.
Qed.

Lemma Ple_refl p: Pos.le p p.
Proof. intros. apply Pos.le_lteq. firstorder. Qed.
