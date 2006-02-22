(* $Id: Qring.v,v 1.8 2004/04/23 10:01:03 lcf Exp $ *)

Require Export Qabgroup.
Require Import CRings.
Require Import Zring.

(** **Example of a ring: $\langle$#&lang;#[Q],[[+]],[[*]]$\rangle$#&rang;#
Because [Q] forms an abelian group with addition, a monoid with 
multiplication and it satisfies the distributive law, it is a ring.
*)

Lemma Q_mult_plus_is_dist : distributive Qmult_is_bin_fun Qplus_is_bin_fun.
Proof.
red in |- *.
simpl in |- *.
exact Qmult_plus_distr_r.
Qed.

Definition Q_is_CRing : is_CRing Q_as_CAbGroup QONE Qmult_is_bin_fun.
apply Build_is_CRing with Qmult_is_assoc.
apply Q_mul_is_CMonoid.
apply Qmult_is_commut.
apply Q_mult_plus_is_dist.
red in |- *.
simpl in |- *.
intro.
elim ONEQ_neq_ZEROQ.
auto.
Defined.

Definition Q_as_CRing := Build_CRing _ _ _ Q_is_CRing.

(** The following lemmas are used in the proof that [Q] is Archimeadian.
*)

Lemma injz_Nring : forall n,
 nring (R:=Q_as_CRing) n[=]inject_Z (nring (R:=Z_as_CRing) n).
Proof.
 intro n.
 induction  n as [| n Hrecn].
 change ((Zero:Q_as_CRing)[=]Zero) in |- *.
 apply eq_reflexive_unfolded.
 change
   (nring (R:=Q_as_CRing) n[+]One[=]inject_Z (nring (R:=Z_as_CRing) n[+]One))
  in |- *.
 Step_final ((inject_Z (nring (R:=Z_as_CRing) n):Q_as_CRing)[+]One).
 astepl
  ((inject_Z (nring (R:=Z_as_CRing) n):Q_as_CRing)[+]
   inject_Z (One:Z_as_CRing)).
 apply eq_symmetric_unfolded.
 apply injz_plus.
Qed.

Lemma injZ_eq : forall x y : Z, x = y -> (inject_Z x:Q_as_CRing)[=]inject_Z y.
Proof.
 intros.
 unfold inject_Z in |- *.
 simpl in |- *. 
 red in |- *.
 simpl in |- *.
 ring.
 assumption.
Qed.

Lemma nring_Q : forall n : nat, nring (R:=Q_as_CRing) n[=]inject_Z n.
Proof.
 intro n.
 induction  n as [| n Hrecn].
 change (Build_Q 0%Z 1%positive{=Q}Build_Q 0%Z 1%positive) in |- *.
 change (Zero[=](Zero:Q_as_CRing)) in |- *.
 apply eq_reflexive_unfolded.

 change (nring (R:=Q_as_CRing) n[+]One[=]inject_Z (S n)) in |- *.
 Step_final ((inject_Z n:Q_as_CRing)[+]One). 
 astepl ((inject_Z n:Q_as_CRing)[+]inject_Z 1).
 simpl in |- *.
 red in |- *.
 unfold Qplus in |- *.
 simpl in |- *.
 ring.
 rewrite Pmult_comm.
 change ((1 + n)%Z = P_of_succ_nat n) in |- *.
 case n; simpl in |- *; auto with zarith. 
 Require Import ZArith.
 intros.
 rewrite BinPos.Pplus_one_succ_l; trivial.
Qed.
