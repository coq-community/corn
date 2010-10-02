(* This module is designed to *not* be Import'ed, only Require'd. *)

Require Import Program Qpossec Qminmax.

Set Automatic Introduction.

(* Non-negativity preservation: *)

Lemma Qplus_nonneg (x y: Q): 0 <= x -> 0 <= y -> 0 <= x + y.
Proof. apply (Qplus_le_compat 0 x 0); assumption. Qed.

Lemma Qmin_nonneg (x y: Q): 0 <= x -> 0 <= y -> 0 <= Qmin x y.
Proof. apply Q.min_glb; assumption. Qed.

Definition T := sig (Qle 0).

Program Definition eq: T -> T -> Prop := Qeq.
Program Definition le: T -> T -> Prop := Qle.
Program Definition lt: T -> T -> Prop := Qlt.
Program Definition zero: T := 0.
Program Definition one: T := 1.

Section binop.

  Variables
    (o: Q -> Q -> Q)
    (o_ok: forall x y, 0 <= x -> 0 <= y -> 0 <= o x y)
    (o_proper: Proper (Qeq ==> Qeq ==> Qeq) o)
    (o_comm: forall x y, o x y == o y x)
    (o_assoc: forall x y z, o x (o y z) == o (o x y) z).

  Program Definition binop: T -> T -> T := o.

  Next Obligation. apply o_ok; apply proj2_sig. Qed.

  Local Infix "==" := eq.

  Lemma binop_comm (x y: T): binop x y == binop y x.
  Proof. unfold eq. simpl. apply o_comm. Qed.

  Lemma binop_assoc (x y z: T): binop x (binop y z) == binop (binop x y) z.
  Proof. unfold eq. simpl. apply o_assoc. Qed.

  Global Instance binop_proper: Proper (eq ==> eq ==> eq) binop.
  Proof. unfold eq. intros ?? H ??. exact (o_proper _ _ H _ _). Qed.

End binop.

Definition plus := binop Qplus Qplus_nonneg.
Definition mult := binop Qmult Qmult_le_0_compat.
Definition min := binop Qmin Qmin_nonneg.

Local Infix "+" := plus.
Local Infix "*" := mult.
Local Infix "==" := eq.

Lemma plus_comm: forall x y, x + y == y + x.
Proof binop_comm _ _ Qplus_comm.

Lemma plus_assoc: forall x y z, x + (y + z) == (x + y) + z.
Proof binop_assoc _ _ Qplus_assoc.

Global Instance: Equivalence eq.
Proof.
 unfold eq. split.
   intros ?. apply reflexivity.
  intros ??. apply symmetry.
 intros ???. apply transitivity.
Qed.

Global Instance: Proper (eq ==> eq ==> eq) plus.
Proof. unfold plus. apply _. Qed.

Global Instance: Proper (eq ==> eq ==> eq) mult.
Proof. unfold mult. apply _. Qed.

Program Definition inv: T -> T := Qinv.

Next Obligation. destruct x as [[[] ?] ?]; auto. Qed.

Global Instance: Proper (eq ==> eq) inv.
Proof. unfold eq. repeat intro. simpl. apply Qinv_comp. assumption. Qed.

Program Coercion from_Qpos (q: Qpos): T := q.

Lemma from_Qpos_plus_homo (x y: Qpos): (x + y)%Qpos == x + y.
Proof. reflexivity. Qed.

Global Instance from_Qpos_Proper: Proper (QposEq ==> eq) from_Qpos.
Proof. repeat intro. assumption. Qed.

Program Definition hash (num: nat) (den: positive): T := Qmake (Z_of_nat num) den.

Next Obligation.
 unfold Qle.
 simpl.
 rewrite Zmult_1_r.
 apply Zle_0_nat.
Qed.

Lemma min_case (P: T -> Type):
  (forall x y: T, x == y -> P x -> P y) -> forall n m, P n -> P m -> P (min n m).
Proof with auto.
 intros. unfold min, binop.
 generalize (binop_obligation_1 Qmin Qmin_nonneg n m).
 apply Q.min_case; intros.
   pose proof q.
   rewrite <- H in H0.
   apply X with (exist (Qle 0) x H0)...
  apply X with n... reflexivity.
 apply X with m... reflexivity.
Qed.

Module notations.

  Delimit Scope Qnn_scope with Qnn. 

  Global Infix "==" := eq: Qnn_scope.
  Global Infix "<=" := le: Qnn_scope.
  Global Infix "<" := lt: Qnn_scope.
  Global Infix "+" := plus: Qnn_scope.
  Global Infix "*" := mult: Qnn_scope.
  Global Infix "#" := hash: Qnn_scope.
  Global Notation "0" := zero: Qnn_scope.
  Global Notation "1" := one: Qnn_scope.
  Global Notation QnonNeg := T.

End notations.

Lemma proj1_sig_nonNeg (q: T): (0 <= `q)%Q.
Proof. apply proj2_sig. Qed.

Hint Immediate proj1_sig_nonNeg.
