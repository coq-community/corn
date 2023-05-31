(* This module is designed to *not* be Import'ed, only Require'd. *)

Require Import CoRN.model.totalorder.QposMinMax 
        Coq.Program.Program CoRN.model.structures.QposInf Coq.QArith.Qminmax.


(* The data type and simple relations/constants: *)

Definition T := sig (Qle 0).

Program Definition eq: T -> T -> Prop := Qeq.
Program Definition zero: T := 0.
Program Definition one: T := 1.
(*Program Definition le: T -> T -> Prop := Qle.
Program Definition lt: T -> T -> Prop := Qlt.*)
  (* Not really needed because we can just use Qle/Qlt directly. This
  is not practical for eq because we want rewriting and Propers and so on. *)

Local Infix "==" := eq.
Local Notation "0" := zero.
Local Notation "1" := one.

Global Instance: Equivalence eq.
Proof. split; repeat intro; firstorder auto with crelations. unfold eq. etransitivity; eauto. Qed.

(* For addition, multiplication, and min/max (and their properties), we factor out the common bits: *)

Section binop.

  Variables
    (o: Q -> Q -> Q)
    (o_ok: forall x y, 0 <= x -> 0 <= y -> 0 <= o x y)
    (o_proper: Proper (Qeq ==> Qeq ==> Qeq) o)
    (o_comm: (forall x y, o x y == o y x)%Q)
    (o_assoc: (forall x y z, o x (o y z) == o (o x y) z)%Q).

  Program Definition binop: T -> T -> T := o.

  Lemma binop_comm (x y: T): binop x y == binop y x.
  Proof. unfold eq. simpl. apply o_comm. Qed.

  Lemma binop_assoc (x y z: T): binop x (binop y z) == binop (binop x y) z.
  Proof. unfold eq. simpl. apply o_assoc. Qed.

  Global Instance binop_proper: Proper (eq ==> eq ==> eq) binop.
  Proof. unfold eq. intros ?? H ??. exact (o_proper _ _ H _ _). Qed.

End binop.

(* ... which we now instantiate: *)

Lemma Qplus_nonneg (x y: Q): 0 <= x -> 0 <= y -> 0 <= x + y.
Proof. apply (Qplus_le_compat 0 x 0); assumption. Qed.

Lemma Qmin_nonneg (x y: Q): 0 <= x -> 0 <= y -> 0 <= Qmin x y.
Proof. apply Q.min_glb; assumption. Qed.

Lemma Qmax_nonneg (x y: Q): 0 <= x -> 0 <= y -> 0 <= Qmax x y.
Proof. intros. apply Qle_trans with x. assumption. apply Q.le_max_l. Qed.

Definition plus := binop Qplus Qplus_nonneg.
Definition mult := binop Qmult Qmult_le_0_compat.
Definition min := binop Qmin Qmin_nonneg.
Definition max := binop Qmax Qmax_nonneg.

Local Infix "+" := plus.
Local Infix "*" := mult.

Lemma plus_comm: forall x y, x + y == y + x.
Proof. intros. destruct x,y. unfold eq. simpl. ring. Qed.
Lemma mult_comm: forall x y, x * y == y * x. 
Proof. intros. destruct x,y. unfold eq. simpl. ring. Qed.
Lemma min_comm: forall x y, min x y == min y x.
Proof. intros. destruct x,y. unfold eq. simpl. apply Q.min_comm. Qed.
Lemma max_comm: forall x y, max x y == max y x. Proof binop_comm _ _ Q.max_comm.
Lemma plus_assoc: forall x y z, x + (y + z) == (x + y) + z. Proof binop_assoc _ _ Qplus_assoc.
Lemma mult_assoc: forall x y z, x * (y * z) == (x * y) * z. Proof binop_assoc _ _ Qmult_assoc.
Lemma max_assoc: forall x y z, max x (max y z) == max (max x y) z. Proof binop_assoc _ _ Q.max_assoc.
Lemma min_assoc: forall x y z, min x (min y z) == min (min x y) z. Proof binop_assoc _ _ Q.min_assoc.

Global Instance: Proper (eq ==> eq ==> eq) plus. Proof. unfold plus. apply _. Qed.
Global Instance: Proper (eq ==> eq ==> eq) mult. Proof. unfold mult. apply _. Qed.

(* Some additional properties: *)

Lemma plus_0_l x: 0 + x == x. Proof. unfold eq. simpl. apply Qplus_0_l. Qed.
Lemma plus_0_r x: x + 0 == x. Proof. unfold eq. simpl. apply Qplus_0_r. Qed.
Lemma mult_1_l x: 1 * x == x. Proof. unfold eq. simpl. apply Qmult_1_l. Qed.
Lemma mult_1_r x: x * 1 == x. Proof. unfold eq. simpl. apply Qmult_1_r. Qed.
Lemma mult_0_l q: 0 * q == 0. Proof. unfold eq. simpl. apply Qmult_0_l. Qed.
Lemma mult_0_r q: q * 0 == 0. Proof. unfold eq. simpl. apply Qmult_0_r. Qed.

(* Inverses: *)

Program Definition inv: T -> T := Qinv.

Next Obligation. destruct x as [[[] ?] ?]; auto. Qed.

Global Instance: Proper (eq ==> eq) inv.
Proof. unfold eq. repeat intro. simpl. apply Qinv_comp. assumption. Qed.

(* Coercions: *)

Module Export coercions.

Definition from_Qpos (q: Qpos): T
  := exist _ (proj1_sig q) (Qpos_nonneg q).

Lemma from_Qpos_plus_homo (x y: Qpos)
  : from_Qpos (Qpos_plus x y) == from_Qpos x + from_Qpos y.
Proof. reflexivity. Qed.

Global Instance from_Qpos_Proper: Proper (QposEq ==> eq) from_Qpos.
Proof. repeat intro. assumption. Qed.

Definition from_nat (n: nat): T.
Proof.
  exists (Z.of_nat n#1).
  unfold Qle; simpl. rewrite Z.mul_1_r. apply Nat2Z.is_nonneg.
Defined.

(*
Definition to_Q: T -> Q := @proj1_sig Q (Qle 0).

Global Coercion to_Q: T >-> Q.

Global Instance: Proper (eq ==> Qeq) to_Q.
Proof. repeat intro. assumption. Qed.
*)

End coercions.

(* Misc: *)

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

Lemma proj1_sig_nonNeg (q: T): 0 <= `q.
Proof. apply proj2_sig. Qed.

#[global]
Hint Immediate proj1_sig_nonNeg.

Lemma rect (P: T -> Type)
  (P0: forall (d: positive) H, P (exist (Qle 0) (0#d) H))
  (Pp: forall (n d: positive) H, P (exist (Qle 0) (Zpos n#d) H)): forall q, P q.
Proof.
 intros [[qn qd] E].
 destruct qn.
   apply P0.
  apply Pp.
 exfalso.
 apply E.
 reflexivity.
Defined.

Lemma Qpos_ind (P: T -> Prop) (Pwd: Proper (eq ==> iff) P) (P0: P 0)
      (Pp: forall q: Qpos, P (from_Qpos q)) : forall q, P q.
Proof with auto.
 intro.
 apply rect; intros.
  apply (Pwd 0)...
  reflexivity.
  assert (0 < (Z.pos n # d)). reflexivity.
  apply (Pwd (from_Qpos (exist _ _ H0))). reflexivity.
  apply Pp.
Qed.

(* Note: We can't make something as nice as Qpos_positive_numerator_rect for QnonNeg because
whereas Qpos contains a Qlt which contains a Zlt which is an equality between "comparison"'s,
proofs of which are unique because comparison is decidable, QnonNeg contains a Qle which
contains a Zle which is a negation of an equality between comparisons, proofs of which we
cannot prove uniqueness of. *)

(* Notations to be imported by clients: *)

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
