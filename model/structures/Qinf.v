Require Import
 Setoid Arith
 Qring QposInf
 stdlib_omissions.Q
 interfaces.abstract_algebra
 stdlib_rationals
 MathClasses.theory.setoids.

Inductive T: Set := finite (q: Q) | infinite.
  (* (This is positive infinity.) *)

Coercion finite: Q >-> T.

Instance eq: Equiv T := λ x y,
  match x, y with
  | infinite, infinite => True
  | finite a, finite b => a = b
  | _, _ => False
  end.

Instance finite_Proper: Proper (=) finite.
Proof. repeat intro. assumption. Qed.

Instance setoid: Setoid T.
Proof with intuition.
 constructor.
   intros []...
  intros [] [] ?...
 intros [x|] [y|] [z|] ??...
 change (x = z).
 transitivity y...
Qed.

Definition le (x y: T): Prop :=
  match x, y with
  | _, infinite => True
  | infinite, finite _ => False
  | finite a, finite b => Qle a b
  end.

Instance: Proper (=) le.
Proof.
 intros [|] [|] E [|] [|] F; intuition; simpl; try reflexivity.
 unfold equiv in * |-. simpl in *.
 now rewrite E, F.
Qed.

Instance: Zero T := finite 0%Q.

Instance plus: Plus T := λ x y,
  match x, y with
  | finite a, finite b => (a + b)%Q
  | _, _ => infinite
  end.

Coercion from_QposInf (q: QposInf): T :=
  match q with
  | QposInfinity => infinite
  | Qpos2QposInf u => u
  end.

Lemma QposInf_le_QinfLe (x y: QposInf): QposInf_le x y → le x y.
Proof. destruct x, y; auto. Qed.

Lemma le_0_plus_compat (x y: T): le 0 x → le 0 y → le 0 (x + y).
Proof with auto.
 destruct x, y...
 simpl. intros. apply Qplus_nonneg...
Qed.

Hint Resolve le_0_plus_compat.

Lemma le_0_Qpos (x: Qpos): le 0 x.
Proof. simpl. auto. Qed.

Hint Immediate le_0_Qpos.

Module notations.

  Delimit Scope Qinf_scope with Qinf.

  Global Infix "==" := eq: Qinf_scope.
  Global Infix "<=" := le: Qinf_scope.
  Global Infix "+" := plus: Qinf_scope.
  Global Infix "*" := mult: Qinf_scope.
  Global Notation Qinf := T.

End notations.
