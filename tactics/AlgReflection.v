(* Copyright © 1998-2006
 * Henk Barendregt
 * Luís Cruz-Filipe
 * Herman Geuvers
 * Mariusz Giero
 * Rik van Ginneken
 * Dimitri Hendriks
 * Sébastien Hinderer
 * Bart Kirkels
 * Pierre Letouzey
 * Iris Loeb
 * Lionel Mamane
 * Milad Niqui
 * Russell O’Connor
 * Randy Pollack
 * Nickolay V. Shmyrev
 * Bas Spitters
 * Dan Synek
 * Freek Wiedijk
 * Jan Zwanenburg
 *
 * This work is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This work is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this work; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 *)

(* begin hide *)
Require Export CLogic.
Require Export Bool.

Section Syntactic_Expressions.

Definition varindex : Set := nat.
Definition pfunindex : Set := nat.
Definition unopindex : Set := nat.
Definition binopindex : Set := nat.

Inductive expr : Set :=
  | expr_var : varindex -> expr
  | expr_int : Z -> expr
  | expr_plus : expr -> expr -> expr
  | expr_mult : expr -> expr -> expr
  | expr_div : expr -> expr -> expr
  | expr_unop : unopindex -> expr -> expr
  | expr_binop : binopindex -> expr -> expr -> expr
  | expr_part : pfunindex -> expr -> expr.

Definition expr_zero : expr := expr_int 0.
Definition expr_one : expr := expr_int 1.
Definition expr_nat (n:nat) : expr := expr_int (Z_of_nat n).
Definition expr_inv (e:expr) : expr := expr_mult e (expr_int (-1)).
Definition expr_minus (e e':expr) : expr := expr_plus e (expr_inv e').
Fixpoint expr_power (n:nat) (e:expr) {struct n} : expr :=
  match n with
  | O => expr_one
  | S m => expr_mult e (expr_power m e)
  end.

End Syntactic_Expressions.

Section Normalization_Function.

Fixpoint eq_nat (n m:nat) {struct n} : bool :=
  match n, m with
  | S n', S m' => eq_nat n' m'
  | O, O => true
  | _, _ => false
  end.

Fixpoint lt_nat (n m:nat) {struct n} : bool :=
  match n, m with
  | S n', S m' => lt_nat n' m'
  | O, S _ => true
  | _, _ => false
  end.

Definition le_nat (n m:nat) := orb (eq_nat n m) (lt_nat n m).

Definition eq_int (z z':Z) : bool :=
  match z, z' with
  | Zpos n, Zpos m => eq_nat (nat_of_P n) (nat_of_P m)
  | Z0, Z0 => true
  | Zneg n, Zneg m => eq_nat (nat_of_P n) (nat_of_P m)
  | _, _ => false
  end.

Definition lt_int (z z':Z) : bool :=
  match z, z' with
  | Zpos n, Zpos m => lt_nat (nat_of_P n) (nat_of_P m)
  | Zpos n, _ => false
  | Z0, Zpos n => true
  | Z0, _ => false
  | Zneg n, Zneg m => lt_nat (nat_of_P m) (nat_of_P n)
  | Zneg n, _ => true
  end.

Definition le_int (z z':Z) := orb (eq_int z z') (lt_int z z').

Fixpoint eq_expr (e f:expr) {struct e} : bool :=
  match e, f with
  | expr_var n, expr_var m => eq_nat n m
  | expr_int z, expr_int z' => eq_int z z'
  | expr_plus e1 e2, expr_plus f1 f2 => andb (eq_expr e1 f1) (eq_expr e2 f2)
  | expr_mult e1 e2, expr_mult f1 f2 => andb (eq_expr e1 f1) (eq_expr e2 f2)
  | expr_div e1 e2, expr_div f1 f2 => andb (eq_expr e1 f1) (eq_expr e2 f2)
  | expr_unop n e', expr_unop m f' => andb (eq_nat n m) (eq_expr e' f')
  | expr_binop n e' e'', expr_binop m f' f'' =>
      andb (eq_nat n m) (andb (eq_expr e' f') (eq_expr e'' f''))
  | expr_part n e', expr_part m f' => andb (eq_nat n m) (eq_expr e' f')
  | _, _ => false
  end.

Fixpoint lt_expr (e f:expr) {struct e} : bool :=
  match e, f with
  | expr_var n, expr_var m => lt_nat n m
  | expr_var n, _ => true
  | _, expr_var n => false
  | expr_int z, expr_int z' => lt_int z z'
  | expr_int _, _ => true
  | _, expr_int _ => false
  | expr_plus e1 e2, expr_plus f1 f2 =>
      orb (lt_expr e1 f1) (andb (eq_expr e1 f1) (lt_expr e2 f2))
  | expr_plus _ _, _ => true
  | _, expr_plus _ _ => false
  | expr_mult e1 e2, expr_mult f1 f2 =>
      orb (lt_expr e1 f1) (andb (eq_expr e1 f1) (lt_expr e2 f2))
  | expr_mult _ _, _ => true
  | _, expr_mult _ _ => false
  | expr_div e1 e2, expr_div f1 f2 =>
      orb (lt_expr e1 f1) (andb (eq_expr e1 f1) (lt_expr e2 f2))
  | expr_div _ _, _ => true
  | _, expr_div _ _ => false
  | expr_unop n e', expr_unop m f' =>
      orb (lt_nat n m) (andb (eq_nat n m) (lt_expr e' f'))
  | expr_unop _ _, _ => true
  | _, expr_unop _ _ => false
  | expr_binop n e' e'', expr_binop m f' f'' =>
      orb (lt_nat n m)
        (orb (andb (eq_nat n m) (lt_expr e' f'))
           (andb (eq_nat n m) (andb (eq_expr e' f') (lt_expr e'' f''))))
  | expr_binop _ _ _, _ => true
  | _, expr_binop _ _ _ => false
  | expr_part n e', expr_part m f' =>
      orb (lt_nat n m) (andb (eq_nat n m) (lt_expr e' f'))
  end.

Definition le_expr (e f:expr) := orb (eq_expr e f) (lt_expr e f).

Fixpoint eq_monom (e f:expr) {struct e} : bool :=
  match e, f with
  | expr_mult (expr_var n) e', expr_mult (expr_var m) f' =>
      andb (eq_nat n m) (eq_monom e' f')
  | expr_mult (expr_unop n e1) e', expr_mult (expr_unop m f1) f' =>
      andb (eq_nat n m) (andb (eq_monom e' f') (eq_expr e1 f1))
  | expr_mult (expr_binop n e1 e2) e', expr_mult (expr_binop m f1 f2) f' =>
      andb (eq_nat n m)
        (andb (eq_monom e' f') (andb (eq_expr e1 f1) (eq_expr e2 f2)))
  | expr_mult (expr_part n e1) e', expr_mult (expr_part m f1) f' =>
      andb (eq_nat n m) (andb (eq_monom e' f') (eq_expr e1 f1))
  | expr_int _, expr_int _ => true
  | _, _ => false
  end.

Fixpoint lt_monom (e f:expr) {struct e} : bool :=
  match e, f with
  | expr_mult (expr_var n) e', expr_mult (expr_var m) f' =>
      ifb (eq_nat n m) (lt_monom e' f') (lt_nat n m)
  | expr_mult (expr_var _) _, expr_mult (expr_unop _ _) _ => true
  | expr_mult (expr_var _) _, expr_mult (expr_binop _ _ _) _ => true
  | expr_mult (expr_var _) _, expr_mult (expr_part _ _) _ => true
  | expr_mult (expr_unop n e1) e', expr_mult (expr_unop m f1) f' =>
      ifb (eq_expr (expr_unop n e1) (expr_unop m f1)) (
        lt_expr e' f') (lt_expr (expr_unop n e1) (expr_unop m f1))
  | expr_mult (expr_unop _ _) _, expr_mult (expr_binop _ _ _) _ => true
  | expr_mult (expr_unop _ _) _, expr_mult (expr_part _ _) _ => true
  | expr_mult (expr_binop n e1 e2) e', expr_mult (expr_binop m f1 f2) f' =>
      ifb (eq_expr (expr_binop n e1 e2) (expr_binop m f1 f2)) (
        lt_expr e' f') (lt_expr (expr_binop n e1 e2) (expr_binop m f1 f2))
  | expr_mult (expr_binop _ _ _) _, expr_mult (expr_part _ _) _ => true
  | expr_mult (expr_part n e1) e', expr_mult (expr_part m f1) f' =>
      ifb (eq_expr (expr_part n e1) (expr_part m f1)) (
        lt_expr e' f') (lt_expr (expr_part n e1) (expr_part m f1))
  | _, expr_int _ => true
  | _, _ => false
  end.

Fixpoint MI_mult (e f:expr) {struct e} : expr :=
  let d := expr_mult e f in
  match e, f with
  | e, expr_int Z0 => expr_int 0
  | expr_mult e1 e2, f => expr_mult e1 (MI_mult e2 f)
  | expr_int i, expr_int j => expr_int (i * j)
  | _, _ => d
  end.

Fixpoint MV_mult (e f:expr) {struct e} : expr :=
  let d := expr_mult e f in
  match e, f with
  | expr_mult (expr_var n) e', expr_var m =>
      match lt_nat n m with
      | true => expr_mult (expr_var n) (MV_mult e' f)
      | false => expr_mult f e
      end
  | expr_mult (expr_var n) e', expr_unop _ _ =>
      expr_mult (expr_var n) (MV_mult e' f)
  | expr_mult (expr_var n) e', expr_binop _ _ _ =>
      expr_mult (expr_var n) (MV_mult e' f)
  | expr_mult (expr_var n) e', expr_part _ _ =>
      expr_mult (expr_var n) (MV_mult e' f)
  | expr_mult (expr_unop _ _) e', expr_var _ => expr_mult f e
  | expr_mult (expr_unop n e') e0, expr_unop m f' =>
      match lt_expr (expr_unop n e') f with
      | true => expr_mult (expr_unop n e') (MV_mult e0 f)
      | false => expr_mult f e
      end
  | expr_mult (expr_unop n e1) e', expr_binop _ _ _ =>
      expr_mult (expr_unop n e1) (MV_mult e' f)
  | expr_mult (expr_unop n e1) e', expr_part _ _ =>
      expr_mult (expr_unop n e1) (MV_mult e' f)
  | expr_mult (expr_binop _ _ _) e', expr_var _ => expr_mult f e
  | expr_mult (expr_binop _ _ _) e', expr_unop _ _ => expr_mult f e
  | expr_mult (expr_binop n e' e'') e0, expr_binop m f' f'' =>
      match lt_expr (expr_binop n e' e'') f with
      | true => expr_mult (expr_binop n e' e'') (MV_mult e0 f)
      | false => expr_mult f e
      end
  | expr_mult (expr_binop n e1 e2) e', expr_part _ _ =>
      expr_mult (expr_binop n e1 e2) (MV_mult e' f)
  | expr_mult (expr_part _ _) e', expr_var _ => expr_mult f e
  | expr_mult (expr_part _ _) e', expr_unop _ _ => expr_mult f e
  | expr_mult (expr_part _ _) e', expr_binop _ _ _ => expr_mult f e
  | expr_mult (expr_part n e') e0, expr_part m f' =>
      match lt_expr (expr_part n e') f with
      | true => expr_mult (expr_part n e') (MV_mult e0 f)
      | false => expr_mult f e
      end
  | expr_int i, f => MI_mult (expr_mult f expr_one) e
  | _, _ => d
  end.

Fixpoint MM_mult (e f:expr) {struct e} : expr :=
  let d := expr_mult e f in
  match e, f with
  | expr_mult e1 e2, f => MV_mult (MM_mult e2 f) e1
  | expr_int i, f => MI_mult f e
  | _, _ => d
  end.

Fixpoint MM_plus (e f:expr) {struct e} : expr :=
  let d := expr_plus e f in
  match e, f with
  | expr_mult (expr_var n) e', expr_mult (expr_var m) f' =>
      match eq_nat n m with
      | true => MV_mult (MM_plus e' f') (expr_var n)
      | false => d
      end
  | expr_mult (expr_unop g arg) e', expr_mult (expr_unop h arg') f' =>
      match eq_expr (expr_unop g arg) (expr_unop h arg') with
      | true => MV_mult (MM_plus e' f') (expr_unop g arg)
      | false => d
      end
  | expr_mult (expr_binop g e1 e2) e', expr_mult (expr_binop h f1 f2) f' =>
      match eq_expr (expr_binop g e1 e2) (expr_binop h f1 f2) with
      | true => MV_mult (MM_plus e' f') (expr_binop g e1 e2)
      | false => d
      end
  | expr_mult (expr_part g arg) e', expr_mult (expr_part h arg') f' =>
      match andb (eq_nat g h) (eq_expr arg arg') with
      | true => MV_mult (MM_plus e' f') (expr_part g arg)
      | false => d
      end
  | expr_int i, expr_int j => expr_int (i + j)
  | _, _ => d
  end.

Fixpoint PM_plus (e f:expr) {struct e} : expr :=
  let d := expr_plus e f in
  match e, f with
  | expr_plus e1 e2, expr_int _ => expr_plus e1 (PM_plus e2 f)
  | expr_int i, expr_int j => MM_plus e f
  | expr_plus e1 e2, f =>
      match eq_monom e1 f with
      | true => PM_plus e2 (MM_plus e1 f)
      | false =>
          match lt_monom e1 f with
          | true => expr_plus e1 (PM_plus e2 f)
          | false => expr_plus f e
          end
      end
  | expr_int i, f => expr_plus f e
  | _, _ => d
  end.

Fixpoint PP_plus (e f:expr) {struct e} : expr :=
  let d := expr_plus e f in
  match e, f with
  | expr_plus e1 e2, f => PM_plus (PP_plus e2 f) e1
  | expr_int i, f => PM_plus f e
  | _, _ => d
  end.

Fixpoint PM_mult (e f:expr) {struct e} : expr :=
  let d := expr_mult e f in
  match e, f with
  | expr_plus e1 e2, f => PM_plus (PM_mult e2 f) (MM_mult e1 f)
  | expr_int i, _ => PM_plus (expr_int 0) (MI_mult f e)
  | _, _ => d
  end.

Fixpoint PP_mult (e f:expr) {struct e} : expr :=
  let d := expr_mult e f in
  match e, f with
  | expr_plus e1 e2, f => PP_plus (PM_mult f e1) (PP_mult e2 f)
  | expr_int i, f => PM_mult f e
  | _, _ => d
  end.

Definition FF_plus (e f:expr) : expr :=
  let d := expr_plus e f in
  match e, f with
  | expr_div e1 e2, expr_div f1 f2 =>
      expr_div (PP_plus (PP_mult e1 f2) (PP_mult e2 f1)) (PP_mult e2 f2)
  | _, _ => d
  end.

Definition FF_mult (e f:expr) : expr :=
  let d := expr_mult e f in
  match e, f with
  | expr_div e1 e2, expr_div f1 f2 =>
      expr_div (PP_mult e1 f1) (PP_mult e2 f2)
  | _, _ => d
  end.

Definition FF_div (e f:expr) : expr :=
  let d := expr_div e f in
  match e, f with
  | expr_div e1 e2, expr_div f1 f2 =>
      expr_div (PP_mult e1 f2) (PP_mult e2 f1)
  | _, _ => d
  end.

Fixpoint NormR (e:expr) : expr :=
  match e with
  | expr_var n => expr_plus (expr_mult e expr_one) expr_zero
  | expr_int i => e
  | expr_plus e1 e2 => PP_plus (NormR e1) (NormR e2)
  | expr_mult e1 e2 => PP_mult (NormR e1) (NormR e2)
  | expr_div e1 e2 => e
  | expr_unop f e =>
      expr_plus (expr_mult (expr_unop f (NormR e)) expr_one) expr_zero
  | expr_binop f e e' =>
      expr_plus (expr_mult (expr_binop f (NormR e) (NormR e')) expr_one)
        expr_zero
  | expr_part f e =>
      expr_plus (expr_mult (expr_part f (NormR e)) expr_one) expr_zero
  end.

Definition NormG := NormR.

Fixpoint NormF (e:expr) : expr :=
  match e with
  | expr_var n =>
      expr_div (expr_plus (expr_mult e expr_one) expr_zero) expr_one
  | expr_int i => expr_div e expr_one
  | expr_plus e1 e2 => FF_plus (NormF e1) (NormF e2)
  | expr_mult e1 e2 => FF_mult (NormF e1) (NormF e2)
  | expr_div e1 e2 => FF_div (NormF e1) (NormF e2)
  | expr_unop f e =>
      expr_div
        (expr_plus (expr_mult (expr_unop f (NormF e)) expr_one) expr_zero)
        expr_one
  | expr_binop f e e' =>
      expr_div
        (expr_plus (expr_mult (expr_binop f (NormF e) (NormF e')) expr_one)
           expr_zero) expr_one
  | expr_part f e =>
      expr_div
        (expr_plus (expr_mult (expr_part f (NormF e)) expr_one) expr_zero)
        expr_one
  end.

Definition expr_is_zero (e:expr) : bool :=
  match e with
  | expr_div (expr_int Z0) _ => true
  | _ => false
  end.

End Normalization_Function.

Section Correctness_Results.

Lemma eq_nat_corr : forall n m:nat, eq_nat n m = true -> n = m.
Proof.
 simple induction n; simple induction m; simpl in |- *; intros.
    trivial.
   inversion H0.
  inversion H0.
 rewrite (H n1 H1). trivial.
Qed.

Lemma eq_int_corr : forall n m:Z, eq_int n m = true -> n = m.
Proof.
 simple induction n; simple induction m; simpl in |- *; intros.
         trivial.
        inversion H.
       inversion H.
      inversion H.
     rewrite <- (convert_is_POS p). rewrite <- (convert_is_POS p0).
     cut (nat_of_P p = nat_of_P p0). auto. apply eq_nat_corr. assumption.
      inversion H.
   inversion H.
  inversion H.
 cut (p = p0); intros.
  rewrite H0; auto.
 rewrite (anti_convert_pred_convert p). rewrite (anti_convert_pred_convert p0).
 cut (nat_of_P p = nat_of_P p0). intro. auto. apply eq_nat_corr. assumption.
Qed.

Lemma eq_expr_corr : forall e e':expr, eq_expr e e' = true -> e = e'.
Proof.
 simple induction e; simple induction e'; simpl in |- *; intros;
   try inversion H3; try inversion H2; try inversion H1; try inversion H0; try inversion H.
        cut (v = v0). intro. rewrite H0; auto. apply eq_nat_corr; assumption.
         cut (z = z0). intro. rewrite H0; auto. apply eq_int_corr; assumption.
        clear H1 H2. elim (andb_prop _ _ H3); intros.
      cut (e0 = e2). cut (e1 = e3). intros. rewrite H4; rewrite H6. auto.
       apply H0. assumption. apply H. assumption.
       clear H1 H2. elim (andb_prop _ _ H3); intros.
     cut (e0 = e2). cut (e1 = e3). intros. rewrite H4; rewrite H6. auto.
      apply H0. assumption. apply H. assumption.
      clear H1 H2. elim (andb_prop _ _ H3); intros.
    cut (e0 = e2). cut (e1 = e3). intros. rewrite H4; rewrite H6. auto.
     apply H0. assumption. apply H. assumption.
     clear H0. elim (andb_prop _ _ H1); intros.
   cut (u = u0). cut (e0 = e1). intros. rewrite H4. rewrite H5. auto.
    apply H. assumption. apply eq_nat_corr. assumption.
    clear H1 H2. elim (andb_prop _ _ H3). intros. elim (andb_prop _ _ H2); intros.
  cut (b = b0). cut (e0 = e2). cut (e1 = e3).
   intros. rewrite H7. rewrite H8. rewrite H9. auto.
     auto. auto. apply eq_nat_corr. assumption.
   clear H0. elim (andb_prop _ _ H1); intros.
 cut (p = p0). cut (e0 = e1). intros. rewrite H4. rewrite H5. auto.
  auto. apply eq_nat_corr. assumption.
Qed.

End Correctness_Results.

Ltac ClosedNat t :=
match t with
| O => constr:true
| (S ?n) => ClosedNat n
| _ => constr:false
end.

Ltac ClosedPositive t :=
match t with
| xH => constr:true
| (xI ?n) => ClosedPositive n
| (xO ?n) => ClosedPositive n
| _ => constr:false
end.

Ltac ClosedZ t :=
match t with
| Z0 => constr:true
| (Zpos ?n) => ClosedPositive n
| (Zneg ?n) => ClosedPositive n
| _ => constr:false
end.

(*To prevent universe inconsitencies, we need lists at a higher
type level than the one provided in algebra/ListType *)

Section MetaList.

Variable A : Type.

Inductive metalist : Type :=
  | Mnil : metalist
  | Mcons : A -> metalist -> metalist.

Fixpoint Mnth (n:nat) (l:metalist) (default:A) {struct l} : A :=
  match n, l with
  | O, Mcons x l' => x
  | O, other => default
  | S m, Mnil => default
  | S m, Mcons x t => Mnth m t default
  end.

End MetaList.
Implicit Arguments Mcons [A].
Implicit Arguments Mnth [A].

Ltac FindIndex t l :=
match l with
| (Mcons ?x ?xs) =>
  match x with
  | t => constr:O
  | _ => let n := FindIndex t xs in constr:(S n)
  end
end.

(*To prevent universe inconsitencies, we define quadruple,
rather than using the ProdT multiple times *)

Section Quadruple.
Variable A B C D: Type.

Inductive quadruple : Type :=
 Quad : A -> B -> C -> D -> quadruple.
End Quadruple.
Implicit Arguments Quad [A B C D].

(* end hide *)
