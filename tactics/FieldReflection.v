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
Require Export CFields.
Require Export AlgReflection.

Section Field_Interpretation_Function.

Variable F : CField.
Variable val : varindex -> F.
Variable unop : unopindex -> CSetoid_un_op F.
Variable binop : binopindex -> CSetoid_bin_op F.
Variable pfun : pfunindex -> PartFunct F.

Inductive interpF : expr -> F -> CProp :=
  | interpF_var :
      forall (i:varindex) (z:F), (val i[=]z) -> interpF (expr_var i) z
  | interpF_int : forall (k:Z) (z:F), (zring k[=]z) -> interpF (expr_int k) z
  | interpF_plus :
      forall (e f:expr) (x y z:F),
        (x[+]y[=]z) ->
        interpF e x -> interpF f y -> interpF (expr_plus e f) z
  | interpF_mult :
      forall (e f:expr) (x y z:F),
        (x[*]y[=]z) ->
        interpF e x -> interpF f y -> interpF (expr_mult e f) z
  | interpF_unop :
      forall (e:expr) (f:unopindex) (x z:F),
        (unop f x[=]z) -> interpF e x -> interpF (expr_unop f e) z
  | interpF_binop :
      forall (e e':expr) (f:binopindex) (x y z:F),
        (binop f x y[=]z) ->
        interpF e x -> interpF e' y -> interpF (expr_binop f e e') z
  | interpF_part :
      forall (e:expr) (f:pfunindex) (x z:F) (Hx:Dom (pfun f) x),
        (pfun f x Hx[=]z) -> interpF e x -> interpF (expr_part f e) z
  | interpF_div :
      forall (e f:expr) (x y z:F) (nzy:y[#][0]),
        ((x[/]y[//]nzy)[=]z) ->
        interpF e x -> interpF f y -> interpF (expr_div e f) z.

Definition wfF (e:expr) := sigT (interpF e).

Inductive xexprF : F -> Type :=
  | xexprF_var : forall i:varindex, xexprF (val i)
  | xexprF_int : forall k:Z, xexprF (zring k)
  | xexprF_plus : forall (x y:F) (e:xexprF x) (f:xexprF y), xexprF (x[+]y)
  | xexprF_mult : forall (x y:F) (e:xexprF x) (f:xexprF y), xexprF (x[*]y)
  | xexprF_unop : forall (x:F) (f:unopindex) (e:xexprF x), xexprF (unop f x)
  | xexprF_binop :
      forall (x y:F) (f:binopindex) (e:xexprF x) (e':xexprF y),
        xexprF (binop f x y)
  | xexprF_part :
      forall (x:F) (f:pfunindex) (e:xexprF x) (Hx:Dom (pfun f) x),
        xexprF (pfun f x Hx)
  | xexprF_div :
      forall (x y
              (* more things rrational translates: *)
              :F) (e:xexprF x) (f:xexprF y) (nzy:y[#][0]),
        xexprF (x[/]y[//]nzy)
  | xexprF_zero : xexprF [0]
  | xexprF_one : xexprF [1]
  | xexprF_nat : forall n:nat, xexprF (nring n)
  | xexprF_inv : forall (x:F) (e:xexprF x), xexprF [--]x
  | xexprF_minus : forall (x y:F) (e:xexprF x) (f:xexprF y), xexprF (x[-]y)
  | xexprF_power : forall (x:F) (e:xexprF x) (n:nat), xexprF (x[^]n).

Fixpoint xforgetF (x:F) (e:xexprF x) {struct e} : expr :=
  match e with
  | xexprF_var i => expr_var i
  | xexprF_int k => expr_int k
  | xexprF_plus _ _ e f => expr_plus (xforgetF _ e) (xforgetF _ f)
  | xexprF_mult _ _ e f => expr_mult (xforgetF _ e) (xforgetF _ f)
  | xexprF_unop _ f e => expr_unop f (xforgetF _ e)
  | xexprF_binop _ _ f e e' => expr_binop f (xforgetF _ e) (xforgetF _ e')
  | xexprF_part _ f e _ => expr_part f (xforgetF _ e)
  | xexprF_div _ _ e f _ => expr_div (xforgetF _ e) (xforgetF _ f)
  | xexprF_zero => expr_zero
  | xexprF_one => expr_one
  | xexprF_nat n => expr_nat n
  | xexprF_inv _ e => expr_inv (xforgetF _ e)
  | xexprF_minus _ _ e f => expr_minus (xforgetF _ e) (xforgetF _ f)
  | xexprF_power _ e n => expr_power n (xforgetF _ e)
  end.

Definition xinterpF (x:F) (e:xexprF x) := x.

Lemma xexprF2interpF : forall (x:F) (e:xexprF x), interpF (xforgetF _ e) x.
Proof.
 intros x e.
 induction e.
              apply (interpF_var i); algebra.
             apply (interpF_int k); algebra.
            apply (interpF_plus (xforgetF _ e1) (xforgetF _ e2) x y (x[+]y)); algebra.
           apply (interpF_mult (xforgetF _ e1) (xforgetF _ e2) x y (x[*]y)); algebra.
          apply (interpF_unop (xforgetF _ e) f x (unop f x)); algebra.
         apply (interpF_binop (xforgetF _ e1) (xforgetF _ e2) f x y (binop f x y)); algebra.
        eapply (interpF_part (xforgetF _ e) f x (pfun f x Hx)).
         apply eq_reflexive_unfolded.
        algebra.
       apply (interpF_div (xforgetF _ e1) (xforgetF _ e2) x y (x[/]y[//]nzy) nzy); algebra.
      apply (interpF_int 0); algebra.
     apply (interpF_int 1); Step_final ([1]:F).
    apply (interpF_int (Z_of_nat n)); algebra.
   apply (interpF_mult (xforgetF _ e) (expr_int (-1)) x (zring (-1)) [--]x); auto.
    Step_final (zring (-1)[*]x).
   apply (interpF_int (-1)); algebra.
  apply (interpF_plus (xforgetF _ e1) (xforgetF _ (xexprF_inv _ e2)) x [--]y (x[-]y)); algebra.
  apply (interpF_mult (xforgetF _ e2) (expr_int (-1)) y (zring (-1)) [--]y); auto.
   Step_final (zring (-1)[*]y).
  apply (interpF_int (-1)); algebra.
 induction n.
  apply (interpF_int 1); Step_final ([1]:F).
 apply (interpF_mult (xforgetF _ e) (expr_power n (xforgetF _ e)) x ( x[^]n) (x[^]S n)); algebra.
Qed.

Definition xexprF_diagram_commutes :
  forall (x:F) (e:xexprF x), interpF (xforgetF _ e) (xinterpF _ e) :=
  xexprF2interpF.

Lemma xexprF2wfF : forall (x:F) (e:xexprF x), wfF (xforgetF _ e).
Proof.
 intros x e.
 exists x.
 apply xexprF2interpF.
Qed.

Record fexprF : Type :=  {finterpF : F; fexprF2xexprF : xexprF finterpF}.

Definition fexprF_var (i:varindex) := Build_fexprF _ (xexprF_var i).
Definition fexprF_int (k:Z) := Build_fexprF _ (xexprF_int k).
Definition fexprF_plus (e e':fexprF) :=
  Build_fexprF _
    (xexprF_plus (finterpF e) (finterpF e') (fexprF2xexprF e)
       (fexprF2xexprF e')).
Definition fexprF_mult (e e':fexprF) :=
  Build_fexprF _
    (xexprF_mult (finterpF e) (finterpF e') (fexprF2xexprF e)
       (fexprF2xexprF e')).

Definition fforgetF (e:fexprF) := xforgetF (finterpF e) (fexprF2xexprF e).

Lemma fexprF2interpF : forall e:fexprF, interpF (fforgetF e) (finterpF e).
Proof.
 intros e.
 elim e. intros x e'.
 unfold fforgetF in |- *. simpl in |- *.
 apply xexprF2interpF.
Qed.

Lemma fexprF2wfF : forall e:fexprF, wfF (fforgetF e).
Proof.
 intro e.
 unfold fforgetF in |- *.
 apply xexprF2wfF.
Qed.

Load "Opaque_algebra".

Lemma refl_interpF :
 forall (e:expr) (x y:F), interpF e x -> interpF e y -> x[=]y.
Proof.
 intro e.
 induction e.
        intros x y Hx Hy.
        inversion Hx.
        inversion Hy.
        Step_final (val v).
       intros x y Hx Hy.
       inversion Hx.
       inversion Hy.
       Step_final (zring z:F).
      intros x y H1 H2.
      inversion H1.
      inversion H2.
      astepl (x0[+]y0).
      Step_final (x1[+]y1).
     intros x y H1 H2.
     inversion H1.
     inversion H2.
     astepl (x0[*]y0).
     Step_final (x1[*]y1).
    intros x y H0 H1.
    inversion H0.
    inversion H1.
    astepl (x0[/]y0[//]nzy). Step_final (x1[/]y1[//]nzy0).
    intros x y H0 H1.
   inversion H0.
   inversion H1.
   astepl (unop u x0); Step_final (unop u x1).
  intros x y H0 H1.
  inversion H0.
  inversion H1.
  astepl (binop b x0 y0); Step_final (binop b x1 y1).
 intros x y H0 H1.
 inversion H0.
 inversion H1.
 astepl (pfun p x0 Hx); Step_final (pfun p x1 Hx0).
Qed.

Lemma interpF_wd :
 forall (e:expr) (x y:F), interpF e x -> (x[=]y) -> interpF e y.
Proof.
 intros e x y H H0.
 inversion H; try (rewrite <- H2; rewrite H3 in H1). (* Compat 8.0 *)
        apply interpF_var. Step_final x.
        apply interpF_int. Step_final x.
       apply interpF_plus with x0 y0; auto. Step_final x.
      apply interpF_mult with x0 y0; auto. Step_final x.
     apply interpF_unop with x0; auto. Step_final x.
    apply interpF_binop with x0 y0; auto. Step_final x.
   apply interpF_part with x0 Hx; auto. Step_final x.
  apply interpF_div with x0 y0 nzy; auto. Step_final x.
Qed.

End Field_Interpretation_Function.

Section Field_NormCorrect.

Variable F : CField.
Variable val : varindex -> F.
Variable unop : unopindex -> CSetoid_un_op F.
Variable binop : binopindex -> CSetoid_bin_op F.
Variable pfun : pfunindex -> PartFunct F.

Notation II := (interpF F val unop binop pfun).

(*
four kinds of exprs:

  I	(expr_int _)
  V	(expr_var _)
  M	(expr_mult V M)
	I
  P	(expr_plus M P)
	I

M: sorted on V
P: sorted on M, all M's not an I
*)

Opaque Zmult.
Lemma MI_mult_corr_F :
 forall (e f:expr) (x y:F), II e x -> II f y -> II (MI_mult e f) (x[*]y).
Proof.
 cut (forall x y:F, II (expr_int 0) y -> II (expr_int 0) (x[*]y)).
  cut (forall (e1 e2 f:expr) (x y:F),
    (forall (f:expr) (x y:F), II e2 x -> II f y -> II (MI_mult e2 f) (x[*]y)) ->
      II (expr_mult e1 e2) x -> II f y -> II (expr_mult e1 (MI_mult e2 f)) (x[*]y)).
   cut (forall (i j:Z) (x y:F),
     II (expr_int i) x -> II (expr_int j) y -> II (expr_int (i * j)) (x[*]y)).
    cut (forall (e f:expr) (x y:F), II e x -> II f y -> II (expr_mult e f) (x[*]y)).
     simple induction e; simple induction f; simpl in |- *; auto.
            simple induction z; simpl in |- *; auto.
           simple induction z0; induction z; simpl in |- *; auto.
          simple induction z; simpl in |- *; auto.
         simple induction z; simpl in |- *; auto.
        induction f; simpl in |- *; auto.
         simple induction z; simpl in |- *; auto.
        simple induction z0; simpl in |- *; auto.
       simple induction z; simpl in |- *; auto.
      simple induction z; simpl in |- *; auto.
     simple induction z; simpl in |- *; auto.
    intros; apply interpF_mult with x y; algebra.
   intros; apply interpF_wd with (zring (i * j):F).
    apply interpF_int; algebra.
   inversion X. inversion X0.
   Step_final (zring i[*]zring j:F).
  intros. inversion X0.
  try (rewrite H in X2; rewrite H1 in X3; rewrite H0 in H2). (* compat 8.0 *)
  apply interpF_wd with (x0[*](y0[*]y)); algebra.
   apply interpF_mult with x0 (y0[*]y); algebra.
  Step_final (x0[*]y0[*]y).
 intros. inversion X. try (rewrite H in H0; rewrite H1 in H0). (* compat 8.0 *)
 apply interpF_wd with (zring 0:F).
  apply interpF_int; algebra.
 astepl ([0]:F).
 astepl (x[*][0]).
 Step_final (x[*]zring 0).
Qed.
Transparent Zmult.

Opaque MI_mult.
Lemma MV_mult_corr_F :
 forall (e f:expr) (x y:F), II e x -> II f y -> II (MV_mult e f) (x[*]y).
Proof.
 cut (forall (e1 e2 f:expr) (x y:F),
   (forall (f:expr) (x y:F), II e2 x -> II f y -> II (MV_mult e2 f) (x[*]y)) ->
     II (expr_mult e1 e2) x -> II f y -> II (expr_mult e1 (MV_mult e2 f)) (x[*]y)).
  cut (forall (e f:expr) (x y:F), II e x -> II f y -> II (MI_mult (expr_mult f expr_one) e) (x[*]y)).
   cut (forall (e f:expr) (x y:F), II e x -> II f y -> II (expr_mult f e) (x[*]y)).
    cut (forall (e f:expr) (x y:F), II e x -> II f y -> II (expr_mult e f) (x[*]y)).
     intros H H0 H1 H2 e. elim e.
     simpl in |- *; auto.
           simpl in |- *; auto.
          intros e1 H3 e2 H4.
          elim e1; simpl in |- *; auto.
         intros e1 H3 e2 H4.
         elim e1; simpl in |- *; auto.
            intros n f.
            elim f; simpl in |- *; auto.
            intro m.
            elim (lt_nat n m); simpl in |- *; auto.
           intros u e0 H5 f.
           elim f; simpl in |- *; auto.
           intros u0 e3 H6.
           elim lt_nat; simpl in |- *; auto.
           elim andb; simpl in |- *; auto.
          intros b e0 H6 e3 H7 f.
          elim f; simpl in |- *; auto.
          intros b0 e4 H8 e5 H9.
          elim lt_nat; simpl in |- *; auto.
          elim andb; simpl in |- *; auto.
          elim andb; simpl in |- *; auto.
         intros n f H5 f0.
         elim f0; simpl in |- *; auto.
         intros f1 e0 H6.
         elim lt_nat; simpl in |- *; auto.
         elim andb; simpl in |- *; auto.
        intros. simpl in |- *. auto.
        intros n e0 H3 f.
       elim f; simpl in |- *; auto.
      intros n e0 H3 e1 H4 f.
      elim f; simpl in |- *; auto.
     intros n e0 H3 f.
     elim f; simpl in |- *; auto.
    intros; apply interpF_mult with x y; algebra.
   intros; apply interpF_wd with (y[*]x); algebra.
   apply interpF_mult with y x; algebra.
  intros; apply interpF_wd with (y[*][1][*]x).
   apply MI_mult_corr_F; auto.
   apply interpF_mult with y ([1]:F); algebra.
   apply (interpF_int F val unop binop pfun 1); algebra.
  Step_final (x[*](y[*][1])).
 intros. inversion X0. try (rewrite H0 in H2; rewrite H in X2; rewrite H1 in X3). (* compat 8.0 *)
 apply interpF_wd with (x0[*](y0[*]y)).
  apply interpF_mult with x0 (y0[*]y); algebra.
 Step_final (x0[*]y0[*]y).
Qed.
Transparent MI_mult.

Opaque MV_mult MI_mult.
Lemma MM_mult_corr_F :
 forall (e f:expr) (x y:F), II e x -> II f y -> II (MM_mult e f) (x[*]y).
Proof.
 cut (forall (e1 e2 f:expr) (x y:F),
   (forall (f:expr) (x y:F), II e2 x -> II f y -> II (MM_mult e2 f) (x[*]y)) ->
     II (expr_mult e1 e2) x -> II f y -> II (MV_mult (MM_mult e2 f) e1) (x[*]y)).
  cut (forall (i:Z) (f:expr) (x y:F),
    II (expr_int i) x -> II f y -> II (MI_mult f (expr_int i)) (x[*]y)).
   cut (forall (e f:expr) (x y:F), II e x -> II f y -> II (expr_mult e f) (x[*]y)).
    intros H H0 H1 e.
    elim e; intros; simpl in |- *; auto.
   intros; apply interpF_mult with x y; algebra.
  intros; apply interpF_wd with (y[*]x); algebra.
  apply MI_mult_corr_F; auto.
 intros. inversion X0. try (rewrite H in X2; rewrite H1 in X3; rewrite H0 in H2). (* compat 8.0 *)
 apply interpF_wd with (y0[*]y[*]x0).
  apply MV_mult_corr_F; auto.
 astepl (x0[*](y0[*]y)).
 Step_final (x0[*]y0[*]y).
Qed.
Transparent MV_mult MI_mult.

Opaque MV_mult.
Lemma MM_plus_corr_F :
 forall (e f:expr) (x y:F), II e x -> II f y -> II (MM_plus e f) (x[+]y).
Proof.
 cut (forall (i j:Z) (x y:F),
   II (expr_int i) x -> II (expr_int j) y -> II (expr_int (i + j)) (x[+]y)).
  cut (forall (e f:expr) (x y:F), II e x -> II f y -> II (expr_plus e f) (x[+]y)).
   intros H H0 e; elim e.
          simpl in |- *; auto.
         intros z f; elim f; simpl in |- *; auto.
        simpl in |- *; auto.
       intros e1 H1 e2 H2.
       elim e1; simpl in |- *; auto.
          intros n f.
          elim f; simpl in |- *; auto.
          intros f1 H3 f2 H4.
          elim f1; simpl in |- *; auto.
          intro m.
          cut (eq_nat n m = true -> n = m).
           elim (eq_nat n m); simpl in |- *; auto.
           intros. inversion X. try (rewrite H6 in X1; rewrite H8 in X2; rewrite H7 in H9). (* compat 8.0 *)
           inversion X0. try (rewrite H10 in X3; rewrite H12 in X4; rewrite H11 in H13). (* compat 8.0 *)
           apply interpF_wd with ((y0[+]y1)[*]x0).
            apply MV_mult_corr_F; auto.
           astepl (x0[*](y0[+]y1)).
           astepl (x0[*]y0[+]x0[*]y1).
           cut (x0[=]x1). intro.
            Step_final (x0[*]y0[+]x1[*]y1).
           apply refl_interpF with val unop binop pfun (expr_var n).
            assumption.
           rewrite (H5 (refl_equal true)). assumption.
           intros; apply eq_nat_corr; auto.
         intros u e0 H3 f.
         elim f; simpl in |- *; auto.
         intros e3 H4 e4 H5.
         elim e3; simpl in |- *; auto.
         intros u0 e5 H6.
         cut (andb (eq_nat u u0) (eq_expr e0 e5) = true -> u = u0).
          cut (andb (eq_nat u u0) (eq_expr e0 e5) = true -> e0 = e5).
           elim andb; simpl in |- *; auto.
           intros H' H''. intros.
           inversion X. try (rewrite H7 in X1; rewrite H9 in X2; rewrite H8 in H10). (* compat 8.0 *)
           inversion X0. try (rewrite H11 in X3; rewrite H13 in X4; rewrite H12 in H14). (* compat 8.0 *)
           apply interpF_wd with ((y0[+]y1)[*]x0).
            apply MV_mult_corr_F; auto.
           astepr (x0[*]y0[+]x1[*]y1). astepl (y0[*]x0[+]y1[*]x0).
           apply bin_op_wd_unfolded. algebra. astepr (y1[*]x1). apply mult_wdr.
            apply refl_interpF with val unop binop pfun (expr_unop u e0).
            auto. rewrite H'. rewrite H''. auto. auto. auto.
           intro. elim (andb_prop _ _ H7); intros. apply eq_expr_corr; auto.
          intro. elim (andb_prop _ _ H7); intros. apply eq_nat_corr; auto.
         intros u e0 H3 e3 H4 f.
        elim f; simpl in |- *; auto.
        intros e4 H5 e5 H6.
        elim e4; simpl in |- *; auto.
        intros u0 e6 H7 e7 H8.
        cut (andb (eq_nat u u0) (andb (eq_expr e0 e6) (eq_expr e3 e7)) = true -> u = u0).
         cut (andb (eq_nat u u0) (andb (eq_expr e0 e6) (eq_expr e3 e7)) = true -> e0 = e6).
          cut (andb (eq_nat u u0) (andb (eq_expr e0 e6) (eq_expr e3 e7)) = true -> e3 = e7).
           elim andb; simpl in |- *; auto.
           intros H' H'' H'''. intros.
           inversion X. try (rewrite H9 in X1; rewrite H11 in X2; rewrite H10 in H12). (* compat 8.0 *)
           inversion X0. try (rewrite H13 in X3; rewrite H15 in X4; rewrite H14 in H16). (* compat 8.0 *)
           apply interpF_wd with ((y0[+]y1)[*]x0).
            apply MV_mult_corr_F; auto.
           astepr (x0[*]y0[+]x1[*]y1). astepl (y0[*]x0[+]y1[*]x0).
           apply bin_op_wd_unfolded. algebra. astepr (y1[*]x1). apply mult_wdr.
            apply refl_interpF with val unop binop pfun (expr_binop u e0 e3).
            auto. rewrite H'. rewrite H''. rewrite H'''. auto. auto. auto.
           auto.
          intro. elim (andb_prop _ _ H9); intros. elim (andb_prop _ _ H11); intros.
          apply eq_expr_corr; auto.
         intro. elim (andb_prop _ _ H9); intros. elim (andb_prop _ _ H11); intros.
         apply eq_expr_corr; auto.
        intro. elim (andb_prop _ _ H9); intros. apply eq_nat_corr; auto.
        intros f e0 H3.
       intro f0.
       elim f0; simpl in |- *; auto.
       intros e3 H4 e4 H5.
       elim e3; simpl in |- *; auto.
       intros f1 e5 H6.
       cut (andb (eq_nat f f1) (eq_expr e0 e5) = true -> f = f1).
        cut (andb (eq_nat f f1) (eq_expr e0 e5) = true -> e0 = e5).
         elim (andb (eq_nat f f1) (eq_expr e0 e5)); simpl in |- *; auto.
         intros.
         inversion X. try (rewrite H9 in X1; rewrite H11 in X2; rewrite H10 in H12). (* compat 8.0 *)
         inversion X0. try (rewrite H13 in X3; rewrite H15 in X4; rewrite H14 in H16). (* compat 8.0 *)
         apply interpF_wd with ((y0[+]y1)[*]x0).
          apply MV_mult_corr_F; auto.
         astepr (x0[*]y0[+]x1[*]y1). astepl (y0[*]x0[+]y1[*]x0).
         apply bin_op_wd_unfolded. algebra. astepr (y1[*]x1). apply mult_wdr.
          apply refl_interpF with val unop binop pfun (expr_part f e0).
          auto. rewrite H7. rewrite H8; auto. auto.
         intro. elim (andb_prop _ _ H7); intros. apply eq_expr_corr; auto.
        intro. elim (andb_prop _ _ H7); intros. apply eq_nat_corr; auto.
       simpl in |- *; auto.
     intros u e0 H1 f.
     elim f; simpl in |- *; auto.
    intros u e0 H1 e1 H2 f.
    elim f; simpl in |- *; auto.
   intros u e0 H1 f.
   elim f; simpl in |- *; auto.
  intros; apply interpF_plus with x y; algebra.
 intros. inversion X. try (rewrite H1 in H0; rewrite H in H0). (* compat 8.0 *)
 inversion X0. try (rewrite H2 in H3; rewrite H4 in H3). (* compat 8.0 *)
 apply interpF_wd with (zring (i + j):F).
  apply interpF_int; algebra.
 Step_final (zring i[+]zring j:F).
Qed.
Transparent MV_mult.

Opaque MM_plus.
Lemma PM_plus_corr_F :
 forall (e f:expr) (x y:F), II e x -> II f y -> II (PM_plus e f) (x[+]y).
Proof.
 cut (forall (e1 e2 f:expr) (x y:F),
   (forall (f:expr) (x y:F), II e2 x -> II f y -> II (PM_plus e2 f) (x[+]y)) ->
     II (expr_plus e1 e2) x -> II f y -> II (expr_plus e1 (PM_plus e2 f)) (x[+]y)).
  cut (forall (e1 e2 f:expr) (x y:F),
    (forall (f:expr) (x y:F), II e2 x -> II f y -> II (PM_plus e2 f) (x[+]y)) ->
      II (expr_plus e1 e2) x -> II f y -> II (PM_plus e2 (MM_plus e1 f)) (x[+]y)).
   cut (forall (e f:expr) (x y:F), II e x -> II f y -> II (MM_plus e f) (x[+]y)).
    cut (forall (e f:expr) (x y:F), II e x -> II f y -> II (expr_plus e f) (x[+]y)).
     cut (forall (e f:expr) (x y:F), II e x -> II f y -> II (expr_plus f e) (x[+]y)).
      intros H H0 H1 H2 H3 e. elim e.
      simpl in |- *; auto.
            intros z f; elim f; intros; simpl in |- *; auto.
           intros e1 H4 e2 H5 f. simpl in |- *.
           elim (lt_monom e1 f); elim (eq_monom e1 f); elim f; intros; simpl in |- *; auto.
          simpl in |- *; auto.
         simpl in |- *; auto.
        simpl in |- *; auto.
       simpl in |- *; auto.
      simpl in |- *; auto.
     intros; apply interpF_wd with (y[+]x); algebra.
     apply interpF_plus with y x; algebra.
    intros; apply interpF_plus with x y; algebra.
   intros; apply MM_plus_corr_F; auto.
  intros. inversion X0. try (rewrite H in X2; rewrite H1 in X3; rewrite H0 in H2). (* compat 8.0 *)
  apply interpF_wd with (y0[+](x0[+]y)).
   apply X; auto.
   apply MM_plus_corr_F; auto.
  astepl (y0[+]x0[+]y).
  Step_final (x0[+]y0[+]y).
 intros. inversion X0. try (rewrite H in X2; rewrite H1 in X3; rewrite H0 in H2). (* compat 8.0 *)
 apply interpF_wd with (x0[+](y0[+]y)).
  apply interpF_plus with x0 (y0[+]y); algebra.
 Step_final (x0[+]y0[+]y).
Qed.
Transparent MM_plus.

Opaque PM_plus.
Lemma PP_plus_corr_F :
 forall (e f:expr) (x y:F), II e x -> II f y -> II (PP_plus e f) (x[+]y).
Proof.
 cut (forall (e1 e2 f:expr) (x y:F),
   (forall (f:expr) (x y:F), II e2 x -> II f y -> II (PP_plus e2 f) (x[+]y)) ->
     II (expr_plus e1 e2) x -> II f y -> II (PM_plus (PP_plus e2 f) e1) (x[+]y)).
  cut (forall (i:Z) (f:expr) (x y:F),
    II (expr_int i) x -> II f y -> II (PM_plus f (expr_int i)) (x[+]y)).
   cut (forall (e f:expr) (x y:F), II e x -> II f y -> II (expr_plus e f) (x[+]y)).
    intros H H0 H1 e.
    elim e; intros; simpl in |- *; auto.
   intros. apply interpF_plus with x y; algebra.
   intros. apply interpF_wd with (y[+]x); algebra.
  apply PM_plus_corr_F; auto.
 intros. inversion X0. try (rewrite H in X2; rewrite H1 in X3; rewrite H0 in H2). (* compat 8.0 *)
 apply interpF_wd with (y0[+]y[+]x0).
  apply PM_plus_corr_F; auto.
 astepl (x0[+](y0[+]y)).
 Step_final (x0[+]y0[+]y).
Qed.
Transparent PM_plus.

Opaque PM_plus MM_mult MI_mult.
Lemma PM_mult_corr_F :
 forall (e f:expr) (x y:F), II e x -> II f y -> II (PM_mult e f) (x[*]y).
Proof.
 cut (forall (e1 e2 f:expr) (x y:F),
   (forall (f:expr) (x y:F), II e2 x -> II f y -> II (PM_mult e2 f) (x[*]y)) ->
     II (expr_plus e1 e2) x -> II f y -> II (PM_plus (PM_mult e2 f) (MM_mult e1 f)) (x[*]y)).
  cut (forall (i:Z) (f:expr) (x y:F), II (expr_int i) x ->
    II f y -> II (PM_plus (expr_int 0) (MI_mult f (expr_int i))) (x[*]y)).
   cut (forall (e f:expr) (x y:F), II e x -> II f y -> II (expr_mult e f) (x[*]y)).
    intros H H0 H1 e.
    elim e; intros; simpl in |- *; auto.
   intros. apply interpF_mult with x y; algebra.
   intros. apply interpF_wd with (zring 0[+]y[*]x).
  apply PM_plus_corr_F.
    apply interpF_int; algebra.
   apply MI_mult_corr_F; auto.
  astepl ([0][+]y[*]x).
  Step_final (y[*]x).
 intros. inversion X0. try (rewrite H in X2; rewrite H1 in X3; rewrite H0 in H2). (* compat 8.0 *)
 apply interpF_wd with (y0[*]y[+]x0[*]y).
  apply PM_plus_corr_F; auto.
  apply MM_mult_corr_F; auto.
 astepl ((y0[+]x0)[*]y).
 Step_final ((x0[+]y0)[*]y).
Qed.

Opaque PM_mult.
Lemma PP_mult_corr_F :
 forall (e f:expr) (x y:F), II e x -> II f y -> II (PP_mult e f) (x[*]y).
Proof.
 cut (forall (e1 e2 f:expr) (x y:F),
   (forall (f:expr) (x y:F), II e2 x -> II f y -> II (PP_mult e2 f) (x[*]y)) ->
     II (expr_plus e1 e2) x -> II f y -> II (PP_plus (PM_mult f e1) (PP_mult e2 f)) (x[*]y)).
  cut (forall (i:Z) (f:expr) (x y:F),
    II (expr_int i) x -> II f y -> II (PM_mult f (expr_int i)) (x[*]y)).
   cut (forall (e f:expr) (x y:F), II e x -> II f y -> II (expr_mult e f) (x[*]y)).
    intros H H0 H1 e.
    elim e; intros; simpl in |- *; auto.
   intros. apply interpF_mult with x y; algebra.
   intros. apply interpF_wd with (y[*]x); algebra.
  apply PM_mult_corr_F; auto.
 intros. inversion X0. try (rewrite H in X2; rewrite H1 in X3; rewrite H0 in H2). (* compat 8.0 *)
 apply interpF_wd with (y[*]x0[+]y0[*]y).
  apply PP_plus_corr_F; auto.
  apply PM_mult_corr_F; auto.
 astepl (x0[*]y[+]y0[*]y).
 Step_final ((x0[+]y0)[*]y).
Qed.

Transparent PP_plus PM_mult PP_mult PM_plus MI_mult.
Lemma FF_plus_corr_F :
 forall (e f:expr) (x y:F), II e x -> II f y -> II (FF_plus e f) (x[+]y).
Proof.
 cut (forall (e1 e2 f1 f2:expr) (x y:F), II (expr_div e1 e2) x -> II (expr_div f1 f2) y ->
   II (expr_div (PP_plus (PP_mult e1 f2) (PP_mult e2 f1)) (PP_mult e2 f2)) (x[+]y)).
  cut (forall (e f:expr) (x y:F), II e x -> II f y -> II (expr_plus e f) (x[+]y)).
   intros H H0 e f.
   elim e; elim f; intros; simpl in |- *; auto.
  intros. apply interpF_plus with x y; algebra.
  intros. inversion X.
 try (rewrite H in X1; rewrite H1 in X2; rewrite H0 in H2). (* compat 8.0 *)
 inversion X0.
 try (rewrite H3 in X3; rewrite H5 in X4; rewrite H4 in H6). (* compat 8.0 *)
 cut (y0[*]y1[#][0]). intro H13.
  apply interpF_div with (x0[*]y1[+]y0[*]x1) (y0[*]y1) H13; auto.
    astepl ((x0[*]y1[/] y0[*]y1[//]H13)[+](y0[*]x1[/] y0[*]y1[//]H13)).
    astepl ((x0[/] y0[//]nzy)[*](y1[/] y1[//]nzy0)[+] (y0[/] y0[//]nzy)[*](x1[/] y1[//]nzy0)).
    astepl ((x0[/] y0[//]nzy)[*][1][+][1][*](x1[/] y1[//]nzy0)).
    Step_final ((x0[/] y0[//]nzy)[+](x1[/] y1[//]nzy0)).
   apply PP_plus_corr_F; auto.
    apply PP_mult_corr_F; auto.
   apply PP_mult_corr_F; auto.
  apply PP_mult_corr_F; auto.
 apply mult_resp_ap_zero; auto.
Qed.

Lemma FF_mult_corr_F :
 forall (e f:expr) (x y:F), II e x -> II f y -> II (FF_mult e f) (x[*]y).
Proof.
 cut (forall (e1 e2 f1 f2:expr) (x y:F), II (expr_div e1 e2) x -> II (expr_div f1 f2) y ->
   II (expr_div (PP_mult e1 f1) (PP_mult e2 f2)) (x[*]y)).
  cut (forall (e f:expr) (x y:F), II e x -> II f y -> II (expr_mult e f) (x[*]y)).
   intros H H0 e f.
   elim e; elim f; intros; simpl in |- *; auto.
  intros. apply interpF_mult with x y; algebra.
  intros. inversion X.
 try (rewrite H in X1; rewrite H1 in X2; rewrite H0 in H2). (* compat 8.0 *)
 inversion X0.
 try (rewrite H3 in X3; rewrite H5 in X4; rewrite H4 in H6). (* compat 8.0 *)
 cut (y0[*]y1[#][0]). intro H13.
  apply interpF_div with (x0[*]x1) (y0[*]y1) H13.
    Step_final ((x0[/] y0[//]nzy)[*](x1[/] y1[//]nzy0)).
   apply PP_mult_corr_F; auto.
  apply PP_mult_corr_F; auto.
 apply mult_resp_ap_zero; auto.
Qed.

Transparent FF_div.
Lemma FF_div_corr_F :
 forall (e f:expr) (x y:F) (nzy:y[#][0]),
   II e x -> II f y -> II (FF_div e f) (x[/]y[//]nzy).
Proof.
 cut (forall (e1 e2 f1 f2:expr) (x y:F) (nzy:y[#][0]), II (expr_div e1 e2) x ->
   II (expr_div f1 f2) y -> II (expr_div (PP_mult e1 f2) (PP_mult e2 f1)) (x[/]y[//]nzy)).
  cut (forall (e f:expr) (x y:F) (nzy:y[#][0]), II e x -> II f y -> II (expr_div e f) (x[/]y[//]nzy)).
   intros H H0 e f.
   elim e; elim f; intros; simpl in |- *; auto.
  intros. apply interpF_div with x y nzy; algebra.
  intros. inversion X.
 try (rewrite H in X1; rewrite H1 in X2; rewrite H0 in H2). (* compat 8.0 *)
 inversion X0.
 try (rewrite H3 in X3; rewrite H5 in X4; rewrite H4 in H6). (* compat 8.0 *)
 cut (x1[#][0]). intro nzx1.
  cut (y0[*]x1[#][0]). intro H13.
   cut ((x1[/]y1[//]nzy1)[#][0]). intro H14.
    apply interpF_div with (x0[*]y1) (y0[*]x1) H13.
      astepl ((y1[*]x0)[/]y0[*]x1[//]H13).
      astepl (((y1[*]x0)[/]y0[//]nzy0)[/]x1[//]nzx1).
      astepl ((y1[*](x0[/]y0[//]nzy0))[/]x1[//]nzx1).
      astepl (((x0[/]y0[//]nzy0)[*]y1)[/]x1[//]nzx1).
      Step_final ((x0[/]y0[//]nzy0)[/]x1[/]y1[//]nzy1[//]H14).
     apply PP_mult_corr_F; auto.
    apply PP_mult_corr_F; auto.
   apply div_resp_ap_zero_rev; auto.
  apply mult_resp_ap_zero; auto.
 apply div_resp_ap_zero with y1 nzy1.
 astepl y. auto.
Qed.

Lemma NormF_corr : forall (e:expr) (x:F), II e x -> II (NormF e) x.
Proof.
 intro; elim e; intros; simpl in |- *.
        apply (interpF_div F val unop binop pfun
          (expr_plus (expr_mult (expr_var v) expr_one) expr_zero) expr_one x ([1]:F) x (ring_non_triv F)).
          algebra.
         apply (interpF_plus F val unop binop pfun (expr_mult (expr_var v) expr_one) expr_zero x ([0]:F) x).
           algebra.
          apply (interpF_mult F val unop binop pfun (expr_var v) expr_one x ([1]:F) x); algebra.
          apply (interpF_int F val unop binop pfun 1); algebra.
         apply (interpF_int F val unop binop pfun 0); algebra.
        apply (interpF_int F val unop binop pfun 1); algebra.
       apply (interpF_div F val unop binop pfun (expr_int z) expr_one x ( [1]:F) x (ring_non_triv F)).
         algebra. algebra. apply (interpF_int F val unop binop pfun 1); algebra.
        inversion X1. try (rewrite H in X2; rewrite H1 in X3; rewrite H0 in H2). (* compat 8.0 *)
      apply interpF_wd with (x0[+]y). apply FF_plus_corr_F; auto. auto.
       inversion X1. try (rewrite H in X2; rewrite H1 in X3; rewrite H0 in H2). (* compat 8.0 *)
     apply interpF_wd with (x0[*]y). apply FF_mult_corr_F; auto. auto.
      inversion X1. try (rewrite H in X2; rewrite H1 in X3; rewrite H0 in H2). (* compat 8.0 *)
    apply interpF_wd with (x0[/]y[//]nzy).
     apply FF_div_corr_F; auto. auto.
    inversion X0. try (rewrite H in H2; rewrite H1 in X1; rewrite H0 in H2). (* compat 8.0 *)
   apply (interpF_div F val unop binop pfun
     (expr_plus (expr_mult (expr_unop u (NormF e0)) expr_one) expr_zero)
       expr_one x ([1]:F) x (ring_non_triv F)).
     algebra.
    apply (interpF_plus F val unop binop pfun (expr_mult (expr_unop u (NormF e0)) expr_one) expr_zero x (
      [0]:F) x).
      algebra.
     apply (interpF_mult F val unop binop pfun (expr_unop u (NormF e0)) expr_one x ([1]:F) x); algebra.
      apply (interpF_unop F val unop binop pfun (NormF e0) u x0); algebra.
     apply (interpF_int F val unop binop pfun 1); algebra.
    apply (interpF_int F val unop binop pfun 0); algebra.
   apply (interpF_int F val unop binop pfun 1); algebra.
  inversion X1. try (rewrite H in H3; rewrite H1 in X2; rewrite H2 in X3; rewrite H0 in H3). (* compat 8.0 *)
  apply (interpF_div F val unop binop pfun
    (expr_plus (expr_mult (expr_binop b (NormF e0) (NormF e1)) expr_one)
      expr_zero) expr_one x ([1]:F) x (ring_non_triv F)).
    algebra.
   apply (interpF_plus F val unop binop pfun
     (expr_mult (expr_binop b (NormF e0) (NormF e1)) expr_one) expr_zero x ([0]:F) x).
     algebra.
    apply (interpF_mult F val unop binop pfun (expr_binop b (NormF e0) (NormF e1))
      expr_one x ([1]:F) x); algebra.
     apply (interpF_binop F val unop binop pfun (NormF e0) (NormF e1) b x0 y); algebra.
    apply (interpF_int F val unop binop pfun 1); algebra.
   apply (interpF_int F val unop binop pfun 0); algebra.
  apply (interpF_int F val unop binop pfun 1); algebra.
 inversion X0.
 try ((generalize Hx H2; clear Hx H2; rewrite H; intros Hx H2);
   rewrite H1 in X1; rewrite H0 in H2). (* compat 8.0 *)
 apply (interpF_div F val unop binop pfun
   (expr_plus (expr_mult (expr_part p (NormF e0)) expr_one) expr_zero)
     expr_one x ([1]:F) x (ring_non_triv F)).
   algebra.
  apply (interpF_plus F val unop binop pfun (expr_mult (expr_part p (NormF e0)) expr_one) expr_zero x (
    [0]:F) x).
    algebra.
   apply (interpF_mult F val unop binop pfun (expr_part p (NormF e0)) expr_one x ([1]:F) x); algebra.
    apply (interpF_part F val unop binop pfun (NormF e0) p x0) with (Hx := Hx); algebra.
   apply (interpF_int F val unop binop pfun 1); algebra.
  apply (interpF_int F val unop binop pfun 0); algebra.
 apply (interpF_int F val unop binop pfun 1); algebra.
Qed.

Lemma Norm_wfF :
 forall e:expr,
   wfF F val unop binop pfun e -> wfF F val unop binop pfun (NormF e).
Proof.
 unfold wfF in |- *.
 intros.
 elim X.
 intros.
 exists x.
 apply NormF_corr.
 assumption.
Qed.

Lemma expr_is_zero_corr_F :
 forall e:expr,
   wfF F val unop binop pfun e -> expr_is_zero e = true -> II e [0].
Proof.
 unfold wfF in |- *.
 intros e H.
 elim H. intro.
 elim e; simpl in |- *; try (intros; elimtype False; inversion H0; fail).
 intros e0 H0 e1 H1.
 elim e0; simpl in |- *; try (intros; elimtype False; inversion H2; fail).
 intro.
 elim z; simpl in |- *; try (intros; elimtype False; inversion H2; fail); intros H2 H3.
 inversion H2. try (rewrite H4 in X; rewrite H6 in X0; rewrite H5 in H7). (* compat 8.0 *)
 apply interpF_div with ([0]:F) y nzy; auto.
  algebra.
 apply (interpF_int F val unop binop pfun 0); algebra.
Qed.

Lemma Tactic_lemma_zero_F :
 forall (x:F) (e:xexprF F val unop binop pfun x),
   expr_is_zero (NormF (xforgetF _ _ _ _ _ _ e)) = true -> x[=][0].
Proof.
 intros.
 apply refl_interpF with val unop binop pfun (NormF (xforgetF _ _ _ _ _ _ e)).
  apply NormF_corr.
  apply xexprF2interpF.
 apply expr_is_zero_corr_F.
  apply Norm_wfF.
  apply xexprF2wfF.
 assumption.
Qed.

Lemma Tactic_lemmaF :
 forall (x y:F) (e:xexprF F val unop binop pfun x)
   (f:xexprF F val unop binop pfun y),
   expr_is_zero
     (NormF (xforgetF _ _ _ _ _ _ (xexprF_minus _ _ _ _ _ _ _ e f))) = true ->
   x[=]y.
Proof.
 intros.
 apply cg_inv_unique_2.
 apply Tactic_lemma_zero_F with (xexprF_minus _ _ _ _ _ _ _ e f).
 assumption.
Qed.

End Field_NormCorrect.

Ltac QuoteF R l t :=
match l with
 (Quad ?vl ?ul ?bl ?pl) =>
(let a := constr:(fun n:varindex => (Mnth n vl (cm_unit R))) in
 let b := constr:(fun n:unopindex => (Mnth n ul (@cg_inv R))) in
 let c := constr:(fun n:binopindex => (Mnth n bl (@csg_op R))) in
 let d := constr:(fun n:pfunindex => (Mnth n pl (total_eq_part _ (@cg_inv R)))) in
 match t with
 | (zring ?k) =>
    match (ClosedZ k) with
    | true => constr:(xexprF_int R a b c d k)
    end
 | (csbf_fun _ _ _ csg_op ?x ?y) =>
    let x' := QuoteF R l x in
    let y' := QuoteF R l y in
    constr:(xexprF_plus R a b c d _ _ x' y')
 | (csbf_fun _ _ _ cr_mult ?x ?y) =>
    let x' := QuoteF R l x in
    let y' := QuoteF R l y in
    constr:(xexprF_mult R a b c d _ _ x' y')
 | (cf_div ?x ?y ?H) =>
    let x' := QuoteF R l x in
    let y' := QuoteF R l y in
    constr:(xexprF_div R a b c d _ _ x' y' H)
 | ([0]) => constr:(xexprF_zero R a b c d)
 | ([1]) => constr:(xexprF_one R a b c d)
 | (nring ?n) =>
    match (ClosedNat n) with
    | true => constr:(xexprF_nat R a b c d n)
    end
 | (csf_fun _ _ cg_inv ?x) =>
    let x' := QuoteF R l x in
    constr:(xexprF_inv R a b c d _ x')
 | (cg_minus ?x ?y) =>
    let x' := QuoteF R l x in
    let y' := QuoteF R l y in
    constr:(xexprF_minus R a b c d _ _ x' y')
 | (csf_fun _ _ (@nexp_op _ ?n) ?x) =>
    match (ClosedNat n) with
    | true => let x' := QuoteF R l x in
              constr:(xexprF_power R a b c d _ x' n)
    end
 | (pfpfun ?f ?x ?h) =>
    let x' := QuoteF R l x in
    let i := FindIndex f pl in
    constr:(xexprF_part R a b c d _ i x' h)
 | (csf_fun _ _ ?f ?x) =>
    let x' := QuoteF R l x in
    let i := FindIndex f ul in
    constr:(xexprF_unop R a b c d _ i x')
 | (csbf_fun _ _ _ ?f ?x ?y) =>
    let x' := QuoteF R l x in
    let y' := QuoteF R l y in
    let i := FindIndex f bl in
    constr:(xexprF_binop R a b c d _ _ i x' y')
 | ?t =>
    let i := FindIndex t vl in
    constr:(xexprF_var R a b c d i)
end)
end.

Ltac FindTermVariablesF t l :=
match t with
| (zring ?k) =>
    match (ClosedZ k) with
    | true => constr:l
    end
| (csbf_fun _ _ _ csg_op ?x ?y) =>
    let l1 := FindTermVariablesF x l in
    let l2 := FindTermVariablesF y l1 in
    constr:l2
| (csbf_fun _ _ _ cr_mult ?x ?y) =>
    let l1 := FindTermVariablesF x l in
    let l2 := FindTermVariablesF y l1 in
    constr:l2
| (cf_div ?x ?y ?H) =>
    let l1 := FindTermVariablesF x l in
    let l2 := FindTermVariablesF y l1 in
    constr:l2
| ([0]) => constr:l
| ([1]) => constr:l
| (nring ?n) =>
    match (ClosedNat n) with
    | true => constr:l
    end
| (csf_fun _ _ cg_inv ?x) =>
    let l1 := FindTermVariablesF x l in
    constr:l1
| (cg_minus ?x ?y) =>
    let l1 := FindTermVariablesF x l in
    let l2 := FindTermVariablesF y l1 in
    constr:l2
| (csf_fun _ _ (@nexp_op _ ?n) ?x) =>
    match (ClosedNat n) with
    | true => let l1 := FindTermVariablesF x l in
              constr:l1
    end
| (pfpfun ?f ?x ?h) =>
    let l1 := FindTermVariablesF x l in
    match l1 with
     (Quad ?vl ?ul ?bl ?pl) => constr:(Quad vl ul bl (Mcons f pl))
    end
| (csf_fun _ _ ?f ?x) =>
    let l1 := FindTermVariablesF x l in
    match l1 with
     (Quad ?vl ?ul ?bl ?pl) => constr:(Quad vl (Mcons f ul) bl pl)
    end
| (csbf_fun _ _ _ ?f ?x ?y) =>
    let l1 := FindTermVariablesF x l in
    let l2 := FindTermVariablesF y l1 in
    match l2 with
     (Quad ?vl ?ul ?bl ?pl) => constr:(Quad vl ul (Mcons f bl) pl)
    end
| ?t => match l with
         (Quad ?vl ?ul ?bl ?pl) => constr:(Quad (Mcons t vl) ul bl pl)
        end
end.

Ltac FindTermsVariablesF fn t1 t2 :=
    let l1 := FindTermVariablesF t1 (Quad (Mnil fn) (Mnil (CSetoid_un_op fn)) (Mnil (CSetoid_bin_op fn)) (Mnil (PartFunct fn))) in
    let l2 := FindTermVariablesF t2 l1 in
    constr:l2.

Ltac rationalF F x y :=
                 let l:=FindTermsVariablesF F x y in
                 let t1:=(QuoteF F l x) in
                 let t2:=(QuoteF F l y) in
                 eapply Tactic_lemmaF with (e:=t1) (f:=t2)
                 ; reflexivity.

(* end hide *)
