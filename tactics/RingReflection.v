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
Require Export CRings.
Require Export AlgReflection.

Section Ring_Interpretation_Function.

Variable R : CRing.
Variable val : varindex -> R.
Variable unop : unopindex -> CSetoid_un_op R.
Variable binop : binopindex -> CSetoid_bin_op R.
Variable pfun : pfunindex -> PartFunct R.

Inductive interpR : expr -> R -> CProp :=
  | interpR_var :
      forall (i:varindex) (z:R), (val i[=]z) -> interpR (expr_var i) z
  | interpR_int : forall (k:Z) (z:R), (zring k[=]z) -> interpR (expr_int k) z
  | interpR_plus :
      forall (e f:expr) (x y z:R),
        (x[+]y[=]z) ->
        interpR e x -> interpR f y -> interpR (expr_plus e f) z
  | interpR_mult :
      forall (e f:expr) (x y z:R),
        (x[*]y[=]z) ->
        interpR e x -> interpR f y -> interpR (expr_mult e f) z
  | interpR_unop :
      forall (e:expr) (f:unopindex) (x z:R),
        (unop f x[=]z) -> interpR e x -> interpR (expr_unop f e) z
  | interpR_binop :
      forall (e e':expr) (f:binopindex) (x y z:R),
        (binop f x y[=]z) ->
        interpR e x -> interpR e' y -> interpR (expr_binop f e e') z
  | interpR_part :
      forall (e:expr) (f:pfunindex) (x z:R) (Hx:Dom (pfun f) x),
        (pfun f x Hx[=]z) -> interpR e x -> interpR (expr_part f e) z.

Definition wfR (e:expr) := sigT (interpR e).

Inductive xexprR : R -> Type :=
  | xexprR_var : forall i:varindex, xexprR (val i)
  | xexprR_int : forall k:Z, xexprR (zring k)
  | xexprR_plus : forall (x y:R) (e:xexprR x) (f:xexprR y), xexprR (x[+]y)
  | xexprR_mult : forall (x y:R) (e:xexprR x) (f:xexprR y), xexprR (x[*]y)
  | xexprR_unop : forall (x:R) (f:unopindex) (e:xexprR x), xexprR (unop f x)
  | xexprR_binop :
      forall (x y:R) (f:binopindex) (e:xexprR x) (e':xexprR y),
        xexprR (binop f x y)
  | xexprR_part :
      forall (x:R) (f:pfunindex) (e:xexprR x) (Hx:Dom (pfun f) x),
        xexprR (pfun f x Hx)
        (* more things rrational translates: *)
  | xexprR_zero : xexprR [0]
  | xexprR_one : xexprR [1]
  | xexprR_nat : forall n:nat, xexprR (nring n)
  | xexprR_inv : forall (x:R) (e:xexprR x), xexprR [--]x
  | xexprR_minus : forall (x y:R) (e:xexprR x) (f:xexprR y), xexprR (x[-]y)
  | xexprR_power : forall (x:R) (e:xexprR x) (n:nat), xexprR (x[^]n).

Fixpoint xforgetR (x:R) (e:xexprR x) {struct e} : expr :=
  match e with
  | xexprR_var i => expr_var i
  | xexprR_int k => expr_int k
  | xexprR_plus _ _ e f => expr_plus (xforgetR _ e) (xforgetR _ f)
  | xexprR_mult _ _ e f => expr_mult (xforgetR _ e) (xforgetR _ f)
  | xexprR_unop _ f e => expr_unop f (xforgetR _ e)
  | xexprR_binop _ _ f e e' => expr_binop f (xforgetR _ e) (xforgetR _ e')
  | xexprR_part _ f e _ => expr_part f (xforgetR _ e)
  | xexprR_zero => expr_zero
  | xexprR_one => expr_one
  | xexprR_nat n => expr_nat n
  | xexprR_inv _ e => expr_inv (xforgetR _ e)
  | xexprR_minus _ _ e f => expr_minus (xforgetR _ e) (xforgetR _ f)
  | xexprR_power _ e n => expr_power n (xforgetR _ e)
  end.

Definition xinterpR (x:R) (e:xexprR x) := x.

Lemma xexprR2interpR : forall (x:R) (e:xexprR x), interpR (xforgetR _ e) x.
Proof.
 intros x e.
 induction e.
             apply (interpR_var i); algebra.
            apply (interpR_int k); algebra.
           apply (interpR_plus (xforgetR _ e1) (xforgetR _ e2) x y (x[+]y)); algebra.
          apply (interpR_mult (xforgetR _ e1) (xforgetR _ e2) x y (x[*]y)); algebra.
         apply (interpR_unop (xforgetR _ e) f x (unop f x)); algebra.
        apply (interpR_binop (xforgetR _ e1) (xforgetR _ e2) f x y (binop f x y)); algebra.
       eapply (interpR_part (xforgetR _ e) f x (pfun f x Hx)).
        apply eq_reflexive_unfolded.
       algebra.
      apply (interpR_int 0); algebra.
     apply (interpR_int 1); Step_final ([1]:R).
    apply (interpR_int (Z_of_nat n)); algebra.
   apply (interpR_mult (xforgetR _ e) (expr_int (-1)) x (zring (-1)) [--]x); auto.
    Step_final (zring (-1)[*]x).
   apply (interpR_int (-1)); algebra.
  apply (interpR_plus (xforgetR _ e1) (xforgetR _ (xexprR_inv _ e2)) x [--]y (x[-]y)); algebra.
  apply (interpR_mult (xforgetR _ e2) (expr_int (-1)) y (zring (-1)) [--]y); auto.
   Step_final (zring (-1)[*]y).
  apply (interpR_int (-1)); algebra.
 induction n.
  apply (interpR_int 1); Step_final ([1]:R).
 apply (interpR_mult (xforgetR _ e) (expr_power n (xforgetR _ e)) x ( x[^]n) (x[^]S n)); algebra.
Qed.

Definition xexprR_diagram_commutes :
  forall (x:R) (e:xexprR x), interpR (xforgetR _ e) (xinterpR _ e) :=
  xexprR2interpR.

Lemma xexprR2wfR : forall (x:R) (e:xexprR x), wfR (xforgetR _ e).
Proof.
 intros x e.
 exists x.
 apply xexprR2interpR.
Qed.

Record fexprR : Type :=  {finterpR : R; fexprR2xexprR : xexprR finterpR}.

Definition fexprR_var (i:varindex) := Build_fexprR _ (xexprR_var i).
Definition fexprR_int (k:Z) := Build_fexprR _ (xexprR_int k).
Definition fexprR_plus (e e':fexprR) :=
  Build_fexprR _
    (xexprR_plus (finterpR e) (finterpR e') (fexprR2xexprR e)
       (fexprR2xexprR e')).
Definition fexprR_mult (e e':fexprR) :=
  Build_fexprR _
    (xexprR_mult (finterpR e) (finterpR e') (fexprR2xexprR e)
       (fexprR2xexprR e')).

Definition fforgetR (e:fexprR) := xforgetR (finterpR e) (fexprR2xexprR e).

Lemma fexprR2interp : forall e:fexprR, interpR (fforgetR e) (finterpR e).
Proof.
 intros e.
 elim e. intros x e'.
 unfold fforgetR in |- *. simpl in |- *.
 apply xexprR2interpR.
Qed.

Lemma fexprR2wf : forall e:fexprR, wfR (fforgetR e).
Proof.
 intro e.
 unfold fforgetR in |- *.
 apply xexprR2wfR.
Qed.

Opaque csg_crr.
Opaque cm_crr.
Opaque cg_crr.
Opaque cr_crr.
Opaque csf_fun.
Opaque csbf_fun.
Opaque csr_rel.
Opaque cs_eq.
Opaque cs_neq.
Opaque cs_ap.
Opaque cm_unit.
Opaque csg_op.
Opaque cg_inv.
Opaque cg_minus.
Opaque cr_one.
Opaque cr_mult.
Opaque nexp_op.

Lemma refl_interpR :
 forall (e:expr) (x y:R), interpR e x -> interpR e y -> x[=]y.
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
       Step_final (zring z:R).
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

Lemma interpR_wd :
 forall (e:expr) (x y:R), interpR e x -> (x[=]y) -> interpR e y.
Proof.
 intros e x y H H0.
 inversion H; (* inversion bug fixed in V8.1 makes these rewritings useless *)
 try (rewrite <- H2; rewrite H3 in H1).
       apply interpR_var. Step_final x.
       apply interpR_int. Step_final x.
      apply interpR_plus with x0 y0; auto. Step_final x.
     apply interpR_mult with x0 y0; auto. Step_final x.
    apply interpR_unop with x0; auto. Step_final x.
   apply interpR_binop with x0 y0; auto. Step_final x.
  apply interpR_part with x0 Hx; auto. Step_final x.
Qed.

End Ring_Interpretation_Function.

Section Ring_NormCorrect.

Variable R : CRing.
Variable val : varindex -> R.
Variable unop : unopindex -> CSetoid_un_op R.
Variable binop : binopindex -> CSetoid_bin_op R.
Variable pfun : pfunindex -> PartFunct R.

Notation II := (interpR R val unop binop pfun).

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
Lemma MI_mult_corr_R :
 forall (e f:expr) (x y:R), II e x -> II f y -> II (MI_mult e f) (x[*]y).
Proof.
 cut (forall x y:R, II (expr_int 0) y -> II (expr_int 0) (x[*]y)).
  cut (forall (e1 e2 f:expr) (x y:R),
    (forall (f:expr) (x y:R), II e2 x -> II f y -> II (MI_mult e2 f) (x[*]y)) ->
      II (expr_mult e1 e2) x -> II f y -> II (expr_mult e1 (MI_mult e2 f)) (x[*]y)).
   cut (forall (i j:Z) (x y:R),
     II (expr_int i) x -> II (expr_int j) y -> II (expr_int (i * j)) (x[*]y)).
    cut (forall (e f:expr) (x y:R), II e x -> II f y -> II (expr_mult e f) (x[*]y)).
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
    intros; apply interpR_mult with x y; algebra.
   intros; apply interpR_wd with (zring (i * j):R).
    apply interpR_int; algebra.
   inversion X. inversion X0.
   Step_final (zring i[*]zring j:R).
  intros. inversion X0.
  try (rewrite H in X2; rewrite H1 in X3; rewrite H0 in H2). (* compat 8.0 *)
  apply interpR_wd with (x0[*](y0[*]y)); algebra.
   apply interpR_mult with x0 (y0[*]y); algebra.
  Step_final (x0[*]y0[*]y).
 intros. inversion X.
 try (rewrite H in H0; rewrite H1 in H0). (* compat 8.0 *)
 apply interpR_wd with (zring 0:R).
  apply interpR_int; algebra.
 astepl ([0]:R).
 astepl (x[*][0]).
 Step_final (x[*]zring 0).
Qed.
Transparent Zmult.

Opaque MI_mult.
Lemma MV_mult_corr_R :
 forall (e f:expr) (x y:R), II e x -> II f y -> II (MV_mult e f) (x[*]y).
Proof.
 cut (forall (e1 e2 f:expr) (x y:R),
   (forall (f:expr) (x y:R), II e2 x -> II f y -> II (MV_mult e2 f) (x[*]y)) ->
     II (expr_mult e1 e2) x -> II f y -> II (expr_mult e1 (MV_mult e2 f)) (x[*]y)).
  cut (forall (e f:expr) (x y:R), II e x -> II f y -> II (MI_mult (expr_mult f expr_one) e) (x[*]y)).
   cut (forall (e f:expr) (x y:R), II e x -> II f y -> II (expr_mult f e) (x[*]y)).
    cut (forall (e f:expr) (x y:R), II e x -> II f y -> II (expr_mult e f) (x[*]y)).
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
        intros. inversion X1.
        intros n e0 H3 f.
       elim f; simpl in |- *; auto.
      intros n e0 H3 e1 H4 f.
      elim f; simpl in |- *; auto.
     intros n e0 H3 f.
     elim f; simpl in |- *; auto.
    intros; apply interpR_mult with x y; algebra.
   intros; apply interpR_wd with (y[*]x); algebra.
   apply interpR_mult with y x; algebra.
  intros; apply interpR_wd with (y[*][1][*]x).
   apply MI_mult_corr_R; auto.
   apply interpR_mult with y ([1]:R); algebra.
   apply (interpR_int R val unop binop pfun 1); algebra.
  Step_final (x[*](y[*][1])).
 intros. inversion X0.
 try (rewrite H0 in H2; rewrite H in X2; rewrite H1 in X3). (* compat 8.0 *)
 apply interpR_wd with (x0[*](y0[*]y)).
  apply interpR_mult with x0 (y0[*]y); algebra.
 Step_final (x0[*]y0[*]y).
Qed.
Transparent MI_mult.

Opaque MV_mult MI_mult.
Lemma MM_mult_corr_R :
 forall (e f:expr) (x y:R), II e x -> II f y -> II (MM_mult e f) (x[*]y).
Proof.
 cut (forall (e1 e2 f:expr) (x y:R),
   (forall (f:expr) (x y:R), II e2 x -> II f y -> II (MM_mult e2 f) (x[*]y)) ->
     II (expr_mult e1 e2) x -> II f y -> II (MV_mult (MM_mult e2 f) e1) (x[*]y)).
  cut (forall (i:Z) (f:expr) (x y:R),
    II (expr_int i) x -> II f y -> II (MI_mult f (expr_int i)) (x[*]y)).
   cut (forall (e f:expr) (x y:R), II e x -> II f y -> II (expr_mult e f) (x[*]y)).
    intros H H0 H1 e.
    elim e; intros; simpl in |- *; auto.
   intros; apply interpR_mult with x y; algebra.
  intros; apply interpR_wd with (y[*]x); algebra.
  apply MI_mult_corr_R; auto.
 intros. inversion X0.
 try (rewrite H0 in H2; rewrite H in X2; rewrite H1 in X3). (* compat 8.0 *)
 apply interpR_wd with (y0[*]y[*]x0).
  apply MV_mult_corr_R; auto.
 astepl (x0[*](y0[*]y)).
 Step_final (x0[*]y0[*]y).
Qed.
Transparent MV_mult MI_mult.

Opaque MV_mult.
Lemma MM_plus_corr_R :
 forall (e f:expr) (x y:R), II e x -> II f y -> II (MM_plus e f) (x[+]y).
Proof.
 cut (forall (i j:Z) (x y:R),
   II (expr_int i) x -> II (expr_int j) y -> II (expr_int (i + j)) (x[+]y)).
  cut (forall (e f:expr) (x y:R), II e x -> II f y -> II (expr_plus e f) (x[+]y)).
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
           intros. inversion X.
           try (rewrite H6 in X1; rewrite H8 in X2; rewrite H7 in H9). (* compat 8.0 *)
           inversion X0.
           try (rewrite H10 in X3; rewrite H12 in X4; rewrite H11 in H13). (* compat 8.0 *)
           apply interpR_wd with ((y0[+]y1)[*]x0).
            apply MV_mult_corr_R; auto.
           astepl (x0[*](y0[+]y1)).
           astepl (x0[*]y0[+]x0[*]y1).
           cut (x0[=]x1). intro.
            Step_final (x0[*]y0[+]x1[*]y1).
           apply refl_interpR with val unop binop pfun (expr_var n).
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
           inversion X.
           try (rewrite -> H7 in X1; rewrite H9 in X2; rewrite H8 in H10). (* compat 8.0 *)
           inversion X0.
           try (rewrite H11 in X3; rewrite H13 in X4; rewrite H12 in H14). (* compat 8.0 *)
           apply interpR_wd with ((y0[+]y1)[*]x0).
            apply MV_mult_corr_R; auto.
           astepr (x0[*]y0[+]x1[*]y1). astepl (y0[*]x0[+]y1[*]x0).
           apply bin_op_wd_unfolded. algebra. astepr (y1[*]x1). apply mult_wdr.
            apply refl_interpR with val unop binop pfun (expr_unop u e0).
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
           inversion X.
           try (rewrite H9 in X1; rewrite H11 in X2; rewrite H10 in H12). (* compat 8.0 *)
           inversion X0.
           try (rewrite H13 in X3; rewrite H15 in X4; rewrite H14 in H16). (* compat 8.0 *)
           apply interpR_wd with ((y0[+]y1)[*]x0).
            apply MV_mult_corr_R; auto.
           astepr (x0[*]y0[+]x1[*]y1). astepl (y0[*]x0[+]y1[*]x0).
           apply bin_op_wd_unfolded. algebra. astepr (y1[*]x1). apply mult_wdr.
            apply refl_interpR with val unop binop pfun (expr_binop u e0 e3).
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
         inversion X.
         try (rewrite H9 in X1; rewrite H11 in X2; rewrite H10 in H12). (* compat 8.0 *)
         inversion X0.
         try (rewrite H13 in X3; rewrite H15 in X4; rewrite H14 in H16). (* compat 8.0 *)
         apply interpR_wd with ((y0[+]y1)[*]x0).
          apply MV_mult_corr_R; auto.
         astepr (x0[*]y0[+]x1[*]y1). astepl (y0[*]x0[+]y1[*]x0).
         apply bin_op_wd_unfolded. algebra. astepr (y1[*]x1). apply mult_wdr.
          apply refl_interpR with val unop binop pfun (expr_part f e0).
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
  intros; apply interpR_plus with x y; algebra.
 intros. inversion X.
 try (rewrite H1 in H0; rewrite H in H0). (* compat 8.0 *)
 inversion X0.
 try (rewrite H2 in H3; rewrite H4 in H3). (* compat 8.0 *)
 apply interpR_wd with (zring (i + j):R).
  apply interpR_int; algebra.
 Step_final (zring i[+]zring j:R).
Qed.
Transparent MV_mult.

Opaque MM_plus.
Lemma PM_plus_corr_R :
 forall (e f:expr) (x y:R), II e x -> II f y -> II (PM_plus e f) (x[+]y).
Proof.
 cut (forall (e1 e2 f:expr) (x y:R),
   (forall (f:expr) (x y:R), II e2 x -> II f y -> II (PM_plus e2 f) (x[+]y)) ->
     II (expr_plus e1 e2) x -> II f y -> II (expr_plus e1 (PM_plus e2 f)) (x[+]y)).
  cut (forall (e1 e2 f:expr) (x y:R),
    (forall (f:expr) (x y:R), II e2 x -> II f y -> II (PM_plus e2 f) (x[+]y)) ->
      II (expr_plus e1 e2) x -> II f y -> II (PM_plus e2 (MM_plus e1 f)) (x[+]y)).
   cut (forall (e f:expr) (x y:R), II e x -> II f y -> II (MM_plus e f) (x[+]y)).
    cut (forall (e f:expr) (x y:R), II e x -> II f y -> II (expr_plus e f) (x[+]y)).
     cut (forall (e f:expr) (x y:R), II e x -> II f y -> II (expr_plus f e) (x[+]y)).
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
     intros; apply interpR_wd with (y[+]x); algebra.
     apply interpR_plus with y x; algebra.
    intros; apply interpR_plus with x y; algebra.
   intros; apply MM_plus_corr_R; auto.
  intros. inversion X0.
  try (rewrite H in X2; rewrite H1 in X3; rewrite H0 in H2). (* compat 8.0 *)
  apply interpR_wd with (y0[+](x0[+]y)).
   apply X; auto.
   apply MM_plus_corr_R; auto.
  astepl (y0[+]x0[+]y).
  Step_final (x0[+]y0[+]y).
 intros. inversion X0.
 try (rewrite H in X2; rewrite H1 in X3; rewrite H0 in H2). (* compat 8.0 *)
 apply interpR_wd with (x0[+](y0[+]y)).
  apply interpR_plus with x0 (y0[+]y); algebra.
 Step_final (x0[+]y0[+]y).
Qed.
Transparent MM_plus.

Opaque PM_plus.
Lemma PP_plus_corr_R :
 forall (e f:expr) (x y:R), II e x -> II f y -> II (PP_plus e f) (x[+]y).
Proof.
 cut (forall (e1 e2 f:expr) (x y:R),
   (forall (f:expr) (x y:R), II e2 x -> II f y -> II (PP_plus e2 f) (x[+]y)) ->
     II (expr_plus e1 e2) x -> II f y -> II (PM_plus (PP_plus e2 f) e1) (x[+]y)).
  cut (forall (i:Z) (f:expr) (x y:R),
    II (expr_int i) x -> II f y -> II (PM_plus f (expr_int i)) (x[+]y)).
   cut (forall (e f:expr) (x y:R), II e x -> II f y -> II (expr_plus e f) (x[+]y)).
    intros H H0 H1 e.
    elim e; intros; simpl in |- *; auto.
   intros. apply interpR_plus with x y; algebra.
   intros. apply interpR_wd with (y[+]x); algebra.
  apply PM_plus_corr_R; auto.
 intros. inversion X0.
 try (rewrite H in X2; rewrite H1 in X3; rewrite H0 in H2). (* compat 8.0 *)
 apply interpR_wd with (y0[+]y[+]x0).
  apply PM_plus_corr_R; auto.
 astepl (x0[+](y0[+]y)).
 Step_final (x0[+]y0[+]y).
Qed.
Transparent PM_plus.

Opaque PM_plus MM_mult MI_mult.
Lemma PM_mult_corr_R :
 forall (e f:expr) (x y:R), II e x -> II f y -> II (PM_mult e f) (x[*]y).
Proof.
 cut (forall (e1 e2 f:expr) (x y:R),
   (forall (f:expr) (x y:R), II e2 x -> II f y -> II (PM_mult e2 f) (x[*]y)) ->
     II (expr_plus e1 e2) x -> II f y -> II (PM_plus (PM_mult e2 f) (MM_mult e1 f)) (x[*]y)).
  cut (forall (i:Z) (f:expr) (x y:R), II (expr_int i) x ->
    II f y -> II (PM_plus (expr_int 0) (MI_mult f (expr_int i))) (x[*]y)).
   cut (forall (e f:expr) (x y:R), II e x -> II f y -> II (expr_mult e f) (x[*]y)).
    intros H H0 H1 e.
    elim e; intros; simpl in |- *; auto.
   intros. apply interpR_mult with x y; algebra.
   intros. apply interpR_wd with (zring 0[+]y[*]x).
  apply PM_plus_corr_R.
    apply interpR_int; algebra.
   apply MI_mult_corr_R; auto.
  astepl ([0][+]y[*]x).
  Step_final (y[*]x).
 intros. inversion X0.
 try (rewrite H in X2; rewrite H1 in X3; rewrite H0 in H2). (* compat 8.0 *)
 apply interpR_wd with (y0[*]y[+]x0[*]y).
  apply PM_plus_corr_R; auto.
  apply MM_mult_corr_R; auto.
 astepl ((y0[+]x0)[*]y).
 Step_final ((x0[+]y0)[*]y).
Qed.

Opaque PM_mult.
Lemma PP_mult_corr_R :
 forall (e f:expr) (x y:R), II e x -> II f y -> II (PP_mult e f) (x[*]y).
Proof.
 cut (forall (e1 e2 f:expr) (x y:R),
   (forall (f:expr) (x y:R), II e2 x -> II f y -> II (PP_mult e2 f) (x[*]y)) ->
     II (expr_plus e1 e2) x -> II f y -> II (PP_plus (PM_mult f e1) (PP_mult e2 f)) (x[*]y)).
  cut (forall (i:Z) (f:expr) (x y:R),
    II (expr_int i) x -> II f y -> II (PM_mult f (expr_int i)) (x[*]y)).
   cut (forall (e f:expr) (x y:R), II e x -> II f y -> II (expr_mult e f) (x[*]y)).
    intros H H0 H1 e.
    elim e; intros; simpl in |- *; auto.
   intros. apply interpR_mult with x y; algebra.
   intros. apply interpR_wd with (y[*]x); algebra.
  apply PM_mult_corr_R; auto.
 intros. inversion X0.
 try (rewrite H in X2; rewrite H1 in X3; rewrite H0 in H2). (* compat 8.0 *)
 apply interpR_wd with (y[*]x0[+]y0[*]y).
  apply PP_plus_corr_R; auto.
  apply PM_mult_corr_R; auto.
 astepl (x0[*]y[+]y0[*]y).
 Step_final ((x0[+]y0)[*]y).
Qed.

(*
Transparent PP_plus PM_mult PP_mult PM_plus MI_mult.
Lemma FF_plus_corr_R : (e,f:expr; x,y:R)
  (II e x)->(II f y)->(II (FF_plus e f) x[+]y).
Cut (e1,e2,f1,f2:expr; x,y:R)
     (II (expr_div e1 e2) x)
     ->(II (expr_div f1 f2) y)
     ->(II
         (expr_div (PP_plus (PP_mult e1 f2) (PP_mult e2 f1))
           (PP_mult e2 f2)) x[+]y).
Cut (e,f:expr; x,y:R)(II e x)->(II f y)->(II (expr_plus e f) x[+]y).
Intros H H0 e f.
Elim e; Elim f; Intros; Simpl; Auto.
Intros. Apply interpR_plus with x y; algebra.
Intros. Inversion H. Inversion H0.
Apply interpR_div_one with x[+]y.
algebra.
Apply interpR_wd with x0[*][1][+][1][*]x1.
Apply PP_plus_corr_R; Apply PP_mult_corr_R; Auto;
  Apply interpR_int with k:=`1`; algebra.
Step_final x0[+]x1.
Apply interpR_wd with ([1]::R)[*][1]; algebra.
Apply PP_mult_corr_R; Auto.
Qed.

Lemma FF_mult_corr_R : (e,f:expr; x,y:R)
  (II e x)->(II f y)->(II (FF_mult e f) x[*]y).
Cut (e1,e2,f1,f2:expr; x,y:R)
     (II (expr_div e1 e2) x)
     ->(II (expr_div f1 f2) y)
     ->(II (expr_div (PP_mult e1 f1) (PP_mult e2 f2)) x[*]y).
Cut (e,f:expr; x,y:R)(II e x)->(II f y)->(II (expr_mult e f) x[*]y).
Intros H H0 e f.
Elim e; Elim f; Intros; Simpl; Auto.
Intros. Apply interpR_mult with x y; algebra.
Intros. Inversion H. Inversion H0.
Apply interpR_div_one with x0[*]x1.
algebra.
Apply PP_mult_corr_R; Auto.
Apply interpR_wd with ([1]::R)[*][1]; algebra.
Apply PP_mult_corr_R; Auto.
Qed.

Transparent FF_div.
Lemma FF_div_corr_R : (e,f:expr; x:R)
  (II (expr_div e f) x)->(II (FF_div e f) x).
Intro e; Case e; Simpl; Auto.
Intros e0 e1 f; Case f; Simpl; Auto.
Intros.
Inversion H; Simpl.
Inversion H3; Inversion H5.
Apply interpR_div_one with x1[*][1].
astepl x1. Step_final x0.
Apply PP_mult_corr_R; Auto.
Apply interpR_wd with [1][*]x2.
Apply PP_mult_corr_R; Auto.
Step_final x2.
Qed.
*)

Lemma NormR_corr : forall (e:expr) (x:R), II e x -> II (NormR e) x.
Proof.
 intro; induction e; intros; simpl in |- *.
        apply (interpR_plus R val unop binop pfun (expr_mult (expr_var v) expr_one) expr_zero x ([0]:R) x).
          algebra.
         apply (interpR_mult R val unop binop pfun (expr_var v) expr_one x ([1]:R) x); algebra.
         apply (interpR_int R val unop binop pfun 1); algebra.
        apply (interpR_int R val unop binop pfun 0); algebra.
       assumption.
      inversion X.
      try (rewrite H in X0; rewrite H1 in X1; rewrite H0 in H2). (* compat 8.0 *)
      apply interpR_wd with (x0[+]y). apply PP_plus_corr_R; auto. auto.
       inversion X.
     try (rewrite H in X0; rewrite H1 in X1; rewrite H0 in H2). (* compat 8.0 *)
     apply interpR_wd with (x0[*]y). apply PP_mult_corr_R; auto. auto.
      assumption.
   inversion X.
   try (rewrite H in H2; rewrite H1 in X0; rewrite H0 in H2). (* compat 8.0 *)
   apply (interpR_plus R val unop binop pfun (expr_mult (expr_unop u (NormR e)) expr_one) expr_zero x (
     [0]:R) x).
     algebra.
    apply (interpR_mult R val unop binop pfun (expr_unop u (NormR e)) expr_one x ([1]:R) x); algebra.
     apply (interpR_unop R val unop binop pfun (NormR e) u x0); algebra.
    apply (interpR_int R val unop binop pfun 1); algebra.
   apply (interpR_int R val unop binop pfun 0); algebra.
  inversion X.
  (* compat 8.0 *)
  try (rewrite H in H3; rewrite H1 in X0; rewrite H2 in X1; rewrite H0 in H3).
  apply (interpR_plus R val unop binop pfun
    (expr_mult (expr_binop b (NormR e1) (NormR e2)) expr_one) expr_zero x ([0]:R) x).
    algebra.
   apply (interpR_mult R val unop binop pfun (expr_binop b (NormR e1) (NormR e2))
     expr_one x ([1]:R) x); algebra.
    apply (interpR_binop R val unop binop pfun (NormR e1) (NormR e2) b x0 y); algebra.
   apply (interpR_int R val unop binop pfun 1); algebra.
  apply (interpR_int R val unop binop pfun 0); algebra.
 inversion X.
 try ((generalize Hx H2; clear Hx H2; rewrite H; intros Hx H2);
   rewrite H1 in X0; rewrite H0 in H2). (* compat 8.0 *)
 apply (interpR_plus R val unop binop pfun (expr_mult (expr_part p (NormR e)) expr_one) expr_zero x (
   [0]:R) x).
   algebra.
  apply (interpR_mult R val unop binop pfun (expr_part p (NormR e)) expr_one x ([1]:R) x); algebra.
   apply (interpR_part R val unop binop pfun (NormR e) p x0) with (Hx := Hx); algebra.
  apply (interpR_int R val unop binop pfun 1); algebra.
 apply (interpR_int R val unop binop pfun 0); algebra.
Qed.

Lemma Tactic_lemmaR :
 forall (x y:R) (e:xexprR R val unop binop pfun x)
   (f:xexprR R val unop binop pfun y),
   eq_expr (NormR (xforgetR _ _ _ _ _ _ e)) (NormR (xforgetR _ _ _ _ _ _ f)) =
   true -> x[=]y.
Proof.
 intros x y e f H.
 apply refl_interpR with val unop binop pfun (NormR (xforgetR _ _ _ _ _ _ e)).
  apply NormR_corr; apply xexprR2interpR.
 rewrite (eq_expr_corr _ _ H).
 apply NormR_corr; apply xexprR2interpR.
Qed.

End Ring_NormCorrect.

Ltac QuoteR R l t :=
match l with
 (Quad ?vl ?ul ?bl ?pl) =>
(let a := constr:(fun n:varindex => (Mnth n vl (cm_unit R))) in
 let b := constr:(fun n:unopindex => (Mnth n ul (@cg_inv R))) in
 let c := constr:(fun n:binopindex => (Mnth n bl (@csg_op R))) in
 let d := constr:(fun n:pfunindex => (Mnth n pl (total_eq_part _ (@cg_inv R)))) in
 match t with
 | (zring ?k) =>
    match (ClosedZ k) with
    | true => constr:(xexprR_int R a b c d k)
    end
 | (csbf_fun _ _ _ csg_op ?x ?y) =>
    let x' := QuoteR R l x in
    let y' := QuoteR R l y in
    constr:(xexprR_plus R a b c d _ _ x' y')
 | (csbf_fun _ _ _ cr_mult ?x ?y) =>
    let x' := QuoteR R l x in
    let y' := QuoteR R l y in
    constr:(xexprR_mult R a b c d _ _ x' y')
 | ([0]) => constr:(xexprR_zero R a b c d)
 | ([1]) => constr:(xexprR_one R a b c d)
 | (nring ?n) =>
    match (ClosedNat n) with
    | true => constr:(xexprR_nat R a b c d n)
    end
 | (csf_fun _ _ cg_inv ?x) =>
    let x' := QuoteR R l x in
    constr:(xexprR_inv R a b c d _ x')
 | (cg_minus ?x ?y) =>
    let x' := QuoteR R l x in
    let y' := QuoteR R l y in
    constr:(xexprR_minus R a b c d _ _ x' y')
 | (csf_fun _ _ (@nexp_op _ ?n) ?x) =>
    match (ClosedNat n) with
    | true => let x' := QuoteR R l x in
              constr:(xexprR_power R a b c d _ x' n)
    end
 | (pfpfun ?f ?x ?h) =>
    let x' := QuoteR R l x in
    let i := FindIndex f pl in
    constr:(xexprR_part R a b c d _ i x' h)
 | (csf_fun _ _ ?f ?x) =>
    let x' := QuoteR R l x in
    let i := FindIndex f ul in
    constr:(xexprR_unop R a b c d _ i x')
 | (csbf_fun _ _ _ ?f ?x ?y) =>
    let x' := QuoteR R l x in
    let y' := QuoteR R l y in
    let i := FindIndex f bl in
    constr:(xexprR_binop R a b c d _ _ i x' y')
 | ?t =>
    let i := FindIndex t vl in
    constr:(xexprR_var R a b c d i)
end)
end.

Ltac FindTermVariablesR t l :=
match t with
| (zring ?k) =>
    match (ClosedZ k) with
    | true => constr:l
    end
| (csbf_fun _ _ _ csg_op ?x ?y) =>
    let l1 := FindTermVariablesR x l in
    let l2 := FindTermVariablesR y l1 in
    constr:l2
| (csbf_fun _ _ _ cr_mult ?x ?y) =>
    let l1 := FindTermVariablesR x l in
    let l2 := FindTermVariablesR y l1 in
    constr:l2
| ([0]) => constr:l
| ([1]) => constr:l
| (nring ?n) =>
    match (ClosedNat n) with
    | true => constr:l
    end
| (csf_fun _ _ cg_inv ?x) =>
    let l1 := FindTermVariablesR x l in
    constr:l1
| (cg_minus ?x ?y) =>
    let l1 := FindTermVariablesR x l in
    let l2 := FindTermVariablesR y l1 in
    constr:l2
| (csf_fun _ _ (@nexp_op _ ?n) ?x) =>
    match (ClosedNat n) with
    | true => let l1 := FindTermVariablesR x l in
              constr:l1
    end
| (pfpfun ?f ?x ?h) =>
    let l1 := FindTermVariablesR x l in
    match l1 with
     (Quad ?vl ?ul ?bl ?pl) => constr:(Quad vl ul bl (Mcons f pl))
    end
| (csf_fun _ _ ?f ?x) =>
    let l1 := FindTermVariablesR x l in
    match l1 with
     (Quad ?vl ?ul ?bl ?pl) => constr:(Quad vl (Mcons f ul) bl pl)
    end
| (csbf_fun _ _ _ ?f ?x ?y) =>
    let l1 := FindTermVariablesR x l in
    let l2 := FindTermVariablesR y l1 in
    match l2 with
     (Quad ?vl ?ul ?bl ?pl) => constr:(Quad vl ul (Mcons f bl) pl)
    end
| ?t => match l with
         (Quad ?vl ?ul ?bl ?pl) => constr:(Quad (Mcons t vl) ul bl pl)
        end
end.

Ltac FindTermsVariablesR fn t1 t2 :=
    let l1 := FindTermVariablesR t1 (Quad (Mnil fn) (Mnil (CSetoid_un_op fn)) (Mnil (CSetoid_bin_op fn)) (Mnil (PartFunct fn))) in
    let l2 := FindTermVariablesR t2 l1 in
    constr:l2.

Ltac rationalR R x y :=
                 let l:=FindTermsVariablesR R x y in
                 let t1:=(QuoteR R l x) in
                 let t2:=(QuoteR R l y) in
                 eapply Tactic_lemmaR with (e:=t1) (f:=t2)
                 ; reflexivity.

(* end hide *)
