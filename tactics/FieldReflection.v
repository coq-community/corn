(* $Id$ *)

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
      forall (e f:expr) (x y z:F) (nzy:y[#]Zero),
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
              :F) (e:xexprF x) (f:xexprF y) (nzy:y[#]Zero),
        xexprF (x[/]y[//]nzy)
  | xexprF_zero : xexprF Zero
  | xexprF_one : xexprF One
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
intros x e.
induction e.

apply (interpF_var i); Algebra.

apply (interpF_int k); Algebra.

apply (interpF_plus (xforgetF _ e1) (xforgetF _ e2) x y (x[+]y)); Algebra.

apply (interpF_mult (xforgetF _ e1) (xforgetF _ e2) x y (x[*]y)); Algebra.

apply (interpF_unop (xforgetF _ e) f x (unop f x)); Algebra.

apply (interpF_binop (xforgetF _ e1) (xforgetF _ e2) f x y (binop f x y));
 Algebra.

eapply (interpF_part (xforgetF _ e) f x (pfun f x Hx)).
 apply eq_reflexive_unfolded.
Algebra.

apply (interpF_div (xforgetF _ e1) (xforgetF _ e2) x y (x[/]y[//]nzy) nzy);
 Algebra.

apply (interpF_int 0); Algebra.

apply (interpF_int 1); Step_final (One:F).

apply (interpF_int (Z_of_nat n)); Algebra.

apply (interpF_mult (xforgetF _ e) (expr_int (-1)) x (zring (-1)) [--]x);
 auto.
Step_final (zring (-1)[*]x).
apply (interpF_int (-1)); Algebra.

apply
 (interpF_plus (xforgetF _ e1) (xforgetF _ (xexprF_inv _ e2)) x [--]y (x[-]y));
 Algebra.
apply (interpF_mult (xforgetF _ e2) (expr_int (-1)) y (zring (-1)) [--]y);
 auto.
Step_final (zring (-1)[*]y).
apply (interpF_int (-1)); Algebra.

induction n.
 apply (interpF_int 1); Step_final (One:F).
apply
 (interpF_mult (xforgetF _ e) (expr_power n (xforgetF _ e)) x (
    x[^]n) (x[^]S n)); Algebra.
Qed.

Definition xexprF_diagram_commutes :
  forall (x:F) (e:xexprF x), interpF (xforgetF _ e) (xinterpF _ e) :=
  xexprF2interpF.

Lemma xexprF2wfF : forall (x:F) (e:xexprF x), wfF (xforgetF _ e).
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
intros e.
elim e. intros x e'.
unfold fforgetF in |- *. simpl in |- *.
apply xexprF2interpF.
Qed.

Lemma fexprF2wfF : forall e:fexprF, wfF (fforgetF e).
intro e.
unfold fforgetF in |- *.
apply xexprF2wfF.
Qed.

Load "Opaque_algebra".

Lemma refl_interpF :
 forall (e:expr) (x y:F), interpF e x -> interpF e y -> x[=]y.
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
AStepl (x0[+]y0).
Step_final (x1[+]y1).

intros x y H1 H2.
inversion H1.
inversion H2.
AStepl (x0[*]y0).
Step_final (x1[*]y1).

intros x y H0 H1.
inversion H0.
inversion H1.
AStepl (x0[/]y0[//]nzy). Step_final (x1[/]y1[//]nzy0).

intros x y H0 H1.
inversion H0.
inversion H1.
AStepl (unop u x0); Step_final (unop u x1).

intros x y H0 H1.
inversion H0.
inversion H1.
AStepl (binop b x0 y0); Step_final (binop b x1 y1).

intros x y H0 H1.
inversion H0.
inversion H1.
AStepl (pfun p x0 Hx); Step_final (pfun p x1 Hx0).
Qed.

Lemma interpF_wd :
 forall (e:expr) (x y:F), interpF e x -> (x[=]y) -> interpF e y.
intros e x y H H0.
inversion H; rewrite <- H2; rewrite H3 in H1.
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
cut (forall x y:F, II (expr_int 0) y -> II (expr_int 0) (x[*]y)).
cut
 (forall (e1 e2 f:expr) (x y:F),
    (forall (f:expr) (x y:F), II e2 x -> II f y -> II (MI_mult e2 f) (x[*]y)) ->
    II (expr_mult e1 e2) x ->
    II f y -> II (expr_mult e1 (MI_mult e2 f)) (x[*]y)).
cut
 (forall (i j:Z) (x y:F),
    II (expr_int i) x -> II (expr_int j) y -> II (expr_int (i * j)) (x[*]y)).
cut
 (forall (e f:expr) (x y:F), II e x -> II f y -> II (expr_mult e f) (x[*]y)).
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
intros; apply interpF_mult with x y; Algebra.
intros; apply interpF_wd with (zring (i * j):F).
apply interpF_int; Algebra.
inversion X. inversion X0.
Step_final (zring i[*]zring j:F).
intros. inversion X0. rewrite H in X2. rewrite H1 in X3. rewrite H0 in H2.
apply interpF_wd with (x0[*](y0[*]y)); Algebra.
apply interpF_mult with x0 (y0[*]y); Algebra.
Step_final (x0[*]y0[*]y).
intros. inversion X. rewrite H in H0. rewrite H1 in H0.
apply interpF_wd with (zring 0:F).
apply interpF_int; Algebra.
AStepl (Zero:F).
AStepl (x[*]Zero).
Step_final (x[*]zring 0).
Qed.
Transparent Zmult.

Opaque MI_mult.
Lemma MV_mult_corr_F :
 forall (e f:expr) (x y:F), II e x -> II f y -> II (MV_mult e f) (x[*]y).
cut
 (forall (e1 e2 f:expr) (x y:F),
    (forall (f:expr) (x y:F), II e2 x -> II f y -> II (MV_mult e2 f) (x[*]y)) ->
    II (expr_mult e1 e2) x ->
    II f y -> II (expr_mult e1 (MV_mult e2 f)) (x[*]y)).
cut
 (forall (e f:expr) (x y:F),
    II e x -> II f y -> II (MI_mult (expr_mult f expr_one) e) (x[*]y)).
cut
 (forall (e f:expr) (x y:F), II e x -> II f y -> II (expr_mult f e) (x[*]y)).
cut
 (forall (e f:expr) (x y:F), II e x -> II f y -> II (expr_mult e f) (x[*]y)).
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
intros; apply interpF_mult with x y; Algebra.
intros; apply interpF_wd with (y[*]x); Algebra.
apply interpF_mult with y x; Algebra.
intros; apply interpF_wd with (y[*]One[*]x).
apply MI_mult_corr_F; auto.
apply interpF_mult with y (One:F); Algebra.
apply (interpF_int F val unop binop pfun 1); Algebra.
Step_final (x[*](y[*]One)).
intros. inversion X0. rewrite H0 in H2. rewrite H in X2. rewrite H1 in X3.
apply interpF_wd with (x0[*](y0[*]y)).
apply interpF_mult with x0 (y0[*]y); Algebra.
Step_final (x0[*]y0[*]y).
Qed.
Transparent MI_mult.

Opaque MV_mult MI_mult.
Lemma MM_mult_corr_F :
 forall (e f:expr) (x y:F), II e x -> II f y -> II (MM_mult e f) (x[*]y).
cut
 (forall (e1 e2 f:expr) (x y:F),
    (forall (f:expr) (x y:F), II e2 x -> II f y -> II (MM_mult e2 f) (x[*]y)) ->
    II (expr_mult e1 e2) x ->
    II f y -> II (MV_mult (MM_mult e2 f) e1) (x[*]y)).
cut
 (forall (i:Z) (f:expr) (x y:F),
    II (expr_int i) x -> II f y -> II (MI_mult f (expr_int i)) (x[*]y)).
cut
 (forall (e f:expr) (x y:F), II e x -> II f y -> II (expr_mult e f) (x[*]y)).
intros H H0 H1 e.
elim e; intros; simpl in |- *; auto.
intros; apply interpF_mult with x y; Algebra.
intros; apply interpF_wd with (y[*]x); Algebra.
apply MI_mult_corr_F; auto.
intros. inversion X0. rewrite H in X2. rewrite H1 in X3. rewrite H0 in H2.
apply interpF_wd with (y0[*]y[*]x0).
apply MV_mult_corr_F; auto.
AStepl (x0[*](y0[*]y)).
Step_final (x0[*]y0[*]y).
Qed.
Transparent MV_mult MI_mult.

Opaque MV_mult.
Lemma MM_plus_corr_F :
 forall (e f:expr) (x y:F), II e x -> II f y -> II (MM_plus e f) (x[+]y).
cut
 (forall (i j:Z) (x y:F),
    II (expr_int i) x -> II (expr_int j) y -> II (expr_int (i + j)) (x[+]y)).
cut
 (forall (e f:expr) (x y:F), II e x -> II f y -> II (expr_plus e f) (x[+]y)).
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
intros. inversion X. rewrite H6 in X1. rewrite H8 in X2. rewrite H7 in H9.
inversion X0. rewrite H10 in X3. rewrite H12 in X4. rewrite H11 in H13.
apply interpF_wd with ((y0[+]y1)[*]x0).
apply MV_mult_corr_F; auto.
AStepl (x0[*](y0[+]y1)).
AStepl (x0[*]y0[+]x0[*]y1).
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
inversion X. rewrite <- H7. rewrite H9 in X2. rewrite H8 in H10.
inversion X0. rewrite H11 in X3. rewrite H13 in X4. rewrite H12 in H14.
apply interpF_wd with ((y0[+]y1)[*]x0).
apply MV_mult_corr_F; auto.
AStepr (x0[*]y0[+]x1[*]y1). AStepl (y0[*]x0[+]y1[*]x0).
apply bin_op_wd_unfolded. Algebra. AStepr (y1[*]x1). apply mult_wd_rht.
apply refl_interpF with val unop binop pfun (expr_unop u e0).
rewrite <- H7; auto. rewrite H'. rewrite H''. auto. auto. auto.
intro. elim (andb_prop _ _ H7); intros. apply eq_expr_corr; auto. 
intro. elim (andb_prop _ _ H7); intros. apply eq_nat_corr; auto.

intros u e0 H3 e3 H4 f.
elim f; simpl in |- *; auto.
intros e4 H5 e5 H6.
elim e4; simpl in |- *; auto.
intros u0 e6 H7 e7 H8.
cut
 (andb (eq_nat u u0) (andb (eq_expr e0 e6) (eq_expr e3 e7)) = true -> u = u0).
cut
 (andb (eq_nat u u0) (andb (eq_expr e0 e6) (eq_expr e3 e7)) = true -> e0 = e6).
cut
 (andb (eq_nat u u0) (andb (eq_expr e0 e6) (eq_expr e3 e7)) = true -> e3 = e7).
elim andb; simpl in |- *; auto.
intros H' H'' H'''. intros.
inversion X. rewrite <- H9. rewrite H11 in X2. rewrite H10 in H12.
inversion X0. rewrite H13 in X3. rewrite H15 in X4. rewrite H14 in H16.
apply interpF_wd with ((y0[+]y1)[*]x0).
apply MV_mult_corr_F; auto.
AStepr (x0[*]y0[+]x1[*]y1). AStepl (y0[*]x0[+]y1[*]x0).
apply bin_op_wd_unfolded. Algebra. AStepr (y1[*]x1). apply mult_wd_rht.
apply refl_interpF with val unop binop pfun (expr_binop u e0 e3).
rewrite <- H9; auto. rewrite H'. rewrite H''. rewrite H'''. auto. auto. auto.
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
inversion X. rewrite <- H9. rewrite H11 in X2. rewrite H10 in H12.
inversion X0. rewrite H13 in X3. rewrite H15 in X4. rewrite H14 in H16.
apply interpF_wd with ((y0[+]y1)[*]x0).
apply MV_mult_corr_F; auto.
AStepr (x0[*]y0[+]x1[*]y1). AStepl (y0[*]x0[+]y1[*]x0).
apply bin_op_wd_unfolded. Algebra. AStepr (y1[*]x1). apply mult_wd_rht.
apply refl_interpF with val unop binop pfun (expr_part f e0).
rewrite <- H9; auto. rewrite H7. rewrite H8; auto. auto.
intro. elim (andb_prop _ _ H7); intros. apply eq_expr_corr; auto. 
intro. elim (andb_prop _ _ H7); intros. apply eq_nat_corr; auto.
simpl in |- *; auto.

intros u e0 H1 f.
elim f; simpl in |- *; auto.
intros u e0 H1 e1 H2 f.
elim f; simpl in |- *; auto.
intros u e0 H1 f.
elim f; simpl in |- *; auto.

intros; apply interpF_plus with x y; Algebra.
intros. inversion X.  rewrite H1 in H0. rewrite H in H0.
inversion X0. rewrite H2 in H3. rewrite H4 in H3.
apply interpF_wd with (zring (i + j):F).
apply interpF_int; Algebra.
Step_final (zring i[+]zring j:F).
Qed.
Transparent MV_mult.

Opaque MM_plus.
Lemma PM_plus_corr_F :
 forall (e f:expr) (x y:F), II e x -> II f y -> II (PM_plus e f) (x[+]y).
cut
 (forall (e1 e2 f:expr) (x y:F),
    (forall (f:expr) (x y:F), II e2 x -> II f y -> II (PM_plus e2 f) (x[+]y)) ->
    II (expr_plus e1 e2) x ->
    II f y -> II (expr_plus e1 (PM_plus e2 f)) (x[+]y)).
cut
 (forall (e1 e2 f:expr) (x y:F),
    (forall (f:expr) (x y:F), II e2 x -> II f y -> II (PM_plus e2 f) (x[+]y)) ->
    II (expr_plus e1 e2) x ->
    II f y -> II (PM_plus e2 (MM_plus e1 f)) (x[+]y)).
cut (forall (e f:expr) (x y:F), II e x -> II f y -> II (MM_plus e f) (x[+]y)).
cut
 (forall (e f:expr) (x y:F), II e x -> II f y -> II (expr_plus e f) (x[+]y)).
cut
 (forall (e f:expr) (x y:F), II e x -> II f y -> II (expr_plus f e) (x[+]y)).
intros H H0 H1 H2 H3 e. elim e.
simpl in |- *; auto.
intros z f; elim f; intros; simpl in |- *; auto.
intros e1 H4 e2 H5 f. simpl in |- *.
elim (lt_monom e1 f); elim (eq_monom e1 f); elim f; intros; simpl in |- *;
 auto.
simpl in |- *; auto.
simpl in |- *; auto.
simpl in |- *; auto.
simpl in |- *; auto.
simpl in |- *; auto.
intros; apply interpF_wd with (y[+]x); Algebra.
apply interpF_plus with y x; Algebra.
intros; apply interpF_plus with x y; Algebra.
intros; apply MM_plus_corr_F; auto.
intros. inversion X0. rewrite H in X2. rewrite H1 in X3. rewrite H0 in H2.
apply interpF_wd with (y0[+](x0[+]y)).
apply X; auto.
apply MM_plus_corr_F; auto.
AStepl (y0[+]x0[+]y).
Step_final (x0[+]y0[+]y).
intros. inversion X0. rewrite H in X2. rewrite H1 in X3. rewrite H0 in H2.
apply interpF_wd with (x0[+](y0[+]y)).
apply interpF_plus with x0 (y0[+]y); Algebra.
Step_final (x0[+]y0[+]y).
Qed.
Transparent MM_plus.

Opaque PM_plus.
Lemma PP_plus_corr_F :
 forall (e f:expr) (x y:F), II e x -> II f y -> II (PP_plus e f) (x[+]y).
cut
 (forall (e1 e2 f:expr) (x y:F),
    (forall (f:expr) (x y:F), II e2 x -> II f y -> II (PP_plus e2 f) (x[+]y)) ->
    II (expr_plus e1 e2) x ->
    II f y -> II (PM_plus (PP_plus e2 f) e1) (x[+]y)).
cut
 (forall (i:Z) (f:expr) (x y:F),
    II (expr_int i) x -> II f y -> II (PM_plus f (expr_int i)) (x[+]y)).
cut
 (forall (e f:expr) (x y:F), II e x -> II f y -> II (expr_plus e f) (x[+]y)).
intros H H0 H1 e.
elim e; intros; simpl in |- *; auto.
intros. apply interpF_plus with x y; Algebra.
intros. apply interpF_wd with (y[+]x); Algebra.
apply PM_plus_corr_F; auto.
intros. inversion X0. rewrite H in X2. rewrite H1 in X3. rewrite H0 in H2.
apply interpF_wd with (y0[+]y[+]x0).
apply PM_plus_corr_F; auto.
AStepl (x0[+](y0[+]y)).
Step_final (x0[+]y0[+]y).
Qed.
Transparent PM_plus.

Opaque PM_plus MM_mult MI_mult.
Lemma PM_mult_corr_F :
 forall (e f:expr) (x y:F), II e x -> II f y -> II (PM_mult e f) (x[*]y).
cut
 (forall (e1 e2 f:expr) (x y:F),
    (forall (f:expr) (x y:F), II e2 x -> II f y -> II (PM_mult e2 f) (x[*]y)) ->
    II (expr_plus e1 e2) x ->
    II f y -> II (PM_plus (PM_mult e2 f) (MM_mult e1 f)) (x[*]y)).
cut
 (forall (i:Z) (f:expr) (x y:F),
    II (expr_int i) x ->
    II f y -> II (PM_plus (expr_int 0) (MI_mult f (expr_int i))) (x[*]y)).
cut
 (forall (e f:expr) (x y:F), II e x -> II f y -> II (expr_mult e f) (x[*]y)).
intros H H0 H1 e.
elim e; intros; simpl in |- *; auto.
intros. apply interpF_mult with x y; Algebra.
intros. apply interpF_wd with (zring 0[+]y[*]x).
apply PM_plus_corr_F.
apply interpF_int; Algebra.
apply MI_mult_corr_F; auto.
AStepl (Zero[+]y[*]x).
Step_final (y[*]x).
intros. inversion X0. rewrite H in X2. rewrite H1 in X3. rewrite H0 in H2.
apply interpF_wd with (y0[*]y[+]x0[*]y).
apply PM_plus_corr_F; auto.
apply MM_mult_corr_F; auto.
AStepl ((y0[+]x0)[*]y).
Step_final ((x0[+]y0)[*]y).
Qed.

Opaque PM_mult.
Lemma PP_mult_corr_F :
 forall (e f:expr) (x y:F), II e x -> II f y -> II (PP_mult e f) (x[*]y).
cut
 (forall (e1 e2 f:expr) (x y:F),
    (forall (f:expr) (x y:F), II e2 x -> II f y -> II (PP_mult e2 f) (x[*]y)) ->
    II (expr_plus e1 e2) x ->
    II f y -> II (PP_plus (PM_mult f e1) (PP_mult e2 f)) (x[*]y)).
cut
 (forall (i:Z) (f:expr) (x y:F),
    II (expr_int i) x -> II f y -> II (PM_mult f (expr_int i)) (x[*]y)).
cut
 (forall (e f:expr) (x y:F), II e x -> II f y -> II (expr_mult e f) (x[*]y)).
intros H H0 H1 e.
elim e; intros; simpl in |- *; auto.
intros. apply interpF_mult with x y; Algebra.
intros. apply interpF_wd with (y[*]x); Algebra.
apply PM_mult_corr_F; auto.
intros. inversion X0. rewrite H in X2. rewrite H1 in X3. rewrite H0 in H2.
apply interpF_wd with (y[*]x0[+]y0[*]y).
apply PP_plus_corr_F; auto.
apply PM_mult_corr_F; auto.
AStepl (x0[*]y[+]y0[*]y).
Step_final ((x0[+]y0)[*]y).
Qed.

Transparent PP_plus PM_mult PP_mult PM_plus MI_mult.
Lemma FF_plus_corr_F :
 forall (e f:expr) (x y:F), II e x -> II f y -> II (FF_plus e f) (x[+]y).
cut
 (forall (e1 e2 f1 f2:expr) (x y:F),
    II (expr_div e1 e2) x ->
    II (expr_div f1 f2) y ->
    II (expr_div (PP_plus (PP_mult e1 f2) (PP_mult e2 f1)) (PP_mult e2 f2))
      (x[+]y)).
cut
 (forall (e f:expr) (x y:F), II e x -> II f y -> II (expr_plus e f) (x[+]y)).
intros H H0 e f.
elim e; elim f; intros; simpl in |- *; auto.
intros. apply interpF_plus with x y; Algebra.
intros. inversion X. rewrite H in X1. rewrite H1 in X2. rewrite H0 in H2.
inversion X0. rewrite H3 in X3. rewrite H5 in X4. rewrite H4 in H6.
cut (y0[*]y1[#]Zero). intro H13.
apply interpF_div with (x0[*]y1[+]y0[*]x1) (y0[*]y1) H13; auto.
AStepl ((x0[*]y1[/] y0[*]y1[//]H13)[+](y0[*]x1[/] y0[*]y1[//]H13)).
AStepl
 ((x0[/] y0[//]nzy)[*](y1[/] y1[//]nzy0)[+]
  (y0[/] y0[//]nzy)[*](x1[/] y1[//]nzy0)).
AStepl ((x0[/] y0[//]nzy)[*]One[+]One[*](x1[/] y1[//]nzy0)).
Step_final ((x0[/] y0[//]nzy)[+](x1[/] y1[//]nzy0)).
apply PP_plus_corr_F; auto.
apply PP_mult_corr_F; auto.
apply PP_mult_corr_F; auto.
apply PP_mult_corr_F; auto.
apply mult_resp_ap_zero; auto.
Qed.

Lemma FF_mult_corr_F :
 forall (e f:expr) (x y:F), II e x -> II f y -> II (FF_mult e f) (x[*]y).
cut
 (forall (e1 e2 f1 f2:expr) (x y:F),
    II (expr_div e1 e2) x ->
    II (expr_div f1 f2) y ->
    II (expr_div (PP_mult e1 f1) (PP_mult e2 f2)) (x[*]y)).
cut
 (forall (e f:expr) (x y:F), II e x -> II f y -> II (expr_mult e f) (x[*]y)).
intros H H0 e f.
elim e; elim f; intros; simpl in |- *; auto.
intros. apply interpF_mult with x y; Algebra.
intros. inversion X. rewrite H in X1. rewrite H1 in X2. rewrite H0 in H2.
inversion X0. rewrite H3 in X3. rewrite H5 in X4. rewrite H4 in H6.
cut (y0[*]y1[#]Zero). intro H13.
apply interpF_div with (x0[*]x1) (y0[*]y1) H13.
Step_final ((x0[/] y0[//]nzy)[*](x1[/] y1[//]nzy0)).
apply PP_mult_corr_F; auto.
apply PP_mult_corr_F; auto.
apply mult_resp_ap_zero; auto.
Qed.

Transparent FF_div.
Lemma FF_div_corr_F :
 forall (e f:expr) (x y:F) (nzy:y[#]Zero),
   II e x -> II f y -> II (FF_div e f) (x[/]y[//]nzy).
cut
 (forall (e1 e2 f1 f2:expr) (x y:F) (nzy:y[#]Zero),
    II (expr_div e1 e2) x ->
    II (expr_div f1 f2) y ->
    II (expr_div (PP_mult e1 f2) (PP_mult e2 f1)) (x[/]y[//]nzy)).
cut
 (forall (e f:expr) (x y:F) (nzy:y[#]Zero),
    II e x -> II f y -> II (expr_div e f) (x[/]y[//]nzy)).
intros H H0 e f.
elim e; elim f; intros; simpl in |- *; auto.
intros. apply interpF_div with x y nzy; Algebra.
intros. inversion X. rewrite H in X1. rewrite H1 in X2. rewrite H0 in H2.
inversion X0. rewrite H3 in X3. rewrite H5 in X4. rewrite H4 in H6.
cut (x1[#]Zero). intro nzx1.
cut (y0[*]x1[#]Zero). intro H13.
cut ((x1[/]y1[//]nzy1)[#]Zero). intro H14.
apply interpF_div with (x0[*]y1) (y0[*]x1) H13.
AStepl ((y1[*]x0)[/]y0[*]x1[//]H13).
AStepl (((y1[*]x0)[/]y0[//]nzy0)[/]x1[//]nzx1).
AStepl ((y1[*](x0[/]y0[//]nzy0))[/]x1[//]nzx1).
AStepl (((x0[/]y0[//]nzy0)[*]y1)[/]x1[//]nzx1).
Step_final ((x0[/]y0[//]nzy0)[/]x1[/]y1[//]nzy1[//]H14).
apply PP_mult_corr_F; auto.
apply PP_mult_corr_F; auto.
apply div_resp_ap_zero_rev; auto.
apply mult_resp_ap_zero; auto.
apply div_resp_ap_zero with y1 nzy1.
AStepl y. auto.
Qed.

Lemma NormF_corr : forall (e:expr) (x:F), II e x -> II (NormF e) x.
intro; elim e; intros; simpl in |- *.
apply
 (interpF_div F val unop binop pfun
    (expr_plus (expr_mult (expr_var v) expr_one) expr_zero) expr_one x
    (One:F) x (ring_non_triv F)).
Algebra.
apply
 (interpF_plus F val unop binop pfun (expr_mult (expr_var v) expr_one)
    expr_zero x (Zero:F) x).
Algebra.
apply (interpF_mult F val unop binop pfun (expr_var v) expr_one x (One:F) x);
 Algebra.
apply (interpF_int F val unop binop pfun 1); Algebra.
apply (interpF_int F val unop binop pfun 0); Algebra.
apply (interpF_int F val unop binop pfun 1); Algebra.
apply
 (interpF_div F val unop binop pfun (expr_int z) expr_one x (
    One:F) x (ring_non_triv F)).
Algebra. Algebra. apply (interpF_int F val unop binop pfun 1); Algebra.

inversion X1. rewrite H in X2. rewrite H1 in X3. rewrite H0 in H2.
 apply interpF_wd with (x0[+]y). apply FF_plus_corr_F; auto. auto.

inversion X1. rewrite H in X2. rewrite H1 in X3. rewrite H0 in H2.
 apply interpF_wd with (x0[*]y). apply FF_mult_corr_F; auto. auto.

inversion X1. rewrite H in X2. rewrite H1 in X3. rewrite H0 in H2.
 apply interpF_wd with (x0[/]y[//]nzy).
apply FF_div_corr_F; auto. auto.

inversion X0. rewrite H in H2. rewrite H1 in X1. rewrite H0 in H2.
apply
 (interpF_div F val unop binop pfun
    (expr_plus (expr_mult (expr_unop u (NormF e0)) expr_one) expr_zero)
    expr_one x (One:F) x (ring_non_triv F)).
Algebra.
apply
 (interpF_plus F val unop binop pfun
    (expr_mult (expr_unop u (NormF e0)) expr_one) expr_zero x (
    Zero:F) x).
Algebra.
apply
 (interpF_mult F val unop binop pfun (expr_unop u (NormF e0)) expr_one x
    (One:F) x); Algebra.
apply (interpF_unop F val unop binop pfun (NormF e0) u x0); Algebra.
apply (interpF_int F val unop binop pfun 1); Algebra.
apply (interpF_int F val unop binop pfun 0); Algebra.
apply (interpF_int F val unop binop pfun 1); Algebra.

inversion X1. rewrite H in H3. rewrite H1 in X2. rewrite H2 in X3. rewrite H0 in H3.
apply
 (interpF_div F val unop binop pfun
    (expr_plus (expr_mult (expr_binop b (NormF e0) (NormF e1)) expr_one)
       expr_zero) expr_one x (One:F) x (ring_non_triv F)).
Algebra.
apply
 (interpF_plus F val unop binop pfun
    (expr_mult (expr_binop b (NormF e0) (NormF e1)) expr_one) expr_zero x
    (Zero:F) x).
Algebra.
apply
 (interpF_mult F val unop binop pfun (expr_binop b (NormF e0) (NormF e1))
    expr_one x (One:F) x); Algebra.
apply (interpF_binop F val unop binop pfun (NormF e0) (NormF e1) b x0 y);
 Algebra.
apply (interpF_int F val unop binop pfun 1); Algebra.
apply (interpF_int F val unop binop pfun 0); Algebra.
apply (interpF_int F val unop binop pfun 1); Algebra.

inversion X0. rewrite <- H. rewrite H1 in X1. rewrite H0 in H2.
apply
 (interpF_div F val unop binop pfun
    (expr_plus (expr_mult (expr_part f (NormF e0)) expr_one) expr_zero)
    expr_one x (One:F) x (ring_non_triv F)).
Algebra.
apply
 (interpF_plus F val unop binop pfun
    (expr_mult (expr_part f (NormF e0)) expr_one) expr_zero x (
    Zero:F) x).
Algebra.
apply
 (interpF_mult F val unop binop pfun (expr_part f (NormF e0)) expr_one x
    (One:F) x); Algebra.
apply (interpF_part F val unop binop pfun (NormF e0) f x0) with (Hx := Hx);
 Algebra.
apply (interpF_int F val unop binop pfun 1); Algebra.
apply (interpF_int F val unop binop pfun 0); Algebra.
apply (interpF_int F val unop binop pfun 1); Algebra.
Qed.

Lemma Norm_wfF :
 forall e:expr,
   wfF F val unop binop pfun e -> wfF F val unop binop pfun (NormF e).
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
   wfF F val unop binop pfun e -> expr_is_zero e = true -> II e Zero.
unfold wfF in |- *.
intros e H.
elim H. intro.
elim e; simpl in |- *; try (intros; elimtype False; inversion H0; fail).
intros e0 H0 e1 H1.
elim e0; simpl in |- *; try (intros; elimtype False; inversion H2; fail).
intro.
elim z; simpl in |- *; try (intros; elimtype False; inversion H2; fail);
 intros H2 H3.
inversion H2. rewrite H4 in X. rewrite H6 in X0. rewrite H5 in H7.
apply interpF_div with (Zero:F) y nzy; auto.
Algebra.
apply (interpF_int F val unop binop pfun 0); Algebra.
Qed.

Lemma Tactic_lemma_zero_F :
 forall (x:F) (e:xexprF F val unop binop pfun x),
   expr_is_zero (NormF (xforgetF _ _ _ _ _ _ e)) = true -> x[=]Zero.
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
intros.
apply cg_inv_unique_2.
apply Tactic_lemma_zero_F with (xexprF_minus _ _ _ _ _ _ _ e f).
assumption.
Qed.

End Field_NormCorrect.
