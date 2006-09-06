
Require Export CLogic.

Section Syntactic_Expressions.

Definition varindex : Set := nat.
Definition unopindex : Set := nat.

Inductive expr : Set :=
  | expr_var : varindex -> expr
  | expr_int : Z -> expr
  | expr_plus : expr -> expr -> expr
  | expr_mult : expr -> expr -> expr
  | expr_div : expr -> expr -> expr
  | expr_unop : unopindex -> expr -> expr.

Definition expr_zero : expr := expr_int 0.
Definition expr_one : expr := expr_int 1.

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
  end.

Definition le_expr (e f:expr) := orb (eq_expr e f) (lt_expr e f).

Fixpoint eq_monom (e f:expr) {struct e} : bool :=
  match e, f with
  | expr_mult (expr_var n) e', expr_mult (expr_var m) f' =>
      andb (eq_nat n m) (eq_monom e' f')
  | expr_mult (expr_unop n e1) e', expr_mult (expr_unop m f1) f' =>
      andb (eq_nat n m) (andb (eq_monom e' f') (eq_expr e1 f1))
  | expr_int _, expr_int _ => true
  | _, _ => false
  end.

Fixpoint lt_monom (e f:expr) {struct e} : bool :=
  match e, f with
  | expr_mult (expr_var n) e', expr_mult (expr_var m) f' =>
      ifb (eq_nat n m) (lt_monom e' f') (lt_nat n m)
  | expr_mult (expr_var _) _, expr_mult (expr_unop _ _) _ => true
  | expr_mult (expr_unop n e1) e', expr_mult (expr_unop m f1) f' =>
      ifb (eq_expr (expr_unop n e1) (expr_unop m f1)) (
        lt_expr e' f') (lt_expr (expr_unop n e1) (expr_unop m f1))
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
  | expr_mult (expr_unop _ _) e', expr_var _ => expr_mult f e
  | expr_mult (expr_unop n e') e0, expr_unop m f' =>
      match lt_expr (expr_unop n e') f with
      | true => expr_mult (expr_unop n e') (MV_mult e0 f)
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
  end.

Definition expr_is_zero (e:expr) : bool :=
  match e with
  | expr_div (expr_int Z0) _ => true
  | _ => false
  end.

End Normalization_Function.

Section Correctness_Results.

Lemma eq_nat_corr : forall n m:nat, eq_nat n m = true -> n = m.
simple induction n; simple induction m; simpl in |- *; intros.
trivial.
inversion H0.
inversion H0.
rewrite (H n1 H1). trivial.
Qed.

Lemma eq_int_corr : forall n m:Z, eq_int n m = true -> n = m.
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
simple induction e; simple induction e'; simpl in |- *; intros;
 try inversion H3; try inversion H2; try inversion H1; 
 try inversion H0; try inversion H.
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
Qed.

End Correctness_Results.

Inductive M : expr -> Set :=
  | M_int : forall z, M (expr_int z)
  | M_1i  : forall n e z, (P e) -> M (expr_mult (expr_unop n e) (expr_int z))
  | M_1M  : forall n1 n2 e1 e2 f, P e1 -> P e2 ->
                   (le_expr (expr_unop n1 e1) (expr_unop n2 e2))=true ->
                   M (expr_mult (expr_unop n2 e2) f) ->
            M (expr_mult (expr_unop n1 e1) (expr_mult (expr_unop n2 e2) f))
  | M_0i  : forall n z, M (expr_mult (expr_var n) (expr_int z))
  | M_0M  : forall m e n f, M (expr_mult (expr_unop m e) f) ->
            M (expr_mult (expr_var n) (expr_mult (expr_unop m e) f))
  | M_0M' : forall n1 n2 f,
                   (le_nat n1 n2)=true -> M (expr_mult (expr_var n2) f) ->
                   M (expr_mult (expr_var n1) (expr_mult (expr_var n2) f))
  with P : expr -> Set :=
  | P_int : forall z, P (expr_int z)
  | P_pi  : forall e f z, M (expr_mult e f) -> 
                          P (expr_plus (expr_mult e f) (expr_int z))
  | P_pP  : forall e f g, M e -> P (expr_plus f g) -> (lt_monom e f)=true ->
                          P (expr_plus e (expr_plus f g)).

Inductive F : expr -> Set :=
  | F_div : forall e f, P e -> P f -> F (expr_div e f).

Opaque Zmult.

Lemma MI_mult_M : forall e z, M e -> M (MI_mult e (expr_int z)).
intros.
induction H; simpl.
case z; simpl; intros; apply M_int.
case z; simpl; intros. apply M_int. apply M_1i; auto. apply M_1i; auto.
generalize IHM. case z; simpl; intros; auto; apply M_1M; auto.
case z; simpl; intros. apply M_int. apply M_0i; auto. apply M_0i; auto.
generalize IHM. case z; simpl; intros; auto; apply M_0M; auto.
generalize IHM. case z; simpl; intros; auto; apply M_0M'; auto.
Qed.

Opaque MI_mult.

Lemma bool_dec : forall b, (b=true) or (b=false).
intro; elim b; auto.
Qed.

Lemma eq_nat_sym : forall m n, eq_nat m n=eq_nat n m.
induction m; induction n; simpl; auto.
Qed.

Lemma eq_int_sym : forall m n, eq_int m n=eq_int n m.
induction m; induction n; simpl; auto; apply eq_nat_sym.
Qed.

Lemma eq_expr_sym : forall e f, eq_expr e f=eq_expr f e.
induction e; simpl; induction f; simpl; auto.
apply eq_nat_sym.
apply eq_int_sym.
rewrite IHe1; rewrite IHe2; auto.
rewrite IHe1; rewrite IHe2; auto.
rewrite IHe1; rewrite IHe2; auto.
rewrite IHe; rewrite eq_nat_sym; auto.
Qed.

Lemma lt_nat_fo : forall m n,
 {lt_nat m n=true}+{eq_nat m n=true}+{lt_nat n m=true}.
induction m; induction n; simpl; auto.
Qed.

Lemma lt_int_fo : forall m n,
 {lt_int m n=true}+{eq_int m n=true}+{lt_int n m=true}.
induction m; induction n; simpl; auto.
apply lt_nat_fo.
elim (lt_nat_fo (nat_of_P p) (nat_of_P p0)); auto.
intro H; elim H; clear H; intro H; auto.
Qed.

Lemma lt_expr_fo : forall e f,
 {lt_expr e f=true}+{eq_expr e f=true}+{lt_expr f e=true}.
induction e; induction f; simpl; auto.
apply lt_nat_fo.
apply lt_int_fo.
clear IHf2 IHf1.
 elim (IHe1 f1); intro H1; try (elim H1; clear H1; intro H1); simpl.
 left. left. apply orb_true_intro. auto.
 elim (IHe2 f2); intro H2; try (elim H2; clear H2; intro H2); simpl.
 left. left. apply orb_true_intro. right. apply andb_true_intro. auto.
 left. right. apply andb_true_intro. auto.
 right. apply orb_true_intro. right. apply andb_true_intro.
 rewrite eq_expr_sym; auto.
 right. apply orb_true_intro. auto.
clear IHf2 IHf1.
 elim (IHe1 f1); intro H1; try (elim H1; clear H1; intro H1); simpl.
 left. left. apply orb_true_intro. auto.
 elim (IHe2 f2); intro H2; try (elim H2; clear H2; intro H2); simpl.
 left. left. apply orb_true_intro. right. apply andb_true_intro. auto.
 left. right. apply andb_true_intro. auto.
 right. apply orb_true_intro. right. apply andb_true_intro.
 rewrite eq_expr_sym; auto.
 right. apply orb_true_intro. auto.
clear IHf2 IHf1.
 elim (IHe1 f1); intro H1; try (elim H1; clear H1; intro H1); simpl.
 left. left. apply orb_true_intro. auto.
 elim (IHe2 f2); intro H2; try (elim H2; clear H2; intro H2); simpl.
 left. left. apply orb_true_intro. right. apply andb_true_intro. auto.
 left. right. apply andb_true_intro. auto.
 right. apply orb_true_intro. right. apply andb_true_intro.
 rewrite eq_expr_sym; auto.
 right. apply orb_true_intro. auto.
clear IHf.
 elim (lt_nat_fo u u0); intro H1; try (elim H1; clear H1; intro H1); simpl.
 left. left. apply orb_true_intro. auto.
 elim (IHe f); intro H2; try (elim H2; clear H2; intro H2); simpl.
 left. left. apply orb_true_intro. right. apply andb_true_intro. auto.
 left. right. apply andb_true_intro. auto.
 right. apply orb_true_intro. right. apply andb_true_intro.
 rewrite eq_nat_sym; auto.
 right. apply orb_true_intro. auto.
Qed.

Lemma lt_nat_lt : forall m n, (lt_nat m n)=true -> lt m n.
induction m. induction n; simpl; auto with arith.
 intro H; inversion H.
induction n. simpl. intro H; inversion H.
intros. auto with arith.
Qed.

Lemma le_nat_le : forall m n, (le_nat m n)=true -> le m n.
induction m. auto with arith.
induction n. simpl. intro H; inversion H.
intros. auto with arith.
Qed.

Lemma lt_lt_nat : forall m n, lt m n -> (lt_nat m n)=true.
induction m. induction n; simpl; auto with arith.
 intro H; inversion H.
induction n. simpl. intro H; inversion H.
intros. simpl. auto with arith.
Qed.

Lemma eq_eq_nat : forall m n, m = n -> (eq_nat m n)=true.
induction m. induction n; simpl. auto. intro H; inversion H.
induction n. simpl. intro H; inversion H.
intros. simpl. auto with arith.
Qed.

Lemma le_le_nat : forall m n, le m n -> (le_nat m n)=true.
induction m. induction n; simpl; auto with arith.
induction n. intro H; inversion H.
intros. unfold le_nat. apply orb_true_intro.
inversion H. left. clear H1 H IHn IHm m. induction n; auto.
right; apply lt_lt_nat; auto with arith.
Qed.

Lemma lt_nat_le_nat_dec : forall m n, (lt_nat m n)=false -> (le_nat n m)=true.
induction m. induction n; simpl; auto.
induction n; simpl; auto.
intro. elim (IHm n); auto.
Qed.

Lemma le_nat_lt_nat_dec : forall m n, (le_nat m n)=false -> (lt_nat n m)=true.
induction m. induction n; simpl; auto.
induction n; simpl; auto.
Qed.

Lemma lt_nat_imp_le_nat : forall m n, (lt_nat m n)=true -> (le_nat m n)=true.
intros. unfold le_nat. rewrite H. rewrite orb_b_true. auto.
Qed.

Lemma lt_nat_lt' : forall m n, (lt_nat m n)=false -> ~lt m n.
intros. cut (le n m). auto with arith.
apply le_nat_le. apply lt_nat_le_nat_dec. auto.
Qed.

Lemma le_nat_le' : forall m n, (le_nat m n)=false -> ~le m n.
intros. cut (lt n m). auto with arith.
apply lt_nat_lt. apply le_nat_lt_nat_dec. auto.
Qed.

Lemma eq_nat_eq' : forall m n, (eq_nat m n)=false -> ~m = n.
induction m. induction n; simpl. intro H; inversion H. auto.
induction n. simpl. auto.
intros. auto with arith.
Qed.

Lemma MV0_mult_M : forall e n, M e -> M (MV_mult e (expr_var n)).
intros.
induction H; simpl.
apply MI_mult_M. unfold expr_one; apply M_0i.
apply M_0M; auto. apply M_1i; auto.
inversion IHM. apply M_0M. apply M_1M; auto.
elim (bool_dec (lt_nat n0 n)); intro H; rewrite H.
 Transparent MI_mult. simpl. case z; simpl; auto. apply M_0i.
  intros; apply M_0M'. apply lt_nat_imp_le_nat; auto. apply M_0i.
 intro. apply M_0M'. apply lt_nat_imp_le_nat; auto. apply M_0i.
apply M_0M'. apply lt_nat_le_nat_dec; auto. apply M_0i.

elim (bool_dec (lt_nat n0 n)); intro H0; rewrite H0.
 apply M_0M'; auto. apply lt_nat_imp_le_nat; auto.
apply M_0M'. apply lt_nat_le_nat_dec; auto. apply M_0M. auto.

generalize IHM. clear IHM. simpl.
elim (bool_dec (lt_nat n1 n)); intro H0; rewrite H0.
 elim (bool_dec (lt_nat n2 n)); intro H1; rewrite H1.
  apply M_0M'; auto. apply M_0M'; auto. apply lt_nat_imp_le_nat; auto.
replace (lt_nat n2 n) with false; simpl. intro. apply M_0M'; auto.
  apply lt_nat_le_nat_dec; auto. apply M_0M'; auto.
symmetry. apply not_true_is_false; intro.
generalize (lt_nat_lt _ _ H1). generalize (le_nat_le _ _ e). intros.
apply eq_true_false_abs with (b:=lt_nat n1 n); auto.
apply lt_lt_nat. eauto with arith.
Qed.

Opaque MI_mult.

Lemma MV1_mult_M : forall e f n, M e -> P f -> M (MV_mult e (expr_unop n f)).
intros. induction H; simpl.

apply MI_mult_M. unfold expr_one. apply M_1i. auto.

elim (bool_dec (lt_nat n0 n)); intro H; rewrite H; simpl.
Transparent MI_mult.
simpl. case z; simpl. apply M_1i; auto. intros; apply M_1M; auto.
 unfold le_expr; simpl; rewrite H; simpl. rewrite orb_b_true; auto.
 apply M_1i; auto. intro; apply M_1M; auto. unfold le_expr; simpl.
 rewrite H; simpl. rewrite orb_b_true; auto. apply M_1i. auto.
elim (bool_dec (andb (eq_nat n0 n) (lt_expr e f))); intro H'.
 rewrite H'; simpl. case z; simpl. apply M_1i; auto. intros; apply M_1M; auto.
 unfold le_expr; simpl; rewrite H'; simpl. repeat rewrite orb_b_true; auto.
 apply M_1i; auto. intro; apply M_1M; auto. unfold le_expr; simpl.
 rewrite H'; simpl. repeat rewrite orb_b_true; auto. apply M_1i. auto.
Opaque MI_mult.
rewrite H'; simpl. apply M_1M; auto. unfold le_expr; simpl.
apply orb_true_intro.
elim (andb_false_elim _ _ H'); intro H''.
 right. apply orb_true_intro; left.
 apply lt_lt_nat. assert (N:=(lt_nat_lt' _ _ H)).
 assert (N':=(eq_nat_eq' _ _ H'')). clear H H' H'' H0 p z e. omega.
 elim (lt_expr_fo e f); intro H'''; try (elim H'''; clear H'''; intro H''').
 rewrite H'' in H'''; inversion H'''.
 elim (lt_nat_fo n n0); intro Hiv; try (elim Hiv; clear Hiv; intro Hiv).
 right. apply orb_true_intro; auto. left; apply andb_true_intro.
 rewrite eq_expr_sym; auto. rewrite H in Hiv; inversion Hiv.
 elim (lt_nat_fo n n0); intro Hiv; try (elim Hiv; clear Hiv; intro Hiv).
 right. apply orb_true_intro; auto. right; apply orb_true_intro; right.
 apply andb_true_intro; auto. rewrite H in Hiv; inversion Hiv.
apply M_1i; auto.
(* *)
Abort.

(*
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
  end.
*)















(*
Lemma NormR_correct : forall e, N (NormR e).
induction e; simpl; auto.
unfold expr_zero, expr_one; apply N_pi. apply M_0i.

apply N_int.

induction IHe1; simpl. induction IHe2; simpl. apply N_int. apply N_pi; auto.
  apply N_pN; auto.
 induction IHe2. simpl; apply N_pi; auto.
  induction e0; simpl; auto. induction e; simpl; auto. elim (eq_nat v v0); simpl; auto.
*)

Lemma NormR_idemp : forall e, P e -> (NormR e)=e.
intros. induction H; simpl; auto.
Abort.


Lemma SG : forall e1 e2 e3, P e1 -> P e2 -> P e3 ->
NormR (expr_plus e1 (expr_plus e2 e3))=NormR (expr_plus (expr_plus e1 e2) e3).
intros.
induction H; induction H0; induction H1; simpl; auto.
replace (z1+z0+z)%Z with (z1+(z0+z))%Z; auto with zarith.
Abort.




