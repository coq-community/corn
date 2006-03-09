(* $Id: FTA.v,v 1.6 2004/04/23 10:00:57 lcf Exp $ *)

Require Export CPoly_Rev.
Require Export FTAreg.

(** * Fundamental Theorem of Algebra
%\begin{convention}% Let [n:nat] and [f] be a complex polynomial of
degree [(S n)].
%\end{convention}%
*)

Section FTA_reg'.

Variable f : cpoly_cring CC.
Variable n : nat.
Hypothesis f_degree : degree (S n) f.

Lemma FTA_reg' : {f1 : CCX | degree 1 f1 | {f2 : CCX | degree n f2 | f [=] f1[*]f2}}.
elim (FTA_reg f (S n)). intro c. intro H.
cut (degree 1 (_X_[-]_C_ c)). intro.
exists (_X_[-]_C_ c). auto.
elim (poly_linear_factor _ _ _ H).
intro f2. intros.
exists f2.
apply degree_mult_imp with (_X_[-]_C_ c) 1. auto.
apply degree_wd with f; auto. auto.
apply degree_minus_lft with 0. apply degree_le_c_. apply degree_x_. auto.
auto with arith.
auto.
Qed.

End FTA_reg'.

(**
%\begin{convention}% Let [n:nat], [f] be a complex polynomial of degree
less than or equal to [(S n)] and [c] be a complex number such that
[f!c  [#]  Zero].
%\end{convention}%
*)

Section FTA_1.

Variable f : cpoly_cring CC.
Variable n : nat.
Hypothesis f_degree : degree_le (S n) f.
Variable c : CC.
Hypothesis f_c : f ! c [#] Zero.

Lemma FTA_1a : degree_le (S n) (Shift c f).
apply Shift_degree_le.
auto.
Qed.

Let g := Rev (S n) (Shift c f).

Lemma FTA_1b : degree (S n) g.
unfold g in |- *.
apply Rev_degree.
astepl f ! c. auto.

Step_final f ! (Zero[+]c).
Qed.

Lemma FTA_1 : {f1 : CCX | {f2 : CCX | degree_le 1 f1 /\ degree_le n f2 /\ f [=] f1[*]f2}}.
elim (FTA_reg' g n FTA_1b). intro g1. intros H H0.
elim H0. clear H0. intro g2. intros H0 H1.
cut (degree_le 1 g1). intro.
cut (degree_le n g2). intro.
exists (Shift [--]c (Rev 1 g1)).
exists (Shift [--]c (Rev n g2)).
split.
apply Shift_degree_le.
apply Rev_degree_le.
split.
apply Shift_degree_le.
apply Rev_degree_le.
cut (degree_le (1 + n) (g1[*]g2)). intro.
cut (degree_le (1 + n) g). intro.
cut (degree_le (1 + n) (Shift c f)). intro.
astepl (Shift [--]c (Shift c f)).
astepl (Shift [--]c (Rev (1 + n) (Rev (S n) (Shift c f)))).
astepl (Shift [--]c (Rev (1 + n) g)).
astepl (Shift [--]c (Rev (1 + n) (g1[*]g2))).
Step_final (Shift [--]c (Rev 1 g1[*]Rev n g2)).
exact FTA_1a.
apply degree_le_wd with (g1[*]g2); algebra.
apply degree_le_mult; auto.
apply degree_imp_degree_le; auto.
apply degree_imp_degree_le; auto.
Qed.

Lemma FTA_1' : {a : CC | {b : CC | {g : CCX | degree_le n g | f [=] (_C_ a[*]_X_[+]_C_ b) [*]g}}}.
elim FTA_1. intro f1. intros H.
elim H. clear H. intros f2 H0.
elim H0. clear H0. intro H. intros H0.
elim H0. clear H0. intros H0 H1.
elim (degree_le_1_imp _ f1); auto. intro a. intros H2. exists a.
elim H2. clear H2. intro b. intros. exists b.
exists f2. auto.
Step_final (f1[*]f2).
Qed.

End FTA_1.

Section Fund_Thm_Alg.

Lemma FTA' : forall n (f : CCX), degree_le n f -> nonConst _ f -> {z : CC | f ! z [=] Zero}.
intro n. induction  n as [| n Hrecn].
unfold nonConst in |- *. unfold degree_le in |- *. intros f H H0.
elim H0. clear H0. intro n. intros H0 H1.
elim (eq_imp_not_ap _ _ _ (H _ H0) H1).
unfold nonConst in |- *. intros f H H0.
elim H0. clear H0. intro m'. intros H0 H1.
elim (poly_apzero_CC f). intro c. intros H2.
elim (FTA_1' f n H c H2). intro a. intros H3.
elim H3. clear H3. intro b. intros H3.
elim H3. clear H3. intro g. intros H3 H4.
elim (O_or_S m'); intro y.
elim y. clear y. intro m. intro y. rewrite <- y in H0. rewrite <- y in H1.
cut (a[*]nth_coeff m g [#] Zero or b[*]nth_coeff (S m) g [#] Zero).
intro H5.
elim H5; clear H5; intros H5.
cut (a [#] Zero). intro H6.
exists ( [--]b[/] a[//]H6).
astepl ((_C_ a[*]_X_[+]_C_ b) [*]g) ! ( [--]b[/] a[//]H6).
astepl ((_C_ a[*]_X_[+]_C_ b) ! ( [--]b[/] a[//]H6) [*]g ! ( [--]b[/] a[//]H6)).
astepl
 (((_C_ a[*]_X_) ! ( [--]b[/] a[//]H6) [+] (_C_ b) ! ( [--]b[/] a[//]H6)) [*]
  g ! ( [--]b[/] a[//]H6)).
astepl
 (((_C_ a) ! ( [--]b[/] a[//]H6) [*]_X_ ! ( [--]b[/] a[//]H6) [+]b) [*]
  g ! ( [--]b[/] a[//]H6)).
astepl ((a[*] ( [--]b[/] a[//]H6) [+]b) [*]g ! ( [--]b[/] a[//]H6)).
rational.
apply cring_mult_ap_zero with (nth_coeff m g). auto.
elim (Hrecn g); auto. intro z. intros. exists z.
astepl ((_C_ a[*]_X_[+]_C_ b) [*]g) ! z.
astepl ((_C_ a[*]_X_[+]_C_ b) ! z[*]g ! z).
Step_final ((_C_ a[*]_X_[+]_C_ b) ! z[*]Zero).
unfold nonConst in |- *. exists (S m). auto.
apply cring_mult_ap_zero_op with b. auto.
apply cg_add_ap_zero.
astepl (nth_coeff (S m) f). auto.
Step_final (nth_coeff (S m) ((_C_ a[*]_X_[+]_C_ b) [*]g)).
rewrite <- y in H0. elim (lt_irrefl 0 H0).
apply nth_coeff_ap_zero_imp with m'. auto.
Qed.

Lemma FTA : forall f : CCX, nonConst _ f -> {z : CC | f ! z [=] Zero}.
intros.
elim (Cpoly_ex_degree _ f). intro n. intros. (* Set_ not necessary *)
apply FTA' with n; auto.
Qed.

Lemma FTA_a_la_Henk : forall f : CCX,
 {x : CC | {y : CC | AbsCC (f ! x[-]f ! y) [>]Zero}} -> {z : CC | f ! z [=] Zero}.
intros f H.
elim H.
intros x H0.
elim H0.
intros y H1.
unfold greater in H1.
generalize (less_imp_ap _ _ _ H1); intro H2.
generalize (AbsCC_ap_zero _ H2); intro H3.

cut
 (Sum 0 (lth_of_poly f) (fun i : nat => nth_coeff i f[*] (x[^]i[-]y[^]i)) [#] 
  Zero). 
intro H4.
cut (0 <= lth_of_poly f); try auto with arith.
intro H5.
generalize (Sum_apzero _ _ _ _ H5 H4); intro H6.
elim H6; intros i H8 H9.
elim H8; intros H10 H11.
apply FTA.
unfold nonConst in |- *.
generalize (cring_mult_ap_zero _ _ _ H9); intro H12.
exists i.
elim (zerop i).
intro H13.
elimtype False.
elim (ap_irreflexive_unfolded _ (Zero:CC)).
rstepl (nth_coeff i f[*] (x[^]0[-]y[^]0)).
rewrite <- H13.
assumption.
auto.
assumption.
apply
 ap_wdl_unfolded
  with
    (Sum 0 (lth_of_poly f)
       (fun i : nat => nth_coeff i f[*]x[^]i[-]nth_coeff i f[*]y[^]i)).
2: apply Sum_wd.
2: intro.
2: algebra.
apply
 ap_wdl_unfolded
  with
    (Sum 0 (lth_of_poly f) (fun i : nat => nth_coeff i f[*]x[^]i) [-]
     Sum 0 (lth_of_poly f) (fun i : nat => nth_coeff i f[*]y[^]i)).
2: apply eq_symmetric_unfolded.
2: change
     (Sum 0 (lth_of_poly f)
        (fun j : nat =>
         (fun i : nat => nth_coeff i f[*]x[^]i) j[-]
         (fun i : nat => nth_coeff i f[*]y[^]i) j) [=] 
      Sum 0 (lth_of_poly f) (fun i : nat => nth_coeff i f[*]x[^]i) [-]
      Sum 0 (lth_of_poly f) (fun i : nat => nth_coeff i f[*]y[^]i)) 
    in |- *.
2: apply Sum_minus_Sum.
apply ap_wdl_unfolded with (f ! x[-]f ! y).
2: unfold cg_minus in |- *.
2: apply csbf_wd_unfolded.
2: apply poly_as_sum.
2: apply poly_degree_lth.
2: apply csf_wd_unfolded.
2: apply poly_as_sum.
2: apply poly_degree_lth.
assumption.
Qed.

End Fund_Thm_Alg.
