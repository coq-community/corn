Require Export COrdFields.

(** printing one_div_succ %\ensuremath{\frac1{\cdot+1}}% *)
(** printing Half %\ensuremath{\frac12}% #&frac12;# *)

(***********************************)
Section Properties_of_leEq.
(***********************************)

(**
** Properties of [[<=]]
%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)

Variable R : COrdField.

Section addition.
(**
*** Addition and subtraction%\label{section:leEq-plus-minus}%
*)

Lemma plus_resp_leEq : forall x y z : R, x [<=] y -> x[+]z [<=] y[+]z.
unfold leEq in |- *.
intros.
intro.
apply H.
apply (plus_cancel_less _ _ _ _ X).
Qed.

Lemma plus_resp_leEq_lft : forall x y z : R, x [<=] y -> z[+]x [<=] z[+]y.
intros.
astepl (x[+]z).
astepr (y[+]z).
apply plus_resp_leEq; auto.
Qed.

Lemma minus_resp_leEq : forall x y z : R, x [<=] y -> x[-]z [<=] y[-]z.
intros.
astepl (x[+][--]z).
astepr (y[+][--]z).
apply plus_resp_leEq; auto.
Qed.

Lemma inv_resp_leEq : forall x y : R, x [<=] y -> [--]y [<=] [--]x.
unfold leEq in |- *.
intros.
intro.
apply H.
apply inv_cancel_less.
assumption.
Qed.

Lemma minus_resp_leEq_rht : forall x y z : R, y [<=] x -> z[-]x [<=] z[-]y.
intros.
Transparent cg_minus.
unfold cg_minus in |- *.
apply plus_resp_leEq_lft.
apply inv_resp_leEq.
assumption.
Qed.

Lemma plus_resp_leEq_both : forall x y a b : R, x [<=] y -> a [<=] b -> x[+]a [<=] y[+]b.
 intros.
 apply leEq_transitive with (y := x[+]b).
 rstepl (a[+]x).
 rstepr (b[+]x).
 apply plus_resp_leEq.
 assumption.
 apply plus_resp_leEq.
 assumption.
Qed.

Lemma plus_resp_less_leEq : forall a b c d : R, a [<] b -> c [<=] d -> a[+]c [<] b[+]d.
intros.
apply leEq_less_trans with (a[+]d).
apply plus_resp_leEq_lft. auto.
apply plus_resp_less_rht. auto.
Qed.

Lemma plus_resp_leEq_less : forall a b c d : R, a [<=] b -> c [<] d -> a[+]c [<] b[+]d.
intros.
astepl (c[+]a).
astepr (d[+]b).
apply plus_resp_less_leEq; auto.
Qed.

Lemma minus_resp_less_leEq : forall x y x' y' : R, x [<=] y -> y' [<] x' -> x[-]x' [<] y[-]y'.
intros.
astepl (x[+][--]x').
astepr (y[+][--]y').
apply plus_resp_leEq_less.
auto.
apply inv_resp_less. auto.
Qed.

Lemma minus_resp_leEq_both : forall x y x' y' : R, x [<=] y -> y' [<=] x' -> x[-]x' [<=] y[-]y'.
intros.
astepl (x[+][--]x').
astepr (y[+][--]y').
apply plus_resp_leEq_both. auto.
apply inv_resp_leEq. auto.
Qed.

(** Cancellation properties
*)

Lemma plus_cancel_leEq_rht : forall x y z : R, x[+]z [<=] y[+]z -> x [<=] y.
 intros.
 rstepl (x[+]z[+][--]z).
 rstepr (y[+]z[+][--]z).
 apply plus_resp_leEq.
 assumption.
Qed.

Lemma inv_cancel_leEq : forall x y : R, [--]y [<=] [--]x -> x [<=] y.
 intros.
 rstepl ([--][--]x).
 rstepr ([--][--]y).
 apply inv_resp_leEq.
 assumption.
Qed.

(** Laws for shifting
*)

Lemma shift_plus_leEq : forall a b c : R, a [<=] c[-]b -> a[+]b [<=] c.
intros.
rstepr (c[-]b[+]b).
apply plus_resp_leEq.
assumption.
Qed.

Lemma shift_leEq_plus : forall a b c : R, a[-]b [<=] c -> a [<=] c[+]b.
intros.
rstepl (a[-]b[+]b).
apply plus_resp_leEq.
assumption.
Qed.

Lemma shift_plus_leEq' : forall a b c : R, b [<=] c[-]a -> a[+]b [<=] c.
intros.
rstepr (a[+] (c[-]a)).
apply plus_resp_leEq_lft.
assumption.
Qed.

Lemma shift_leEq_plus' : forall a b c : R, a[-]b [<=] c -> a [<=] b[+]c.
intros.
rstepl (b[+] (a[-]b)).
apply plus_resp_leEq_lft. auto.
Qed.

Lemma shift_leEq_rht : forall a b : R, Zero [<=] b[-]a -> a [<=] b.
intros.
astepl (Zero[+]a).
rstepr (b[-]a[+]a).
apply plus_resp_leEq. auto.
Qed.

Lemma shift_leEq_lft : forall a b : R, a [<=] b -> Zero [<=] b[-]a.
intros.
astepl (a[-]a).
apply minus_resp_leEq. auto.
Qed.

Lemma shift_minus_leEq : forall a b c : R, a [<=] c[+]b -> a[-]b [<=] c.
intros.
rstepr (c[+]b[-]b).
apply minus_resp_leEq.
assumption.
Qed.

Lemma shift_leEq_minus : forall a b c : R, a[+]c [<=] b -> a [<=] b[-]c.
intros.
rstepl (a[+]c[-]c).
apply minus_resp_leEq.
assumption.
Qed.

Lemma shift_leEq_minus' : forall a b c : R, c[+]a [<=] b -> a [<=] b[-]c.
intros.
rstepl (c[+]a[-]c).
apply minus_resp_leEq.
assumption.
Qed.

Lemma shift_zero_leEq_minus : forall x y : R, x [<=] y -> Zero [<=] y[-]x.
intros.
rstepl (x[-]x).
apply minus_resp_leEq.
assumption.
Qed.

Lemma shift_zero_leEq_minus' : forall x y : R, Zero [<=] y[-]x -> x [<=] y.
intros.
apply plus_cancel_leEq_rht with ([--]x).
rstepl (Zero:R).
assumption.
Qed.

End addition.

Section multiplication.
(**
*** Multiplication and division

Multiplication and division respect [[<=]]
*)

Lemma mult_resp_leEq_rht : forall x y z : R, x [<=] y -> Zero [<=] z -> x[*]z [<=] y[*]z.
unfold leEq in |- *.
intros.
intro H1.
generalize (shift_zero_less_minus _ _ _ H1); intro H2.
cut (Zero [<] (x[-]y) [*]z).
intro H3.
2: rstepr (x[*]z[-]y[*]z).
2: assumption.
cut
 (forall a b : R,
  Zero [<] a[*]b -> Zero [<] a and Zero [<] b or a [<] Zero and b [<] Zero).
intro H4.
generalize (H4 _ _ H3); intro H5.
elim H5; intro H6.
elim H6; intros.
elim H.
astepl (Zero[+]y).
apply shift_plus_less.
assumption.
elim H6; intros.
elim H0.
assumption.

intros a b H4.
generalize (Greater_imp_ap _ _ _ H4); intro H5.
generalize (mult_cancel_ap_zero_lft _ _ _ H5); intro H6.
generalize (mult_cancel_ap_zero_rht _ _ _ H5); intro H7.
elim (ap_imp_less _ _ _ H6); intro H8.
right.
split.
assumption.
elim (ap_imp_less _ _ _ H7); intro H9.
assumption.
elimtype False.
elim (less_irreflexive_unfolded R Zero).
apply less_leEq_trans with (a[*]b).
assumption.
apply less_leEq.
apply inv_cancel_less.
astepl (Zero:R).
astepr ([--]a[*]b).
apply mult_resp_pos.
astepl ([--](Zero:R)).
apply inv_resp_less.
assumption.
assumption.
left.
split.
assumption.
elim (ap_imp_less _ _ _ H7); intro H9.
elimtype False.
elim (less_irreflexive_unfolded R Zero).
apply less_leEq_trans with (a[*]b).
assumption.
apply less_leEq.
apply inv_cancel_less.
astepl (Zero:R).
astepr (a[*][--]b).
apply mult_resp_pos.
assumption.
astepl ([--](Zero:R)).
apply inv_resp_less.
assumption.
assumption.
Qed.

Lemma mult_resp_leEq_lft : forall x y z : R, x [<=] y -> Zero [<=] z -> z[*]x [<=] z[*]y.
intros.
astepl (x[*]z).
astepr (y[*]z).
apply mult_resp_leEq_rht.
assumption.
assumption.
Qed.

Lemma mult_resp_leEq_both : forall x x' y y' : R,
 Zero [<=] x -> Zero [<=] y -> x [<=] x' -> y [<=] y' -> x[*]y [<=] x'[*]y'.
intros.
apply leEq_transitive with (x[*]y').
apply mult_resp_leEq_lft; assumption.
apply mult_resp_leEq_rht.
assumption.
apply leEq_transitive with y; assumption.
Qed.

Lemma recip_resp_leEq : forall (x y : R) x_ y_, Zero [<] y -> y [<=] x -> (One[/] x[//]x_) [<=] (One[/] y[//]y_).
unfold leEq in |- *.
intros x y x_ y_ H H0. intro H1. apply H0.
cut ((One[/] x[//]x_) [#] Zero). intro x'_.
cut ((One[/] y[//]y_) [#] Zero). intro y'_.
rstepl (One[/] One[/] x[//]x_[//]x'_).
rstepr (One[/] One[/] y[//]y_[//]y'_).
apply recip_resp_less.
apply recip_resp_pos; auto.
auto.
apply div_resp_ap_zero_rev. apply ring_non_triv.
apply div_resp_ap_zero_rev. apply ring_non_triv.
Qed.

Lemma div_resp_leEq : forall (x y z : R) z_, Zero [<] z -> x [<=] y -> (x[/] z[//]z_) [<=] (y[/] z[//]z_).
intros.
rstepl (x[*] (One[/] z[//]z_)).
rstepr (y[*] (One[/] z[//]z_)).
apply mult_resp_leEq_rht.
assumption.
apply less_leEq.
apply recip_resp_pos.
auto.
Qed.

Hint Resolve recip_resp_leEq: algebra.

(** Cancellation properties
*)

Lemma mult_cancel_leEq : forall x y z : R, Zero [<] z -> x[*]z [<=] y[*]z -> x [<=] y.
unfold leEq in |- *.
intros.
intro.
apply H.
apply mult_resp_less.
assumption.
assumption.
Qed.

(** Laws for shifting
*)

Lemma shift_mult_leEq : forall (x y z : R) z_, Zero [<] z -> x [<=] (y[/] z[//]z_) -> x[*]z [<=] y.
intros.
rstepr ((y[/] z[//]z_) [*]z).
apply mult_resp_leEq_rht; [ assumption | apply less_leEq; assumption ].
Qed.

Lemma shift_mult_leEq' : forall (x y z : R) z_, Zero [<] z -> x [<=] (y[/] z[//]z_) -> z[*]x [<=] y.
intros.
rstepr (z[*] (y[/] z[//]z_)).
apply mult_resp_leEq_lft; [ assumption | apply less_leEq; assumption ].
Qed.

Lemma shift_leEq_mult' : forall (x y z : R) y_, Zero [<] y -> (x[/] y[//]y_) [<=] z -> x [<=] y[*]z.
unfold leEq in |- *. intros x y z H. intros. intro. apply H0.
apply shift_less_div. auto.
astepl (y[*]z). auto.
Qed.

Lemma shift_div_leEq : forall x y z : R, Zero [<] z -> forall z_ : z [#] Zero, x [<=] y[*]z -> (x[/] z[//]z_) [<=] y.
intros.
rstepr (y[*]z[/] z[//]z_).
apply div_resp_leEq.
assumption.
assumption.
Qed.

Lemma shift_div_leEq' : forall (x y z : R) z_, Zero [<] z -> x [<=] z[*]y -> (x[/] z[//]z_) [<=] y.
intros.
rstepr (z[*]y[/] z[//]z_).
apply div_resp_leEq.
assumption.
assumption.
Qed.

Lemma shift_leEq_div : forall (x y z : R) y_, Zero [<] y -> x[*]y [<=] z -> x [<=] (z[/] y[//]y_).
unfold leEq in |- *. intros x y z H. intros. intro. apply H0.
astepr (y[*]x).
apply shift_less_mult' with H; auto.
Qed.

Hint Resolve shift_leEq_div: algebra.

Lemma eps_div_leEq_eps : forall (eps d : R) d_, Zero [<=] eps -> One [<=] d -> (eps[/] d[//]d_) [<=] eps.
intros.
apply shift_div_leEq'.
apply less_leEq_trans with (One:R).
apply pos_one.

assumption.

astepl (One[*]eps).
apply mult_resp_leEq_rht.
assumption.

assumption.
Qed.

Lemma nonneg_div_two : forall eps : R, Zero [<=] eps -> Zero [<=] eps [/]TwoNZ.
intros.
apply shift_leEq_div.
apply pos_two.

astepl (Zero:R).
assumption.
Qed.

Lemma nonneg_div_two' : forall eps : R, Zero [<=] eps -> eps [/]TwoNZ [<=] eps.
intros.
apply shift_div_leEq.
apply pos_two.
astepl (eps[+]Zero); rstepr (eps[+]eps).
apply plus_resp_leEq_lft; auto.
Qed.

Lemma nonneg_div_three : forall eps : R, Zero [<=] eps -> Zero [<=] eps [/]ThreeNZ.
intros.
apply mult_cancel_leEq with (Three:R).
apply pos_three.
astepl (Zero:R); rstepr eps.
assumption.
Qed.

Lemma nonneg_div_three' : forall eps : R, Zero [<=] eps -> eps [/]ThreeNZ [<=] eps.
intros.
apply shift_div_leEq.
apply pos_three.
rstepl (eps[+]Zero[+]Zero); rstepr (eps[+]eps[+]eps).
repeat apply plus_resp_leEq_both; auto.
apply leEq_reflexive.
Qed.

Lemma nonneg_div_four : forall eps : R, Zero [<=] eps -> Zero [<=] eps [/]FourNZ.
intros.
rstepr ((eps [/]TwoNZ) [/]TwoNZ).
apply nonneg_div_two; apply nonneg_div_two; assumption.
Qed.

Lemma nonneg_div_four' : forall eps : R, Zero [<=] eps -> eps [/]FourNZ [<=] eps.
intros.
rstepl ((eps [/]TwoNZ) [/]TwoNZ).
apply leEq_transitive with (eps [/]TwoNZ).
2: apply nonneg_div_two'; assumption.
apply nonneg_div_two'.
apply nonneg_div_two.
assumption.
Qed.

End multiplication.

Section misc.
(**
*** Miscellaneous Properties
*)

Lemma sqr_nonneg : forall x : R, Zero [<=] x[^]2.
unfold leEq in |- *. intros. intro H.
cut (Zero [<] x[^]2). intro H0.
elim (less_antisymmetric_unfolded _ _ _ H H0).
cut (x [<] Zero or Zero [<] x). intro H0. elim H0; clear H0; intros H0.
rstepr ([--]x[*][--]x).
cut (Zero [<] [--]x). intro H1.
apply mult_resp_pos; auto.
astepl ([--](Zero:R)). apply inv_resp_less. auto.
rstepr (x[*]x).
apply mult_resp_pos; auto.
apply ap_imp_less.
apply cring_mult_ap_zero with x.
astepl (x[^]2).
apply less_imp_ap. auto.
Qed.

Lemma nring_nonneg : forall n : nat, Zero [<=] nring (R:=R) n.
intro; induction  n as [| n Hrecn].
apply leEq_reflexive.
apply leEq_transitive with (nring (R:=R) n);
 [ assumption | apply less_leEq; simpl in |- *; apply less_plusOne ].
Qed.


Lemma suc_leEq_dub : forall n, nring (R:=R) (S (S n)) [<=] Two[*]nring (S n).
intro n.
induction  n as [| n Hrecn].
apply eq_imp_leEq.
rational.

astepl (nring (R:=R) (S (S n)) [+]nring 1).
apply leEq_transitive with (nring (R:=R) 2[*]nring (S n) [+]nring 1).
apply plus_resp_leEq.
astepr ((Two:R) [*]nring (S n)).
exact Hrecn.

simpl in |- *.
astepr
 (((Zero:R) [+]One[+]One) [*] (nring n[+]One) [+] ((Zero:R) [+]One[+]One) [*]One).
apply plus_resp_leEq_lft.
astepr ((Zero:R) [+]One[+]One).
astepr ((Zero:R) [+] (One[+]One)).
apply plus_resp_leEq_lft.
astepr (Two:R).
apply less_leEq.
apply one_less_two.

simpl in |- *.
astepl (nring (R:=R) n[+]One[+] (One[+] (Zero[+]One))).
astepl (nring (R:=R) n[+] (One[+] (One[+] (Zero[+]One)))).
astepr (nring (R:=R) n[+]One[+] (One[+]One)).
astepr (nring (R:=R) n[+] (One[+] (One[+]One))).
rational.
Qed.

Lemma leEq_nring : forall n m, nring (R:=R) n [<=] nring m -> n <= m.
intro n; induction  n as [| n Hrecn].
intros.
auto with arith.
intros.
induction  m as [| m Hrecm].
elimtype False.
cut (nring (R:=R) n [<] Zero).
change (nring 0 [<=] nring (R:=R) n) in |- *.
apply nring_leEq.
auto with arith.
change (nring n [<] nring (R:=R) 0) in |- *.
apply nring_less.
apply lt_le_trans with (S n).
auto with arith.
elimtype False; apply H.
apply nring_less; auto with arith.
cut (n <= m).
auto with arith.
apply Hrecn.
rstepr (nring (R:=R) m[+]One[-]One).
apply shift_leEq_minus.
apply H.
Qed.

Lemma cc_abs_aid : forall x y : R, Zero [<=] x[^]2[+]y[^]2.
intros.
astepl (Zero[+] (Zero:R)).
apply plus_resp_leEq_both; apply sqr_nonneg.
Qed.

Load "Transparent_algebra".

Lemma nexp_resp_pos : forall (x : R) k, Zero [<] x -> Zero [<] x[^]k.
intros.
elim k.
simpl in |- *.
apply pos_one.
intros.
simpl in |- *.
apply mult_resp_pos.
assumption.
assumption.
Qed.

Load "Opaque_algebra".

Lemma mult_resp_nonneg : forall x y : R, Zero [<=] x -> Zero [<=] y -> Zero [<=] x[*]y.
unfold leEq in |- *. intros x y H H0. intro H1. apply H0.
cut (x[*]y [#] Zero). intro H2.
cut (x [#] Zero). intro H3.
cut (y [#] Zero). intro H4.
elim (ap_imp_less _ _ _ H4); intro H5. auto.
elim (ap_imp_less _ _ _ H3); intro H6. elim (H H6).
elim (less_antisymmetric_unfolded _ _ _ H1 (mult_resp_pos _ _ _ H6 H5)).
apply cring_mult_ap_zero_op with x. auto.
apply cring_mult_ap_zero with y. auto.
apply less_imp_ap. auto.
Qed.

Load "Transparent_algebra".

Lemma nexp_resp_nonneg : forall (x : R) (k : nat), Zero [<=] x -> Zero [<=] x[^]k.
intros. induction  k as [| k Hreck]. intros.
astepr (One:R). apply less_leEq. apply pos_one.
astepr (x[^]k[*]x).
apply mult_resp_nonneg; auto.
Qed.

Lemma power_resp_leEq : forall (x y : R) k, Zero [<=] x -> x [<=] y -> x[^]k [<=] y[^]k.
intros. induction  k as [| k Hreck]; intros.
astepl (One:R).
astepr (One:R).
apply leEq_reflexive.
astepl (x[^]k[*]x).
astepr (y[^]k[*]y).
apply leEq_transitive with (x[^]k[*]y).
apply mult_resp_leEq_lft. auto.
apply nexp_resp_nonneg; auto.
apply mult_resp_leEq_rht. auto.
apply leEq_transitive with x; auto.
Qed.

Lemma nexp_resp_less : forall (x y : R) n, 1 <= n -> Zero [<=] x -> x [<] y -> x[^]n [<] y[^]n.
intros.
induction  n as [| n Hrecn].
elimtype False.
inversion H.
elim n.
simpl in |- *.
astepl x.
astepr y.
assumption.
intros.
change (x[^]S n0[*]x [<] y[^]S n0[*]y) in |- *.
apply mult_resp_less_both.
apply nexp_resp_nonneg.
assumption.
assumption.
assumption.
assumption.
Qed.

Lemma power_cancel_leEq : forall (x y : R) k, 0 < k -> Zero [<=] y -> x[^]k [<=] y[^]k -> x [<=] y.
unfold leEq in |- *. intros. intro. apply H1.
apply nexp_resp_less; auto.
Qed.

Lemma power_cancel_less : forall (x y : R) k, Zero [<=] y -> x[^]k [<] y[^]k -> x [<] y.
intros x y k H H0.
elim (zerop k); intro y0.
rewrite y0 in H0.
cut (One [<] (One:R)). intro H1.
elim (less_irreflexive_unfolded _ _ H1).
astepl (x[^]0). astepr (y[^]0). auto.
cut (x [<] y or y [<] x). intro H1.
elim H1; clear H1; intros H1. auto.
cut (x [<=] y). intro. elim (H2 H1).
apply power_cancel_leEq with k; auto.
apply less_leEq. auto.
apply ap_imp_less. apply un_op_strext_unfolded with (nexp_op (R:=R) k).
apply less_imp_ap. auto.
Qed.

Lemma nat_less_bin_nexp : forall p : nat, Snring R p [<] Two[^]S p.
intro n.
unfold Snring in |- *.
induction  n as [| n Hrecn].
simpl in |- *.
astepl (One:R).
astepr ((Zero:R) [+]One[+]One).
astepr ((One:R) [+]One).
astepr (Two:R).
apply one_less_two.

astepl (nring (R:=R) (S n) [+]One).
astepr ((Two:R)[^]S n[*]Two).
astepr ((Two:R)[^]S n[*]One[+]Two[^]S n[*]One).
apply plus_resp_less_both.
astepr ((Two:R)[^]S n).
exact Hrecn.

astepr ((Two:R)[^]S n).
astepl ((One:R)[^]S n).
apply nexp_resp_less.
intuition.

apply less_leEq.
apply pos_one.

apply one_less_two.
rational.
Qed.

Lemma Sum_resp_leEq : forall (f g : nat -> R) a b, a <= S b ->
 (forall i, a <= i -> i <= b -> f i [<=] g i) -> Sum a b f [<=] Sum a b g.
intros. induction  b as [| b Hrecb]; intros.
unfold Sum in |- *. unfold Sum1 in |- *.
generalize (toCle _ _ H); clear H; intro H.
inversion H.
astepl (Zero:R).
astepr (Zero:R).
apply leEq_reflexive.
inversion X.
simpl in |- *.
rstepl (f 0).
rstepr (g 0).
apply H0; auto. rewrite H1. auto.
elim (le_lt_eq_dec _ _ H); intro H1.
apply leEq_wdl with (Sum a b f[+]f (S b)).
apply leEq_wdr with (Sum a b g[+]g (S b)).
apply plus_resp_leEq_both.
apply Hrecb. auto with arith. auto.
apply H0. auto with arith. auto.
apply eq_symmetric_unfolded. apply Sum_last.
apply eq_symmetric_unfolded. apply Sum_last.
unfold Sum in |- *. unfold Sum1 in |- *.
rewrite H1.
simpl in |- *.
astepl (Zero:R).
astepr (Zero:R).
apply leEq_reflexive.
Qed.

Lemma Sumx_resp_leEq : forall n (f g : forall i, i < n -> R),
 (forall i H, f i H [<=] g i H) -> Sumx f [<=] Sumx g.
simple induction n.
intros; simpl in |- *; apply leEq_reflexive.
clear n; intros; simpl in |- *.
apply plus_resp_leEq_both.
apply H; intros; apply H0.
apply H0.
Qed.

Lemma Sum2_resp_leEq : forall m n, m <= S n -> forall f g : forall i, m <= i -> i <= n -> R,
 (forall i Hm Hn, f i Hm Hn [<=] g i Hm Hn) -> Sum2 f [<=] Sum2 g.
intros.
unfold Sum2 in |- *.
apply Sum_resp_leEq.
assumption.
intros.
elim (le_lt_dec m i); intro;
 [ simpl in |- * | elimtype False; apply (le_not_lt m i); auto with arith ].
elim (le_lt_dec i n); intro;
 [ simpl in |- * | elimtype False; apply (le_not_lt i n); auto with arith ].
apply H0.
Qed.

Lemma approach_zero : forall x : R, (forall e, Zero [<] e -> x [<] e) -> Not (Zero [<] x).
 intros.
 intro.
 cut (x [<] x [/]TwoNZ).
 change (Not (x [<] x [/]TwoNZ)) in |- *.
 apply less_antisymmetric_unfolded.
 apply plus_cancel_less with (z := [--](x [/]TwoNZ)).
 apply mult_cancel_less with (z := Two:R).
 apply pos_two.
 rstepl (Zero:R).
 rstepr x.
 assumption.
 apply X.
 apply pos_div_two.
 assumption.
Qed.

Lemma approach_zero_weak : forall x : R, (forall e, Zero [<] e -> x [<=] e) -> Not (Zero [<] x).
 intros.
 intro.
 cut (x [<=] x [/]TwoNZ).
 change (~ Not (x [/]TwoNZ [<] x)) in |- *.
 intro H1.
 apply H1.
 apply plus_cancel_less with (z := [--](x [/]TwoNZ)).
 apply mult_cancel_less with (z := Two:R).
 apply pos_two.
 rstepl (Zero:R).
 rstepr x.
 assumption.
 apply H.
 apply pos_div_two.
 assumption.
Qed.
End misc.

Lemma equal_less_leEq : forall a b x y : R,
 (a [<] b -> x [<=] y) -> (a [=] b -> x [<=] y) -> a [<=] b -> x [<=] y.
intros.
red in |- *.
apply CNot_Not_or with (a [<] b) (a [=] b); auto.
intro.
cut (a [=] b); intros.
2: apply leEq_imp_eq; auto.
auto.
intro; auto.
Qed.

End Properties_of_leEq.

(***********************************)
Section PosP_properties.
(***********************************)

(**
** Properties of positive numbers
%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)
Variable R : COrdField.

(* begin hide *)
Notation ZeroR := (Zero:R).
Notation OneR := (One:R).
(* end hide *)

Lemma mult_pos_imp : forall a b : R, Zero [<] a[*]b -> Zero [<] a and Zero [<] b or a [<] Zero and b [<] Zero.
generalize I; intro.
generalize I; intro.
generalize I; intro.
generalize I; intro.
generalize I; intro.
intros a b H4.
generalize (Greater_imp_ap _ _ _ H4); intro H5.
generalize (mult_cancel_ap_zero_lft _ _ _ H5); intro H6.
generalize (mult_cancel_ap_zero_rht _ _ _ H5); intro H7.
elim (ap_imp_less _ _ _ H6); intro H8.
right.
split.
assumption.
elim (ap_imp_less _ _ _ H7); intro.
assumption.
elimtype False.
elim (less_irreflexive_unfolded R Zero).
apply less_leEq_trans with (a[*]b).
assumption.
apply less_leEq.
apply inv_cancel_less.
astepl ZeroR.
astepr ([--]a[*]b).
apply mult_resp_pos.
astepl ([--]ZeroR).
apply inv_resp_less.
assumption.
assumption.
left.
split.
assumption.
elim (ap_imp_less _ _ _ H7); intro.
elimtype False.
elim (less_irreflexive_unfolded R Zero).
apply less_leEq_trans with (a[*]b).
assumption.
apply less_leEq.
apply inv_cancel_less.
astepl ZeroR.
astepr (a[*][--]b).
apply mult_resp_pos.
assumption.
astepl ([--]ZeroR).
apply inv_resp_less.
assumption.
assumption.
Qed.

Lemma plus_resp_pos_nonneg : forall x y : R, Zero [<] x -> Zero [<=] y -> Zero [<] x[+]y.
intros.
apply less_leEq_trans with x. auto.
astepl (x[+]Zero).
apply plus_resp_leEq_lft. auto.
Qed.

Lemma plus_resp_nonneg_pos : forall x y : R, Zero [<=] x -> Zero [<] y -> Zero [<] x[+]y.
intros.
astepr (y[+]x).
apply plus_resp_pos_nonneg; auto.
Qed.

Lemma pos_square : forall x : R, x [#] Zero -> Zero [<] x[^]2.
intros x H.
elim (ap_imp_less _ _ _ H); intro H1.
rstepr ([--]x[*][--]x).
cut (Zero [<] [--]x). intro.
apply mult_resp_pos; auto.
astepl ([--]ZeroR).
apply inv_resp_less. auto.
rstepr (x[*]x).
apply mult_resp_pos; auto.
Qed.

Lemma mult_cancel_pos_rht : forall x y : R, Zero [<] x[*]y -> Zero [<=] x -> Zero [<] y.
intros x y H H0.
elim (mult_pos_imp _ _ H); intro H1.
elim H1; auto.
elim H1; intros.
elim (H0 a).
Qed.

Lemma mult_cancel_pos_lft : forall x y : R, Zero [<] x[*]y -> Zero [<=] y -> Zero [<] x.
intros.
apply mult_cancel_pos_rht with y.
astepr (x[*]y).
auto. auto.
Qed.

Lemma pos_wd : forall x y : R, x [=] y -> Zero [<] y -> Zero [<] x.
intros.
astepr y.
auto.
Qed.

Lemma even_power_pos : forall n, even n -> forall x : R, x [#] Zero -> Zero [<] x[^]n.
intros.
elim (even_2n n H). intros m y.
replace n with (2 * m).
astepr ((x[^]2)[^]m).
apply nexp_resp_pos.
apply pos_square. auto.
rewrite y. unfold double in |- *. omega.
Qed.


Lemma odd_power_cancel_pos : forall n, odd n -> forall x : R, Zero [<] x[^]n -> Zero [<] x.
intros n H x H0.
induction  n as [| n Hrecn].
generalize (to_Codd _ H); intro H1.
inversion H1.
apply mult_cancel_pos_rht with (x[^]n).
astepr (x[^]S n). auto.
apply less_leEq; apply even_power_pos.
inversion H. auto.
apply un_op_strext_unfolded with (nexp_op (R:=R) (S n)).
cut (0 < S n). intro.
astepr ZeroR.
apply Greater_imp_ap. auto.
auto with arith.
Qed.

Lemma plus_resp_pos : forall x y : R, Zero [<] x -> Zero [<] y -> Zero [<] x[+]y.
intros.
apply plus_resp_pos_nonneg.
auto.
apply less_leEq. auto.
Qed.

Lemma pos_nring_S : forall n, ZeroR [<] nring (S n).
simple induction n; simpl in |- *; intros.
(* base *)
astepr OneR; apply pos_one.
(* step *)
apply less_leEq_trans with (nring (R:=R) n0[+]One).
assumption.
apply less_leEq.
apply less_plusOne.
Qed.

Lemma square_eq_pos : forall x a : R, Zero [<] a -> Zero [<] x -> x[^]2 [=] a[^]2 -> x [=] a.
intros.
elim (square_eq _ x a); intros; auto.
elimtype False.
apply less_irreflexive_unfolded with (x := ZeroR).
apply less_leEq_trans with x.
auto.
apply less_leEq.
astepl ([--]a); apply inv_cancel_less.
astepl ZeroR; astepr a; auto.
apply Greater_imp_ap; auto.
Qed.

Lemma square_eq_neg : forall x a : R, Zero [<] a -> x [<] Zero -> x[^]2 [=] a[^]2 -> x [=] [--]a.
intros.
elim (square_eq _ x a); intros; auto.
elimtype False.
apply less_irreflexive_unfolded with (x := ZeroR).
apply leEq_less_trans with x.
astepr a; apply less_leEq; auto.
auto.
apply Greater_imp_ap; auto.
Qed.

End PosP_properties.

Hint Resolve mult_resp_nonneg.

(**
** Properties of one over successor
%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)

Definition one_div_succ (R : COrdField) i : R := One[/] Snring R i[//]nringS_ap_zero _ i.

Implicit Arguments one_div_succ [R].

Section One_div_succ_properties.

Variable R : COrdField.

Lemma one_div_succ_resp_leEq : forall m n, m <= n -> one_div_succ (R:=R) n [<=] one_div_succ m.
unfold one_div_succ in |- *. unfold Snring in |- *. intros.
apply recip_resp_leEq.
apply pos_nring_S.
apply nring_leEq.
auto with arith.
Qed.

Lemma one_div_succ_pos : forall i, (Zero:R) [<] one_div_succ i.
intro.
unfold one_div_succ in |- *.
unfold Snring in |- *.
apply recip_resp_pos.
apply nring_pos.
auto with arith.
Qed.

Lemma one_div_succ_resp_less : forall i j, i < j -> one_div_succ j [<] one_div_succ (R:=R) i.
intros.
unfold one_div_succ in |- *. unfold Snring in |- *. intros.
apply recip_resp_less.
apply pos_nring_S.
apply nring_less.
auto with arith.
Qed.

End One_div_succ_properties.

(**
** Properties of [Half]
*)

Definition Half (R : COrdField) := (One:R) [/]TwoNZ.

Implicit Arguments Half [R].

Section Half_properties.

(**
%\begin{convention}%
Let [R] be an ordered field.
%\end{convention}%
*)

Variable R : COrdField.

Lemma half_1 : (Half:R) [*]Two [=] One.
unfold Half in |- *.
apply div_1.
Qed.
Hint Resolve half_1: algebra.

Lemma pos_half : (Zero:R) [<] Half.
apply mult_cancel_pos_lft with (Two:R).
apply (pos_wd R (Half[*]Two) One).
exact half_1.
apply pos_one.
apply less_leEq; apply pos_two.
Qed.

Lemma half_1' : forall x : R, x[*]Half[*]Two [=] x.
intros.
unfold Half in |- *.
rational.
Qed.

Lemma half_2 : (Half:R) [+]Half [=] One.
unfold Half in |- *.
rational.
Qed.

Lemma half_lt1 : (Half:R) [<] One.
astepr (Half[+] (Half:R)).
rstepl ((Half:R) [+]Zero).
apply plus_resp_less_lft.
exact pos_half.
exact half_2.
Qed.

Lemma half_3 : forall x : R, Zero [<] x -> Half[*]x [<] x.
intros.
astepr (One[*]x).
apply mult_resp_less; auto.
exact half_lt1.
Qed.

End Half_properties.
Hint Resolve half_1 half_1' half_2: algebra.
