(* $Id$ *)

Require Export IVT.

(** * Roots of polynomials of odd degree *)

Section CPoly_Big.

(** ** Monic polys are positive near infinity
%\begin{convention}%
Let [R] be an ordered field.
%\end{convention}%
*)

Variable R : COrdField.

Lemma Cbigger : forall x y : R, {z : R | x[<=]z | y[<=]z}.
intros.
elim (cotrans_less_unfolded _ x (x[+]One) (less_plusOne _ _) y); intro.
exists (y[+]One); apply less_leEq.
apply less_leEq_trans with y. auto. apply less_leEq; apply less_plusOne.
apply less_plusOne.
exists (x[+]One); apply less_leEq.
apply less_plusOne.
auto.
Qed.

Lemma Ccpoly_big :
 forall (p : cpoly R) (n : nat),
 0 < n ->
 monic n p -> forall Y : R, {X : R | forall x : R, X[<=]x -> Y[<=]p ! x}.
intro. elim p.
unfold monic in |- *. simpl in |- *. intros. elim H0. intros H1 H2.
cut (Zero[~=](One:R)). intro. elim (H3 H1).
apply ap_imp_neq. apply ap_symmetric_unfolded. apply ring_non_triv.
intros c q. intros H n H0 H1 Y. 
elim (O_or_S n); intro y. elim y. intro m. intro y0.
rewrite <- y0 in H1.
elim (zerop m); intro y1. simpl in |- *.
exists (Y[-]c). intros.
rewrite y1 in H1.
apply shift_leEq_plus'.
cut (q ! x[=]One). intro.
AStepr (x[*]One). AStepr x. auto.
apply monic_one with c. auto.
cut (monic m q). intro H2.
elim (Cbigger Zero (Y[-]c)). intro Y'. intros H3 H4.
elim (H m y1 H2 Y'). intro X'. intro H5.
simpl in |- *.
elim (Cbigger One X'). intro X. intros H6 H7.
exists X. intros.
apply shift_leEq_plus'.
apply leEq_transitive with (One[*]Y').
AStepr Y'. auto.
apply mult_resp_leEq_both; auto.
apply less_leEq. apply pos_one.
apply leEq_transitive with X; auto.
change (Y'[<=]q ! x) in |- *.
apply H5.
apply leEq_transitive with X; auto.
apply monic_cpoly_linear with c; auto.
rewrite <- y in H0.
elim (lt_irrefl _ H0).
Qed.

Lemma cpoly_pos :
 forall (p : cpoly R) (n : nat),
 0 < n -> monic n p -> {x : R | Zero[<=]p ! x}.
intros.
elim (Ccpoly_big _ _ H H0 Zero). intros x H1.
exists (x[+]One).
apply H1. apply less_leEq. apply less_plusOne.
Qed.

Lemma Ccpoly_pos' :
 forall (p : cpoly R) (a : R) (n : nat),
 0 < n -> monic n p -> {x : R | a[<]x | Zero[<=]p ! x}.
intros.
elim (Ccpoly_big _ _ H H0 Zero). intro x'. intro H1.
elim (Cbigger (a[+]One) x'). intro x. intros.
exists x; auto.
apply less_leEq_trans with (a[+]One).
apply less_plusOne. auto.
Qed.

End CPoly_Big.

Section Flip_Poly.
(** **Flipping a polynomial
%\begin{convention}%
Let [R] be a ring.
%\end{convention}%
*)

Variable R : CRing.

Fixpoint flip (p : cpoly R) : cpoly R :=
  match p with
  | cpoly_zero => cpoly_zero _
  | cpoly_linear c q => cpoly_inv _ (cpoly_linear _ c (flip q))
  end.

Lemma flip_poly :
 forall (p : cpoly R) (x : R), (flip p) ! x[=][--]p ! ([--]x).
intro p. elim p.
intros. simpl in |- *. Algebra.
intros c q. intros.
change
  ([--]c[+]x[*](cpoly_inv _ (flip q)) ! x[=][--](c[+][--]x[*]q ! ([--]x)))
 in |- *.
AStepl ([--]c[+]x[*][--](flip q) ! x).
AStepl ([--]c[+]x[*][--][--]q ! ([--]x)).
rational.
Qed.

Lemma flip_coefficient :
 forall (p : cpoly R) (i : nat),
 nth_coeff i (flip p)[=][--]([--]One[^]i)[*]nth_coeff i p.
intro p. elim p.
simpl in |- *. Algebra.
intros c q. intros.
elim i. simpl in |- *. rational.
intros. simpl in |- *.
AStepl ([--](nth_coeff n (flip q))).
AStepl ([--]([--]([--]One[^]n)[*]nth_coeff n q)).
simpl in |- *. rational.
Qed.

Hint Resolve flip_coefficient: algebra.

Lemma flip_odd :
 forall (p : cpoly R) (n : nat), odd n -> monic n p -> monic n (flip p).
unfold monic in |- *. unfold degree_le in |- *.
intros.
elim H0. clear H0. intros.
split.
AStepl ([--]([--]One[^]n)[*]nth_coeff n p).
AStepl ([--][--](One[^]n)[*]nth_coeff n p).
AStepl (One[^]n[*]nth_coeff n p).
AStepl (One[*]nth_coeff n p).
Step_final (One[*](One:R)).
intros.
AStepl ([--]([--]One[^]m)[*]nth_coeff m p).
Step_final ([--]([--]One[^]m)[*](Zero:R)).
Qed.

End Flip_Poly.

Hint Resolve flip_poly: algebra.


Section OddPoly_Signs.
(** ** Sign of a polynomial of odd degree
%\begin{convention}%
Let [R] be an ordered field.
%\end{convention}%
*)

Variable R : COrdField.

Lemma oddpoly_pos :
 forall (p : cpoly R) (n : nat),
 odd n -> monic n p -> {x : R | Zero[<=]p ! x}.
intros.
apply cpoly_pos with n; auto.
elim H. intros. auto with arith.
Qed.

Lemma oddpoly_pos' :
 forall (p : cpoly R) (a : R) (n : nat),
 odd n -> monic n p -> {x : R | a[<]x | Zero[<=]p ! x}.
intros.
elim (Ccpoly_pos' _ p a n). intros x H1 H2.
exists x; assumption.
elim H; auto with arith.
assumption.
Qed.

Lemma oddpoly_neg :
 forall (p : cpoly R) (n : nat),
 odd n -> monic n p -> {x : R | p ! x[<=]Zero}.
intros.
elim (oddpoly_pos _ _ H (flip_odd _ _ _ H H0)). intro x. intros.
exists ([--]x).
AStepl ([--][--]p ! ([--]x)). AStepr ([--](Zero:R)).
apply inv_resp_leEq.
AStepr (flip _ p) ! x. auto.
Qed.

End OddPoly_Signs.


Section Poly_Norm.

(** ** The norm of a polynomial
%\begin{convention}%
Let [R] be a field, and [RX] the polynomials over this field.
%\end{convention}%
*)

Variable R : CField.
(* begin hide *)
Let RX := cpoly_cring R.
(* end hide *)

Lemma poly_norm_aux :
 forall (p : RX) (n : nat) (H : degree n p), nth_coeff n p[#]Zero.
unfold degree in |- *. intros.
elim H. auto.
Qed.

Definition poly_norm (p : RX) (n : nat) (H : degree n p) :=
  _C_ (One[/] nth_coeff n p[//]poly_norm_aux p n H)[*]p.

Lemma poly_norm_monic :
 forall (p : RX) (n : nat) (H : degree n p), monic n (poly_norm p n H).
unfold poly_norm in |- *. unfold monic in |- *. unfold degree in |- *. unfold degree_le in |- *. intros.
elim H. intros H0 H1. 
split.
Step_final
 ((One[/] nth_coeff n p[//]poly_norm_aux p n (CAnd_intro _ _ H0 H1))[*]
  nth_coeff n p).
intros.
AStepl
 ((One[/] nth_coeff n p[//]poly_norm_aux p n (CAnd_intro _ _ H0 H1))[*]
  nth_coeff m p).
Step_final ((One[/] nth_coeff n p[//]poly_norm_aux p n H)[*]Zero).
Qed.

Lemma poly_norm_apply :
 forall (p : RX) (n : nat) (H : degree n p) (x : R),
 (poly_norm p n H) ! x[=]Zero -> p ! x[=]Zero.
unfold poly_norm in |- *. intros.
apply mult_cancel_lft with (One[/] nth_coeff n p[//]poly_norm_aux p n H).
apply div_resp_ap_zero_rev. apply ring_non_triv.
AStepl ((_C_ (One[/] nth_coeff n p[//]poly_norm_aux p n H)) ! x[*]p ! x).
AStepl (_C_ (One[/] nth_coeff n p[//]poly_norm_aux p n H)[*]p) ! x.
Step_final (Zero:R).
Qed.

End Poly_Norm.


Section OddPoly_Root.
(** ** Roots of polynomials of odd degree *)

Lemma oddpoly_root' :
 forall (f : cpoly IR) (n : nat),
 odd n -> monic n f -> {x : IR | f ! x[=]Zero}.
intros.
elim (oddpoly_neg _ f n); auto. intro a. intro H1.
elim (oddpoly_pos' _ f a n); auto. intro b. intros H2 H3.
cut {x : IR | a[<=]x /\ x[<=]b /\ f ! x[=]Zero}.
intro H4.
elim H4. clear H4. intros x H4.
elim H4. clear H4. intros H4 H5. 
elim H5. clear H5. intros.
exists x. auto.
apply Civt_poly; auto. 
apply monic_apzero with n; auto.
Qed.

Lemma oddpoly_root :
 forall (f : cpoly IR) (n : nat),
 odd n -> degree n f -> {x : IR | f ! x[=]Zero}.
intros f n H H0.
elim (oddpoly_root' (poly_norm _ f n H0) n); auto.
intros. exists x.
apply poly_norm_apply with n H0; auto.
apply poly_norm_monic; auto.
Qed.

Lemma realpolyn_oddhaszero :
 forall f : cpoly_cring IR, odd_cpoly _ f -> {x : IR | f ! x[=]Zero}.
unfold odd_cpoly in |- *.
intros f H.
elim H. clear H. intro n. intros H H0.
cut (odd n).
intro.
elim (oddpoly_root f n H1 H0). intros. exists x. auto.
apply Codd_to.
assumption.
Qed.

End OddPoly_Root.