(* $Id$ *)

(**
* Continuity of polynomials
*)

Require Export RealFuncts.

Opaque IR.

Lemma mult_op_contin :
 forall f g h : CSetoid_un_op IR,
 contin f -> contin g -> (forall x : IR, f x[*]g x[=]h x) -> contin h.
intros f g h f_contin g_contin f_g_h.
unfold contin in f_contin.
unfold continAt in f_contin.
unfold funLim in f_contin.
unfold contin in g_contin.
unfold continAt in g_contin.
unfold funLim in g_contin.
unfold contin in |- *. unfold continAt in |- *. unfold funLim in |- *.
intros x e H.
elim (mult_contin _ (f x) (g x) e H). intro b. intros H0 H1.
elim H1. clear H1. intro c. intros H1 H2.
elim (f_contin x b H0). clear f_contin. intro d'. intros H3 H4.
elim (g_contin x c H1). clear g_contin. intro d''. intros H5 H6.
exists (Min d' d'').
apply less_Min; auto. intro x'. intros.
AStepr (f x[*]g x[-]f x'[*]g x').
apply H2.
apply H4. apply AbsSmall_leEq_trans with (Min d' d''); auto. apply Min_leEq_lft.
apply H6. apply AbsSmall_leEq_trans with (Min d' d''); auto. apply Min_leEq_rht.
Qed.

Lemma plus_contin :
 forall (R : COrdField) (x y e : R),
 Zero[<]e ->
 {c : R | Zero[<]c |
 {d : R | Zero[<]d |
 forall x' y' : R,
 AbsSmall c (x[-]x') -> AbsSmall d (y[-]y') -> AbsSmall e (x[+]y[-](x'[+]y'))}}.
intros.
cut (Zero[<]e [/]TwoNZ). intro.
exists (e [/]TwoNZ). auto.
exists (e [/]TwoNZ). auto.
intros.
apply AbsSmall_wd_rht_unfolded with (x[-]x'[+](y[-]y')).
apply AbsSmall_eps_div_two; auto.
rational.
apply div_resp_pos. apply pos_two. auto.
Qed.

Lemma plus_op_contin :
 forall f g h : CSetoid_un_op IR,
 contin f -> contin g -> (forall x : IR, f x[+]g x[=]h x) -> contin h.
intros f g h f_contin g_contin f_g_h.
unfold contin in f_contin.
unfold continAt in f_contin.
unfold funLim in f_contin.
unfold contin in g_contin.
unfold continAt in g_contin.
unfold funLim in g_contin.
unfold contin in |- *. unfold continAt in |- *. unfold funLim in |- *.
intros x e H.
elim (plus_contin _ (f x) (g x) e H). intro b. intros H0 H1.
elim H1. clear H1. intro c. intros H1 H2.
elim (f_contin x b H0). clear f_contin. intro d'. intros H3 H4.
elim (g_contin x c H1). clear g_contin. intro d''. intros H5 H6.
exists (Min d' d'').
apply less_Min; auto. intro x'. intros H10.
AStepr (f x[+]g x[-](f x'[+]g x')).
apply H2.
apply H4. apply AbsSmall_leEq_trans with (Min d' d''); auto. apply Min_leEq_lft.
apply H6. apply AbsSmall_leEq_trans with (Min d' d''); auto. apply Min_leEq_rht.
Qed.

Lemma linear_op_contin :
 forall (f g : CSetoid_un_op IR) (a : IR),
 contin f -> (forall x : IR, x[*]f x[+]a[=]g x) -> contin g.
intros f g a f_contin f_g.
unfold contin in f_contin.
unfold continAt in f_contin.
unfold funLim in f_contin.
unfold contin in |- *. unfold continAt in |- *. unfold funLim in |- *.
intros.
elim (mult_contin _ x (f x) e). intro d'. intros H0 H1.
elim H1. clear H1. intro c. intros H1 H2.
elim (f_contin x c). clear f_contin. intro d''. intros H3 H4.
exists (Min d' d''). 
apply less_Min; auto. intro x'. intros H8.
AStepr (x[*]f x[+]a[-](x'[*]f x'[+]a)).
RStepr (x[*]f x[-]x'[*]f x').
apply H2. clear H2.
apply AbsSmall_leEq_trans with (Min d' d''); auto. apply Min_leEq_lft.
apply H4. clear H4.
apply AbsSmall_leEq_trans with (Min d' d''); auto. apply Min_leEq_rht.
auto. auto. 
Qed.

Lemma cpoly_op_contin : forall g : cpoly IR, contin (cpoly_csetoid_op _ g).
intro g.
elim g.
unfold contin in |- *. unfold continAt in |- *. unfold funLim in |- *.
intros.
exists OneR. apply pos_one.
intros.
simpl in |- *.
unfold AbsSmall in |- *.
split; apply less_leEq.
RStepr ([--]ZeroR). apply inv_resp_less. auto.
AStepl ZeroR. auto.
intros a f. intros.
apply linear_op_contin with (cpoly_csetoid_op _ f) a. auto.
intros. simpl in |- *. rational.
Qed.
