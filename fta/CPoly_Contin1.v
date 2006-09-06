
Require Export CC_Props.

(** * Continuity of complex polynomials
*)

Section Mult_CC_Continuous.

Lemma mult_absCC : forall (x y : CC) (X Y : IR),
 AbsCC x [<=] X -> AbsCC y [<=] Y -> AbsCC (x[*]y) [<=] X[*]Y.
intros.
astepl (AbsCC x[*]AbsCC y).
apply mult_resp_leEq_both.
apply AbsCC_nonneg. apply AbsCC_nonneg. auto. auto.
Qed.

Lemma estimate_absCC : forall x : CC, {X : IR | Zero [<] X | AbsCC x [<=] X}.
intros.
exists (AbsCC x[+]One).
astepl (Zero[+]ZeroR).
apply plus_resp_leEq_less. apply AbsCC_nonneg. apply pos_one.
astepl (AbsCC x[+]Zero).
apply less_leEq.
apply plus_resp_less_lft. apply pos_one.
Qed.

Lemma mult_CC_contin : forall (x y : CC) (e : IR),
 Zero [<] e -> {c : IR | Zero [<] c | {d : IR | Zero [<] d | forall x' y',
 AbsCC (x[-]x') [<=] c -> AbsCC (y[-]y') [<=] d -> AbsCC (x[*]y[-]x'[*]y') [<=] e}}.
do 3 intro. intro H.
cut (Zero [<] e [/]TwoNZ). intro H0.
elim (estimate_absCC x). intro X. intros H1 H2.
elim (estimate_absCC y). intro Y. intros H3 H4.
cut (Y[#]Zero). intro H5.
exists (e [/]TwoNZ[/] Y[//]H5).
apply div_resp_pos. auto. auto.
cut (Zero [<] X[+](e [/]TwoNZ[/] Y[//]H5)). intro.
cut (X[+](e [/]TwoNZ[/] Y[//]H5)[#]Zero). intro H7.
exists (e [/]TwoNZ[/] X[+](e [/]TwoNZ[/] Y[//]H5)[//]H7).
apply div_resp_pos. auto. auto.
intros.
apply leEq_wdl with (AbsCC ((x[-]x')[*]y[+]x'[*](y[-]y'))).
apply leEq_transitive with (AbsCC ((x[-]x')[*]y)[+]AbsCC (x'[*](y[-]y'))).
apply triangle.
rstepr (e [/]TwoNZ[+]e [/]TwoNZ).
apply plus_resp_leEq_both.
apply leEq_wdr with ((e [/]TwoNZ[/] Y[//]H5)[*]Y).
apply mult_absCC; auto.
rational.
apply
 leEq_wdr
  with
    ((X[+](e [/]TwoNZ[/] Y[//]H5))[*]
     (e [/]TwoNZ[/] X[+](e [/]TwoNZ[/] Y[//]H5)[//]H7)).
apply mult_absCC; auto.
apply leEq_wdl with (AbsCC (x[+](x'[-]x))).
apply leEq_transitive with (AbsCC x[+]AbsCC (x'[-]x)).
apply triangle.
apply plus_resp_leEq_both. auto.
astepl (AbsCC [--](x'[-]x)).
apply leEq_wdl with (AbsCC (x[-]x')). auto.
apply AbsCC_wd. rational.
apply AbsCC_wd. rational.
rational.
apply AbsCC_wd. rational.
apply Greater_imp_ap. auto.
apply plus_resp_pos; auto.
apply div_resp_pos; auto.
apply Greater_imp_ap. auto.
apply pos_div_two. auto.
Qed.

End Mult_CC_Continuous.


Section CPoly_CC_Continuous.

(**
%\begin{convention}% Let [g] be a polynomial over the complex numbers.
%\end{convention}%
*)

Variable g : CCX.

Lemma cpoly_CC_contin : forall (x : CC) (e : IR), Zero [<] e ->
 {d : IR | Zero [<] d | forall x', AbsCC (x[-]x') [<=] d -> AbsCC (g ! x[-]g ! x') [<=] e}.
elim g.
intros.
exists OneR. intros. apply pos_one. intros.
apply leEq_wdl with ZeroR. apply less_leEq. auto.
cut (Zero [=] AbsCC (Zero[-]Zero)). auto.
Step_final (AbsCC Zero).
intros a f. intro H. do 2 intro. intro H0.
elim (mult_CC_contin x f ! x e H0). intro d1. intros H1 H2.
elim H2. clear H2. intro c. intros H2 H3.
elim (H x c H2). clear H. intro d2. intros H H4.
exists (Min d1 d2). apply less_Min; auto. intros.
simpl in |- *.
cut (AbsCC (a[+]x[*]f ! x[-](a[+]x'[*]f ! x')) [<=] e). auto.
apply leEq_wdl with (AbsCC (x[*]f ! x[-]x'[*]f ! x')).
apply H3. clear H3.
apply leEq_transitive with (Min d1 d2); auto. apply Min_leEq_lft.
apply H4. clear H4.
apply leEq_transitive with (Min d1 d2); auto. apply Min_leEq_rht.
apply AbsCC_wd.
rational.
Qed.

Lemma contin_polyCC : CCcontin (fun x => g ! x).
unfold CCcontin in |- *. unfold CCcontinAt in |- *. unfold CCfunLim in |- *.
intros.
elim (cpoly_CC_contin x e); auto.
intro d. intros H0 H1.
exists d. auto. intros.
apply H1; auto.
Qed.

End CPoly_CC_Continuous.
