(* $Id: Derivative.v,v 1.7 2004/04/23 10:00:58 lcf Exp $ *)

Require Export Continuity.

Section Definitions.

(** *Derivatives

We will now proceed toward the development of differential calculus.
To begin with, the main notion is that of derivative.

At this stage we will not define a notion of differentiable function,
mainly because the natural definition (that of being a function which
has some derivative) poses some technical problems; thus, we will
postpone that part of our work to a subsequent stage.

Derivative is a binary relation in the type of partial functions,
dependent (once again) on a compact interval with distinct
endpoints#. #%\footnote{%As before, we do not define pointwise
differentiability, mainly for coherence reasons.  See Bishop [1967]
for a discussion on the relative little interest of that concept.%}.%
The reason for requiring the endpoints to be apart is mainly to be
able to derive the usual properties of the derivative
relation---namely, that any two derivatives of the same function must
coincide.

%\begin{convention}% Let [a,b:IR] with [a [<] b] and denote by [I] the
interval [[a,b]].  Throughout this chapter, [F, F', G, G'] and [H]
will be partial functions with domains respectively [P, P', Q, Q'] and
[R].
%\end{convention}%
*)

Variables a b : IR.
Hypothesis Hab' : a [<] b.

(* begin hide *)
Let Hab := less_leEq _ _ _ Hab'.
Let I := Compact Hab.
(* end hide *)

Variable F : PartIR.
(* begin hide *)
Let P := Dom F.
(* end hide *)

Definition Derivative_I F' (P':=Dom F') := included I (Dom F) and included I (Dom F') and
 (forall e, Zero [<] e -> {d : IR | Zero [<] d | forall x y, I x -> I y -> forall Hx Hy Hx',
 AbsIR (x[-]y) [<=] d -> AbsIR (F y Hy[-]F x Hx[-]F' x Hx'[*] (y[-]x)) [<=] e[*]AbsIR (y[-]x)}).

End Definitions.

Implicit Arguments Derivative_I [a b].

Section Basic_Properties.

(** **Basic Properties
*)

Variables a b : IR.
Hypothesis Hab' : a [<] b.

(* begin hide *)
Let Hab := less_leEq _ _ _ Hab'.
Let I := Compact Hab.
(* end hide *)

(**
Like we did for equality, we begin by stating a lemma that makes proofs of derivation easier in practice.
*)

Lemma Derivative_I_char : forall F F' (P:=Dom F) (P':=Dom F'),
 included I (Dom F) -> included I (Dom F') ->
 (forall e,  Zero [<] e -> {d : IR | Zero [<] d | forall x y, I x -> I y -> forall Hx Hy Hx',
 AbsIR (x[-]y) [<=] d -> AbsIR (F y Hy[-]F x Hx[-]F' x Hx'[*] (y[-]x)) [<=] e[*]AbsIR (y[-]x)}) ->
 Derivative_I Hab' F F'.
(* begin hide *)
unfold Hab in |- *.
intros.
repeat (split; auto).
Qed.
(* end hide *)

(**
Derivative is a well defined relation; we will make this explicit for both arguments:
*)

Variables F G H : PartIR.

(* begin hide *)
Let P := Dom F.
Let Q := Dom G.
Let R := Dom H.
(* end hide *)

Lemma Derivative_I_wdl : Feq I F G ->
 Derivative_I Hab' F H -> Derivative_I Hab' G H.
intros H0 H1.
elim H0; intros incF H0'.
elim H0'; intros incG Heq.
elim H1; intros incF' H2.
elim H2; intros incH H3.
clear H0' H1 H2.
apply Derivative_I_char; auto.
intros e He.
elim (H3 e He); clear H3; intros d H1 H2.
exists d; auto.
intros x y H3 H4 Hx Hy Hx' H5.
astepl (AbsIR (F y (incF y H4) [-]F x (incF x H3) [-]H x Hx'[*] (y[-]x))); auto.
Qed.

Lemma Derivative_I_wdr : Feq I F G ->
 Derivative_I Hab' H F -> Derivative_I Hab' H G.
intros H0 H1.
elim H0; intros incF H0'.
elim H0'; intros incG Heq.
elim H1; intros incH H2.
elim H2; intros incF0 H3.
apply Derivative_I_char; auto.
intros e He.
elim (H3 e He); clear H3; intros d H3 H4.
exists d; auto.
intros x y H5 H6 Hx Hy Hx' H7.
astepl (AbsIR (H y Hy[-]H x Hx[-]F x (incF x H5) [*] (y[-]x))); auto.
Qed.

(* begin hide *)
Let Derivative_I_unique_lemma :
  forall x : IR,
  Compact Hab x ->
  forall d : IR,
  Zero [<] d -> {y : IR | AbsIR (x[-]y) [<=] d | Compact Hab y and y[-]x [#] Zero}.
intros x Hx d Hd.
elim (less_cotransitive_unfolded _ _ _ Hab' x); intro.
exists (Max a (x[-]d [/]TwoNZ)); auto.
eapply leEq_wdl.
2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
apply less_leEq; apply shift_minus_less'; apply shift_less_plus.
apply less_leEq_trans with (x[-]d [/]TwoNZ).
apply minus_resp_less_rht.
apply pos_div_two'; assumption.
simpl in |- *.
apply rht_leEq_Max.
apply shift_leEq_minus.
simpl in |- *.
astepl (Max a (x[-]d [/]TwoNZ)).
apply less_leEq.
apply Max_less; [ assumption | astepr (x[-]Zero) ].
apply minus_resp_less_rht; apply pos_div_two; assumption.
split.
split.
apply lft_leEq_Max.
apply Max_leEq.
apply less_leEq; assumption.
apply leEq_transitive with x.
apply shift_minus_leEq; apply shift_leEq_plus'; astepl ZeroR.
apply less_leEq; apply pos_div_two; assumption.
inversion_clear Hx; assumption.
apply less_imp_ap; apply shift_minus_less; astepr x; apply Max_less.
assumption.
apply shift_minus_less; apply shift_less_plus'; astepl ZeroR.
apply pos_div_two with (eps := d); assumption.
exists (Min b (x[+]d [/]TwoNZ)).
apply leEq_wdl with (Min b (x[+]d [/]TwoNZ) [-]x).
apply less_leEq.
apply shift_minus_less.
rstepr (x[+]d).
eapply leEq_less_trans.
apply Min_leEq_rht.
apply plus_resp_less_lft.
apply pos_div_two'; assumption.
apply eq_symmetric_unfolded.
eapply eq_transitive_unfolded; [ apply AbsIR_minus | apply AbsIR_eq_x ].
apply less_leEq; apply shift_less_minus; astepl x; apply less_Min.
assumption.
astepl (x[+]Zero); apply plus_resp_less_lft.
apply pos_div_two; assumption.
split.
split.
apply leEq_Min.
auto.
apply leEq_transitive with x.
inversion_clear Hx; auto.
astepl (x[+]ZeroR); apply plus_resp_leEq_lft; apply less_leEq;
 apply pos_div_two; assumption.
apply Min_leEq_lft.
apply Greater_imp_ap.
apply shift_less_minus; astepl x.
astepr (Min b (x[+]d [/]TwoNZ)); apply less_Min.
assumption.
astepl (x[+]Zero); apply plus_resp_less_lft; apply pos_div_two; assumption.
Qed.
(* end hide *)

(**
Derivative is unique.
*)

Lemma Derivative_I_unique : Derivative_I Hab' F G -> Derivative_I Hab' F H ->
 Feq I G H.
intros H0 H1.
elim H0; intros incF H2.
elim H2; intros incG H3.
elim H1; intros incF' H6.
elim H6; intros incH H4.
clear H0 H2 H6.
apply eq_imp_Feq; auto.
intros x H0 Hx Hx'.
apply cg_inv_unique_2.
apply AbsIR_approach_zero; intros e H2.
elim (H3 _ (pos_div_two _ _ H2)).
intros dg H6 H7.
elim (H4 _ (pos_div_two _ _ H2)).
clear H4 H3; intros dh H3 H4.
set (d := Min (Min dg dh) One) in *.
elim (Derivative_I_unique_lemma x H0 d).
intros y Hy' Hy''.
elim Hy''; clear Hy''; intros Hy'' Hy.
apply mult_cancel_leEq with (AbsIR (y[-]x)).
apply AbsIR_pos; assumption.
eapply leEq_wdl.
2: apply AbsIR_resp_mult.
set (Hxx := incF x H0) in *.
set (Hyy := incF y Hy'') in *.
apply
 leEq_wdl
  with
    (AbsIR
       (F y Hyy[-]F x Hxx[-]H x Hx'[*] (y[-]x) [-]
        (F y Hyy[-]F x Hxx[-]G x Hx[*] (y[-]x)))).
2: apply un_op_wd_unfolded; rational.
eapply leEq_transitive.
apply triangle_IR_minus.
rstepr (e [/]TwoNZ[*]AbsIR (y[-]x) [+]e [/]TwoNZ[*]AbsIR (y[-]x)).
apply plus_resp_leEq_both; [ apply H4 | apply H7 ]; try assumption;
 eapply leEq_transitive; try apply Hy'; unfold d in |- *;
 eapply leEq_transitive.
apply Min_leEq_lft.
apply Min_leEq_rht.
apply Min_leEq_lft.
apply Min_leEq_lft.
unfold d in |- *; repeat apply less_Min;
 [ assumption | assumption | apply pos_one ].
Qed.

(**
Finally, the set where we are considering the relation is included in the domain of both functions.
*)

Lemma derivative_imp_inc : Derivative_I Hab' F G -> included I P.
intro H0.
inversion_clear H0; assumption.
Qed.

Lemma derivative_imp_inc' : Derivative_I Hab' F G -> included I Q.
intro H0.
elim H0; intros H1 H2.
inversion_clear H2; assumption.
Qed.

(**
Any function that is or has a derivative is continuous.
*)

Variable Hab'' : a [<=] b.

Lemma deriv_imp_contin'_I : Derivative_I Hab' F G -> Continuous_I Hab'' G.
intro derF.
elim derF; intros incF H0.
elim H0; intros incG derivFG.
clear derF H0.
split.
Included.
intros e He.
elim (derivFG _ (pos_div_two _ _ He)); intros d posd Hde; clear derivFG.
exists d. auto. intros x y H0 H1 Hx Hy H2.
set (Hx' := incF _ H0) in *.
set (Hy' := incF _ H1) in *.
apply equal_less_leEq with (a := ZeroR) (b := AbsIR (y[-]x)); intros.
3: apply AbsIR_nonneg.
apply mult_cancel_leEq with (AbsIR (y[-]x)); auto.
rstepr (e [/]TwoNZ[*]AbsIR (y[-]x) [+]e [/]TwoNZ[*]AbsIR (y[-]x)).
eapply leEq_wdl.
2: apply AbsIR_resp_mult.
apply
 leEq_wdl
  with
    (AbsIR
       (F y Hy'[-]F x Hx'[-]G x Hx[*] (y[-]x) [+]
        (F x Hx'[-]F y Hy'[-]G y Hy[*] (x[-]y)))).
2: eapply eq_transitive_unfolded.
2: apply AbsIR_inv.
2: apply AbsIR_wd; rational.
eapply leEq_transitive.
apply triangle_IR.
apply plus_resp_leEq_both.
auto.
apply leEq_wdr with (e [/]TwoNZ[*]AbsIR (x[-]y)).
apply Hde; auto.
eapply leEq_wdl.
apply H2.
apply AbsIR_minus.
apply mult_wdr; apply AbsIR_minus.
apply leEq_wdl with ZeroR.
apply less_leEq; auto.
astepl (AbsIR Zero).
apply AbsIR_wd.
apply eq_symmetric_unfolded; apply x_minus_x.
apply pfwdef.
apply cg_inv_unique_2.
apply AbsIR_eq_zero.
apply eq_symmetric_unfolded; eapply eq_transitive_unfolded.
apply H3.
apply AbsIR_minus.
Qed.

Lemma deriv_imp_contin_I : Derivative_I Hab' F G -> Continuous_I Hab'' F.
intro derF.
elim derF; intros incF H2; elim H2; clear H2; intros incG deriv.
split; auto.
intros e He.
elim deriv with e; auto.
clear deriv; intros d posd Hd.
set (contG := deriv_imp_contin'_I derF) in *.
set (M := Norm_Funct contG) in *.
set
 (D :=
  Min d
    (Min (One [/]TwoNZ)
       (e[/] _[//]
        mult_resp_ap_zero _ _ _ (two_ap_zero IR) (max_one_ap_zero M)))) 
 in *.
exists D.
unfold D in |- *; repeat apply less_Min.
auto.
apply (pos_half IR).
apply div_resp_pos; auto.
apply shift_less_mult' with (two_ap_zero IR).
apply pos_two.
astepl ZeroR.
eapply less_leEq_trans.
2: apply rht_leEq_Max.
apply pos_one.
intros x y H0 H1 Hx Hy H2.
apply
 leEq_wdl
  with
    (AbsIR
       (F x Hx[-]F y Hy[-]G y (incG _ H1) [*] (x[-]y) [+]
        G y (incG _ H1) [*] (x[-]y))).
2: apply AbsIR_wd; rational.
eapply leEq_transitive.
apply triangle_IR.
rstepr (e [/]TwoNZ[+]e [/]TwoNZ).
apply plus_resp_leEq_both.
apply leEq_transitive with (e[*]AbsIR (x[-]y)).
apply Hd; auto.
apply leEq_transitive with D.
eapply leEq_wdl; [ apply H2 | apply AbsIR_minus ].
unfold D in |- *; apply Min_leEq_lft.
rstepr (e[*]One [/]TwoNZ).
apply mult_resp_leEq_lft.
apply leEq_transitive with D; auto.
unfold D in |- *; eapply leEq_transitive;
 [ apply Min_leEq_rht | apply Min_leEq_lft ].
apply less_leEq; auto.
eapply leEq_wdl.
2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
apply leEq_transitive with (Max M One[*]AbsIR (x[-]y)).
apply mult_resp_leEq_rht.
2: apply AbsIR_nonneg.
eapply leEq_transitive.
2: apply lft_leEq_Max.
unfold M in |- *; apply norm_bnd_AbsIR; auto.
apply shift_mult_leEq' with (max_one_ap_zero M).
eapply less_leEq_trans; [ apply pos_one | apply rht_leEq_Max ].
eapply leEq_wdr.
eapply leEq_transitive.
apply H2.
unfold D in |- *.
eapply leEq_transitive; apply Min_leEq_rht.
rational.
Qed.

End Basic_Properties.

(**
If [G] is the derivative of [F] in a given interval, then [G] is also the derivative of [F] in any smaller interval.
*)

Lemma included_imp_deriv : forall a b Hab c d Hcd F F',
 included (compact c d (less_leEq _ _ _ Hcd)) (compact a b (less_leEq _ _ _ Hab)) ->
 Derivative_I Hab F F' -> Derivative_I Hcd F F'.
intros a b Hab c d Hcd F F' H H0.
elim H0; clear H0; intros incF H0.
elim H0; clear H0; intros incF' H0.
apply Derivative_I_char.
apply included_trans with (Compact (less_leEq _ _ _ Hab)); auto.
apply included_trans with (Compact (less_leEq _ _ _ Hab)); auto.
intros e He; elim (H0 e He); intros e' He'.
exists e'; auto.
Qed.
