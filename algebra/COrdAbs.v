Require Export COrdFields2.

(**
** Properties of [AbsSmall]
*)

(* Begin_SpecReals *)

Definition AbsSmall (R : COrdField) (e x : R) : Prop := [--]e[<=]x /\ x[<=]e.

Implicit Arguments AbsSmall [R].

(* End_SpecReals *)

Section AbsSmall_properties.

(**
%\begin{convention}%
Let [R] be an ordered field.
%\end{convention}%
*)
Variable R : COrdField.

Lemma AbsSmall_wd_rht : rel_well_def_rht R (AbsSmall (R:=R)).
unfold rel_well_def_rht in |- *.
unfold AbsSmall in |- *.
intros.
elim H; intros.
split.
AStepr y.
assumption.

AStepl y.
assumption.
Qed.

Lemma AbsSmall_wd_rht_unfolded :
 forall x y z : R, AbsSmall x y -> y[=]z -> AbsSmall x z.
Proof AbsSmall_wd_rht.

Lemma AbsSmall_wd_lft : rel_well_def_lft R (AbsSmall (R:=R)).
unfold rel_well_def_lft in |- *.
unfold AbsSmall in |- *.
intros.
elim H; intros.
split.
AStepl ([--]x).
assumption.

AStepr x.
assumption.
Qed.

Lemma AbsSmall_wd_lft_unfolded :
 forall x y z : R, AbsSmall x y -> x[=]z -> AbsSmall z y.
Proof AbsSmall_wd_lft.

Declare Left Step AbsSmall_wd_lft_unfolded.
Declare Right Step AbsSmall_wd_rht_unfolded.

(* begin hide *)
Notation ZeroR := (Zero:R).
(* end hide *)

Lemma AbsSmall_leEq_trans :
 forall e1 e2 d : R, e1[<=]e2 -> AbsSmall e1 d -> AbsSmall e2 d.
unfold AbsSmall in |- *.
intros.
elim H0; intros.
split.
apply leEq_transitive with ([--]e1).
apply inv_resp_leEq.
assumption.

assumption.

apply leEq_transitive with e1.
assumption.

assumption.
Qed.

Lemma zero_AbsSmall : forall e : R, Zero[<=]e -> AbsSmall e Zero.
intros.
unfold AbsSmall in |- *.
split.
AStepr ([--]ZeroR).
apply inv_resp_leEq.
assumption.
assumption.
Qed.

Lemma AbsSmall_trans :
 forall e1 e2 d : R, e1[<]e2 -> AbsSmall e1 d -> AbsSmall e2 d.
intros.
apply AbsSmall_leEq_trans with e1.
apply less_leEq.
assumption.
assumption.
Qed.

Lemma leEq_imp_AbsSmall : forall e d : R, Zero[<=]e -> e[<=]d -> AbsSmall d e.
intros.
unfold AbsSmall in |- *.
split; try assumption.
apply leEq_transitive with ZeroR; try assumption.
AStepr ([--]ZeroR).
apply inv_resp_leEq.
apply leEq_transitive with e; assumption.
Qed.

Lemma inv_resp_AbsSmall : forall x y : R, AbsSmall x y -> AbsSmall x [--]y.
unfold AbsSmall in |- *.
intros.
elim H; intros.
split.
apply inv_resp_leEq.
assumption.
AStepr ([--][--]x).
apply inv_resp_leEq.
assumption.
Qed.

Lemma AbsSmall_minus :
 forall e x1 x2 : R, AbsSmall e (x1[-]x2) -> AbsSmall e (x2[-]x1).
intros.
RStepr ([--](x1[-]x2)).
apply inv_resp_AbsSmall.
assumption.
Qed.

Lemma AbsSmall_plus :
 forall e1 e2 x1 x2 : R,
 AbsSmall e1 x1 -> AbsSmall e2 x2 -> AbsSmall (e1[+]e2) (x1[+]x2).
unfold AbsSmall in |- *.
intros.
elim H; intros.
elim H0; intros.
split.
RStepl ([--]e1[+][--]e2).
apply plus_resp_leEq_both; assumption.
apply plus_resp_leEq_both; assumption.
Qed.

Lemma AbsSmall_eps_div_two :
 forall e x1 x2 : R,
 AbsSmall (e [/]TwoNZ) x1 -> AbsSmall (e [/]TwoNZ) x2 -> AbsSmall e (x1[+]x2).
intros.
RStepl (e [/]TwoNZ[+]e [/]TwoNZ).
apply AbsSmall_plus.
assumption.
assumption.
Qed.

Lemma AbsSmall_x_plus_delta :
 forall x eps delta : R,
 Zero[<=]eps ->
 Zero[<=]delta -> delta[<=]eps -> AbsSmall eps (x[-](x[+]delta)).
intros.
(* AStepr ((x[-]x)[-]delta).
AStepr (Zero[-]delta). *)
RStepr ([--]delta).
apply inv_resp_AbsSmall.
apply leEq_imp_AbsSmall.
assumption.
assumption.
Qed.

Lemma AbsSmall_x_minus_delta :
 forall x eps delta : R,
 Zero[<=]eps ->
 Zero[<=]delta -> delta[<=]eps -> AbsSmall eps (x[-](x[-]delta)).
intros.
(* AStepr ((x[-]x)[+]delta).
   AStepr (Zero[+]delta). *)
RStepr delta.
apply leEq_imp_AbsSmall.
assumption.
assumption.
Qed.

Lemma AbsSmall_x_plus_eps_div2 :
 forall x eps : R, Zero[<=]eps -> AbsSmall eps (x[-](x[+]eps [/]TwoNZ)).
intros.
apply AbsSmall_x_plus_delta.
assumption.

apply nonneg_div_two.
assumption.

apply nonneg_div_two'.
assumption.
Qed.

Lemma AbsSmall_x_minus_eps_div2 :
 forall x eps : R, Zero[<=]eps -> AbsSmall eps (x[-](x[-]eps [/]TwoNZ)).
intros.
apply AbsSmall_x_minus_delta.
assumption.

apply nonneg_div_two.
assumption.

apply eps_div_leEq_eps.
assumption.

apply less_leEq.
apply one_less_two.
Qed.

Lemma AbsSmall_intermediate :
 forall x y z eps : R,
 x[<=]y -> y[<=]z -> AbsSmall eps (z[-]x) -> AbsSmall eps (z[-]y).
intros.
apply leEq_imp_AbsSmall.
apply shift_leEq_minus; AStepl y.
assumption.
unfold AbsSmall in H1.
elim H1; intros.
apply leEq_transitive with (z[-]x); try assumption.
apply minus_resp_leEq_rht.
assumption.
Qed.

Lemma AbsSmall_eps_div2 :
 forall eps : R, Zero[<=]eps -> AbsSmall eps (eps [/]TwoNZ).
intros.
apply leEq_imp_AbsSmall.
apply nonneg_div_two.
assumption.

apply eps_div_leEq_eps.
assumption.

apply less_leEq.
apply one_less_two.
Qed.

Lemma AbsSmall_nonneg : forall e x : R, AbsSmall e x -> Zero[<=]e.
 unfold AbsSmall in |- *.
 intros.
 elim H.
 intros.
 cut ([--]e[<=]e).
 intros.
 apply mult_cancel_leEq with (z := Two:R).
 apply pos_two.
 apply plus_cancel_leEq_rht with (z := [--]e).
 RStepl ([--]e).
 RStepr e.
 assumption.
 apply leEq_transitive with (y := x).
 assumption.
 assumption.
Qed.


Lemma AbsSmall_mult :
 forall e1 e2 x1 x2 : R,
 AbsSmall e1 x1 -> AbsSmall e2 x2 -> AbsSmall (Three[*](e1[*]e2)) (x1[*]x2).
 unfold AbsSmall in |- *.
 intros.
 elim H.
 intros.
 elim H0.
 intros.
 cut (Zero[<=]e1).
 intro.
 cut (Zero[<=]e2).
 intro.
 split.

 apply plus_cancel_leEq_rht with (z := Three[*](e1[*]e2)).
 RStepl ZeroR.
 RStepr (x1[*]x2[+]e1[*]e2[+]e1[*]e2[+]e1[*]e2).
 apply leEq_transitive with (y := x1[*]x2[+]e1[*]e2[+]x1[*]e2[+]e1[*]x2).
 RStepr ((e1[+]x1)[*](e2[+]x2)).
 apply mult_resp_nonneg.
 apply plus_cancel_leEq_rht with (z := [--]x1).
 RStepl ([--]x1).
 RStepr ([--][--]e1).
 apply inv_resp_leEq.
 assumption.

 apply plus_cancel_leEq_rht with (z := [--]x2).
 RStepl ([--]x2).
 RStepr ([--][--]e2).
 apply inv_resp_leEq.
 assumption.

 RStepl (x1[*]x2[+]e1[*]e2[+](x1[*]e2[+]e1[*]x2)).
 RStepr (x1[*]x2[+]e1[*]e2[+](e1[*]e2[+]e1[*]e2)).
 apply plus_resp_leEq_lft.
 apply plus_resp_leEq_both.
 apply mult_resp_leEq_rht.
 assumption.
 assumption.
 apply mult_resp_leEq_lft.
 assumption.
 assumption.

 apply plus_cancel_leEq_rht with (z := [--](x1[*]x2)).
 RStepl ZeroR.
 RStepr ([--](x1[*]x2)[+]e1[*]e2[+](e1[*]e2[+]e1[*]e2)).
 apply
  leEq_transitive with (y := [--](x1[*]x2)[+]e1[*]e2[+](x1[*]e2[-]e1[*]x2)).
 RStepr ((e1[+]x1)[*](e2[-]x2)).
 apply mult_resp_nonneg.
 apply plus_cancel_leEq_rht with (z := [--]x1).
 RStepl ([--]x1).
 RStepr ([--][--]e1).
 apply inv_resp_leEq.
 assumption.

 apply plus_cancel_leEq_rht with (z := x2).
 RStepl x2.
 RStepr e2.
 assumption.

 apply plus_resp_leEq_lft.
 RStepl (x1[*]e2[+][--]e1[*]x2).
 apply plus_resp_leEq_both.
 apply mult_resp_leEq_rht.
 assumption.
 assumption.
 RStepl (e1[*][--]x2).
 apply mult_resp_leEq_lft.
 RStepr ([--][--]e2).
 apply inv_resp_leEq.
 assumption.
 assumption.

 apply AbsSmall_nonneg with (e := e2) (x := x2).
 assumption.
 apply AbsSmall_nonneg with (e := e1) (x := x1).
 assumption.
Qed.

Lemma AbsSmall_cancel_mult :
 forall e x z : R, Zero[<]z -> AbsSmall (e[*]z) (x[*]z) -> AbsSmall e x.
 unfold AbsSmall in |- *.
 intros.
 elim H.
 intros.
 split.
 apply mult_cancel_leEq with (z := z).
 assumption.
 RStepl ([--](e[*]z)).
 assumption.
 apply mult_cancel_leEq with (z := z).
 assumption.
 assumption.
Qed.

Lemma AbsSmall_approach_zero :
 forall x : R, (forall e : R, Zero[<]e -> AbsSmall e x) -> x[=]Zero.
Proof.
 intros.
 apply not_ap_imp_eq.
 intro H0.
 elim (ap_imp_less _ _ _ H0).
 change (Zero[<=]x) in |- *.
 apply inv_cancel_leEq.
 AStepr ZeroR.
 red in |- *; apply approach_zero_weak.
 intros.
 apply inv_cancel_leEq; AStepr x.
 elim (H e); auto.

 change (x[<=]Zero) in |- *.
 red in |- *; apply approach_zero_weak.
 intros.
 elim (H e); auto.
Qed.

End AbsSmall_properties.

Declare Left Step AbsSmall_wd_lft_unfolded.
Declare Right Step AbsSmall_wd_rht_unfolded.

(**
** Properties of [AbsBig]
*)

Definition absBig (R : COrdField) (e x : R) : CProp :=
  Zero[<]e and (e[<=]x or x[<=][--]e).

Notation AbsBig := (absBig _).

Lemma AbsBigSmall_minus :
 forall (R : COrdField) (e1 e2 x1 x2 : R),
 e2[<]e1 -> AbsBig e1 x1 -> AbsSmall e2 x2 -> AbsBig (e1[-]e2) (x1[-]x2).
Proof.
 intros.
 unfold absBig in |- *.
 split.

 apply plus_cancel_less with (z := e2).
 RStepl e2.
 RStepr e1.
 assumption.

 unfold absBig in X0.
 elim X0.
 intros H2 H3.
 case H3.

 intro H4.
 left.
 unfold AbsSmall in H.
 elim H.
 intros.
 RStepl (e1[+][--]e2).
 RStepr (x1[+][--]x2).
 apply plus_resp_leEq_both.
 assumption.
 apply inv_cancel_leEq.
 RStepl x2.
 RStepr e2.
 assumption.

 intro H4.
 right.
 unfold AbsSmall in H.
 elim H.
 intros H5 H6.
 RStepr ([--]e1[+]e2).
 RStepl (x1[+][--]x2).
 apply plus_resp_leEq_both.
 assumption.
 apply inv_cancel_leEq.
 RStepr x2.
 RStepl ([--]e2).
 assumption.
Qed.


Section absBig_wd_properties.
(**
%\begin{convention}%
Let [R] be an ordered field.
%\end{convention}%
*)

Variable R : COrdField.

Lemma AbsBig_wd_rht : Crel_well_def_rht R AbsBig.
Proof.
 red in |- *.
 intros.
 unfold absBig in |- *.
 unfold absBig in H.
 elim X.
 intros H1 H2.
 split.

  assumption.

  case H2.

   intro H3.
   left.
   apply leEq_wdr with y.
   assumption.
   assumption.

   intro H3.
   right.
   apply leEq_wdl with y.
   assumption.
   assumption.
Qed.

Lemma AbsBig_wd_lft : Crel_well_def_lft R AbsBig.
 red in |- *.
 unfold absBig in |- *.
 intros.
 elim X.
 intros H1 H2.
 split.

  AStepr x.
  assumption.

  case H2.

   intro H3.
   left.
   AStepl x.
   assumption.

   intro H3.
   right.
   AStepr ([--]x).
   assumption.
Qed.

Lemma AbsBig_wd_rht_unfolded :
 forall x y z : R, AbsBig x y -> y[=]z -> AbsBig x z.
Proof AbsBig_wd_rht.

Lemma AbsBig_wd_lft_unfolded :
 forall x y z : R, AbsBig x y -> x[=]z -> AbsBig z y.
Proof AbsBig_wd_lft.

End absBig_wd_properties.

Declare Left Step AbsBig_wd_lft_unfolded.
Declare Right Step AbsBig_wd_rht_unfolded.