(* $Id$ *)

(** printing ExpCC %\ensuremath{\exp_{\mathbb C}}% *)

Require Export Triangle.
Require Export Exponential.
Require Export Pi.

(**
** The Complex Exponential
*)

Definition ExpCC (z : CC) := cc_IR (Exp (Re z))[*](Cos (Im z)[+I*]Sin (Im z)).

Lemma ExpCC_wd : forall z1 z2 : CC, z1[=]z2 -> ExpCC z1[=]ExpCC z2.
intro z1. elim z1. intros x1 y1.
intro z2. elim z2. intros x2 y2.
unfold ExpCC in |- *. unfold Re, Im in |- *.
intros (H1, H2).
simpl in H1. simpl in H2.
apply bin_op_wd_unfolded.

apply cc_IR_wd. apply Exp_wd. assumption.

AStepl (Cos y2[+I*]Sin y1).
AStepl (Cos y2[+I*]Sin y2).
apply eq_reflexive.
Qed.

(* begin hide *)
Let ExpCC_equation_aid_1 :
  forall z1 z2 : CC,
  ExpCC (z1[+]z2)[=]
  cc_IR (Exp (Re z1[+]Re z2))[*](Cos (Im z1[+]Im z2)[+I*]Sin (Im z1[+]Im z2)).
intro z1. elim z1. intros x1 y1.
intro z2. elim z2. intros x2 y2.
unfold Re, Im in |- *.
unfold ExpCC in |- *.
apply bin_op_wd_unfolded.
apply cc_IR_wd.
apply Exp_wd.
Algebra.

split; Algebra.

Qed.

Let ExpCC_equation_aid_2 :
  forall z1 z2 : CC,
  cc_IR (Exp (Re z1[+]Re z2))[*](Cos (Im z1[+]Im z2)[+I*]Sin (Im z1[+]Im z2))[=]
  cc_IR (Exp (Re z1)[*]Exp (Re z2))[*]
  ((Cos (Im z1)[*]Cos (Im z2)[-]Sin (Im z1)[*]Sin (Im z2))[+I*]
   (Sin (Im z1)[*]Cos (Im z2)[+]Cos (Im z1)[*]Sin (Im z2))).
intros z1 z2. apply bin_op_wd_unfolded.

apply cc_IR_wd. Algebra.

split; Algebra.

Qed.

Let ExpCC_equation_aid_3 :
  forall z1 z2 : CC,
  cc_IR (Exp (Re z1)[*]Exp (Re z2))[*]
  ((Cos (Im z1)[*]Cos (Im z2)[-]Sin (Im z1)[*]Sin (Im z2))[+I*]
   (Sin (Im z1)[*]Cos (Im z2)[+]Cos (Im z1)[*]Sin (Im z2)))[=]
  cc_IR (Exp (Re z1)[*]Exp (Re z2))[*]
  ((Cos (Im z1)[+I*]Sin (Im z1))[*](Cos (Im z2)[+I*]Sin (Im z2))).
intros z1 z2. apply bin_op_wd_unfolded.

apply eq_reflexive.

set (c1 := Cos (Im z1)) in *.
set (c2 := Cos (Im z2)) in *.
set (s1 := Sin (Im z1)) in *.
set (s2 := Sin (Im z2)) in *.
split; simpl in |- *; Algebra.
Qed.

Let ExpCC_equation_aid_4 :
  forall z1 z2 : CC,
  cc_IR (Exp (Re z1)[*]Exp (Re z2))[*]
  ((Cos (Im z1)[+I*]Sin (Im z1))[*](Cos (Im z2)[+I*]Sin (Im z2)))[=]
  ExpCC z1[*]ExpCC z2.
intros z1 z2.
unfold ExpCC in |- *.
set (c := Cos (Im z1)[+I*]Sin (Im z1)) in *.
set (d := Cos (Im z2)[+I*]Sin (Im z2)) in *.
AStepl (cc_IR (Exp (Re z1))[*]cc_IR (Exp (Re z2))[*](c[*]d)).
rational.
Qed.
(* end hide *)

Lemma ExpCC_plus : forall z1 z2 : CC, ExpCC (z1[+]z2)[=]ExpCC z1[*]ExpCC z2.
intros z1 z2.
apply
 eq_transitive_unfolded
  with
    (S := cc_csetoid)
    (y := cc_IR (Exp (Re z1)[*]Exp (Re z2))[*]
          ((Cos (Im z1)[*]Cos (Im z2)[-]Sin (Im z1)[*]Sin (Im z2))[+I*]
           (Sin (Im z1)[*]Cos (Im z2)[+]Cos (Im z1)[*]Sin (Im z2)))).
eapply eq_transitive_unfolded.
apply ExpCC_equation_aid_1. apply ExpCC_equation_aid_2.
eapply eq_transitive_unfolded.
apply ExpCC_equation_aid_3. apply ExpCC_equation_aid_4.
Qed.

Hint Resolve ExpCC_plus: algebra.

Lemma ExpCC_Zero : ExpCC Zero[=]One.
unfold ExpCC in |- *.
AStepl (cc_IR (Exp Zero)[*](Cos Zero[+I*]Sin Zero)).
AStepl (cc_IR One[*](Cos Zero[+I*]Sin Zero)).
AStepl (cc_IR One[*](One[+I*]Zero)).
simpl in |- *. split; simpl in |- *; rational.
Qed.

Hint Resolve ExpCC_Zero: algebra.

Lemma ExpCC_inv_aid : forall z : CC, ExpCC z[*]ExpCC [--]z[=]One.
intro z.
apply eq_transitive_unfolded with (S := cc_csetoid) (y := ExpCC Zero).
AStepl (ExpCC (z[+][--]z)).
apply ExpCC_wd.
rational.
Algebra.
Qed.

Hint Resolve ExpCC_inv_aid: algebra.

Lemma ExpCC_ap_zero : forall z : CC, ExpCC z[#]Zero.
intro z.
cut (ExpCC z[*]ExpCC [--]z[#]Zero).
intro H.
apply (mult_cancel_ap_zero_lft _ _ _ H).
AStepl (One:CC).
apply cc_cr_non_triv.
Qed.

Lemma ExpCC_inv :
 forall (z : CC) (H : ExpCC z[#]Zero), (One[/] _[//]H)[=]ExpCC [--]z.
intros z H.
AStepl (ExpCC z[*]ExpCC [--]z[/] ExpCC z[//]H). rational.
Qed.

Hint Resolve ExpCC_inv: algebra.

Lemma ExpCC_pow :
 forall (z : CC) (n : nat), ExpCC z[^]n[=]ExpCC (nring n[*]z).
intro z. simple induction n.
unfold nexp in |- *.
AStepl (One:CC).
AStepr (ExpCC Zero).
AStepr (One:CC).
apply eq_reflexive.
apply ExpCC_wd.
rational.

intros n0 Hrec.
AStepl (ExpCC z[^]n0[*]ExpCC z).
AStepl (ExpCC (nring n0[*]z)[*]ExpCC z).
AStepl (ExpCC (nring n0[*]z[+]z)).
apply ExpCC_wd.
Algebra.
RStepl ((nring n0[+]One)[*]z). Algebra.
Qed.

Hint Resolve ExpCC_pow: algebra.

Lemma AbsCC_ExpCC : forall z : CC, AbsCC (ExpCC z)[=]Exp (Re z).
intro z. unfold ExpCC in |- *.
AStepl (AbsCC (cc_IR (Exp (Re z)))[*]AbsCC (Cos (Im z)[+I*]Sin (Im z))).
AStepr (Exp (Re z)[*]One).
apply bin_op_wd_unfolded.
assert (H : AbsCC (cc_IR (Exp (Re z)))[=]Exp (Re z)).
apply AbsCC_IR.
apply less_leEq.
apply Exp_pos.
AStepl (Exp (Re z)).
apply eq_reflexive.
cut (AbsCC (Cos (Im z)[+I*]Sin (Im z))[^]2[=]One).
set (x := AbsCC (Cos (Im z)[+I*]Sin (Im z))) in *.
intro H0.

assert (H1 : x[+]One[~=]Zero).
apply ap_imp_neq.
apply Greater_imp_ap.
apply leEq_less_trans with (y := x).
unfold x in |- *. apply AbsCC_nonneg.
apply less_plusOne.

assert (H2 : (x[+]One)[*](x[-]One)[=]Zero).
cut (x[^]2[-]One[^]2[=]Zero).
intro H'.
AStepl (x[^]2[-]One[^]2).
assumption.
AStepl (x[^]2[-]One).
AStepr (OneR[-]OneR).
apply cg_minus_wd; [ assumption | apply eq_reflexive ].
assert (H3 : x[-]One[=]Zero).
apply (mult_eq_zero _ _ _ H1 H2).
RStepl (One[+](x[-]One)).
AStepr (OneR[+]ZeroR).
apply plus_resp_eq. assumption.

AStepl (Cos (Im z)[^]2[+]Sin (Im z)[^]2).
AStepl OneR.
apply eq_reflexive.
apply AbsCC_square_Re_Im.
Qed.

Hint Resolve AbsCC_ExpCC: algebra.

Lemma ExpCC_Periodic :
 forall z : CC, ExpCC (z[+]II[*]Two[*]cc_IR Pi)[=]ExpCC z.
intro z. elim z. intros x y.
AStepl (ExpCC (x[+I*](y[+]Two[*]Pi))).
unfold ExpCC in |- *.
apply bin_op_wd_unfolded.
apply cc_IR_wd.
apply Exp_wd.
simpl in |- *. apply eq_reflexive_unfolded.

AStepl (Cos (y[+]Two[*]Pi)[+I*]Sin (y[+]Two[*]Pi)).
AStepl (Cos y[+I*]Sin y).
apply eq_reflexive.

apply ExpCC_wd.
split; simpl in |- *; rational.
Qed.

Hint Resolve ExpCC_Periodic: algebra.

Lemma ExpCC_Exp : forall x : IR, ExpCC (cc_IR x)[=]cc_IR (Exp x).
intro x. unfold ExpCC in |- *.
AStepl (cc_IR (Exp x)[*](Cos (Im (cc_IR x))[+I*]Sin (Im (cc_IR x)))).
AStepr (cc_IR (Exp x)[*]One).
apply bin_op_wd_unfolded.
Algebra.
AStepl (Cos Zero[+I*]Sin Zero).
Step_final (One[+I*]Zero).
Qed.

Hint Resolve ExpCC_Exp: algebra.

Lemma CExp_formula : (ExpCC (II[*](cc_IR Pi)))[+]One[=]Zero.
split.
Opaque Sin Cos Exp.
simpl.
RStepl ((Exp Zero)[*](Cos Pi)[+]One).
AStepl ((One:IR)[*][--]One[+]One).
rational.
simpl.
RStepl ((Exp Zero)[*](Sin Pi)).
Step_final ((One:IR)[*]Zero).
Qed.
