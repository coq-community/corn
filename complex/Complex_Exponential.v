(* $Id: Complex_Exponential.v,v 1.4 2004/04/23 10:00:55 lcf Exp $ *)

(** printing ExpCC %\ensuremath{\exp_{\mathbb C}}% *)

Require Export AbsCC.
Require Export Exponential.
Require Export Pi.

(** ** The Complex Exponential *)

Definition ExpCC (z : CC) := cc_IR (Exp (Re z)) [*] (Cos (Im z) [+I*]Sin (Im z)).

Lemma ExpCC_wd : forall z1 z2 : CC, z1 [=] z2 -> ExpCC z1 [=] ExpCC z2.
intro z1. elim z1. intros x1 y1.
intro z2. elim z2. intros x2 y2.
unfold ExpCC in |- *. unfold Re, Im in |- *.
intros (H1, H2).
simpl in H1. simpl in H2.
apply bin_op_wd_unfolded.

apply cc_IR_wd. apply Exp_wd. assumption.

astepl (Cos y2[+I*]Sin y1).
astepl (Cos y2[+I*]Sin y2).
apply eq_reflexive.
Qed.

(* begin hide *)
Lemma ExpCC_equation_aid_1 :
  forall z1 z2 : CC,
  ExpCC (z1[+]z2) [=] 
  cc_IR (Exp (Re z1[+]Re z2)) [*] (Cos (Im z1[+]Im z2) [+I*]Sin (Im z1[+]Im z2)).
intro z1. elim z1. intros x1 y1.
intro z2. elim z2. intros x2 y2.
unfold Re, Im in |- *.
unfold ExpCC in |- *.
apply bin_op_wd_unfolded.
apply cc_IR_wd.
apply Exp_wd.
algebra.

split; algebra.

Qed.

Lemma ExpCC_equation_aid_2 :
  forall z1 z2 : CC,
  cc_IR (Exp (Re z1[+]Re z2)) [*] (Cos (Im z1[+]Im z2) [+I*]Sin (Im z1[+]Im z2)) [=] 
  cc_IR (Exp (Re z1) [*]Exp (Re z2)) [*]
  ((Cos (Im z1) [*]Cos (Im z2) [-]Sin (Im z1) [*]Sin (Im z2)) [+I*]
   (Sin (Im z1) [*]Cos (Im z2) [+]Cos (Im z1) [*]Sin (Im z2))).
intros z1 z2. apply bin_op_wd_unfolded.

apply cc_IR_wd. algebra.

split; algebra.

Qed.

Lemma ExpCC_equation_aid_3 :
  forall z1 z2 : CC,
  cc_IR (Exp (Re z1) [*]Exp (Re z2)) [*]
  ((Cos (Im z1) [*]Cos (Im z2) [-]Sin (Im z1) [*]Sin (Im z2)) [+I*]
   (Sin (Im z1) [*]Cos (Im z2) [+]Cos (Im z1) [*]Sin (Im z2))) [=] 
  cc_IR (Exp (Re z1) [*]Exp (Re z2)) [*]
  ((Cos (Im z1) [+I*]Sin (Im z1)) [*] (Cos (Im z2) [+I*]Sin (Im z2))).
intros z1 z2. apply bin_op_wd_unfolded.

apply eq_reflexive.

set (c1 := Cos (Im z1)) in *.
set (c2 := Cos (Im z2)) in *.
set (s1 := Sin (Im z1)) in *.
set (s2 := Sin (Im z2)) in *.
split; simpl in |- *; algebra.
Qed.

Lemma ExpCC_equation_aid_4 :
  forall z1 z2 : CC,
  cc_IR (Exp (Re z1) [*]Exp (Re z2)) [*]
  ((Cos (Im z1) [+I*]Sin (Im z1)) [*] (Cos (Im z2) [+I*]Sin (Im z2))) [=] 
  ExpCC z1[*]ExpCC z2.
intros z1 z2.
unfold ExpCC in |- *.
set (c := Cos (Im z1) [+I*]Sin (Im z1)) in *.
set (d := Cos (Im z2) [+I*]Sin (Im z2)) in *.
astepl (cc_IR (Exp (Re z1)) [*]cc_IR (Exp (Re z2)) [*] (c[*]d)).
rational.
Qed.
(* end hide *)

Lemma ExpCC_plus : forall z1 z2 : CC, ExpCC (z1[+]z2) [=] ExpCC z1[*]ExpCC z2.
intros z1 z2.
apply
 eq_transitive_unfolded
  with
    (S := cc_csetoid)
    (y := cc_IR (Exp (Re z1) [*]Exp (Re z2)) [*]
          ((Cos (Im z1) [*]Cos (Im z2) [-]Sin (Im z1) [*]Sin (Im z2)) [+I*]
           (Sin (Im z1) [*]Cos (Im z2) [+]Cos (Im z1) [*]Sin (Im z2)))).
eapply eq_transitive_unfolded.
apply ExpCC_equation_aid_1. apply ExpCC_equation_aid_2.
eapply eq_transitive_unfolded.
apply ExpCC_equation_aid_3. apply ExpCC_equation_aid_4.
Qed.

Hint Resolve ExpCC_plus: algebra.

Lemma ExpCC_Zero : ExpCC Zero [=] One.
unfold ExpCC in |- *.
astepl (cc_IR (Exp Zero) [*] (Cos Zero[+I*]Sin Zero)).
astepl (cc_IR One[*] (Cos Zero[+I*]Sin Zero)).
astepl (cc_IR One[*] (One[+I*]Zero)).
simpl in |- *. split; simpl in |- *; rational.
Qed.

Hint Resolve ExpCC_Zero: algebra.

Lemma ExpCC_inv_aid : forall z : CC, ExpCC z[*]ExpCC [--]z [=] One.
intro z.
apply eq_transitive_unfolded with (S := cc_csetoid) (y := ExpCC Zero).
astepl (ExpCC (z[+][--]z)).
apply ExpCC_wd.
rational.
algebra.
Qed.

Hint Resolve ExpCC_inv_aid: algebra.

Lemma ExpCC_ap_zero : forall z : CC, ExpCC z [#] Zero.
intro z.
cut (ExpCC z[*]ExpCC [--]z [#] Zero).
intro H.
apply (mult_cancel_ap_zero_lft _ _ _ H).
astepl (One:CC).
apply cc_cr_non_triv.
Qed.

Lemma ExpCC_inv : forall z z_, (One[/] (ExpCC z) [//]z_) [=] ExpCC [--]z.
intros z H.
astepl (ExpCC z[*]ExpCC [--]z[/] ExpCC z[//]H). rational.
Qed.

Hint Resolve ExpCC_inv: algebra.

Lemma ExpCC_pow : forall z n, ExpCC z[^]n [=] ExpCC (nring n[*]z).
intro z. simple induction n.
unfold nexp in |- *.
astepl (One:CC).
astepr (ExpCC Zero).
astepr (One:CC).
apply eq_reflexive.
apply ExpCC_wd.
rational.

intros n0 Hrec.
astepl (ExpCC z[^]n0[*]ExpCC z).
astepl (ExpCC (nring n0[*]z) [*]ExpCC z).
astepl (ExpCC (nring n0[*]z[+]z)).
apply ExpCC_wd.
algebra.
rstepl ((nring n0[+]One) [*]z). algebra.
Qed.

Hint Resolve ExpCC_pow: algebra.

Lemma AbsCC_ExpCC : forall z : CC, AbsCC (ExpCC z) [=] Exp (Re z).
intro z. unfold ExpCC in |- *.
astepl (AbsCC (cc_IR (Exp (Re z))) [*]AbsCC (Cos (Im z) [+I*]Sin (Im z))).
astepr (Exp (Re z) [*]One).
apply bin_op_wd_unfolded.
assert (H : AbsCC (cc_IR (Exp (Re z))) [=] Exp (Re z)).
apply AbsCC_IR.
apply less_leEq.
apply Exp_pos.
astepl (Exp (Re z)).
apply eq_reflexive.
cut (AbsCC (Cos (Im z) [+I*]Sin (Im z)) [^]2 [=] One).
set (x := AbsCC (Cos (Im z) [+I*]Sin (Im z))) in *.
intro H0.

assert (H1 : x[+]One[~=]Zero).
apply ap_imp_neq.
apply Greater_imp_ap.
apply leEq_less_trans with (y := x).
unfold x in |- *. apply AbsCC_nonneg.
apply less_plusOne.

assert (H2 : (x[+]One) [*] (x[-]One) [=] Zero).
cut (x[^]2[-]One[^]2 [=] Zero).
intro H'.
astepl (x[^]2[-]One[^]2).
assumption.
astepl (x[^]2[-]One).
astepr (OneR[-]OneR).
apply cg_minus_wd; [ assumption | apply eq_reflexive ].
assert (H3 : x[-]One [=] Zero).
apply (mult_eq_zero _ _ _ H1 H2).
rstepl (One[+] (x[-]One)).
astepr (OneR[+]ZeroR).
apply plus_resp_eq. assumption.

astepl (Cos (Im z) [^]2[+]Sin (Im z) [^]2).
astepl OneR.
apply eq_reflexive.
apply AbsCC_square_Re_Im.
Qed.

Hint Resolve AbsCC_ExpCC: algebra.

Lemma ExpCC_Periodic : forall z, ExpCC (z[+]II[*]Two[*]cc_IR Pi) [=] ExpCC z.
intro z. elim z. intros x y.
astepl (ExpCC (x[+I*] (y[+]Two[*]Pi))).
unfold ExpCC in |- *.
apply bin_op_wd_unfolded.
apply cc_IR_wd.
apply Exp_wd.
simpl in |- *. apply eq_reflexive_unfolded.

astepl (Cos (y[+]Two[*]Pi) [+I*]Sin (y[+]Two[*]Pi)).
astepl (Cos y[+I*]Sin y).
apply eq_reflexive.

apply ExpCC_wd.
split; simpl in |- *; rational.
Qed.

Hint Resolve ExpCC_Periodic: algebra.

Lemma ExpCC_Exp : forall x : IR, ExpCC (cc_IR x) [=] cc_IR (Exp x).
intro x. unfold ExpCC in |- *.
astepl (cc_IR (Exp x) [*] (Cos (Im (cc_IR x)) [+I*]Sin (Im (cc_IR x)))).
astepr (cc_IR (Exp x) [*]One).
apply bin_op_wd_unfolded.
algebra.
astepl (Cos Zero[+I*]Sin Zero).
Step_final (One[+I*]Zero).
Qed.

Hint Resolve ExpCC_Exp: algebra.

Theorem Euler : (ExpCC (II[*] (cc_IR Pi))) [+]One [=] Zero.
split.
Opaque Sin Cos Exp.
simpl.
rstepl ((Exp Zero) [*] (Cos Pi) [+]One).
astepl ((One:IR) [*][--]One[+]One).
rational.
simpl.
rstepl ((Exp Zero) [*] (Sin Pi)).
Step_final ((One:IR) [*]Zero).
Qed.
