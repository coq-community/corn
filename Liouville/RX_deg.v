(*
Copyright © 2009 Valentin Blot

Permission is hereby granted, free of charge, to any person obtaining a copy of
this proof and associated documentation files (the "Proof"), to deal in
the Proof without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Proof, and to permit persons to whom the Proof is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Proof.

THE PROOF IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE PROOF OR THE USE OR OTHER DEALINGS IN THE PROOF.
*)
Require Import CPoly_Degree RingClass CRingClass.

Section RX_deg.

Variable R : CRing.
Let RX := cpoly_cring R.
Add Ring r_r : (r_rt (Ring:=CRing_is_Ring R)).
Add Ring rx_r : (r_rt (Ring:=CRing_is_Ring (cpoly_cring R))).
Hypothesis R_dec : forall x y : R, COr (x [=] y) (x [#] y).

Lemma RX_dec : forall p q : RX, COr (p [=] q) (p [#] q).
Proof.
unfold RX; intros p q; pattern p, q; apply Ccpoly_double_sym_ind; clear p q.
    intros p q H.
    case H.
      left; symmetry; assumption.
    right; apply ap_symmetric; assumption.
  intro p; pattern p; apply Ccpoly_induc; clear p.
    left; reflexivity.
  intros p c; case (R_dec c Zero).
    intros H1 H2; destruct H2.
      left; apply _linear_eq_zero; split; assumption.
    right; rewrite linear_ap_zero; right; assumption.
  right; rewrite linear_ap_zero; left; assumption.
intros p q c d H; case (R_dec c d).
  case H.
    left; apply _linear_eq_linear; split; assumption.
  right; rewrite linear_ap_linear; right; assumption.
right; rewrite linear_ap_linear; left; assumption.
Qed.

Fixpoint RX_deg (p : RX) : nat :=
  match p with
    | cpoly_zero => 0
    | cpoly_linear c p => if (RX_dec p Zero) then 0 else S (RX_deg p)
  end.

Lemma RX_deg_zero : RX_deg Zero = 0. Proof. reflexivity. Qed.
Lemma RX_deg_linear : forall c p, RX_deg (c[+X*]p) = if (RX_dec p Zero) then 0 else S (RX_deg p).
Proof. reflexivity. Qed.

Lemma RX_deg_spec : forall p : RX, p [#] Zero -> degree (RX_deg p) p.
Proof.
intro p; pattern p; apply Ccpoly_induc; clear p.
  intro H; destruct (ap_irreflexive _ _ H).
unfold RX; intros p c Hrec.
rewrite linear_ap_zero; intro H.
rewrite RX_deg_linear.
case (RX_dec p Zero).
  case H.
    split.
      assumption.
    intro m; case m.
      intro H1; inversion H1.
    intros; rewrite coeff_Sm_lin.
    rewrite <- (nth_coeff_zero _ n).
    apply nth_coeff_wd; assumption.
  intros Hap Heq; destruct (eq_imp_not_ap _ _ _ Heq Hap).
intro H0; destruct (Hrec H0) as [Hcoeff Hdeg].
split.
  case (R_dec (nth_coeff (S (RX_deg p)) (c[+X*]p)) Zero).
    intro H1; destruct (ap_imp_neq _ _ _ Hcoeff).
    rewrite coeff_Sm_lin in H1; assumption.
  tauto.
intro m; case m.
intro H1; inversion H1.
clear m; intros m Hlt; rewrite coeff_Sm_lin.
apply Hdeg; apply le_S_n; assumption.
Qed.

Lemma RX_deg_wd : forall P Q, P [=] Q -> RX_deg P = RX_deg Q.
Proof.
intros P Q; pattern P, Q; apply Ccpoly_double_sym_ind; clear P Q.
intros P Q Hsym Heq.
symmetry; apply Hsym; symmetry; assumption.
intro p; pattern p; apply Ccpoly_induc; clear p.
reflexivity.
intros.
rewrite RX_deg_linear.
case (RX_dec p Zero).
reflexivity.
intro Hap; destruct (ap_imp_neq _ _ _ Hap).
apply (linear_eq_zero_ _ _ _ H0).
intros P Q c d Hrec Heq.
destruct (linear_eq_linear_ _ _ _ _ _ Heq).
rewrite RX_deg_linear.
rewrite RX_deg_linear.
case (RX_dec P Zero).
case (RX_dec Q Zero).
reflexivity.
intros H1 H2; destruct (ap_imp_neq _ _ _ H1).
rewrite <- H0; assumption.
case (RX_dec Q Zero).
intros H1 H2; destruct (ap_imp_neq _ _ _ H2).
rewrite H0; assumption.
intros HQ HP.
f_equal; apply Hrec; assumption.
Qed.

Lemma degree_inj : forall (P : RX) m n, degree m P -> degree n P -> m = n.
Proof.
intros P m n Hm Hn.
destruct Hm as [Hm1 Hm2].
destruct Hn as [Hn1 Hn2].
case (lt_eq_lt_dec m n).
  intro H; destruct H.
    destruct (ap_imp_neq _ _ _ Hn1).
    apply Hm2; assumption.
  assumption.
intro Hlt; destruct (ap_imp_neq _ _ _ Hm1).
apply Hn2; assumption.
Qed.

Lemma RX_deg_c_ : forall a : R, RX_deg (_C_ a) = 0.
Proof.
simpl; case (RX_dec (cpoly_zero R) (cpoly_zero R)); [reflexivity|].
intro H; destruct (ap_irreflexive _ _ H).
Qed.

Lemma RX_deg_x_ : RX_deg _X_ = 1.
Proof.
simpl.
case (RX_dec (cpoly_one R) (cpoly_zero R)).
intro H; destruct (eq_imp_not_ap _ _ _ H (ring_non_triv _)).
intro; case (RX_dec (cpoly_zero R) (cpoly_zero R)); [reflexivity|].
intro H; destruct (ap_irreflexive _ _ H).
Qed.

Lemma RX_deg_inv : forall p, RX_deg p = RX_deg ([--]p).
Proof.
intro p.
case (RX_dec p Zero).
  intro H; rewrite (RX_deg_wd _ _ H), RX_deg_zero.
  rewrite <- RX_deg_zero; apply RX_deg_wd; rewrite H; unfold RX; ring.
intro Hp.
apply (degree_inj p).
apply RX_deg_spec; assumption.
apply (degree_wd _ ([--][--]p)); [apply cg_inv_inv|].
apply degree_inv.
apply RX_deg_spec.
apply inv_resp_ap_zero; assumption.
Qed.

Lemma RX_deg_sum : forall p q, RX_deg p <> RX_deg q -> RX_deg (p[+]q)=max (RX_deg p) (RX_deg q).
Proof.
intros p q Hneq.
case (RX_dec p Zero).
  intro H; rewrite (RX_deg_wd _ _  H).
  transitivity (RX_deg q); [apply RX_deg_wd; rewrite H; unfold RX; ring|].
  rewrite RX_deg_zero; reflexivity.
case (RX_dec q Zero).
  intro H; rewrite (RX_deg_wd _ _  H).
  transitivity (RX_deg p); [apply RX_deg_wd; rewrite H; unfold RX; ring|].
  rewrite RX_deg_zero; rewrite max_comm; reflexivity.
intros Hq Hp.
set (RX_deg_spec _ Hp).
set (RX_deg_spec _ Hq).
case (le_lt_dec (RX_deg p) (RX_deg q)); intro.
  rewrite max_r; [|assumption].
  inversion l.
    destruct (Hneq H0).
  apply (degree_inj (p[+]q)).
    apply RX_deg_spec.
    case (RX_dec (p[+]q) Zero); [|tauto].
    intro; destruct Hneq.
    rewrite (RX_deg_wd p ([--]q)).
      symmetry; apply RX_deg_inv.
    apply cg_inv_unique'; assumption.
  apply (degree_plus_rht _ _ _ m); [| |apply le_n].
    apply (degree_le_mon _ _ (RX_deg p)); [assumption|apply d].
  rewrite H; apply RX_deg_spec; assumption.
rewrite max_l; [|apply lt_le_weak; assumption].
apply (degree_inj (p[+]q)).
  apply RX_deg_spec.
  case (RX_dec (p[+]q) Zero); [|tauto].
  intro; destruct Hneq.
  rewrite (RX_deg_wd p ([--]q)).
    symmetry; apply RX_deg_inv.
  apply cg_inv_unique'; assumption.
apply (degree_wd _ _ _ _ (cag_commutes _ _ _)).
  apply (degree_plus_rht _ _ _ (RX_deg q)); [| |assumption].
  apply degree_imp_degree_le.
  apply RX_deg_spec; assumption.
apply RX_deg_spec; assumption.
Qed.

Lemma RX_deg_minus : forall p q, RX_deg p <> RX_deg q -> RX_deg (p[-]q)=max (RX_deg p) (RX_deg q).
Proof.
unfold cg_minus; intros p q Hneq.
rewrite (RX_deg_inv q) in Hneq.
rewrite (RX_deg_sum _ _ Hneq).
f_equal.
symmetry; apply RX_deg_inv.
Qed.

End RX_deg.
