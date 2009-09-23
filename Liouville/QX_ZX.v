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
Require Import CPoly_Degree.
Require Import rings.Qring.
Require Import Zring.
Require Import Qordfield.
Require Import CRing_Homomorphisms.

Require Import RingClass CRingClass.
Require Import Zlcm Q_can RX_deg.

Section Z_Q.

Let QX := cpoly_cring Q_as_CRing.
Add Ring q_r : (r_rt (Ring:=CRing_is_Ring Q_as_CRing)).
Add Ring qx_r : (r_rt (Ring:=CRing_is_Ring (cpoly_cring Q_as_CRing))).
Let ZX := cpoly_cring Z_as_CRing.
Add Ring z_r : (r_rt (Ring:=CRing_is_Ring Z_as_CRing)).
Add Ring zx_r : (r_rt (Ring:=CRing_is_Ring (cpoly_cring Z_as_CRing))).

Let ZX_deg := RX_deg Z_as_CRing Z_dec.
Let ZX_dec := RX_dec Z_as_CRing Z_dec.
Let QX_dec := RX_dec Q_as_CRing Q_dec.
Let QX_deg := RX_deg Q_as_CRing Q_dec.


Definition in_ZX (P : QX) := forall n, in_Z (nth_coeff n P).

Definition QX_normalize (p : QX) : Q_as_CRing :=
  match (dec_Qeq (nth_coeff (QX_deg p) p) Zero) with
    | left _ => Zero
    | right H => One [/] (nth_coeff (QX_deg p) p) [//] H
  end.

Lemma QX_normalize_spec : forall p : QX, p [#] Zero -> monic (QX_deg p) ((_C_ (QX_normalize p)) [*] p).
Proof.
 intros p H.
 destruct (RX_deg_spec _ Q_dec _ H) as [Hcoeff Hdeg].
 split.
  rewrite nth_coeff_c_mult_p.
  unfold QX_normalize.
  case (dec_Qeq (nth_coeff (QX_deg p) p) Zero).
   intro; destruct Hcoeff; assumption.
  intro Hap.
  apply (div_1 Q_as_CField).
 intros m Hlt; rewrite nth_coeff_c_mult_p.
 rewrite (Hdeg m Hlt).
 ring.
Qed.

Definition QX_to_monic (p : QX) : QX := (_C_ (QX_normalize p)) [*] p.

Lemma QX_to_monic_spec : forall p : QX, p [#] Zero -> monic (QX_deg p) (QX_to_monic p).
Proof.
 intros p H.
 apply QX_normalize_spec.
 assumption.
Qed.

Lemma QX_to_monic_apply : forall (p : QX) (a : Q), p ! a [=] Zero ->
  (QX_to_monic p) ! a [=] Zero.
Proof.
 intros p a Heq.
 unfold QX_to_monic; rewrite mult_apply; rewrite Heq; ring.
Qed.

Fixpoint den_list (P : QX) : list Z_as_CRing :=
  match P with
    | cpoly_zero => One::nil
    | cpoly_linear c P => Q_can_den c::den_list P
  end.

Lemma den_list_zero : den_list Zero = One::nil.
Proof. reflexivity. Qed.

Lemma den_list_linear : forall c P, den_list (c[+X*]P) = Q_can_den c::den_list P.
Proof. reflexivity. Qed.

Lemma den_list_spec : forall P n, n <= QX_deg P ->
                      In (Q_can_den (nth_coeff n P)) (den_list P).
Proof.
 intro P; pattern P; apply Ccpoly_induc; clear P.
  simpl; left.
  rewrite Q_can_den_pos_val_spec.
  unfold Q_can_den_pos_val; reflexivity.
 intros P c Hrec n.
 unfold QX_deg; rewrite RX_deg_linear; fold QX_deg; fold QX_dec.
 case (QX_dec P Zero).
  simpl.
  case n.
   left; reflexivity.
  intros A B C; inversion C.
 intros Hap Hle.
 simpl.
 destruct n.
  left; reflexivity.
 right; apply Hrec.
 apply le_S_n; assumption.
Qed.

Definition Zlcm_den_poly (P : QX) :=
    Zlcm_gen (den_list P).

Lemma Zlcm_den_poly_nz : forall P, Zlcm_den_poly P [#] Zero.
Proof.
 intro P; apply Zlcm_gen_nz.
 intro a; pattern P; apply Ccpoly_induc; clear P.
  simpl; intro H; destruct H; [|contradiction].
  rewrite <- H; discriminate.
 intros P c.
 rewrite den_list_linear.
 rewrite Q_can_den_pos_val_spec.
 induction (den_list P).
  simpl; intros.
  destruct H0; [rewrite <- H0; discriminate|contradiction].
 simpl; intros.
 destruct H0; [rewrite <- H0; discriminate|].
 apply H; assumption.
Qed.

Lemma den_1_div_iff : forall q : Q_as_CRing, Q_can_den q = 1 <-> Zdivides (Qden q) (Qnum q).
Proof.
 intro q.
 split; intro H.
  unfold Q_can_den in H.
  destruct q; simpl in *.
  cut (Zpos Qden = Zgcd Qnum Qden).
   intro H0; rewrite H0.
   apply Zgcd_is_divisor_lft.
  rewrite {1} (Zgcd_div_mult_rht Qnum Qden).
   rewrite H.
   apply Zmult_1_l.
  intro.
  destruct (Zgcd_zero _ _ H0).
  rewrite H1 in H.
  rewrite H2 in H.
  rewrite Zgcd_zero_rht in H.
  rewrite Zdiv_0_r in H.
  discriminate.
 unfold Q_can_den.
 destruct q; simpl in *.
 case (Z_dec Qnum 0).
  intro H0; rewrite H0.
  rewrite Zgcd_zero_lft.
  apply Z_div_same_full.
  discriminate.
 intro Hap.
 cut (Zpos Qden = Zgcd Qnum Qden).
  intro H0; rewrite {1} H0.
  apply Z_div_same_full.
  intro H1; destruct (Zgcd_zero _ _ H1).
  discriminate.
 symmetry.
 apply Zgcd_divisor; assumption.
Qed.

Fixpoint Q_can_num_poly (P : QX) : ZX :=
  match P with
    | cpoly_zero => cpoly_zero Z_as_CRing
    | cpoly_linear c Q => cpoly_linear Z_as_CRing (Q_can_num c) (Q_can_num_poly Q)
  end.

Lemma Q_can_num_poly_zero : Q_can_num_poly Zero = Zero.
Proof. reflexivity. Qed.

Lemma Q_can_num_poly_linear : forall c P, Q_can_num_poly (c[+X*]P) = Q_can_num c[+X*]Q_can_num_poly P.
Proof. reflexivity. Qed.

Lemma Q_can_num_poly_spec : forall P Q, P [=] Q -> Q_can_num_poly P [=] Q_can_num_poly Q.
Proof.
 intros P Q; pattern P, Q; apply Ccpoly_double_sym_ind; clear P Q.
   intros P Q Hsym Heq.
   symmetry; apply Hsym; symmetry; assumption.
  intro P.
  pattern P; apply Ccpoly_induc; clear P.
   reflexivity.
  intros P c Hrec Heq.
  destruct (zero_eq_linear_ _ _ _ Heq).
  split.
   rewrite (Q_can_num_spec _ Zero).
    reflexivity.
   assumption.
  change (Zero [=] Q_can_num_poly P).
  symmetry; apply Hrec; symmetry; assumption.
 intros P Q c d Hrec Heq.
 destruct (linear_eq_linear_ _ _ _ _ _ Heq).
 rewrite Q_can_num_poly_linear Q_can_num_poly_linear.
 apply _linear_eq_linear.
 split.
  apply Q_can_num_spec; assumption.
 apply Hrec; assumption.
Qed.

Lemma Q_can_num_poly_deg_eq : forall P, QX_deg P = ZX_deg (Q_can_num_poly P).
Proof.
 intro P.
 pattern P; apply Ccpoly_induc; clear P.
  reflexivity.
 intros P c Heq.
 rewrite Q_can_num_poly_linear.
 unfold QX_deg, ZX_deg.
 rewrite RX_deg_linear; fold QX_dec.
 rewrite RX_deg_linear; fold ZX_dec.
 fold QX_deg; fold ZX_deg.
 rewrite <- Heq.
 case (QX_dec P Zero).
  case (ZX_dec (Q_can_num_poly P) Zero).
   reflexivity.
  intros Hap Heq2; destruct (ap_imp_neq _ _ _ Hap); revert Heq2; clear.
  pattern P; apply Ccpoly_induc; clear P.
   reflexivity.
  intros P c Hrec Heq; destruct (linear_eq_zero_ _ _ _ Heq).
  rewrite Q_can_num_poly_linear.
  apply _linear_eq_zero; split.
   rewrite (Q_can_num_spec _ _ H); reflexivity.
  apply Hrec; assumption.
 intro Hap; case (ZX_dec (Q_can_num_poly P) Zero).
  intro Heq2; destruct (ap_imp_neq _ _ _ Hap); revert Heq2; clear.
  pattern P; apply Ccpoly_induc; clear P.
   reflexivity.
  intros P c Hrec Heq.
  rewrite Q_can_num_poly_linear in Heq.
  destruct (linear_eq_zero_ _ _ _ Heq).
  apply _linear_eq_zero; split; [|apply Hrec; assumption].
  revert H; clear; destruct c as [qn qd].
  unfold Q_can_num; simpl; unfold Qeq; simpl.
  rewrite Zmult_1_r.
  intro H; rewrite (Zgcd_div_mult_lft qn qd).
   rewrite H.
   apply Zmult_0_l.
  intro H0; destruct (Zgcd_zero _ _ H0); discriminate.
 reflexivity.
Qed.

Lemma nth_coeff_Q_can_num_poly_spec : forall P n, nth_coeff n (Q_can_num_poly P) = Q_can_num (nth_coeff n P).
Proof.
 intro P; pattern P; apply Ccpoly_induc; clear P.
  simpl; unfold Q_can_num.
  rewrite Zdiv_0_l; reflexivity.
 destruct n.
  reflexivity.
 rewrite Q_can_num_poly_linear.
 rewrite coeff_Sm_lin.
 rewrite H.
 apply Q_can_num_spec.
 symmetry; apply coeff_Sm_lin.
Qed.

Lemma injZ_strext : fun_strext (inject_Z : Z_as_CRing -> Q_as_CRing).
Proof.
 intros x y.
 unfold inject_Z; simpl; unfold Qap, Qeq, ap_Z; simpl.
 rewrite Zmult_1_r Zmult_1_r; tauto.
Qed.
Lemma injZ_spec : forall q : Q_as_CRing, in_Z q -> q [=] (Q_can_num q).
Proof.
 unfold in_Z.
 intros q Hin.
 destruct q as [qn qd].
 unfold inject_Z.
 simpl; unfold Qeq; simpl.
 rewrite Zmult_1_r.
 unfold Q_can_num; simpl.
 unfold Q_can_den in Hin.
 simpl in Hin.
 cut (Zpos qd = Zgcd qn qd).
  intro H; rewrite {2} H.
  rewrite Zmult_comm.
  symmetry; apply Zdivides_spec.
  apply Zgcd_is_divisor_lft.
 rewrite {1} (Zgcd_div_mult_rht qn qd).
  rewrite Hin; rewrite Zmult_1_l; reflexivity.
 intro H; destruct (Zgcd_zero _ _ H); discriminate.
Qed.
Lemma injZ_spec2 : forall p : Z_as_CRing, p = Q_can_num p.
Proof.
 intro p.
 unfold Q_can_num, inject_Z; simpl.
 rewrite Zgcd_one_rht Zdiv_1_r; reflexivity.
Qed.
Definition injZ_fun := Build_CSetoid_fun _ _ _ injZ_strext.

Lemma injZ_pres_plus : fun_pres_plus _ _ injZ_fun.
Proof.
 intros x y.
 simpl; unfold inject_Z, Qeq; simpl.
 ring.
Qed.
Lemma injZ_pres_unit : fun_pres_unit _ _ injZ_fun.
Proof.
 unfold fun_pres_unit; simpl; unfold inject_Z, Qeq.
 simpl; reflexivity.
Qed.
Lemma injZ_pres_mult : fun_pres_mult _ _ injZ_fun.
Proof.
 intros x y.
 simpl; unfold inject_Z, Qeq; simpl.
 ring.
Qed.
Definition injZ_rh := Build_RingHom _ _ _ injZ_pres_plus injZ_pres_mult injZ_pres_unit.
Definition zx2qx := cpoly_map injZ_rh.

Lemma zx2qx_zero : zx2qx Zero = Zero.
Proof. reflexivity. Qed.
Lemma zx2qx_linear : forall c P, zx2qx (c[+X*]P) = (c:Q_as_CRing)[+X*]zx2qx P.
Proof. reflexivity. Qed.

Lemma nth_coeff_zx2qx : forall P n, nth_coeff n (zx2qx P) [=] nth_coeff n P.
Proof.
 intro P; pattern P; apply Ccpoly_induc; clear P.
  reflexivity.
 intros P c Hrec n.
 rewrite zx2qx_linear.
 induction n.
  reflexivity.
 rewrite coeff_Sm_lin coeff_Sm_lin.
 apply Hrec.
Qed.

Lemma zx2qx_spec : forall P : QX, in_ZX P -> P [=] zx2qx (Q_can_num_poly P).
Proof.
 intros P Hin.
 apply all_nth_coeff_eq_imp.
 intro n.
 set (Hin n).
 rewrite nth_coeff_zx2qx.
 rewrite (injZ_spec _ i).
 unfold inject_Z; simpl; unfold Qeq; simpl.
 rewrite Zmult_1_r Zmult_1_r.
 symmetry; apply nth_coeff_Q_can_num_poly_spec.
Qed.

Lemma Zlcm_den_poly_spec0 : forall P n, nth_coeff n (_C_ (Zlcm_den_poly P:Q_as_CRing) [*] P) [=] Qmake (Zlcm_den_poly P * Qnum (nth_coeff n P)) (Qden (nth_coeff n P)).
Proof.
 intros P n.
 rewrite nth_coeff_c_mult_p.
 simpl.
 generalize (Zlcm_den_poly P), (nth_coeff n P); clear; intros z q.
 destruct q as [qn qd]; simpl.
 unfold Qmult; simpl.
 reflexivity.
Qed.

Lemma Zlcm_den_poly_spec : forall P,
  in_ZX (_C_ (Zlcm_den_poly P:Q_as_CRing) [*] P).
Proof.
 intros P n.
 unfold in_Z.
 case (le_lt_dec n (QX_deg P)).
  transitivity (Q_can_den ((Qmake (Zlcm_den_poly P) xH) [*] nth_coeff n P)).
   apply Q_can_den_spec.
   apply nth_coeff_c_mult_p.
  simpl; unfold Qmult; simpl.
  rewrite den_1_div_iff.
  unfold Qmult; simpl.
  unfold Zlcm_den_poly.
  rewrite (Zgcd_div_mult_rht (Qnum (nth_coeff n P)) (Qden (nth_coeff n P)));
    try (intro H0; destruct (Zgcd_zero _ _ H0); discriminate).
  fold (Q_can_den (nth_coeff n P)).
  apply Zdivides_mult_elim; try apply Zgcd_is_divisor_lft.
  apply Zlcm_gen_spec.
  apply den_list_spec; assumption.
 intros Hgt.
 cut (nth_coeff n (_C_ (Zlcm_den_poly P:Q_as_CRing)[*]P) [=] Zero).
  intro Heq.
  transitivity (Q_can_den Zero).
   apply Q_can_den_spec; assumption.
  rewrite Q_can_den_pos_val_spec; reflexivity.
 case (RX_dec _ Q_dec P Zero).
  intro H.
  transitivity (nth_coeff n (Zero:QX)).
   apply nth_coeff_wd.
   rewrite {2} H.
   apply I.
  reflexivity.
 intro Hap.
 rewrite nth_coeff_c_mult_p.
 cut (nth_coeff n P [=] Zero).
  intro H; rewrite H; ring.
 cut (degree_le (QX_deg P) P).
  intro H; apply H; assumption.
 destruct (RX_deg_spec _ Q_dec P); assumption.
Qed.

Definition qx2zx (P : QX) : ZX := Q_can_num_poly (_C_ (Zlcm_den_poly P:Q_as_CRing) [*] P).

Lemma qx2zx_spec : forall P, zx2qx (qx2zx P) [=] _C_ (Zlcm_den_poly P:Q_as_CRing) [*] P.
Proof.
 intro P.
 unfold qx2zx.
 symmetry; apply zx2qx_spec.
 apply Zlcm_den_poly_spec.
Qed.

End Z_Q.
