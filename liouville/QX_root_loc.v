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
Require Import CRing_Homomorphisms.
Require Import Qring.
Require Import Zring.
Require Import Qordfield.

Require Import RingClass CRingClass.
Require Import Zlcm Q_can nat_Q_lists RX_deg QX_ZX.

Section QX_root.

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

Lemma Sum0_ring_hom : forall R S (phi : RingHom R S) f n,
  phi (Sum0 n f) [=] Sum0 n (fun i => phi (f i)).
Proof.
 intros.
 induction n; [apply rh_pres_zero|].
 simpl; rewrite -> rh_pres_plus, IHn; reflexivity.
Qed.

Lemma Sum_ring_hom : forall R S (phi : RingHom R S) f i j,
  phi (Sum i j f) [=] Sum i j (fun i => phi (f i)).
Proof.
 intros; unfold Sum, Sum1; simpl.
 rewrite -> rh_pres_minus, rh_pres_plus.
 rewrite -> Sum0_ring_hom, Sum0_ring_hom; reflexivity.
Qed.

Lemma nexp_ring_hom : forall R S (phi : RingHom R S) a n, phi (a[^]n) [=] phi a[^]n.
Proof.
 intros; induction n; [apply rh_pres_unit|].
 rewrite <- nexp_Sn, <- nexp_Sn; rewrite -> rh_pres_mult, IHn; reflexivity.
Qed.

Lemma Q_Z_nexp : forall (p : Z_as_CRing) (q : positive) i, ((p#q)[^]i[*](q:Q_as_CRing)[^]i [=] p[^]i)%Q.
Proof.
 intros p q.
 induction i.
  reflexivity.
 rewrite <- nexp_Sn, <- nexp_Sn, <- nexp_Sn.
 rewrite -> (mult_commutes _ (p#q)%Q).
 rewrite <- CRings.mult_assoc.
 rewrite -> (mult_commutes _ (p#q)%Q).
 rewrite -> (mult_commutes _ (q:Q_as_CRing)).
 rewrite -> CRings.mult_assoc.
 rewrite -> CRings.mult_assoc.
 rewrite -> IHi.
 rewrite (mult_commutes _ p).
 rewrite <- CRings.mult_assoc.
 apply (mult_wdr _ (inject_Z ((p:Z_as_CRing)[^]i)) ((q:Q_as_CRing)[*](p # q)%Q) p).
 simpl; unfold Qeq; simpl.
 case p.
   rewrite Zmult_0_l, Zmult_0_l; reflexivity.
  intro r; rewrite Zmult_1_r; rewrite Zmult_comm; reflexivity.
 intro r; rewrite Zmult_1_r; rewrite Zmult_comm; reflexivity.
Qed.

Lemma Q_Z_poly_apply : forall (P : ZX) (p : Z_as_CRing) (q : positive), let n := ZX_deg P in
  (q:Q_as_CRing)[^]n [*] (zx2qx P) ! (p # q)%Q [=] Sum 0 n (fun i => (nth_coeff i P) [*] p [^] i [*] (q : Z_as_CRing)[^](n - i)).
Proof.
 intros P p q n.
 assert (degree_le n (zx2qx P)).
  case (ZX_dec P [0]).
   intro H; apply (degree_le_wd _ (_C_ [0])).
    rewrite -> H; split; [reflexivity|apply I].
   apply (degree_le_mon _ _ 0).
    apply Nat.le_0_l.
   apply degree_le_c_.
  intro Hap.
  destruct (RX_deg_spec _ Z_dec _ Hap).
  clear c; fold (ZX_deg P) in d; fold n in d.
  intros m Hlt.
  rewrite -> nth_coeff_zx2qx.
  rewrite d; [reflexivity|assumption].
 rewrite -> (poly_as_sum _ _ _ H).
 rewrite <- mult_distr_sum_lft.
 rewrite -> (Sum_ring_hom _ _ injZ_rh).
 apply Sum_wd'.
  apply Nat.le_0_l.
 intros i H0 Hn.
 rewrite -> nth_coeff_zx2qx.
 rewrite -> rh_pres_mult.
 rewrite -> rh_pres_mult.
 rewrite -> mult_commutes.
 rewrite -> nexp_ring_hom, nexp_ring_hom.
 rewrite <- CRings.mult_assoc, <- CRings.mult_assoc.
 apply mult_wdr.
 rewrite <- (Nat.sub_add _ _ Hn) at 1.
 rewrite Nat.add_comm.
 clear H0 Hn.
 rewrite <- nexp_plus.
 rewrite -> CRings.mult_assoc.
 apply mult_wdl.
 simpl (injZ_rh p).
 rewrite -> (Q_Z_nexp p q i).
 apply (nexp_ring_hom _ _ injZ_rh).
Qed.

Lemma RX_deg_cmult_p : forall P a, a [#] [0] -> QX_deg (_C_ a [*] P) = QX_deg P.
Proof.
 intros P a Hap.
 case (QX_dec P [0]).
  intro; apply RX_deg_wd.
  rewrite -> s; ring.
 intro HapP.
 apply (degree_inj _ (_C_ a [*] P)).
  case (QX_dec (_C_ a[*]P) [0]).
   intro Heq; destruct (ap_imp_neq _ _ _ HapP); clear HapP.
   apply all_nth_coeff_eq_imp.
   intro i; generalize (nth_coeff_wd _ i _ _ Heq).
   rewrite -> nth_coeff_c_mult_p.
   fold QX; simpl (nth_coeff i ([0]:QX)).
   intro Heq2; apply (mult_eq_zero _ a); [apply Hap|assumption].
  apply RX_deg_spec.
 destruct (RX_deg_spec _ Q_dec _ HapP).
 split.
  intro.
  destruct c.
  rewrite -> nth_coeff_c_mult_p in H.
  apply (mult_eq_zero _ _ _ Hap H).
 intros m Hlt.
 rewrite -> nth_coeff_c_mult_p.
 rewrite -> (d m Hlt); ring.
Qed.

Lemma den_div_Pn0 : forall (Q : ZX) (n : nat) (p q : Z_as_CRing),
      Sum 0 n (fun i : nat => nth_coeff i Q[*]p[^]i[*]q[^](n - i))[=][0] ->
      Zdivides q (nth_coeff n Q[*]p[^]n).
Proof.
 clear QX QX_dec QX_deg.
 intros P n p q.
 destruct n.
  rewrite -> Sum_one.
  simpl.
  rewrite Zmult_1_r; intro H; rewrite H.
  apply Zdivides_zero_rht.
 rewrite -> Sum_last.
 rewrite Nat.sub_diag.
 simpl (q[^]0).
 rewrite -> mult_one.
 generalize (nth_coeff (S n) P[*]p[^]S n); intro r.
 exists ([--](Sum 0 n (fun i : nat => nth_coeff i P[*]p[^]i[*]q[^](n - i)))).
 rewrite Zopp_mult_distr_l_reverse.
 symmetry; apply (cg_inv_unique Z_as_CRing).
 rewrite <- H.
 apply cs_bin_op_wd; [|reflexivity].
 rewrite <- (mult_distr_sum_rht Z_as_CRing).
 apply Sum_wd'.
  apply Nat.le_0_l.
 intros i H0 Hn.
 rewrite <- CRings.mult_assoc.
 apply mult_wd.
  reflexivity.
 rewrite Nat.sub_succ_l; [|assumption].
 reflexivity.
Qed.

Lemma qx2zx_deg : forall P, QX_deg P = ZX_deg (qx2zx P).
Proof.
 intro P; unfold qx2zx.
 rewrite <- Q_can_num_poly_deg_eq.
 symmetry; apply RX_deg_cmult_p.
 intro; apply (Zlcm_den_poly_nz P).
 rewrite (injZ_spec2 (Zlcm_den_poly P)).
 revert H; generalize (inject_Z (Zlcm_den_poly P)); clear.
 intro q; destruct q as [qn qd].
 unfold Qeq, Q_can_num; simpl.
 rewrite Zmult_1_r; intro H; rewrite H.
 compute; reflexivity.
Qed.

Let Pn (P : QX) := nth_coeff (QX_deg P) (qx2zx P).

Lemma den_div_Pn1 : forall (P : QX) (a : Q_as_CRing), P ! a [=] [0] ->
                   Zdivides (Qden a) (Pn P[*](Qnum a:Z_as_CRing)[^]QX_deg P).
Proof.
 intros P a Hval.
 set (P0 := _C_ (Zlcm_den_poly P:Q_as_CRing)[*]P).
 assert (H : P0 ! a [=] [0]).
  unfold P0; rewrite -> mult_apply, c_apply, Hval; ring.
 clear Hval; revert H.
 rewrite -> (zx2qx_spec P0); [|apply Zlcm_den_poly_spec].
 unfold P0; clear P0.
 destruct a as [p q]; unfold Qnum, Qden.
 set (Q := qx2zx P).
 intro Hval.
 assert ((q:Q_as_CRing)[^](ZX_deg Q) [*] (zx2qx Q) ! (p # q)%Q [=] [0]).
  unfold Q.
  rewrite -> Hval; ring.
 assert (Q_can_num ((q:Q_as_CRing)[^](ZX_deg Q) [*] (zx2qx Q) ! (p # q)%Q) [=] [0]).
  rewrite (Q_can_num_spec _ _ H).
  unfold Q_can_num; simpl.
  rewrite Zgcd_one_rht, Zdiv_0_l; reflexivity.
 clear Hval H; revert H0.
 rewrite (Q_can_num_spec _ _ (Q_Z_poly_apply _ _ _)).
 rewrite <- injZ_spec2.
 assert (ZX_deg Q = QX_deg P).
  symmetry; apply qx2zx_deg.
 assert (nth_coeff (QX_deg P) (qx2zx P) = nth_coeff (QX_deg P) Q).
  reflexivity.
 unfold Q.
 unfold Pn; rewrite H0.
 rewrite <- H; clear H H0.
 apply den_div_Pn0.
Qed.

Lemma Zrelprime_nexp : forall (p q : Z_as_CRing) n, Zrelprime p q -> Zrelprime p (q[^]n).
Proof.
 intros p q n; intro H.
 induction n.
  apply Zgcd_one_rht.
 rewrite <- nexp_Sn.
 apply Zrelprime_symm.
 apply Zrelprime_mult_elim_lft.
  apply Zrelprime_symm; assumption.
 apply Zrelprime_symm; assumption.
Qed.

Lemma den_div_Pn : forall (P : QX) (a : Q_as_CRing), P ! a [=] [0] ->
                   Zdivides (Q_can_den a) (Pn P).
Proof.
 intros P a Hval.
 rewrite Q_can_den_pos_val_spec.
 apply (Zrelprime_div_mult_intro _ ((Q_can_num a:Z_as_CRing)[^]QX_deg P)).
  apply Zrelprime_nexp.
  apply Zrelprime_symm.
  apply (Q_can_spec2 a).
 rewrite Zmult_comm.
 apply (den_div_Pn1 _ (Q_can a)).
 rewrite <- Hval.
 apply cpoly_apply_wd; [reflexivity|].
 symmetry; apply Q_can_spec.
Qed.

Lemma Sum_shift_simpl : forall (G : CAbGroup) (f : nat -> G) m n,
         Sum (S m) (S n) f [=] Sum m n (fun i => f (S i)).
Proof.
 intros G f m n.
 symmetry; apply Sum_shift.
 intro; reflexivity.
Qed.

Lemma den_div_P00 : forall (Q : ZX) (n : nat) (p q : Z_as_CRing),
      Sum 0 n (fun i : nat => nth_coeff i Q[*]p[^]i[*]q[^](n - i))[=][0] ->
      Zdivides p (nth_coeff 0 Q[*]q[^]n).
Proof.
 clear Pn QX QX_dec QX_deg.
 intros P n p q.
 destruct n.
  rewrite -> Sum_one.
  simpl.
  rewrite Zmult_1_r; intro H; rewrite H.
  apply Zdivides_zero_rht.
 rewrite -> Sum_first.
 rewrite -> Sum_shift_simpl.
 simpl (p[^]0).
 rewrite -> mult_one.
 simpl (S n - 0).
 generalize (nth_coeff 0 P[*]q[^]S n); intro r.
 exists ([--](Sum 0 n (fun i : nat => nth_coeff (S i) P[*]p[^]i[*]q[^](n - i)))).
 rewrite Zopp_mult_distr_l_reverse.
 symmetry; apply (cg_inv_unique Z_as_CRing).
 rewrite <- H.
 rewrite -> cag_commutes.
 apply cs_bin_op_wd; [reflexivity|].
 rewrite <- (mult_distr_sum_rht Z_as_CRing).
 apply Sum_wd'.
  apply Nat.le_0_l.
 intros i H0 Hn.
 rewrite <- nexp_Sn.
 simpl (S n - S i).
 ring.
Qed.

Let P0 (P : QX) := nth_coeff 0 (qx2zx P).

Lemma den_div_P01 : forall (P : QX) (a : Q_as_CRing), P ! a [=] [0] ->
                   Zdivides (Qnum a) (P0 P[*](Qden a:Z_as_CRing)[^]QX_deg P).
Proof.
 intros P a Hval.
 set (Q := _C_ (Zlcm_den_poly P:Q_as_CRing)[*]P).
 assert (H : Q ! a [=] [0]).
  unfold Q; rewrite -> mult_apply, c_apply, Hval; ring.
 clear Hval; revert H.
 rewrite -> (zx2qx_spec Q); [|apply Zlcm_den_poly_spec].
 unfold Q; clear Q.
 destruct a as [p q]; unfold Qnum, Qden.
 set (Q := qx2zx P).
 intro Hval.
 assert ((q:Q_as_CRing)[^](ZX_deg Q) [*] (zx2qx Q) ! (p # q)%Q [=] [0]).
  unfold Q.
  rewrite -> Hval; ring.
 assert (Q_can_num ((q:Q_as_CRing)[^](ZX_deg Q) [*] (zx2qx Q) ! (p # q)%Q) [=] [0]).
  rewrite (Q_can_num_spec _ _ H).
  unfold Q_can_num; simpl.
  rewrite Zgcd_one_rht, Zdiv_0_l; reflexivity.
 clear Hval H; revert H0.
 rewrite (Q_can_num_spec _ _ (Q_Z_poly_apply _ _ _)).
 rewrite <- injZ_spec2.
 assert (ZX_deg Q = QX_deg P).
  symmetry; apply qx2zx_deg.
 assert (nth_coeff 0 (qx2zx P) = nth_coeff 0 Q).
  reflexivity.
 unfold Q.
 unfold P0; rewrite H0.
 rewrite <- H; clear H H0.
 apply den_div_P00.
Qed.

Lemma den_div_P0 : forall (P : QX) (a : Q_as_CRing), P ! a [=] [0] ->
                   Zdivides (Q_can_num a) (P0 P).
Proof.
 intros P a Hval.
 apply (Zrelprime_div_mult_intro _ ((Q_can_den a:Z_as_CRing)[^]QX_deg P)).
  apply Zrelprime_nexp.
  rewrite Q_can_den_pos_val_spec.
  apply (Q_can_spec2 a).
 rewrite Zmult_comm.
 rewrite Q_can_den_pos_val_spec.
 apply (den_div_P01 _ (Q_can a)).
 rewrite <- Hval.
 apply cpoly_apply_wd; [reflexivity|].
 symmetry; apply Q_can_spec.
Qed.

Lemma QX_root_loc : forall (P : QX) (a : Q_as_CRing), P ! [0] [#] [0] -> P ! a [=] [0] ->
      In (Q_can a) (list_Q (P0 P) (Pn P)).
Proof.
 intros P a Hap Hval.
 apply list_Q_spec.
    intro; apply Hap; clear Hap.
    unfold P0 in H.
    cut ((_C_ (Zlcm_den_poly P:Q_as_CRing) [*] P) ! [0] [=] [0]).
     rewrite -> mult_apply, c_apply.
     intro H0; apply (Qmult_integral_l (Zlcm_den_poly P)); [|assumption].
     intro H1; destruct (Zlcm_den_poly_nz P).
     unfold Qeq in H1; simpl in H1.
     rewrite Zmult_1_r in H1; assumption.
    cut ((zx2qx (qx2zx P)) ! [0] [=] [0]).
     rewrite -> qx2zx_spec; tauto.
    unfold zx2qx.
    rewrite <- (rh_pres_zero _ _ injZ_rh) at 1.
    rewrite <- cpoly_map_apply.
    cut ((qx2zx P) ! [0] [=] [0]).
     intro H0; rewrite H0; reflexivity.
    rewrite -> poly_at_zero; assumption.
   case (QX_dec P [0]).
    intro H; destruct Hap; rewrite -> H; reflexivity.
   intros Hap2 Heq; apply (ap_imp_neq _ _ _ Hap2); clear Hap Hval; revert Heq.
   unfold Pn.
   destruct (RX_deg_spec _ Z_dec (qx2zx P)); [|].
    case (ZX_dec (qx2zx P) [0]); [|tauto].
    intro Heq; destruct (ap_imp_neq _ _ _ Hap2); clear Hap2.
    cut (_C_(Zlcm_den_poly P:Q_as_CRing) [*] P [=] [0]).
     intro Heq2; apply all_nth_coeff_eq_imp; intro i.
     apply (Qmult_integral_l (Zlcm_den_poly P)).
      intro H1; destruct (Zlcm_den_poly_nz P).
      unfold Qeq in H1; simpl in H1.
      rewrite Zmult_1_r in H1; assumption.
     generalize (nth_coeff_wd _ i _ _ Heq2).
     rewrite -> nth_coeff_c_mult_p.
     simpl; tauto.
    rewrite <- qx2zx_spec.
    rewrite -> Heq.
    apply (rh_pres_zero _ _ zx2qx).
   intro H; destruct c; fold (ZX_deg (qx2zx P)).
   rewrite <- qx2zx_deg; assumption.
  apply den_div_P0; assumption.
 rewrite inj_Zabs_nat.
 rewrite <- Q_can_den_pos_val_spec.
 apply Zdivides_abs_elim_lft.
 apply den_div_Pn; assumption.
Qed.

End QX_root.
