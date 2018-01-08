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
Require Import CRings Zring.

Section Zgcd_lin.

Lemma Z_dec : forall x y : Z_as_CRing, x [=] y or x [#] y.
Proof.
 intros x y; case (Z_eq_dec x y).
  left; assumption.
 right; assumption.
Qed.

Lemma Zgcd_lin : forall a b c, (Zabs c * Zgcd a b = Zgcd (c * a) (c * b))%Z.
Proof.
 intros a b c.
 case (Z_eq_dec a 0).
  intro H; rewrite H; rewrite Zmult_0_r, Zgcd_zero_lft, Zgcd_zero_lft; apply Zabs_mult_compat.
 intro Ha; case (Z_eq_dec b 0).
  intro H; rewrite H; rewrite Zmult_0_r, Zgcd_zero_rht, Zgcd_zero_rht; apply Zabs_mult_compat.
 intro Hb; case (Z_eq_dec c 0).
  intro H; rewrite H; rewrite Zmult_0_l, Zmult_0_l, Zmult_0_l, Zgcd_zero_lft; reflexivity.
 intro Hc; apply Zdivides_antisymm.
    rewrite <- (Zmult_0_r (Zabs c)).
    apply Zmult_pos_mon_lt_lft.
     apply Zlt_gt.
     apply Zgcd_pos.
     left; assumption.
    destruct c; [destruct Hc| |]; reflexivity.
   apply Zlt_gt.
   apply Zgcd_pos.
   left.
   intro H0; destruct (Zmult_zero_div _ _ H0).
    destruct Hc; assumption.
   destruct Ha; assumption.
  apply Zdiv_gcd_elim.
   apply Zdivides_mult_elim.
    apply Zdivides_abs_elim_lft.
    apply Zdivides_ref.
   apply Zgcd_is_divisor_lft.
  apply Zdivides_mult_elim.
   apply Zdivides_abs_elim_lft.
   apply Zdivides_ref.
  apply Zgcd_is_divisor_rht.
 cut (forall c : positive, Zdivides (Zgcd (c * a) (c * b)) (Zabs c * Zgcd a b)).
  intro H; case c.
    simpl; rewrite Zgcd_zero_lft; apply Zdivides_ref.
   apply H.
  intro p; rewrite Zgcd_abs.
  rewrite <- Zabs_mult_compat, <- Zabs_mult_compat.
  simpl (Zabs (Zneg p)).
  assert ((p:Z) = Zabs p).
   reflexivity.
  rewrite H0; clear H0.
  rewrite Zabs_mult_compat, Zabs_mult_compat.
  rewrite <- Zgcd_abs.
  apply H.
 clear c Hc; intro c.
 rewrite (Zgcd_lin_comb a b).
 rewrite Zmult_plus_distr_r.
 simpl (Zabs c).
 rewrite Zmult_assoc, Zmult_assoc.
 rewrite (Zmult_comm c (Zgcd_coeff_a a b)).
 rewrite (Zmult_comm c (Zgcd_coeff_b a b)).
 rewrite <- Zmult_assoc, <- Zmult_assoc.
 apply Zdivides_plus_elim.
  apply Zdivides_mult_elim_lft.
  apply Zgcd_is_divisor_lft.
 apply Zdivides_mult_elim_lft.
 apply Zgcd_is_divisor_rht.
Qed.

End Zgcd_lin.

Definition Zlcm (a b : Z_as_CRing) : Z_as_CRing := Zdiv (a [*] b) (Zgcd a b).

Lemma Zlcm_specl : forall a b : Z_as_CRing, Zdivides a (Zlcm a b).
Proof.
 intros a b.
 unfold Zlcm.
 case (Z_eq_dec (Zgcd a b) ([0]:Z_as_CRing)).
  intro H; rewrite H; simpl.
  rewrite Zdiv_0_r.
  apply Zdivides_zero_rht.
 intro H; rewrite -> (Zgcd_div_mult_rht a b) at 1; [|assumption].
 simpl.
 rewrite Zmult_assoc.
 rewrite Z_div_mult_full; [|assumption].
 apply Zdivides_mult_rht.
Qed.

Lemma Zlcm_specr : forall a b : Z_as_CRing, Zdivides b (Zlcm a b).
Proof.
 intros a b.
 unfold Zlcm.
 case (Z_eq_dec (Zgcd a b) ([0]:Z_as_CRing)).
  intro H; rewrite H; simpl.
  rewrite Zdiv_0_r.
  apply Zdivides_zero_rht.
 intro H; rewrite -> (Zgcd_div_mult_lft a b) at 1; [|assumption].
 simpl.
 rewrite Zmult_comm.
 rewrite Zmult_assoc.
 rewrite Z_div_mult_full; [|assumption].
 apply Zdivides_mult_rht.
Qed.

Lemma Zlcm_spec : forall a b c : Z_as_CRing, Zdivides a c -> Zdivides b c -> Zdivides (Zlcm a b) c.
Proof.
 intros a b c Hac Hbc; unfold Zlcm; simpl.
 case (Z_eq_dec (Zgcd a b) ([0]:Z_as_CRing)).
  intro H; rewrite H; simpl.
  destruct (Zgcd_zero _ _ H).
  rewrite H0 in Hac; clear H H0 H1.
  rewrite Zdiv_0_r; assumption.
 case (Z_eq_dec c ([0]:Z_as_CRing)).
  intro Hc; rewrite Hc.
  intro Hap; apply Zdivides_zero_rht.
 intros Hc Hap.
 apply Zdivides_abs_intro_rht.
 rewrite <- (Zmult_1_r (Zabs c)).
 rewrite <- (Zgcd_div_gcd_1 a b); [|assumption].
 rewrite Zgcd_lin.
 apply Zdiv_gcd_elim.
  cut (a * b / Zgcd a b = b * (a / Zgcd a b))%Z.
   intro H; rewrite H; clear H.
   apply Zdivides_mult_cancel_rht.
   assumption.
  rewrite Zmult_comm.
  apply (Zmult_reg_r _ _ (Zgcd a b) Hap).
  rewrite <- Zmult_assoc.
  rewrite <- (Zgcd_div_mult_lft _ _ Hap).
  rewrite Zmult_comm.
  rewrite <- (Z_div_exact_full_2 _ _ Hap).
   reflexivity.
  apply Zmod0_Zdivides.
   apply Hap.
  apply Zdivides_mult_elim_lft.
  apply Zgcd_is_divisor_lft.
 cut (a * b / Zgcd a b = a * (b / Zgcd a b))%Z.
  intro H; rewrite H; clear H.
  apply Zdivides_mult_cancel_rht.
  assumption.
 apply (Zmult_reg_r _ _ (Zgcd a b) Hap).
 rewrite <- Zmult_assoc.
 rewrite <- (Zgcd_div_mult_rht _ _ Hap).
 rewrite Zmult_comm.
 rewrite <- (Z_div_exact_full_2 _ _ Hap).
  reflexivity.
 apply Zmod0_Zdivides.
  apply Hap.
 apply Zdivides_mult_elim_lft.
 apply Zgcd_is_divisor_rht.
Qed.

Lemma Zlcm_zero : forall p q, Zlcm p q [=] [0] -> p [=] [0] or q [=] [0].
Proof.
 intros p q; unfold Zlcm; intro Heq.
 case (Z_eq_dec p ([0]:Z_as_CRing)).
  left; assumption.
 intro Happ; right.
 simpl in *.
 unfold ap_Z in Happ.
 apply (Zmult_integral_l _ _ Happ).
 rewrite Zmult_comm.
 revert Heq.
 assert (Zgcd p q <> 0%Z).
  intro H; destruct Happ; apply (Zgcd_zero _ _ H).
 rewrite -> (Zgcd_div_mult_lft p q) at 1; [|assumption].
 rewrite (Zmult_comm (p / Zgcd p q)).
 rewrite <- Zmult_assoc.
 rewrite Zdiv_mult_cancel_lft; [|assumption].
 intro Heq.
 rewrite (Zgcd_div_mult_lft p q); [|assumption].
 rewrite <- Zmult_assoc, (Zmult_comm _ q), Zmult_assoc.
 rewrite Heq, Zmult_0_l; reflexivity.
Qed.

Fixpoint Zlcm_gen (l : list Z_as_CRing) : Z_as_CRing :=
  match l with
    | nil => [1]
    | h::q => Zlcm h (Zlcm_gen q)
  end.

Lemma Zlcm_gen_spec : forall l x, In x l -> Zdivides x (Zlcm_gen l).
Proof.
 induction l.
  intros x Hin; destruct Hin.
 intros x Hin; destruct Hin.
  rewrite <- H; clear H.
  apply Zlcm_specl.
 fold (In x l) in H.
 simpl.
 apply (Zdivides_trans _ _ _ (IHl _ H)).
 apply Zlcm_specr.
Qed.

Lemma Zlcm_gen_spec2 : forall l x, (forall y, In y l -> Zdivides y x) -> Zdivides (Zlcm_gen l) x.
Proof.
 induction l.
  intros; apply Zdivides_one.
 intros x H; apply Zlcm_spec.
  apply H; left; reflexivity.
 fold (Zlcm_gen l).
 apply IHl.
 intros y Hin; apply H.
 right; assumption.
Qed.

Lemma Zdivides_spec : forall (a b : Z), Zdivides a b -> (a * (b / a) = b)%Z.
Proof.
 intros a b Hdiv.
 case (Z_eq_dec a 0).
  intro H; rewrite H; simpl.
  symmetry; apply Zdivides_zero_lft; rewrite <- H; assumption.
 intro  Hap.
 rewrite <- Z_div_exact_full_2.
   reflexivity.
  assumption.
 case (Z_eq_dec a 0).
  intro H; rewrite H; simpl; apply Zmod_0_r.
 intro H; clear H.
 apply Zmod0_Zdivides; assumption.
Qed.

Lemma Zlcm_gen_nz : forall l, (forall x, In x l -> x [#] [0]) -> Zlcm_gen l [#] [0].
Proof.
 induction l.
  intro; intro; discriminate.
 simpl.
 intros H1 H2; simpl.
 destruct (Zlcm_zero a (Zlcm_gen l) H2).
  apply (H1 a); [left; reflexivity|assumption].
 destruct IHl; [|assumption].
 intros; apply H1; right; assumption.
Qed.

