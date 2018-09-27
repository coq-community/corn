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
Require Import Zring Qring Q_can.

Section nat_Q_lists.

Fixpoint list_nat (p : nat) : list nat :=
  match p with
    | O => O::nil
    | S p => S p::list_nat p
  end.

Lemma list_nat_spec : forall p a, a <= p -> In a (list_nat p).
Proof.
 intro p; induction p.
  intros a Hle; inversion Hle; left; reflexivity.
 intros a Hle; simpl.
 case (eq_nat_dec (S p) a).
  left; assumption.
 right; apply IHp.
 inversion Hle.
  destruct n; symmetry; assumption.
 assumption.
Qed.

Definition list_nat_prod (p q : nat) : list (nat * nat) :=
  list_prod (list_nat p) (list_nat q).

Lemma list_nat_prod_spec : forall p q a b,
  a <= p -> b <= q -> In (a, b) (list_nat_prod p q).
Proof.
 intros; apply in_prod; apply list_nat_spec; assumption.
Qed.

Definition nat_prod_to_Q (pq : nat * nat) : list Q_as_CRing :=
  let (p, q) := pq in
  match p with
    | O => Qmake Z0 (P_of_succ_nat q)::nil
    | S p =>
      match q with
        | O => nil
        | S q => Qmake (Zpos (P_of_succ_nat p)) (P_of_succ_nat q)::
                 Qmake (Zneg (P_of_succ_nat p)) (P_of_succ_nat q)::nil
      end
  end.

Definition list_Q (a b : Z_as_CRing) : list Q_as_CRing :=
  flat_map nat_prod_to_Q (list_nat_prod (Z.abs_nat a) (Z.abs_nat b)).

Lemma list_Q_spec_pos : forall a b c d, Z.abs_nat c <= Z.abs_nat a ->
  Z.abs_nat (Zpos d) <= Z.abs_nat b -> In (Qmake c d) (list_Q a b).
Proof.
 intros a b c d Hca Hdb.
 case (Qeq_dec (c#d)%Q [0]).
  unfold Qeq; simpl; rewrite Zmult_1_r.
  intro Heq; rewrite Heq.
  clear c Hca Heq.
  unfold list_Q.
  rewrite -> in_flat_map.
  exists (0, pred (nat_of_P d)).
  split.
   apply list_nat_prod_spec.
    apply le_O_n.
   apply (le_trans _ _ _ (le_pred_n _) Hdb).
  left.
  f_equal.
  destruct (ZL4 d).
  rewrite H.
  simpl.
  rewrite <- nat_of_P_o_P_of_succ_nat_eq_succ in H.
  apply nat_of_P_inj; symmetry; assumption.
 unfold list_Q.
 rewrite -> in_flat_map.
 exists (Z.abs_nat c, Z.abs_nat d).
 split.
  apply list_nat_prod_spec; assumption.
 simpl.
 case (ZL4 d).
 intros d' Hd'.
 unfold Z.abs_nat at 1 in Hdb.
 rewrite Hd'.
 rewrite Hd' in Hdb.
 case_eq (Z.abs_nat c).
  intro Heq.
  destruct H.
  destruct c.
    reflexivity.
   simpl in Heq; destruct (ZL4 p); rewrite Heq in H; discriminate.
  simpl in Heq; destruct (ZL4 p); rewrite Heq in H; discriminate.
 intros.
 destruct c as [|c|c].
   discriminate.
  constructor 1.
  unfold Qeq; simpl.
  assert (c = P_of_succ_nat n).
   rewrite <- nat_of_P_o_P_of_succ_nat_eq_succ in H0.
   simpl in H.
   apply nat_of_P_inj; assumption.
  rewrite H1.
  cut (P_of_succ_nat d' = d).
   intro H2; rewrite H2; reflexivity.
  apply nat_of_P_inj.
  rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
  symmetry; assumption.
 constructor 2.
 constructor 1.
 unfold Qeq; simpl.
 assert (c = P_of_succ_nat n).
  rewrite <- nat_of_P_o_P_of_succ_nat_eq_succ in H0.
  simpl in H.
  apply nat_of_P_inj; assumption.
 rewrite H1.
 cut (P_of_succ_nat d' = d).
  intro H2; rewrite H2; reflexivity.
 apply nat_of_P_inj.
 rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
 symmetry; assumption.
Qed.

Lemma list_Q_spec_neg : forall a b c d, Z.abs_nat c <= Z.abs_nat a ->
  Z.abs_nat (Zneg d) <= Z.abs_nat b -> In (Qmake c d) (list_Q a b).
Proof.
 intros a b c d.
 apply list_Q_spec_pos.
Qed.

Lemma list_Q_spec_zero : forall a b d, nat_of_P d <= Z.abs_nat b ->
  In (Qmake Z0 d) (list_Q a b).
Proof.
 intros a b d Hle.
 unfold list_Q.
 rewrite -> in_flat_map.
 exists (0, pred (nat_of_P d)).
 split.
  apply list_nat_prod_spec.
   apply le_O_n.
  apply (le_trans _ _ _ (le_pred_n _) Hle).
 left.
 f_equal.
 destruct (ZL4 d).
 rewrite H.
 simpl.
 rewrite <- nat_of_P_o_P_of_succ_nat_eq_succ in H.
 apply nat_of_P_inj; symmetry; assumption.
Qed.

Lemma div_imp_leq : forall a b : Z_as_CRing,
  b [#] [0] -> Zdivides a b -> Z.abs_nat a <= Z.abs_nat b.
Proof.
 intros a b Hap Hdiv.
 destruct Hdiv.
 rewrite <- H.
 rewrite Zabs_nat_mult.
 rewrite <- H in Hap.
 destruct x.
   destruct Hap.
   reflexivity.
  simpl.
  destruct (ZL4 p).
  rewrite H0.
  simpl.
  rewrite <- (plus_0_r (Z.abs_nat a)) at 1.
  apply plus_le_compat_l.
  apply le_O_n.
 simpl.
 destruct (ZL4 p).
 rewrite H0.
 simpl.
 rewrite <- (plus_0_r (Z.abs_nat a)) at 1.
 apply plus_le_compat_l.
 apply le_O_n.
Qed.

Lemma list_Q_spec : forall (a b : Z_as_CRing) q, a [#] [0] -> b [#] [0] ->
  Zdivides (Q_can_num q) a -> Zdivides (Z.abs_nat (Q_can_den_pos_val q)) b ->
  In (Q_can q) (list_Q a b).
Proof.
 intros a b q Hapa Hapb Ha Hb.
 destruct q as [qn qd].
 destruct qn.
   apply list_Q_spec_zero.
   revert Hb; generalize (Q_can_den_pos_val (0#qd)%Q).
   intros p Hdiv.
   assert (nat_of_P p = Z.abs_nat p).
    reflexivity.
   rewrite H; apply div_imp_leq.
    assumption.
   rewrite inj_Zabs_nat in Hdiv.
   apply Zdivides_abs_intro_lft; assumption.
  apply list_Q_spec_pos.
   apply div_imp_leq; assumption.
  apply div_imp_leq.
   assumption.
  apply Zdivides_abs_intro_lft.
  rewrite <- inj_Zabs_nat.
  assumption.
 apply list_Q_spec_neg.
  apply div_imp_leq; assumption.
 apply div_imp_leq.
  assumption.
 apply Zdivides_abs_intro_lft.
 rewrite <- inj_Zabs_nat.
 assumption.
Qed.

End nat_Q_lists.
