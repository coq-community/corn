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

Require Import CRings Qring Zring.
Require Import Zlcm.

Section Q_can.

Lemma Q_dec : forall x y : Q_as_CRing, (x [=] y) or (x [#] y).
Proof. intros x y; case (dec_Qeq x y); [left|right]; assumption. Qed.
Definition Q_can_num (q : Q_as_CRing) : Z_as_CRing := Zdiv (Qnum q) (Zgcd (Qnum q) (Qden q)).

Lemma Q_can_num_spec : forall q q', q [=] q' -> Q_can_num q = Q_can_num q'.
Proof.
intros q q'.
unfold Q_can_num.
destruct q as [qn qd]; destruct q' as [q'n q'd].
simpl; unfold Qeq; simpl.
intro Heq.
apply (Zmult_reg_l _ _ (Zgcd qn qd * Zgcd q'n q'd)).
  intro; destruct (Zmult_integral _ _ H); destruct (Zgcd_zero _ _ H0); discriminate.
rewrite -> (Zmult_comm (Zgcd qn qd)) at 1.
rewrite <- Zmult_assoc, <- Zmult_assoc.
rewrite -> (Zmult_comm (Zgcd qn qd)) at 1.
rewrite -> (Zmult_comm (Zgcd q'n q'd) (q'n / Zgcd q'n q'd)).
rewrite <- Zgcd_div_mult_lft, <- Zgcd_div_mult_lft;
    try (intro H; destruct (Zgcd_zero _ _ H); discriminate).
rewrite Zmult_comm (Zmult_comm _ q'n).
rewrite <- (Zabs_Zsgn qn) at 1; rewrite <- (Zabs_Zsgn q'n) at 2.
rewrite (Zmult_comm (Zabs qn)) (Zmult_comm (Zabs q'n)).
rewrite <- Zmult_assoc, <- Zmult_assoc.
rewrite Zgcd_lin Zgcd_lin.
rewrite Heq.
rewrite (Zmult_comm qn q'n).
cut (Zsgn qn = Zsgn q'n).
  intro H; rewrite H; reflexivity.
destruct qn; destruct q'n; reflexivity||discriminate.
Qed.

Definition Q_can_den (q : Q_as_CRing) : Z_as_CRing := Zdiv (Qden q) (Zgcd (Qnum q) (Qden q)).

Lemma Q_can_den_spec : forall q q', q [=] q' -> Q_can_den q = Q_can_den q'.
Proof.
intros q q'.
unfold Q_can_den.
destruct q as [qn qd]; destruct q' as [q'n q'd].
simpl; unfold Qeq; simpl.
intro Heq.
apply (Zmult_reg_l _ _ (Zgcd qn qd * Zgcd q'n q'd)).
  intro; destruct (Zmult_integral _ _ H); destruct (Zgcd_zero _ _ H0); discriminate.
rewrite -> (Zmult_comm (Zgcd qn qd)) at 1.
rewrite <- Zmult_assoc, <- Zmult_assoc.
rewrite -> (Zmult_comm (Zgcd qn qd)) at 1.
rewrite (Zmult_comm (Zgcd q'n q'd) (q'd / Zgcd q'n q'd)).
rewrite <- Zgcd_div_mult_rht, <- Zgcd_div_mult_rht;
    try (intro H; destruct (Zgcd_zero _ _ H); discriminate).
rewrite Zmult_comm (Zmult_comm _ q'd).
rewrite <- (Zabs_Zsgn qd) at 1; rewrite <- (Zabs_Zsgn q'd) at 2.
rewrite (Zmult_comm (Zabs qd)) (Zmult_comm (Zabs q'd)).
rewrite <- Zmult_assoc, <- Zmult_assoc.
rewrite Zgcd_lin Zgcd_lin.
rewrite (Zmult_comm qd q'n) (Zmult_comm q'd qn).
rewrite Heq.
rewrite (Zmult_comm qd q'd).
reflexivity.
Qed.

Lemma Q_can_den_pos : forall q : Q_as_CRing, (0 < Q_can_den q)%Z.
Proof.
intro q; destruct q as [qn qd]; unfold Q_can_den.
simpl.
set (Zdiv_le_lower_bound qd (Zgcd qn qd) 1).
assert (0 <= qd)%Z.
  discriminate.
assert (0 < Zgcd qn qd)%Z.
  apply Zgcd_pos.
  right.
  discriminate.
assert (1 * Zgcd qn qd <= qd)%Z.
  rewrite Zmult_1_l.
  apply Zgcd_le_rht.
  reflexivity.
set (z H H0 H1).
revert z0; generalize (qd / Zgcd qn qd)%Z; clear; intros x H.
destruct x.
    destruct H; reflexivity.
  reflexivity.
destruct H; reflexivity.
Qed.

Definition Q_can_den_pos_val (q : Q_as_CRing) : positive :=
  match (Q_can_den q) with
    | Zpos p => p
    | _ => xH
  end.

Lemma Q_can_den_pos_val_spec : forall q : Q_as_CRing, Q_can_den q = Q_can_den_pos_val q.
Proof.
intro q; set (Q_can_den_pos q).
unfold Q_can_den_pos_val.
revert z.
case (Q_can_den q).
    intro; discriminate.
  reflexivity.
intros; discriminate.
Qed.

Definition Q_can (q : Q_as_CRing) := Qmake (Q_can_num q) (Q_can_den_pos_val q).

Lemma Q_can_spec : forall q : Q_as_CRing, q [=] Q_can q.
Proof.
intro q; destruct q as [qn qd]; unfold Q_can; simpl; unfold Qeq; simpl.
rewrite <- Q_can_den_pos_val_spec.
unfold Q_can_den, Q_can_num; simpl.
assert (Zgcd qn qd <> 0).
  intro.
  destruct (Zgcd_zero _ _ H).
  discriminate.
rewrite -> (Zgcd_div_mult_lft qn qd) at 1.
  rewrite -> (Zgcd_div_mult_rht qn qd) at 6.
   ring.
  assumption.
assumption.
Qed.

Lemma Q_can_spec2 : forall q : Q_as_CRing, Zrelprime (Qnum (Q_can q)) (Qden (Q_can q)).
Proof.
intro q; destruct q as [qn qd].
unfold Q_can; simpl.
rewrite <- Q_can_den_pos_val_spec.
unfold Q_can_den, Q_can_num; simpl.
apply Zgcd_div_gcd_1.
intro.
destruct (Zgcd_zero _ _ H).
discriminate.
Qed.

Definition in_Z (q : Q_as_CRing) := Q_can_den q = 1.

End Q_can.
