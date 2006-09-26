(* Copyright © 1998-2006
 * Henk Barendregt
 * Luís Cruz-Filipe
 * Herman Geuvers
 * Mariusz Giero
 * Rik van Ginneken
 * Dimitri Hendriks
 * Sébastien Hinderer
 * Bart Kirkels
 * Pierre Letouzey
 * Iris Loeb
 * Lionel Mamane
 * Milad Niqui
 * Russell O’Connor
 * Randy Pollack
 * Nickolay V. Shmyrev
 * Bas Spitters
 * Dan Synek
 * Freek Wiedijk
 * Jan Zwanenburg
 * 
 * This work is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * This work is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along
 * with this work; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 *) 

Require Export Cauchy_IR.

Lemma pring_aux_Q :
 forall (p : positive) (a : nat) (x : R_CRing Q_as_COrdField) (n : nat),
 CS_seq _ x n = Build_Q (Z_of_nat a) 1 ->
 CS_seq _ (pring_aux (R_CRing Q_as_COrdField) p x) n =
 Build_Q (Pmult_nat p a) 1.
simple induction p; intros.

simpl in |- *.
rewrite (H (a + a)).
rewrite H0; unfold Qplus in |- *; simpl in |- *.
apply (f_equal2 Build_Q); [ rewrite Znat.inj_plus; omega | trivial ].
simpl in |- *.
rewrite H0.
unfold Qplus in |- *; simpl in |- *.
unfold Qmult in |- *.
simpl (num (Build_Q 2%positive 1)) in |- *.
simpl (num (Build_Q a 1)) in |- *.
apply (f_equal2 Build_Q); [ rewrite Znat.inj_plus; omega | trivial ].

simpl in |- *.
apply H; simpl in |- *.
rewrite H0.
unfold Qplus in |- *; simpl in |- *.
unfold Qmult in |- *.
simpl (num (Build_Q 2%positive 1)) in |- *.
simpl (num (Build_Q a 1)) in |- *.
apply (f_equal2 Build_Q); [ rewrite Znat.inj_plus; omega | trivial ].

trivial.
Qed.

Lemma pring_Q :
 forall (p : positive) (n : nat),
 CS_seq _ (pring (R_CRing Q_as_COrdField) p) n = Build_Q p 1.
intros; unfold pring in |- *.
rewrite (pring_aux_Q p 1 One n); auto.
apply (f_equal2 Build_Q); [ exact (convert_is_POS p) | trivial ].
Qed.

Lemma pring_pos_opt_opt : forall p : positive, Zero[<]pring Cauchy_IR p.
intros.
red in |- *.
simpl in |- *.
unfold R_lt in |- *.
exists 0.
exists (inject_Z 1).
constructor.
intros. 
rewrite pring_Q.
simpl in |- *.
red in |- *; simpl in |- *.
intro H0; inversion H0.
generalize H2.
case (p * 1 * 1)%positive; intros; inversion H1.
Qed.

Lemma pring_ap_zero_opt_opt : forall p : positive, pring Cauchy_IR p[#]Zero.
intros.
right.
exact (pring_pos_opt_opt p).
Qed.

Lemma pring_inject_Q :
 forall p : positive,
 pring Cauchy_IR p[=]inject_Q Q_as_COrdField (inject_Z p).
intros.
astepl (nring (R:=Cauchy_IR) (nat_of_P p)).
astepr (inject_Q Q_as_COrdField (nring (nat_of_P p))).
apply (ing_nring Q_as_COrdField).
apply (ing_eq Q_as_COrdField).
astepr (inject_Z (nat_of_P p)).
apply nring_Q.
rewrite convert_is_POS.
rational.
Qed.

Hint Resolve pring_inject_Q: algebra.

(* Simplier, but not as good, because of the initial Stepr. *)

Lemma pring_pos_opt : forall p : positive, Zero[<]pring Cauchy_IR p.
intros.
astepr (inject_Q Q_as_COrdField (inject_Z p)).
red in |- *.
simpl in |- *.
unfold R_lt in |- *.
exists 0.
exists (inject_Z 1).
constructor.
intros.
red in |- *.
intro H0.
red in H0.
simpl in H0.
unfold Qlt, Zlts in H0.
inversion H0.
simpl in |- *.
rewrite Pmult_comm in H2.
simpl in H2.
rewrite Pmult_comm in H2.
simpl in H2.
generalize H2.
case p; intros; inversion H1.
Qed.

Lemma pring_ap_zero_opt : forall p : positive, pring Cauchy_IR p[#]Zero.
intros.
right.
exact (pring_pos_opt p).
Qed.
