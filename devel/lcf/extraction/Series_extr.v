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
(* begin hide *)
(* Facts for extraction *)
Require Export Series.

Section temporary_section.

Variable F : COrdField.

Lemma pring_aux_mon : forall (p : positive) (r r' : F),
 (Zero [<] r) -> (r [<=] r') -> pring_aux F p r [<=] pring_aux F p r'.
intro; induction  p as [p Hrecp| p Hrecp| ]; intros; simpl in |- *.
apply plus_resp_leEq_both; auto.
apply Hrecp.
rstepr (r[+]r); apply plus_resp_pos; auto.
apply mult_resp_leEq_lft; auto.
rstepr (Two:F); apply less_leEq; apply pos_two.
apply Hrecp.
rstepr (r[+]r); apply plus_resp_pos; auto.
apply mult_resp_leEq_lft; auto.
rstepr (Two:F); apply less_leEq; apply pos_two.
auto.
Qed.

Lemma old_pring_pos : forall p : positive, Zero [<] pring F p.
intros.
unfold pring in |- *; induction  p as [p Hrecp| p Hrecp| ]; simpl in |- *.
astepl ((Zero:F)[+]Zero).
apply plus_resp_less_leEq.
apply pos_one.
apply less_leEq; eapply less_leEq_trans.
apply Hrecp.
apply pring_aux_mon.
apply pos_one.
rstepr (Two:F); apply less_leEq; apply one_less_two.
eapply less_leEq_trans.
apply Hrecp.
apply pring_aux_mon.
apply pos_one.
rstepr (Two:F); apply less_leEq; apply one_less_two.
apply pos_one.
Qed.

(* A new proof of the same result, using 0<1<= pring F p *)

Lemma pring_ge_one : forall p : positive, One [<=] pring F p.
intros.
unfold pring; induction p; simpl.
astepl ((Zero:F)[+]One).
apply plus_resp_leEq_both.
apply less_leEq; apply pos_one.
eapply leEq_transitive.
apply IHp.
apply pring_aux_mon.
apply pos_one.
rstepr (Two:F); apply less_leEq;apply one_less_two.
eapply leEq_transitive.
apply IHp.
apply pring_aux_mon.
apply pos_one.
rstepr (Two:F); apply less_leEq; apply one_less_two.
apply leEq_reflexive.
Qed.

Lemma pring_pos : forall p : positive, Zero [<] pring F p.
intros; apply less_leEq_trans with (One:F).
apply pos_one.
apply pring_ge_one.
Qed.

Definition pos_fact : nat -> positive.
intro n.
induction  n as [| n Hrecn].
apply 1%positive.
apply (P_of_succ_nat n * Hrecn)%positive.
Defined.

Lemma pos_fact_ap_zero__orig : forall n : nat, pring F (pos_fact n) [#] Zero.
intros.
set (p := pos_fact n) in *.
apply pos_ap_zero.
apply pring_pos.
Qed.

Lemma pring_mult : forall p q : positive,
 pring F (p * q) [=] pring F p[*]pring F q.
intros.
astepl (nring (R:=F) (nat_of_P (p * q))).
astepr (nring (R:=F) (nat_of_P p)[*]nring (nat_of_P q)).
astepr (nring (R:=F) (nat_of_P p * nat_of_P q)).
rewrite nat_of_P_mult_morphism.
algebra.
Qed.

Hint Resolve pring_mult: algebra.

Lemma pos_fact_ap_zero__linear : forall n : nat, pring F (pos_fact n) [#] Zero.
intros.
induction  n as [| n Hrecn].
unfold pring in |- *; simpl in |- *.
apply one_ap_zero.
simpl in |- *.
astepl (pring F (P_of_succ_nat n)[*]pring F (pos_fact n)).
apply mult_resp_ap_zero; auto.
astepl (nring (R:=F) (nat_of_P (P_of_succ_nat n))).
rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
apply nring_ap_zero'.
discriminate.
Qed.

End temporary_section.

Section Important_Numbers2.

Definition e_series
  (pos_fact_ap_zero : forall n : nat, pring IR (pos_fact n)[#]Zero)
  (n : nat) := One[/]_[//]pos_fact_ap_zero n.

Lemma e_series_conv :
 forall pos_fact_ap_zero : forall n : nat, pring IR (pos_fact n)[#]Zero,
 convergent (e_series pos_fact_ap_zero).
intros.
apply ratio_test_conv.
exists 1.
exists (OneR [/]TwoNZ).
apply pos_div_two'; apply pos_one.
split.
apply less_leEq; apply pos_div_two; apply pos_one.
intros.
unfold e_series in |- *.
eapply leEq_wdr.
2: apply mult_commutes.
eapply leEq_wdr.
2: apply AbsIR_mult_pos.
2: apply less_leEq; apply pos_div_two; apply pos_one.
eapply leEq_wdl.
2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
eapply leEq_wdr.
2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
rstepr
 ((One[*]One)[/]_[//]
  mult_resp_ap_zero _ _ _ (two_ap_zero IR) (pos_fact_ap_zero n)).
rstepr
 (One[/]_[//]mult_resp_ap_zero _ _ _ (two_ap_zero IR) (pos_fact_ap_zero n)).
apply recip_resp_leEq.
astepl ((Two:IR)[*]Zero); apply mult_resp_less_lft.
apply pring_pos.
apply pos_two.
astepl (Two[*]nring (R:=IR) (nat_of_P (pos_fact n))).
astepr (nring (R:=IR) (nat_of_P (pos_fact (S n)))).
replace (nat_of_P (pos_fact (S n))) with (S n * nat_of_P (pos_fact n)).
eapply leEq_wdr.
2: apply eq_symmetric_unfolded; apply nring_comm_mult.
apply mult_resp_leEq_rht.
apply nring_leEq; auto with arith.
apply nring_nonneg.
simpl (pos_fact (S n)) in |- *.
rewrite nat_of_P_mult_morphism.
rewrite nat_of_P_o_P_of_succ_nat_eq_succ; auto.
apply less_leEq; apply mult_resp_pos; apply recip_resp_pos.
apply pring_pos.
apply pos_two.
apply less_leEq; apply recip_resp_pos; apply pring_pos.
Qed.

Definition E_2 := series_sum _ (e_series_conv (pos_fact_ap_zero__orig IR)).

Definition E_3 := series_sum _ (e_series_conv (pos_fact_ap_zero__linear IR)).

Axiom
  pos_fact_ap_zero__to_realize : forall n : nat, pring IR (pos_fact n)[#]Zero.

Definition E_4 := series_sum _ (e_series_conv pos_fact_ap_zero__to_realize).

End Important_Numbers2.
(* end hide *)
