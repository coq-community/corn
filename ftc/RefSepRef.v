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

Require Export COrdLemmas.
Require Export Partitions.

Section Refining_Separated.

Variables a b : IR.
Hypothesis Hab : a[<=]b.
Let I := compact a b Hab.

Variable F : PartIR.
Hypothesis contF : Continuous_I Hab F.
Hypothesis incF : included (compact a b Hab) (Dom F).

Variables m n : nat.
Variable P : Partition Hab n.
Variable R : Partition Hab m.

Hypothesis HPR : Separated P R.

Lemma RSR_HP : _Separated P.
elim HPR; intros; assumption.
Qed.

Lemma RSR_HP' : a[=]b -> 0 = n.
intro.
apply _Separated_imp_length_zero with (P := P).
exact RSR_HP.
assumption.
Qed.

Lemma RSR_HR : _Separated R.
elim HPR; intros.
elim b0; intros; assumption.
Qed.

Lemma RSR_HR' : a[=]b -> 0 = m.
intro.
apply _Separated_imp_length_zero with (P := R).
exact RSR_HR.
assumption.
Qed.

Lemma RSR_mn0 : 0 = m -> 0 = n.
intro; apply RSR_HP'; apply partition_length_zero with Hab.
rewrite H; apply R.
Qed.

Lemma RSR_nm0 : 0 = n -> 0 = m.
intro; apply RSR_HR'; apply partition_length_zero with Hab.
rewrite H; apply P.
Qed.

Lemma RSR_H' :
  forall i j : nat,
  0 < i ->
  0 < j ->
  i < n -> j < m -> forall (Hi : i <= n) (Hj : j <= m), P i Hi[#]R j Hj.
elim HPR; do 2 intro.
elim b0; do 2 intro; assumption.
Qed.

Let f' (i : nat) (H : i < pred n) := P _ (lt_8 _ _ H).
Let g' (j : nat) (H : j < pred m) := R _ (lt_8 _ _ H).

Lemma RSR_f'_nlnf : nat_less_n_fun f'.
red in |- *; intros; unfold f' in |- *; apply prf1; auto.
Qed.

Lemma RSR_g'_nlnf : nat_less_n_fun g'.
red in |- *; intros; unfold g' in |- *; apply prf1; auto.
Qed.

Lemma RSR_f'_mon : forall (i i' : nat) Hi Hi', i < i' -> f' i Hi[<]f' i' Hi'.
intros.
apply local_mon_imp_mon_lt with (n := pred n).
intros; unfold f' in |- *; apply RSR_HP.
assumption.
Qed.

Lemma RSR_g'_mon : forall (j j' : nat) Hj Hj', j < j' -> g' j Hj[<]g' j' Hj'.
intros.
apply local_mon_imp_mon_lt with (n := pred m).
intros; unfold g' in |- *; apply RSR_HR.
assumption.
Qed.

Lemma RSR_f'_ap_g' : forall (i j : nat) Hi Hj, f' i Hi[#]g' j Hj.
intros.
unfold f', g' in |- *; apply RSR_H'.
apply lt_O_Sn.
apply lt_O_Sn.
apply pred_lt; assumption.
apply pred_lt; assumption.
Qed.

Let h := om_fun _ _ _ _ _ RSR_f'_ap_g'.

Lemma RSR_h_nlnf : nat_less_n_fun h.
unfold h in |- *; apply om_fun_1.
exact RSR_f'_nlnf.
exact RSR_g'_nlnf.
Qed.

Lemma RSR_h_mon : forall (i i' : nat) Hi Hi', i < i' -> h i Hi[<]h i' Hi'.
unfold h in |- *; apply om_fun_2; auto.
exact RSR_f'_nlnf.
exact RSR_g'_nlnf.
exact RSR_f'_mon.
exact RSR_g'_mon.
Qed.

Lemma RSR_h_mon' : forall (i i' : nat) Hi Hi', i <= i' -> h i Hi[<=]h i' Hi'.
intros; apply mon_imp_mon'_lt with (n := pred m + pred n).
apply RSR_h_nlnf.
apply RSR_h_mon.
assumption.
Qed.

Lemma RSR_h_f' : forall (i : nat) Hi, {j : nat | {Hj : _ < _ | f' i Hi[=]h j Hj}}.
unfold h in |- *; apply om_fun_3a; auto.
exact RSR_f'_nlnf.
exact RSR_g'_nlnf.
Qed.

Lemma RSR_h_g' : forall (j : nat) Hj, {i : nat | {Hi : _ < _ | g' j Hj[=]h i Hi}}.
unfold h in |- *; apply om_fun_3b; auto.
exact RSR_f'_nlnf.
exact RSR_g'_nlnf.
Qed.

Lemma RSR_h_PropAll :
  forall P : IR -> Prop,
  pred_wd' IR P ->
  (forall (i : nat) Hi, P (f' i Hi)) ->
  (forall (j : nat) Hj, P (g' j Hj)) -> forall (k : nat) Hk, P (h k Hk).
unfold h in |- *; apply om_fun_4b.
Qed.

Lemma RSR_h_PropEx :
  forall P : IR -> Prop,
  pred_wd' IR P ->
  {i : nat | {Hi : _ < _ | P (f' i Hi)}}
  or {j : nat | {Hj : _ < _ | P (g' j Hj)}} ->
  {k : nat | {Hk : _ < _ | P (h k Hk)}}.
unfold h in |- *; intros; apply om_fun_4d; auto.
exact RSR_f'_nlnf.
exact RSR_g'_nlnf.
Qed.

Definition Separated_Refinement_fun : forall i : nat, i <= pred (m + n) -> IR.
intros.
elim (le_lt_eq_dec _ _ H); intro.
elim (le_lt_dec i 0); intro.
apply a.
apply (h (pred i) (lt_10 _ _ _ b0 a0)).
apply b.
Defined.

Lemma Separated_Refinement_lemma1 :
 forall i j : nat,
 i = j ->
 forall (Hi : i <= pred (m + n)) (Hj : j <= pred (m + n)),
 Separated_Refinement_fun i Hi[=]Separated_Refinement_fun j Hj.
do 3 intro.
rewrite <- H; intros; unfold Separated_Refinement_fun in |- *; simpl in |- *.
elim (le_lt_eq_dec _ _ Hi); elim (le_lt_eq_dec _ _ Hj); elim (le_lt_dec i 0);
 intros; simpl in |- *.
algebra.
apply RSR_h_nlnf; reflexivity.
elimtype False; rewrite <- b0 in a1; apply (lt_irrefl _ a1).
elimtype False; rewrite <- b1 in a0; apply (lt_irrefl _ a0).
elimtype False; rewrite <- b0 in a1; apply (lt_irrefl _ a1).
elimtype False; rewrite <- b1 in a0; apply (lt_irrefl _ a0).
algebra.
algebra.
Qed.

Lemma Separated_Refinement_lemma3 :
 forall H : 0 <= pred (m + n), Separated_Refinement_fun 0 H[=]a.
intros; unfold Separated_Refinement_fun in |- *; simpl in |- *.
elim (le_lt_eq_dec _ _ H); elim (le_lt_dec 0 0); intros; simpl in |- *.
algebra.
elimtype False; inversion b0.
apply eq_symmetric_unfolded; apply partition_length_zero with Hab.
cut (m + n <= 1); [ intro | omega ].
elim (plus_eq_one_imp_eq_zero _ _ H0); intro.
rewrite <- a1; apply R.
rewrite <- b1; apply P.
elimtype False; inversion b0.
Qed.

Lemma Separated_Refinement_lemma4 :
 forall H : pred (m + n) <= pred (m + n),
 Separated_Refinement_fun (pred (m + n)) H[=]b.
intros; unfold Separated_Refinement_fun in |- *; simpl in |- *.
elim (le_lt_eq_dec _ _ H); elim (le_lt_dec 0 0); intros; simpl in |- *.
algebra.
elimtype False; apply (lt_irrefl _ a1).
elimtype False; apply (lt_irrefl _ a0).
algebra.
algebra.
Qed.

Lemma Separated_Refinement_lemma2 :
 forall (i : nat) (H : i <= pred (m + n)) (H' : S i <= pred (m + n)),
 Separated_Refinement_fun i H[<=]Separated_Refinement_fun (S i) H'.
intros; unfold Separated_Refinement_fun in |- *; simpl in |- *.
elim (le_lt_eq_dec _ _ H); elim (le_lt_eq_dec _ _ H'); intros; simpl in |- *.
elim (le_lt_dec i 0); elim (le_lt_dec (S i) 0); intros; simpl in |- *.
elimtype False; inversion a2.
apply RSR_h_PropAll with (P := fun x : IR => a[<=]x).
red in |- *; intros.
apply leEq_wdr with x; assumption.
intros; unfold f' in |- *.
astepl (P 0 (le_O_n _)).
apply Partition_mon; apply le_O_n.
intros; unfold g' in |- *.
astepl (R 0 (le_O_n _)).
apply Partition_mon; apply le_O_n.
elimtype False; inversion a2.
apply less_leEq; apply RSR_h_mon; auto with arith.
elim (le_lt_dec i 0); elim (le_lt_dec (S i) 0); intros; simpl in |- *.
elimtype False; inversion a1.
assumption.
elimtype False; inversion a1.
apply RSR_h_PropAll with (P := fun x : IR => x[<=]b).
red in |- *; intros.
apply leEq_wdl with x; assumption.
intros; unfold f' in |- *.
apply leEq_wdr with (P _ (le_n _)).
apply Partition_mon; apply le_trans with (pred n); auto with arith.
apply finish.
intros; unfold g' in |- *.
apply leEq_wdr with (R _ (le_n _)).
apply Partition_mon; apply le_trans with (pred m); auto with arith.
apply finish.
elimtype False; rewrite <- b0 in H'; apply (le_Sn_n _ H').
apply leEq_reflexive.
Qed.

Definition Separated_Refinement : Partition Hab (pred (m + n)).
apply Build_Partition with Separated_Refinement_fun.
exact Separated_Refinement_lemma1.
exact Separated_Refinement_lemma2.
exact Separated_Refinement_lemma3.
exact Separated_Refinement_lemma4.
Defined.

Definition RSR_auxP : nat -> nat.
intro i.
elim (le_lt_dec i 0); intro.
apply 0.
elim (le_lt_dec n i); intro.
apply (pred (m + n) + (i - n)).
apply (S (ProjT1 (RSR_h_f' (pred i) (lt_pred' _ _ b0 b1)))).
Defined.

Definition RSR_auxR : nat -> nat.
intro i.
elim (le_lt_dec i 0); intro.
apply 0.
elim (le_lt_dec m i); intro.
apply (pred (m + n) + (i - m)).
apply (S (ProjT1 (RSR_h_g' (pred i) (lt_pred' _ _ b0 b1)))).
Defined.

Lemma RSR_auxP_lemma0 : RSR_auxP 0 = 0.
unfold RSR_auxP in |- *.
elim (le_lt_dec 0 0); intro; simpl in |- *.
reflexivity.
elimtype False; inversion b0.
Qed.

Lemma RSR_h_inj : forall (i j : nat) Hi Hj, h i Hi[=]h j Hj -> i = j.
intros.
eapply mon_imp_inj_lt with (f := h).
exact RSR_h_mon.
apply H.
Qed.

Lemma RSR_auxP_lemmai :
  forall (i : nat) (Hi : 0 < i) (Hi' : i < n),
  RSR_auxP i = S (ProjT1 (RSR_h_f' (pred i) (lt_pred' _ _ Hi Hi'))).
intros.
unfold RSR_auxP in |- *.
elim (le_lt_dec n i); intro; simpl in |- *.
elimtype False; apply le_not_lt with n i; auto.
elim (le_lt_dec i 0); intro; simpl in |- *.
elimtype False; apply lt_irrefl with 0; apply lt_le_trans with i; auto.
set (x := ProjT1 (RSR_h_f' _ (lt_pred' _ _ b1 b0))) in *.
set (y := ProjT1 (RSR_h_f' _ (lt_pred' _ _ Hi Hi'))) in *.
cut (x = y).
intro; auto with arith.
assert (H := ProjT2 (RSR_h_f' _ (lt_pred' _ _ b1 b0))).
assert (H0 := ProjT2 (RSR_h_f' _ (lt_pred' _ _ Hi Hi'))).
elim H; clear H; intros Hx Hx'.
elim H0; clear H0; intros Hy Hy'.
apply RSR_h_inj with Hx Hy.
eapply eq_transitive_unfolded.
2: apply Hy'.
eapply eq_transitive_unfolded.
apply eq_symmetric_unfolded; apply Hx'.
apply RSR_f'_nlnf; reflexivity.
Qed.

Lemma RSR_auxP_lemman : RSR_auxP n = pred (m + n).
unfold RSR_auxP in |- *.
elim (le_lt_dec n 0); intro; simpl in |- *.
cut (n = 0); [ intro | auto with arith ].
transitivity (pred m).
2: rewrite H; auto.
cut (0 = m); [ intro; rewrite <- H0; auto | apply RSR_HR' ].
apply partition_length_zero with Hab; rewrite <- H; apply P.
elim (le_lt_dec n n); intro; simpl in |- *.
rewrite <- minus_n_n; auto.
elimtype False; apply lt_irrefl with n; auto.
Qed.

Lemma RSR_auxP_lemma1 : forall i j : nat, i < j -> RSR_auxP i < RSR_auxP j.
intros; unfold RSR_auxP in |- *.
assert (X:=not_not_lt); assert (X':=plus_pred_pred_plus).
assert (X'':=RSR_mn0); assert (X''':=RSR_nm0).
elim (le_lt_dec i 0); intro.
elim (le_lt_dec j 0); intros; simpl in |- *.
apply lt_le_trans with j; try apply le_lt_trans with i; auto with arith.
elim (le_lt_dec n j); intros; simpl in |- *.
omega.
apply lt_O_Sn.
elim (le_lt_dec n i); elim (le_lt_dec j 0); intros; simpl in |- *.
elim (lt_irrefl 0); apply lt_le_trans with j; try apply le_lt_trans with i;
 auto with arith.
elim (le_lt_dec n j); intro; simpl in |- *.
apply plus_lt_compat_l.
apply plus_lt_reg_l with n.
repeat rewrite <- le_plus_minus; auto.
elim (le_not_lt n i); auto; apply lt_trans with j; auto.
elim (lt_irrefl 0); apply lt_trans with i; auto; apply lt_le_trans with j;
 auto.
elim (le_lt_dec n j); intro; simpl in |- *.
apply lt_le_trans with (S (pred m + pred n)).
apply lt_n_S.
apply (ProjT1 (ProjT2 (RSR_h_f' (pred i) (lt_pred' _ _ b0 b2)))).
rewrite plus_n_Sm.
rewrite <- S_pred with n 0.
2: apply lt_trans with i; auto.
replace (pred m + n) with (pred (m + n)).
auto with arith.
cut (S (pred (m + n)) = S (pred m + n)); auto.
rewrite <- plus_Sn_m.
rewrite (S_pred m 0); auto with arith.
apply neq_O_lt.
intro.
apply lt_irrefl with 0.
apply lt_trans with i; auto.
rewrite RSR_mn0; auto.
apply lt_n_S.
cut
 (~
  ~
  ProjT1 (RSR_h_f' (pred i) (lt_pred' _ _ b0 b2)) <
  ProjT1 (RSR_h_f' (pred j) (lt_pred' _ _ b1 b3))); intro.
apply not_not_lt; assumption.
cut
 (ProjT1 (RSR_h_f' (pred j) (lt_pred' _ _ b1 b3)) <=
  ProjT1 (RSR_h_f' (pred i) (lt_pred' _ _ b0 b2))); intros.
2: apply not_lt; assumption.
cut
 (h _ (ProjT1 (ProjT2 (RSR_h_f' (pred j) (lt_pred' _ _ b1 b3))))[<=]
  h _ (ProjT1 (ProjT2 (RSR_h_f' (pred i) (lt_pred' _ _ b0 b2))))).
intro.
2: apply RSR_h_mon'; assumption.
cut (f' (pred j) (lt_pred' _ _ b1 b3)[<=]f' (pred i) (lt_pred' _ _ b0 b2)).
2: apply
    leEq_wdl
     with (h _ (ProjT1 (ProjT2 (RSR_h_f' (pred j) (lt_pred' _ _ b1 b3))))).
2: apply
    leEq_wdr
     with (h _ (ProjT1 (ProjT2 (RSR_h_f' (pred i) (lt_pred' _ _ b0 b2))))).
2: assumption.
3: apply eq_symmetric_unfolded;
    exact (ProjT2 (ProjT2 (RSR_h_f' (pred j) (lt_pred' _ _ b1 b3)))).
2: apply eq_symmetric_unfolded;
    exact (ProjT2 (ProjT2 (RSR_h_f' (pred i) (lt_pred' _ _ b0 b2)))).
clear H2 H1; intro.
cut (f' _ (lt_pred' _ _ b0 b2)[<]f' _ (lt_pred' _ _ b1 b3)).
2: apply RSR_f'_mon.
2: apply lt_pred'; assumption.
intro.
elimtype False.
apply less_irreflexive_unfolded with (x := f' _ (lt_pred' _ _ b1 b3)).
eapply leEq_less_trans; [ apply H1 | apply X0 ].
Qed.

Lemma RSR_auxP_lemma2 :
  forall (i : nat) (H : i <= n),
  {H' : RSR_auxP i <= _ | P i H[=]Separated_Refinement _ H'}.
intros.
unfold Separated_Refinement in |- *; simpl in |- *.
unfold Separated_Refinement_fun in |- *; simpl in |- *.
elim (le_lt_dec i 0); intro; simpl in |- *.
cut (i = 0); [ intro | auto with arith ].
generalize H; clear a0 H; rewrite H0.
rewrite RSR_auxP_lemma0.
clear H0; intros.
exists (le_O_n (pred (m + n))).
elim le_lt_eq_dec; intro; simpl in |- *.
elim (le_lt_dec 0 0); intro; simpl in |- *.
apply start.
elimtype False; inversion b0.
apply eq_transitive_unfolded with a.
apply start.
apply partition_length_zero with Hab.
cut (m + n <= 1).
intro.
elim (plus_eq_one_imp_eq_zero _ _ H0); intro.
rewrite <- a0; apply R.
rewrite <- b1; apply P.
generalize b0; clear b0.
case (m + n).
auto.
intros.
simpl in b0; rewrite <- b0; auto.
elim (le_lt_eq_dec _ _ H); intro.
cut (pred i < pred n);
 [ intro | apply lt_pred; rewrite <- S_pred with i 0; auto ].
cut (RSR_auxP i <= pred (m + n)).
intro; exists H1.
elim le_lt_eq_dec; intro; simpl in |- *.
elim (le_lt_dec (RSR_auxP i) 0); intro; simpl in |- *.
cut (RSR_auxP i = 0); [ intro | auto with arith ].
rewrite <- RSR_auxP_lemma0 in H2.
cut (RSR_auxP 0 < RSR_auxP i); [ intro | apply RSR_auxP_lemma1; assumption ].
elimtype False; rewrite H2 in H3; apply (lt_irrefl _ H3).
generalize b1 a1; clear b1 a1.
rewrite (RSR_auxP_lemmai i b0 a0); intros.
simpl in |- *.
elim (ProjT2 (RSR_h_f' _ (lt_pred' i n b0 a0))); intros.
eapply eq_transitive_unfolded.
2: eapply eq_transitive_unfolded.
2: apply p.
unfold f' in |- *.
apply prf1; apply S_pred with 0; auto.
apply RSR_h_nlnf; reflexivity.
rewrite <- RSR_auxP_lemman in b1.
cut (i = n).
intro; elimtype False; rewrite H2 in a0; apply (lt_irrefl _ a0).
apply nat_mon_imp_inj with (h := RSR_auxP).
apply RSR_auxP_lemma1.
assumption.
unfold RSR_auxP in |- *.
elim (le_lt_dec i 0); intro; simpl in |- *.
apply le_O_n.
elim (le_lt_dec n i); intro; simpl in |- *.
elim (lt_irrefl n); apply le_lt_trans with i; auto.
apply plus_pred_pred_plus.
elim (ProjT2 (RSR_h_f' _ (lt_pred' i n b1 b2))); intros.
assumption.
generalize H; clear H; rewrite b1; intro.
rewrite RSR_auxP_lemman.
exists (le_n (pred (m + n))).
elim le_lt_eq_dec; intro; simpl in |- *.
elimtype False; apply (lt_irrefl _ a0).
apply finish.
Qed.

Lemma Separated_Refinement_lft : Refinement P Separated_Refinement.
exists RSR_auxP; repeat split.
exact RSR_auxP_lemman.
intros; apply RSR_auxP_lemma1; assumption.
exact RSR_auxP_lemma2.
Qed.

Lemma RSR_auxR_lemma0 : RSR_auxR 0 = 0.
unfold RSR_auxR in |- *.
elim (le_lt_dec 0 0); intro; simpl in |- *.
reflexivity.
elimtype False; inversion b0.
Qed.

Lemma RSR_auxR_lemmai :
  forall (i : nat) (Hi : 0 < i) (Hi' : i < m),
  RSR_auxR i = S (ProjT1 (RSR_h_g' (pred i) (lt_pred' _ _ Hi Hi'))).
intros.
unfold RSR_auxR in |- *.
elim (le_lt_dec m i); intro; simpl in |- *.
elimtype False; apply le_not_lt with m i; auto.
elim (le_lt_dec i 0); intro; simpl in |- *.
elimtype False; apply lt_irrefl with 0; apply lt_le_trans with i; auto.
set (x := ProjT1 (RSR_h_g' _ (lt_pred' _ _ b1 b0))) in *.
set (y := ProjT1 (RSR_h_g' _ (lt_pred' _ _ Hi Hi'))) in *.
cut (x = y).
intro; auto with arith.
assert (H := ProjT2 (RSR_h_g' _ (lt_pred' _ _ b1 b0))).
assert (H0 := ProjT2 (RSR_h_g' _ (lt_pred' _ _ Hi Hi'))).
elim H; clear H; intros Hx Hx'.
elim H0; clear H0; intros Hy Hy'.
apply RSR_h_inj with Hx Hy.
eapply eq_transitive_unfolded.
2: apply Hy'.
eapply eq_transitive_unfolded.
apply eq_symmetric_unfolded; apply Hx'.
apply RSR_g'_nlnf; reflexivity.
Qed.

Lemma RSR_auxR_lemmam : RSR_auxR m = pred (m + n).
unfold RSR_auxR in |- *.
elim (le_lt_dec m 0); intro; simpl in |- *.
cut (m = 0); [ intro | auto with arith ].
transitivity (pred m).
rewrite H; auto.
cut (0 = n); [ intro; rewrite <- H0; auto | apply RSR_HP' ].
apply partition_length_zero with Hab; rewrite <- H; apply R.
elim (le_lt_dec m m); intro; simpl in |- *.
rewrite <- minus_n_n; auto.
elim (lt_irrefl _ b1).
Qed.

Lemma RSR_auxR_lemma1 : forall i j : nat, i < j -> RSR_auxR i < RSR_auxR j.
intros; unfold RSR_auxR in |- *.
assert (X:=not_not_lt); assert (X':=plus_pred_pred_plus).
assert (X'':=RSR_mn0); assert (X''':=RSR_nm0).
elim (le_lt_dec i 0); intro.
elim (le_lt_dec j 0); intros; simpl in |- *.
apply le_lt_trans with i; try apply lt_le_trans with j; auto with arith.
elim (le_lt_dec m j); intros; simpl in |- *.
omega.
apply lt_O_Sn.
elim (le_lt_dec m i); elim (le_lt_dec j 0); intros; simpl in |- *.
elim (lt_irrefl 0); apply le_lt_trans with i; try apply lt_le_trans with j;
 auto with arith.
elim (le_lt_dec m j); intro; simpl in |- *.
apply plus_lt_compat_l.
apply plus_lt_reg_l with m.
repeat rewrite <- le_plus_minus; auto.
elim (le_not_lt m i); auto; apply lt_trans with j; auto.
elim (lt_irrefl 0); apply lt_trans with i; auto; apply lt_le_trans with j;
 auto.
elim (le_lt_dec m j); intro; simpl in |- *.
set (H0 := RSR_nm0) in *; set (H1 := RSR_mn0) in *;
 apply lt_le_trans with (S (pred m + pred n)).
apply lt_n_S.
apply (ProjT1 (ProjT2 (RSR_h_g' (pred i) (lt_pred' _ _ b0 b2)))).
rewrite <- plus_Sn_m.
rewrite <- S_pred with m 0.
2: apply lt_trans with i; auto.
replace (m + pred n) with (pred (m + n)).
auto with arith.
cut (S (pred (m + n)) = S (m + pred n)); auto.
rewrite plus_n_Sm.
rewrite <- S_pred with n 0; auto with arith.
symmetry  in |- *; apply S_pred with 0.
apply lt_le_trans with m; auto with arith.
apply lt_trans with i; auto.
apply neq_O_lt.
intro.
apply lt_irrefl with 0.
apply lt_trans with i; auto.
rewrite RSR_nm0; auto.
apply lt_n_S.
cut
 (~
  ~
  ProjT1 (RSR_h_g' (pred i) (lt_pred' _ _ b0 b2)) <
  ProjT1 (RSR_h_g' (pred j) (lt_pred' _ _ b1 b3))); intro.
apply not_not_lt; assumption.
cut
 (ProjT1 (RSR_h_g' (pred j) (lt_pred' _ _ b1 b3)) <=
  ProjT1 (RSR_h_g' (pred i) (lt_pred' _ _ b0 b2))); intros.
2: apply not_lt; assumption.
cut
 (h _ (ProjT1 (ProjT2 (RSR_h_g' (pred j) (lt_pred' _ _ b1 b3))))[<=]
  h _ (ProjT1 (ProjT2 (RSR_h_g' (pred i) (lt_pred' _ _ b0 b2))))).
intro.
2: apply RSR_h_mon'; assumption.
cut (g' (pred j) (lt_pred' _ _ b1 b3)[<=]g' (pred i) (lt_pred' _ _ b0 b2)).
2: apply
    leEq_wdl
     with (h _ (ProjT1 (ProjT2 (RSR_h_g' (pred j) (lt_pred' _ _ b1 b3))))).
2: apply
    leEq_wdr
     with (h _ (ProjT1 (ProjT2 (RSR_h_g' (pred i) (lt_pred' _ _ b0 b2))))).
2: assumption.
3: apply eq_symmetric_unfolded;
    exact (ProjT2 (ProjT2 (RSR_h_g' (pred j) (lt_pred' _ _ b1 b3)))).
2: apply eq_symmetric_unfolded;
    exact (ProjT2 (ProjT2 (RSR_h_g' (pred i) (lt_pred' _ _ b0 b2)))).
clear H2 H1; intro.
cut (g' _ (lt_pred' _ _ b0 b2)[<]g' _ (lt_pred' _ _ b1 b3)).
2: apply RSR_g'_mon.
2: apply lt_pred'; assumption.
intro.
elimtype False.
apply less_irreflexive_unfolded with (x := g' _ (lt_pred' _ _ b1 b3)).
eapply leEq_less_trans; [ apply H1 | apply X0 ].
Qed.

Lemma RSR_auxR_lemma2 :
  forall (j : nat) (H : j <= m),
  {H' : RSR_auxR j <= _ | R j H[=]Separated_Refinement _ H'}.
intros.
unfold Separated_Refinement in |- *; simpl in |- *.
unfold Separated_Refinement_fun in |- *; simpl in |- *.
elim (le_lt_dec j 0); intro; simpl in |- *.
cut (j = 0); [ intro | auto with arith ].
generalize H; clear a0 H; rewrite H0.
rewrite RSR_auxR_lemma0.
clear H0; intros.
exists (le_O_n (pred (m + n))).
elim le_lt_eq_dec; intro; simpl in |- *.
elim (le_lt_dec 0 0); intro; simpl in |- *.
apply start.
elimtype False; inversion b0.
apply eq_transitive_unfolded with a.
apply start.
apply partition_length_zero with Hab.
cut (m + n <= 1).
intros.
elim (plus_eq_one_imp_eq_zero _ _ H0); intro.
rewrite <- a0; apply R.
rewrite <- b1; apply P.
generalize b0; clear b0.
case (m + n).
auto.
intros.
simpl in b0; rewrite <- b0; auto.
elim (le_lt_eq_dec _ _ H); intro.
cut (pred j < pred m);
 [ intro | red in |- *; rewrite <- S_pred with j 0; auto; apply le_2; auto ].
cut (RSR_auxR j <= pred (m + n)).
intro; exists H1.
elim le_lt_eq_dec; intro; simpl in |- *.
elim (le_lt_dec (RSR_auxR j) 0); intro; simpl in |- *.
cut (RSR_auxR j = 0); [ intro | auto with arith ].
rewrite <- RSR_auxR_lemma0 in H2.
cut (RSR_auxR 0 < RSR_auxR j); [ intro | apply RSR_auxR_lemma1; assumption ].
elimtype False; rewrite H2 in H3; apply (lt_irrefl _ H3).
generalize b1 a1; clear b1 a1.
rewrite (RSR_auxR_lemmai j b0 a0); intros.
simpl in |- *.
elim (ProjT2 (RSR_h_g' _ (lt_pred' _ _ b0 a0))); intros.
eapply eq_transitive_unfolded.
2: eapply eq_transitive_unfolded.
2: apply p.
unfold g' in |- *.
apply prf1; apply S_pred with 0; auto.
apply RSR_h_nlnf; reflexivity.
rewrite <- RSR_auxR_lemmam in b1.
cut (j = m).
intro; elimtype False; rewrite H2 in a0; apply (lt_irrefl _ a0).
apply nat_mon_imp_inj with (h := RSR_auxR).
apply RSR_auxR_lemma1.
assumption.
unfold RSR_auxR in |- *.
elim (le_lt_dec j 0); intro; simpl in |- *.
apply le_O_n.
elim (le_lt_dec m j); intro; simpl in |- *.
rewrite not_le_minus_0.
rewrite <- plus_n_O; auto with arith.
apply lt_not_le; auto.
apply plus_pred_pred_plus.
elim (ProjT2 (RSR_h_g' _ (lt_pred' _ _ b1 b2))); intros.
assumption.
generalize H; clear H; rewrite b1; intro.
rewrite RSR_auxR_lemmam.
exists (le_n (pred (m + n))).
elim le_lt_eq_dec; intro; simpl in |- *.
elimtype False; apply (lt_irrefl _ a0).
apply finish.
Qed.

Lemma Separated_Refinement_rht : Refinement R Separated_Refinement.
exists RSR_auxR; repeat split.
exact RSR_auxR_lemmam.
intros; apply RSR_auxR_lemma1; assumption.
exact RSR_auxR_lemma2.
Qed.

End Refining_Separated.
(* end hide *)
