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

Require Export CReals1.

(**
* Sums over Reals

%\begin{convention}% Let [c] be a real.
%\end{convention}%

Here we prove that
$\Sigma_{m\leq i \leq n}~c^k = \frac{c^{n+1}-c^m}{c-1}.$
#sum_(m&le; i &le; n) c^k = frac (c^(n+1) -c^m) (c-1)#
*)

Section Sums_over_Reals.

Variable c : IR.

Lemma Sum0_c_exp : forall H m, Sum0 m (fun i => c[^]i) [=] (c[^]m[-]One[/] c[-]One[//]H).
Proof.
 intros.
 elim m.
  simpl in |- *.
  rational.
 simpl in |- *.
 intros.
 astepl ((nexp IR n c[-]One[/] c[-]One[//]H) [+]nexp IR n c).
 rational.
Qed.

Hint Resolve Sum0_c_exp.

Lemma Sum_c_exp : forall H m n,
 Sum m n (fun i => c[^]i) [=] (c[^]S n[-]c[^]m[/] c[-]One[//]H).
Proof.
 intros.
 unfold Sum in |- *.
 unfold Sum1 in |- *.
 astepl ((c[^]S n[-]One[/] c[-]One[//]H) [-] (c[^]m[-]One[/] c[-]One[//]H)).
 rational.
Qed.
Hint Resolve Sum_c_exp.

(** The following formulation is often more useful if [c [<] 1]. *)

Lemma Sum_c_exp' : forall H m n,
 Sum m n (fun i => c[^]i) [=] (c[^]m[-]c[^]S n[/] One[-]c[//]H).
Proof.
 intros.
 cut (c[-]One [#] Zero).
  intro H0.
  astepl (c[^]S n[-]c[^]m[/] c[-]One[//]H0).
  rational.
 rstepl ( [--] (One[-]c)).
 apply inv_resp_ap_zero.
 assumption.
Qed.

Hint Resolve Sum_c_exp'.

End Sums_over_Reals.

Hint Resolve Sum0_c_exp Sum_c_exp Sum_c_exp': algebra.

Lemma diff_is_Sum0 : forall (s : nat -> IR) n, s n[-]s 0 [=] Sum0 n (fun i => s (S i) [-]s i).
Proof.
 intros s.
 simple induction n.
  simpl in |- *. algebra.
  intros.
 simpl in |- *.
 apply eq_transitive_unfolded with (s (S n0) [-]s n0[+] (s n0[-]s 0)).
  rational.
 apply eq_transitive_unfolded with (s (S n0) [-]s n0[+]Sum0 n0 (fun i : nat => s (S i) [-]s i)).
  exact (plus_resp_eq _ _ _ _ H).
 rational.
Qed.

Lemma diff_is_sum : forall (s : nat -> IR) N m,
 N < m -> s m[-]s N [=] Sum N (pred m) (fun i => s (S i) [-]s i).
Proof.
 intros s N m ltNm.
 unfold Sum in |- *. unfold Sum1 in |- *.
 generalize (S_pred m N ltNm).
 intro H.
 rewrite <- H.
 generalize (diff_is_Sum0 s N).
 intro HsN.
 generalize (diff_is_Sum0 s m).
 intro Hsm.
 apply eq_transitive_unfolded with (s m[-]s 0[-] (s N[-]s 0)).
  rational.
 apply (cg_minus_wd IR).
  assumption.
 assumption.
Qed.

Lemma Sum0_pres_less : forall s t : nat -> IR, (forall i, s i [<] t i) -> forall n, Sum0 n s [<=] Sum0 n t.
Proof.
 intros s t H.
 simple induction n.
  simpl in |- *.
  exact (leEq_reflexive _ _).
 intros.
 simpl in |- *.
 apply leEq_transitive with (Sum0 n0 t[+]s n0).
  apply plus_resp_leEq.
  assumption.
 apply plus_resp_leEq_lft.
 apply less_leEq; exact (H _).
Qed.

Lemma Sum_pres_less : forall s t : nat -> IR,
 (forall i, s i [<] t i) -> forall N m, N <= m -> Sum N m s [<=] Sum N m t.
Proof.
 intros.
 apply less_leEq.
 apply Sum_resp_less; auto.
Qed.

Lemma Sum_pres_leEq : forall s t : nat -> IR,
 (forall i, s i [<=] t i) -> forall N m, N <= m -> Sum N m s [<=] Sum N m t.
Proof.
 intros.
 apply Sum_resp_leEq; auto.
Qed.

Lemma Sum0_comm_scal : forall (s : nat -> IR) a m,
 Sum0 m (fun i => s i[*]a) [=] Sum0 m s [*]a.
Proof.
 intros. induction  m as [| m Hrecm]; intros.
 simpl in |- *. algebra.
  simpl in |- *. Step_final (Sum0 m s [*]a[+]s m[*]a).
Qed.

Hint Resolve Sum0_comm_scal: algebra.

Lemma Sum_comm_scal : forall (s : nat -> IR) a N m,
 Sum N m (fun i => s i[*]a) [=] Sum N m s [*]a.
Proof.
 unfold Sum in |- *. unfold Sum1 in |- *. intros.
 Step_final (Sum0 (S m) s [*]a[-]Sum0 N s [*]a).
Qed.

Lemma Sum0_comm_scal' : forall (s : nat -> IR) a m,
 Sum0 m (fun i => a[*]s i) [=] a[*]Sum0 m s.
Proof.
 intros.
 apply eq_transitive_unfolded with (Sum0 m s[*]a).
  2: astepr (Sum0 m s[*]a); apply mult_wdl.
  2: apply Sum0_wd; algebra.
 eapply eq_transitive_unfolded.
  2: apply Sum0_comm_scal.
 apply Sum0_wd; algebra.
Qed.

Lemma Sum_comm_scal' : forall (s : nat -> IR) a m n,
 Sum m n (fun i => a[*]s i) [=] a[*]Sum m n s.
Proof.
 intros.
 unfold Sum, Sum1 in |- *.
 eapply eq_transitive_unfolded.
  2: apply eq_symmetric_unfolded; apply dist_2a.
 apply cg_minus_wd; apply Sum0_comm_scal'.
Qed.

Lemma Sumx_comm_scal' : forall n (a : IR) (f : forall i, i < n -> IR),
 Sumx (fun i H => a[*]f i H) [=] a[*]Sumx f.
Proof.
 simple induction n.
  intros; simpl in |- *; algebra.
 clear n; intros; simpl in |- *.
 eapply eq_transitive_unfolded.
  2: apply eq_symmetric_unfolded; apply ring_dist_unfolded.
 apply bin_op_wd_unfolded.
  apply H with (f := fun i l => f i (lt_S _ _ l)).
 algebra.
Qed.

Lemma Sum2_comm_scal' : forall a m n (f: forall i, m <= i -> i <= n -> IR),
 m <= S n -> Sum2 (fun i Hm Hn => a[*]f i Hm Hn) [=] a[*]Sum2 f.
Proof.
 intros; unfold Sum2 in |- *.
 eapply eq_transitive_unfolded.
  2: apply Sum_comm_scal'.
 apply Sum_wd'.
  assumption.
 intros.
 elim (le_lt_dec m i); intros; simpl in |- *.
  elim (le_lt_dec i n); intros; simpl in |- *; algebra.
 algebra.
Qed.
