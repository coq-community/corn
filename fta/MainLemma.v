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

(** printing two_n %\ensuremath{2n}% #2n# *)
(** printing Small %\ensuremath{\frac13^n}% *)
(** printing Smaller %\ensuremath{\frac13^{2n^2}}% *)

Require Export CSumsReals.
Require Export KeyLemma.

(**
** Main Lemma
*)

Section Main_Lemma.

(**
%\begin{convention}%
Let [a : nat->IR], [n : nat], [a_0 : IR]  and [eps : IR] such that [0 < n],
[(Zero [<] eps)], [forall (k : nat)(Zero [<=] (a k))], [(a n) [=] One], and
[(eps [<=] a_0)].
%\end{convention}%
*)

Variable a : nat -> IR.
Variable n : nat.
Hypothesis gt_n_0 : 0 < n.
Variable eps : IR.
Hypothesis eps_pos : Zero [<] eps.
Hypothesis a_nonneg : forall k : nat, Zero [<=] a k.
Hypothesis a_n_1 : a n [=] One.
Variable a_0 : IR.
Hypothesis eps_le_a_0 : eps [<=] a_0.

Lemma a_0_pos : Zero [<] a_0.
apply less_leEq_trans with eps; auto.
Qed.

(** 
%\begin{convention}% We define the following local abbreviations:
 - [two_n := 2 * n]
 - [Small := p3m n]
 - [Smaller := p3m (two_n * n)]

%\end{convention}%
*)

(* begin hide *)
Let two_n := 2 * n.
Let Small := p3m n.
Let Smaller := p3m (two_n * n).
(* end hide *)

Lemma Main_1a' : forall (t : IR) (j k : nat),
 let r' := t[*]p3m (S (S j)) in let r := t[*]p3m (S j) in
 (forall i, 1 <= i -> i <= n -> a i[*]r'[^]i[-]eps [<=] a k[*]r'[^]k) ->
 forall i : nat, 1 <= i -> i <= n -> a i[*] (r [/]ThreeNZ) [^]i[-]eps [<=] a k[*] (r [/]ThreeNZ) [^]k.
(* begin hide *)
intros.
cut ((t[*]p3m (S j)) [/]ThreeNZ [=] t[*]p3m (S (S j))). intro.
astepl (a i[*] (t[*]p3m (S (S j))) [^]i[-]eps).
astepr (a k[*] (t[*]p3m (S (S j))) [^]k).
auto.

Step_final (t[*]p3m (S j) [/]ThreeNZ).
Qed.
(* end hide *)

Lemma Main_1b' : forall (t : IR) (j k : nat),
 let r' := t[*]p3m j in let r := t[*]p3m (S j) in
 (forall i, 1 <= i -> i <= n -> a i[*]r'[^]i[-]eps [<=] a k[*]r'[^]k) ->
 forall i, 1 <= i -> i <= n -> a i[*] (r[*]Three) [^]i[-]eps [<=] a k[*] (r[*]Three) [^]k.
(* begin hide *)
intros.
cut (t[*]p3m (S j) [*]Three [=] t[*]p3m j). intro.
astepl (a i[*] (t[*]p3m j) [^]i[-]eps).
astepr (a k[*] (t[*]p3m j) [^]k).
auto.

Step_final (t[*] (p3m (S j) [*]Three)).
Qed.
(* end hide *)

Lemma Main_1a : forall (r : IR) (k : nat), Zero [<=] r -> 1 <= k -> k <= n ->
 (forall i, 1 <= i -> i <= n -> a i[*] (r [/]ThreeNZ) [^]i[-]eps [<=] a k[*] (r [/]ThreeNZ) [^]k) ->
 let p_ := fun i : nat => a i[*]r[^]i in let p_k := a k[*]r[^]k in
 Sum 1 (pred k) p_ [<=] Half[*] (One[-]Small) [*]p_k[+]Half[*]Three[^]n[*]eps.
(* begin hide *)
intros r k H H0 H1 H2 p_ p_k.
unfold p_, p_k in |- *.
apply
 leEq_transitive
  with
    (Sum 1 (pred k)
       (fun i : nat => Three[^]i[*] (a k[*] (r [/]ThreeNZ) [^]k[+]eps))).
 apply Sum_resp_leEq.
  auto with arith.
 intros i H3 H4.
 cut (Three[^]i [#] ZeroR).
 intro H5.
 apply shift_leEq_mult' with H5.
  apply nexp_resp_pos.
  apply pos_three.
 astepl (a i[*] (r[^]i[/] Three[^]i[//]H5)).
 astepl (a i[*] (r [/]ThreeNZ) [^]i).
 astepr (eps[+]a k[*] (r [/]ThreeNZ) [^]k).
 apply shift_leEq_plus'.
 apply H2.
  assumption.
 omega.

 apply nexp_resp_ap_zero.
 apply three_ap_zero.
apply
 leEq_wdl
  with
    (Sum 1 (pred k) (fun i : nat => Three[^]i) [*]
     (a k[*] (r [/]ThreeNZ) [^]k[+]eps)).
 cut (Three[-]One [#] ZeroR).
 intro H3.
 astepl
  ((Three[^]S (pred k) [-]Three[^]1[/] Three[-]One[//]H3) [*]
   (a k[*] (r [/]ThreeNZ) [^]k[+]eps)).
 rewrite <- (S_pred _ _ H0).
 astepl
  ((Three[^]k[-]Three[/] Three[-]One[//]H3) [*]
   (a k[*] (r [/]ThreeNZ) [^]k[+]eps)).
 rstepl
  (One [/]TwoNZ[*] (Three[^]k[-]Three) [*] (a k[*] (r [/]ThreeNZ) [^]k) [+]
   One [/]TwoNZ[*] (Three[^]k[-]Three) [*]eps).
 apply
  leEq_transitive
   with
     (Half[*] (One[-]Small) [*] (a k[*]r[^]k) [+]
      One [/]TwoNZ[*] (Three[^]k[-]Three) [*]eps).
  apply plus_resp_leEq.
  cut (Three[^]k [#] ZeroR).
  intro H4.
  astepl
   (One [/]TwoNZ[*] (Three[^]k[-]Three) [*] (a k[*] (r[^]k[/] Three[^]k[//]H4))).
  rstepl (One [/]TwoNZ[*]a k[*]r[^]k[*] (One[-] (Three[/] Three[^]k[//]H4))).
  rstepr (Half[*]a k[*]r[^]k[*] (One[-]Small)).
  unfold Half in |- *.
  apply mult_resp_leEq_lft.
   apply minus_resp_leEq_both.
    apply leEq_reflexive.
   unfold Small in |- *.
   unfold p3m in |- *.
   cut (Three[^]pred k [#] ZeroR).
   intro H5.
   apply leEq_wdr with (One[/] Three[^]pred k[//]H5).
    cut (Three[^]n [#] ZeroR).
    intro H6.
    astepl (One[/] Three[^]n[//]H6).
    apply recip_resp_leEq.
     apply nexp_resp_pos.
     apply pos_three.
    apply great_nexp_resp_le.
     apply less_leEq; apply one_less_three.
    omega.

    apply nexp_resp_ap_zero.
    apply three_ap_zero.
   apply eq_div.
   pattern k at 1 in |- *.
   rewrite (S_pred _ _ H0).
   astepl (One[*] (Three[*]Three[^]pred k):IR).
   rational.

   apply nexp_resp_ap_zero.
   apply three_ap_zero.
  apply mult_resp_nonneg.
   apply mult_resp_nonneg.
    apply less_leEq.
    astepr (Half:IR).
    apply pos_half.
   apply a_nonneg.
  apply nexp_resp_nonneg; auto.

  apply nexp_resp_ap_zero.
  apply three_ap_zero.
 apply plus_resp_leEq_lft.
 rstepl (One [/]TwoNZ[*]eps[*] (Three[^]k[-]Three)).
 rstepr (Half[*]eps[*]Three[^]n).
 unfold Half in |- *.
 apply mult_resp_leEq_lft.
  apply leEq_transitive with (Three[^]k:IR).
   astepr (Three[^]k[-]ZeroR).
   apply minus_resp_leEq_rht.
   apply less_leEq; apply pos_three.
  apply great_nexp_resp_le; auto.
  apply less_leEq; apply one_less_three.
 apply less_leEq; apply mult_resp_pos; auto.
 astepr (Half:IR); apply pos_half.
rstepl (Two:IR).
apply two_ap_zero.

apply eq_symmetric_unfolded.
apply mult_distr_sum_rht with (f := fun i : nat => (Three:IR) [^]i).
Qed.
(* end hide *)

Lemma Main_1b : forall (r : IR) (k : nat), Zero [<=] r -> 1 <= k -> k <= n ->
 (forall i,  1 <= i -> i <= n -> a i[*] (r[*]Three) [^]i[-]eps [<=] a k[*] (r[*]Three) [^]k) ->
 let p_ := fun i => a i[*]r[^]i in let p_k := a k[*]r[^]k in
 Sum (S k) n p_ [<=] Half[*] (One[-]Small) [*]p_k[+]Half[*]Three[^]n[*]eps.
(* begin hide *)
intros r k H H0 H1 H2 p_ p_k.
unfold p_, p_k in |- *.
cut (forall i : nat, Three[^]i [#] ZeroR).
intro H3.
 2: intro i; apply pos_ap_zero.
 2: apply nexp_resp_pos.
 2: apply pos_three.
apply
 leEq_transitive
  with
    (Sum (S k) n
       (fun i : nat => a k[*] (r[*]Three) [^]k[+]eps[/] Three[^]i[//]H3 i)).
 apply Sum_resp_leEq.
  auto with arith.
 intros i H4 H5.
 apply shift_leEq_div.
  apply nexp_resp_pos; apply pos_three.
 rstepr (eps[+]a k[*] (r[*]Three) [^]k).
 apply shift_leEq_plus'.
 rstepl (a i[*] (r[^]i[*]Three[^]i) [-]eps).
 astepl (a i[*] (r[*]Three) [^]i[-]eps).
 apply H2; auto with arith.
 apply le_trans with (S k); auto.
astepl
 (Sum (S k) n
    (fun i : nat => (a k[*] (r[*]Three) [^]k[+]eps) [*]One[/] Three[^]i[//]H3 i)).
astepl
 (Sum (S k) n
    (fun i : nat =>
     (a k[*] (r[*]Three) [^]k[+]eps) [*] (One[/] Three[^]i[//]H3 i))).
apply
 leEq_wdl
  with
    ((a k[*] (r[*]Three) [^]k[+]eps) [*]
     Sum (S k) n (fun i : nat => One[/] Three[^]i[//]H3 i)).
 2: apply eq_symmetric_unfolded.
 2: apply
     mult_distr_sum_lft with (f := fun i : nat => One[/] Three[^]i[//]H3 i).
astepl
 ((a k[*] (r[*]Three) [^]k[+]eps) [*]
  Sum (S k) n (fun i : nat => (One [/]ThreeNZ) [^]i)).
cut (One[-]One [/]ThreeNZ [#] ZeroR).
 2: rstepl ((Two:IR) [/]ThreeNZ).
 2: apply div_resp_ap_zero_rev.
 2: apply two_ap_zero.
intro H4.
astepl
 ((a k[*] (r[*]Three) [^]k[+]eps) [*]
  ((One [/]ThreeNZ) [^]S k[-] (One [/]ThreeNZ) [^]S n[/]
   One[-]One [/]ThreeNZ[//]H4)).
astepl
 ((a k[*] (r[*]Three) [^]k[+]eps) [*]
  (One [/]ThreeNZ[*] (One [/]ThreeNZ) [^]k[-]
   One [/]ThreeNZ[*] (One [/]ThreeNZ) [^]n[/] One[-]One [/]ThreeNZ[//]H4)).
rstepl
 (One [/]TwoNZ[*] (a k[*] (r[*]Three) [^]k) [*]
  ((One [/]ThreeNZ) [^]k[-] (One [/]ThreeNZ) [^]n) [+]
  One [/]TwoNZ[*]eps[*] ((One [/]ThreeNZ) [^]k[-] (One [/]ThreeNZ) [^]n)).
apply
 leEq_transitive
  with
    (Half[*] (One[-]Small) [*] (a k[*]r[^]k) [+]
     One [/]TwoNZ[*]eps[*] ((One [/]ThreeNZ) [^]k[-] (One [/]ThreeNZ) [^]n)).
 apply plus_resp_leEq.
 astepl
  (One [/]TwoNZ[*] (a k[*] (r[^]k[*]Three[^]k)) [*]
   ((One [/]ThreeNZ) [^]k[-] (One [/]ThreeNZ) [^]n)).
 rstepl
  (One [/]TwoNZ[*]a k[*]r[^]k[*]
   (Three[^]k[*] (One [/]ThreeNZ) [^]k[-]Three[^]k[*] (One [/]ThreeNZ) [^]n)).
 unfold Half in |- *.
 rstepr (One [/]TwoNZ[*]a k[*]r[^]k[*] (One[-]Small)).
 apply mult_resp_leEq_lft.
  astepl
   (((Three:IR) [*]One [/]ThreeNZ) [^]k[-]Three[^]k[*] (One [/]ThreeNZ) [^]n).
  astepl
   ((((Three:IR) [*]One) [/]ThreeNZ) [^]k[-]Three[^]k[*] (One [/]ThreeNZ) [^]n).
  astepl (((Three:IR) [/]ThreeNZ) [^]k[-]Three[^]k[*] (One [/]ThreeNZ) [^]n).
  astepl (OneR[^]k[-]Three[^]k[*] (One [/]ThreeNZ) [^]n).
  astepl (OneR[-]Three[^]k[*] (One [/]ThreeNZ) [^]n).
  apply less_leEq.
  apply minus_resp_less_rht.
  unfold Small in |- *.
  unfold p3m in |- *.
  rstepl (OneR[*] (One [/]ThreeNZ) [^]n).
  apply mult_resp_less.
   astepl (OneR[^]k).
   apply nexp_resp_less; auto.
    apply less_leEq; apply pos_one.
   apply one_less_three.
   apply nexp_resp_pos.
   apply pos_div_three; apply pos_one.
 apply mult_resp_nonneg.
  apply mult_resp_nonneg.
   apply less_leEq.
   apply pos_div_two; apply pos_one.
  apply a_nonneg.
 apply nexp_resp_nonneg; assumption.
apply plus_resp_leEq_lft.
rstepr (Half[*]eps[*]Three[^]n).
unfold Half in |- *.
apply mult_resp_leEq_lft.
 apply leEq_transitive with OneR.
  apply leEq_transitive with ((OneR [/]ThreeNZ) [^]k).
   astepr ((OneR [/]ThreeNZ) [^]k[-]Zero).
   apply less_leEq.
   apply minus_resp_less_rht.
   apply nexp_resp_pos.
   apply pos_div_three; apply pos_one.
  astepr (One[^]k:IR).
  apply nexp_resp_leEq.
   apply less_leEq; apply pos_div_three; apply pos_one.
  astepr (OneR [/]OneNZ).
  apply less_leEq; apply recip_resp_less.
   apply pos_one.
  apply one_less_three.
  astepl (OneR[^]n).
  apply nexp_resp_leEq; apply less_leEq.
  apply pos_one.
  apply one_less_three.
apply less_leEq.
apply mult_resp_pos; auto.
apply pos_div_two; apply pos_one.
Qed.
(* end hide *)

Lemma Main_1 : forall (r : IR) (k : nat), Zero [<=] r -> 1 <= k -> k <= n ->
 (forall i,  1 <= i ->  i <= n -> a i[*] (r [/]ThreeNZ) [^]i[-]eps [<=] a k[*] (r [/]ThreeNZ) [^]k) ->
 (forall i,  1 <= i -> i <= n -> a i[*] (r[*]Three) [^]i[-]eps [<=] a k[*] (r[*]Three) [^]k) ->
 let p_ := fun i => a i[*]r[^]i in let p_k := a k[*]r[^]k in
 Sum 1 (pred k) p_[+]Sum (S k) n p_ [<=] (One[-]Small) [*]p_k[+]Three[^]n[*]eps.
(* begin hide *)
intros r k H H0 H1 H2 H3 p_ p_k.
unfold p_, p_k in |- *.
set (h := Half[*] (One[-]Small) [*]p_k[+]Half[*]Three[^]n[*]eps) in *.
apply leEq_wdr with (h[+]h); unfold h, p_k in |- *.
 apply plus_resp_leEq_both.
  apply Main_1a; auto.
 apply Main_1b; auto.
unfold Half in |- *; rational.
Qed.
(* end hide *)

Lemma Main_2' : forall (t : IR) (i k : nat),
 a i[*] (t[*]p3m 0) [^]i[-]eps [<=] a k[*] (t[*]p3m 0) [^]k -> a i[*]t[^]i[-]eps [<=] a k[*]t[^]k.
intros.
cut (t[*]p3m 0 [=] t). intro.
astepl (a i[*] (t[*]p3m 0) [^]i[-]eps).
astepr (a k[*] (t[*]p3m 0) [^]k).
auto.

Step_final (t[*]One).
Qed.

Lemma Main_2 : forall (t : IR) (j k : nat), let r := t[*]p3m j in
 Zero [<=] t -> a k[*]t[^]k [=] a_0[-]eps -> (forall i, 1 <= i -> i <= n -> a i[*]t[^]i[-]eps [<=] a k[*]t[^]k) ->
 forall i, 1 <= i -> i <= n -> a i[*]r[^]i [<=] a_0.
(* begin hide *)
intros.
unfold r in |- *.
apply leEq_transitive with (a i[*]t[^]i).
 astepl (a i[*] (t[^]i[*]p3m j[^]i)).
 rstepl (p3m j[^]i[*] (a i[*]t[^]i)).
 astepr (One[*] (a i[*]t[^]i)).
 apply mult_resp_leEq_rht.
  astepr (One[^]i:IR).
  apply nexp_resp_leEq.
   apply less_leEq; apply p3m_pos.
  apply p3m_small.
 astepl (Zero[*]t[^]i).
 apply mult_resp_leEq_rht; auto.
 astepl (Zero[^]i:IR).
 apply nexp_resp_leEq; auto.
 apply leEq_reflexive.
apply leEq_wdr with (eps[+]a k[*]t[^]k).
 apply shift_leEq_plus'; auto.
astepl (eps[+] (a_0[-]eps)); rational.
Qed.
(* end hide *)

Lemma Main_3a : forall (t : IR) (j k k_0 : nat), let r := t[*]p3m j in
 k_0 <= n -> a k_0[*]t[^]k_0 [=] a_0[-]eps -> a k_0[*]r[^]k_0[-]eps [<=] a k[*]r[^]k ->
 p3m (j * n) [*]a_0[-]Two[*]eps [<=] a k[*]r[^]k.
(* begin hide *)
intros.
unfold r in |- *.
rstepl (p3m (j * n) [*]a_0[-]eps[-]eps).
apply leEq_transitive with (a k_0[*] (t[*]p3m j) [^]k_0[-]eps); auto.
apply minus_resp_leEq.
astepr (a k_0[*] (t[^]k_0[*]p3m j[^]k_0)).
astepr (a k_0[*] (t[^]k_0[*]p3m (j * k_0))).
rstepr (p3m (j * k_0) [*] (a k_0[*]t[^]k_0)).
astepr (p3m (j * k_0) [*] (a_0[-]eps)).
astepr (p3m (j * k_0) [*]a_0[-]p3m (j * k_0) [*]eps).
apply minus_resp_leEq_both.
 apply mult_resp_leEq_rht.
  apply p3m_mon'; auto with arith.
 apply less_leEq; apply a_0_pos.
astepr (One[*]eps).
apply mult_resp_leEq_rht.
 apply p3m_small.
apply less_leEq; auto.
Qed.
(* end hide *)

Lemma Main_3 : forall (t : IR) (j k k_0 : nat), let r := t[*]p3m j in
 j < two_n -> k_0 <= n -> a k_0[*]t[^]k_0 [=] a_0[-]eps -> a k_0[*]r[^]k_0[-]eps [<=] a k[*]r[^]k ->
 Smaller[*]a_0[-]Two[*]eps [<=] a k[*]r[^]k.
(* begin hide *)
intros t j k k_0 r H H0 H1 H2.
unfold r in |- *.
apply leEq_transitive with (p3m (j * n) [*]a_0[-]Two[*]eps).
 apply minus_resp_leEq.
 apply mult_resp_leEq_rht.
  unfold Smaller in |- *.
  apply p3m_mon'.
  apply mult_le_compat_r; auto with arith.
 apply less_leEq; apply a_0_pos.
apply Main_3a with k_0; auto.
Qed.
(* end hide *)

Lemma Main : {r : IR | Zero [<=] r | {k : nat | 1 <= k /\ k <= n /\
 (let p_ := fun i => a i[*]r[^]i in let p_k := a k[*]r[^]k in
  Sum 1 (pred k) p_[+]Sum (S k) n p_ [<=] (One[-]Small) [*]p_k[+]Three[^]n[*]eps /\
  r[^]n [<=] a_0 /\ Smaller[*]a_0[-]Two[*]eps [<=] p_k /\ p_k [<=] a_0)}}.
(* begin hide *)
Proof.
elim (Key a n gt_n_0 eps eps_pos a_nonneg a_n_1 a_0 eps_le_a_0).
intro t. intros H0 H1. 
elim (H1 two_n). intro k. intros H2.
elim H2. intros H3 H4. 
elim H4. intros H5 H6.
elim H6. intros H7 H8.
elim (kseq_prop k n H3 H5). intro j. intros H9.
elim H9. intros H10 H11. elim H11. intros H12 H13.
clear H9 H6 H4 H2 H1.
cut (Zero [<=] t[*]p3m (S j)). intro H14.
2: apply mult_resp_nonneg; auto.
2: apply less_leEq; apply p3m_pos.
exists (t[*]p3m (S j)).
auto.
exists (k (S j)).
elim (H3 (S j)); intros H3' H3''.
split. auto.
split. auto.
intros p_ p_k. (* patch *)
split; unfold p_, p_k in |- *.
 apply Main_1; auto.
  intros i H15 H16.
  apply Main_1a'; auto.
  intros i0 H17 H18.
  rewrite H13.
  apply H8; auto with arith.
 intros i H15 H16.
 apply Main_1b'; auto.
 intros i0 H17 H18.
 rewrite <- H12.
 apply H8; auto with arith.
 apply le_trans with (S j); auto with arith.
split.
 astepl (One[*] (t[*]p3m (S j)) [^]n).
 astepl (a n[*] (t[*]p3m (S j)) [^]n).
 apply Main_2 with (k 0); auto.
 intros i H15 H16.
 apply Main_2'.
 apply H8; auto with arith.
elim (H3 0); intros H3''' H3''''.
split.
 apply Main_3 with (k 0); auto.
 apply H8; auto with arith.
apply Main_2 with (k 0); auto.
intros i H15 H16.
apply Main_2'; auto with arith.
Qed.
(* end hide *)

End Main_Lemma.
