(* $Id$ *)

(** printing two_n %\ensuremath{2n}% #2n# *)
(** printing Small %\ensuremath{\frac13^n}% *)
(** printing Smaller %\ensuremath{\frac13^{2n^2}}% *)

Require Export CSumsReals.
Require Export KeyLemma.

(**
* Main Lemma
*)

Section Main_Lemma.

(**
%\begin{convention}%
Let [a:nat->IR], [n:nat], [a_0:IR]  and [eps:IR] such that [(lt (0) n)],
[(Zero [<] eps)], [(k:nat)(Zero [<=] (a k))], [(a n) [=] One], and
[(eps [<=] a_0)].
%\end{convention}%
*)
Variable a : nat -> IR.
Variable n : nat.
Hypothesis gt_n_0 : 0 < n.
Variable eps : IR.
Hypothesis eps_pos : Zero[<]eps.
Hypothesis a_nonneg : forall k : nat, Zero[<=]a k.
Hypothesis a_n_1 : a n[=]One.
Variable a_0 : IR.
Hypothesis eps_le_a_0 : eps[<=]a_0.

Lemma a_0_pos : Zero[<]a_0.
apply less_leEq_trans with eps; auto.
Qed.


Let two_n := 2 * n.
Let Small := p3m n.
Let Smaller := p3m (two_n * n).

Lemma Main_1a' :
 forall (t : IR) (j k : nat),
 let r' := t[*]p3m (S (S j)) in
 let r := t[*]p3m (S j) in
 (forall i : nat, 1 <= i -> i <= n -> a i[*]r'[^]i[-]eps[<=]a k[*]r'[^]k) ->
 forall i : nat,
 1 <= i ->
 i <= n -> a i[*](r [/]ThreeNZ)[^]i[-]eps[<=]a k[*](r [/]ThreeNZ)[^]k.
intros.
cut ((t[*]p3m (S j)) [/]ThreeNZ[=]t[*]p3m (S (S j))). intro.
AStepl (a i[*](t[*]p3m (S (S j)))[^]i[-]eps).
AStepr (a k[*](t[*]p3m (S (S j)))[^]k).
auto.

Step_final (t[*]p3m (S j) [/]ThreeNZ).
Qed.

Lemma Main_1b' :
 forall (t : IR) (j k : nat),
 let r' := t[*]p3m j in
 let r := t[*]p3m (S j) in
 (forall i : nat, 1 <= i -> i <= n -> a i[*]r'[^]i[-]eps[<=]a k[*]r'[^]k) ->
 forall i : nat,
 1 <= i -> i <= n -> a i[*](r[*]Three)[^]i[-]eps[<=]a k[*](r[*]Three)[^]k.
intros.
cut (t[*]p3m (S j)[*]Three[=]t[*]p3m j). intro.
AStepl (a i[*](t[*]p3m j)[^]i[-]eps).
AStepr (a k[*](t[*]p3m j)[^]k).
auto.

Step_final (t[*](p3m (S j)[*]Three)).
Qed.

Lemma Main_1a :
 forall (r : IR) (k : nat),
 Zero[<=]r ->
 1 <= k ->
 k <= n ->
 (forall i : nat,
  1 <= i ->
  i <= n -> a i[*](r [/]ThreeNZ)[^]i[-]eps[<=]a k[*](r [/]ThreeNZ)[^]k) ->
 let p_ := fun i : nat => a i[*]r[^]i in
 let p_k := a k[*]r[^]k in
 Sum 1 (pred k) p_[<=]Half[*](One[-]Small)[*]p_k[+]Half[*]Three[^]n[*]eps.
intros r k H H0 H1 H2 p_ p_k.
unfold p_, p_k in |- *.
apply
 leEq_transitive
  with
    (Sum 1 (pred k)
       (fun i : nat => Three[^]i[*](a k[*](r [/]ThreeNZ)[^]k[+]eps))).
 apply Sum_resp_leEq.
  auto with arith.
 intros i H3 H4.
 cut (Three[^]i[#]ZeroR).
 intro H5.
 apply shift_leEq_mult' with H5.
  apply nexp_resp_pos.
  apply pos_three.
 AStepl (a i[*](r[^]i[/] Three[^]i[//]H5)).
 AStepl (a i[*](r [/]ThreeNZ)[^]i).
 AStepr (eps[+]a k[*](r [/]ThreeNZ)[^]k).
 apply shift_leEq_plus'.
 apply H2.
  assumption.
 omega.

 apply nexp_resp_ap_zero.
 apply three_ap_zero.
apply
 leEq_wdl
  with
    (Sum 1 (pred k) (fun i : nat => Three[^]i)[*]
     (a k[*](r [/]ThreeNZ)[^]k[+]eps)).
 cut (Three[-]One[#]ZeroR).
 intro H3.
 AStepl
  ((Three[^]S (pred k)[-]Three[^]1[/] Three[-]One[//]H3)[*]
   (a k[*](r [/]ThreeNZ)[^]k[+]eps)).
 rewrite <- (S_pred _ _ H0).
 AStepl
  ((Three[^]k[-]Three[/] Three[-]One[//]H3)[*]
   (a k[*](r [/]ThreeNZ)[^]k[+]eps)).
 RStepl
  (One [/]TwoNZ[*](Three[^]k[-]Three)[*](a k[*](r [/]ThreeNZ)[^]k)[+]
   One [/]TwoNZ[*](Three[^]k[-]Three)[*]eps).
 apply
  leEq_transitive
   with
     (Half[*](One[-]Small)[*](a k[*]r[^]k)[+]
      One [/]TwoNZ[*](Three[^]k[-]Three)[*]eps).
  apply plus_resp_leEq.
  cut (Three[^]k[#]ZeroR).
  intro H4.
  AStepl
   (One [/]TwoNZ[*](Three[^]k[-]Three)[*](a k[*](r[^]k[/] Three[^]k[//]H4))).
  RStepl (One [/]TwoNZ[*]a k[*]r[^]k[*](One[-](Three[/] Three[^]k[//]H4))).
  RStepr (Half[*]a k[*]r[^]k[*](One[-]Small)).
  unfold Half in |- *.
  apply mult_resp_leEq_lft.
   apply minus_resp_leEq_both.
    apply leEq_reflexive.
   unfold Small in |- *.
   unfold p3m in |- *.
   cut (Three[^]pred k[#]ZeroR).
   intro H5.
   apply leEq_wdr with (One[/] Three[^]pred k[//]H5).
    cut (Three[^]n[#]ZeroR).
    intro H6.
    AStepl (One[/] Three[^]n[//]H6).
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
   AStepl (One[*](Three[*]Three[^]pred k):IR).
   rational.

   apply nexp_resp_ap_zero.
   apply three_ap_zero.
  apply mult_resp_nonneg.
   apply mult_resp_nonneg.
    apply less_leEq.
    AStepr (Half:IR).
    apply pos_half.
   apply a_nonneg.
  apply nexp_resp_nonneg; auto.

  apply nexp_resp_ap_zero.
  apply three_ap_zero.
 apply plus_resp_leEq_lft.
 RStepl (One [/]TwoNZ[*]eps[*](Three[^]k[-]Three)).
 RStepr (Half[*]eps[*]Three[^]n).
 unfold Half in |- *.
 apply mult_resp_leEq_lft.
  apply leEq_transitive with (Three[^]k:IR).
   AStepr (Three[^]k[-]ZeroR).
   apply minus_resp_leEq_rht.
   apply less_leEq; apply pos_three.
  apply great_nexp_resp_le; auto.
  apply less_leEq; apply one_less_three.
 apply less_leEq; apply mult_resp_pos; auto.
 AStepr (Half:IR); apply pos_half.
RStepl (Two:IR).
apply two_ap_zero.

apply eq_symmetric_unfolded.
apply mult_distr_sum_rht with (f := fun i : nat => (Three:IR)[^]i).
Qed.

Lemma Main_1b :
 forall (r : IR) (k : nat),
 Zero[<=]r ->
 1 <= k ->
 k <= n ->
 (forall i : nat,
  1 <= i -> i <= n -> a i[*](r[*]Three)[^]i[-]eps[<=]a k[*](r[*]Three)[^]k) ->
 let p_ := fun i : nat => a i[*]r[^]i in
 let p_k := a k[*]r[^]k in
 Sum (S k) n p_[<=]Half[*](One[-]Small)[*]p_k[+]Half[*]Three[^]n[*]eps.
intros r k H H0 H1 H2 p_ p_k.
unfold p_, p_k in |- *.
cut (forall i : nat, Three[^]i[#]ZeroR).
intro H3.
 2: intro i; apply pos_ap_zero.
 2: apply nexp_resp_pos.
 2: apply pos_three.
apply
 leEq_transitive
  with
    (Sum (S k) n
       (fun i : nat => a k[*](r[*]Three)[^]k[+]eps[/] Three[^]i[//]H3 i)).
 apply Sum_resp_leEq.
  auto with arith.
 intros i H4 H5.
 apply shift_leEq_div.
  apply nexp_resp_pos; apply pos_three.
 RStepr (eps[+]a k[*](r[*]Three)[^]k).
 apply shift_leEq_plus'.
 RStepl (a i[*](r[^]i[*]Three[^]i)[-]eps).
 AStepl (a i[*](r[*]Three)[^]i[-]eps).
 apply H2; auto with arith.
 apply le_trans with (S k); auto.
AStepl
 (Sum (S k) n
    (fun i : nat => (a k[*](r[*]Three)[^]k[+]eps)[*]One[/] Three[^]i[//]H3 i)).
AStepl
 (Sum (S k) n
    (fun i : nat =>
     (a k[*](r[*]Three)[^]k[+]eps)[*](One[/] Three[^]i[//]H3 i))).
apply
 leEq_wdl
  with
    ((a k[*](r[*]Three)[^]k[+]eps)[*]
     Sum (S k) n (fun i : nat => One[/] Three[^]i[//]H3 i)).
 2: apply eq_symmetric_unfolded.
 2: apply
     mult_distr_sum_lft with (f := fun i : nat => One[/] Three[^]i[//]H3 i).
AStepl
 ((a k[*](r[*]Three)[^]k[+]eps)[*]
  Sum (S k) n (fun i : nat => (One [/]ThreeNZ)[^]i)).
cut (One[-]One [/]ThreeNZ[#]ZeroR).
 2: RStepl ((Two:IR) [/]ThreeNZ).
 2: apply div_resp_ap_zero_rev.
 2: apply two_ap_zero.
intro H4.
AStepl
 ((a k[*](r[*]Three)[^]k[+]eps)[*]
  ((One [/]ThreeNZ)[^]S k[-](One [/]ThreeNZ)[^]S n[/]
   One[-]One [/]ThreeNZ[//]H4)).
AStepl
 ((a k[*](r[*]Three)[^]k[+]eps)[*]
  (One [/]ThreeNZ[*](One [/]ThreeNZ)[^]k[-]
   One [/]ThreeNZ[*](One [/]ThreeNZ)[^]n[/] One[-]One [/]ThreeNZ[//]H4)).
RStepl
 (One [/]TwoNZ[*](a k[*](r[*]Three)[^]k)[*]
  ((One [/]ThreeNZ)[^]k[-](One [/]ThreeNZ)[^]n)[+]
  One [/]TwoNZ[*]eps[*]((One [/]ThreeNZ)[^]k[-](One [/]ThreeNZ)[^]n)).
apply
 leEq_transitive
  with
    (Half[*](One[-]Small)[*](a k[*]r[^]k)[+]
     One [/]TwoNZ[*]eps[*]((One [/]ThreeNZ)[^]k[-](One [/]ThreeNZ)[^]n)).
 apply plus_resp_leEq.
 AStepl
  (One [/]TwoNZ[*](a k[*](r[^]k[*]Three[^]k))[*]
   ((One [/]ThreeNZ)[^]k[-](One [/]ThreeNZ)[^]n)).
 RStepl
  (One [/]TwoNZ[*]a k[*]r[^]k[*]
   (Three[^]k[*](One [/]ThreeNZ)[^]k[-]Three[^]k[*](One [/]ThreeNZ)[^]n)).
 unfold Half in |- *.
 RStepr (One [/]TwoNZ[*]a k[*]r[^]k[*](One[-]Small)).
 apply mult_resp_leEq_lft.
  AStepl
   (((Three:IR)[*]One [/]ThreeNZ)[^]k[-]Three[^]k[*](One [/]ThreeNZ)[^]n).
  AStepl
   ((((Three:IR)[*]One) [/]ThreeNZ)[^]k[-]Three[^]k[*](One [/]ThreeNZ)[^]n).
  AStepl (((Three:IR) [/]ThreeNZ)[^]k[-]Three[^]k[*](One [/]ThreeNZ)[^]n).
  AStepl (OneR[^]k[-]Three[^]k[*](One [/]ThreeNZ)[^]n).
  AStepl (OneR[-]Three[^]k[*](One [/]ThreeNZ)[^]n).
  apply less_leEq.
  apply minus_resp_less_rht.
  unfold Small in |- *.
  unfold p3m in |- *.
  RStepl (OneR[*](One [/]ThreeNZ)[^]n).
  apply mult_resp_less.
   AStepl (OneR[^]k).
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
RStepr (Half[*]eps[*]Three[^]n).
unfold Half in |- *.
apply mult_resp_leEq_lft.
 apply leEq_transitive with OneR.
  apply leEq_transitive with ((OneR [/]ThreeNZ)[^]k).
   AStepr ((OneR [/]ThreeNZ)[^]k[-]Zero).
   apply less_leEq.
   apply minus_resp_less_rht.
   apply nexp_resp_pos.
   apply pos_div_three; apply pos_one.
  AStepr (One[^]k:IR).
  apply nexp_resp_leEq.
   apply less_leEq; apply pos_div_three; apply pos_one.
  AStepr (OneR [/]OneNZ).
  apply less_leEq; apply recip_resp_less.
   apply pos_one.
  apply one_less_three.
  AStepl (OneR[^]n).
  apply nexp_resp_leEq; apply less_leEq.
  apply pos_one.
  apply one_less_three.
apply less_leEq.
apply mult_resp_pos; auto.
apply pos_div_two; apply pos_one.
Qed.

Lemma Main_1 :
 forall (r : IR) (k : nat),
 Zero[<=]r ->
 1 <= k ->
 k <= n ->
 (forall i : nat,
  1 <= i ->
  i <= n -> a i[*](r [/]ThreeNZ)[^]i[-]eps[<=]a k[*](r [/]ThreeNZ)[^]k) ->
 (forall i : nat,
  1 <= i -> i <= n -> a i[*](r[*]Three)[^]i[-]eps[<=]a k[*](r[*]Three)[^]k) ->
 let p_ := fun i : nat => a i[*]r[^]i in
 let p_k := a k[*]r[^]k in
 Sum 1 (pred k) p_[+]Sum (S k) n p_[<=](One[-]Small)[*]p_k[+]Three[^]n[*]eps.
intros r k H H0 H1 H2 H3 p_ p_k.
unfold p_, p_k in |- *.
set (h := Half[*](One[-]Small)[*]p_k[+]Half[*]Three[^]n[*]eps) in *.
apply leEq_wdr with (h[+]h); unfold h, p_k in |- *.
 apply plus_resp_leEq_both.
  apply Main_1a; auto.
 apply Main_1b; auto.
unfold Half in |- *; rational.
Qed.

Lemma Main_2' :
 forall (t : IR) (i k : nat),
 a i[*](t[*]p3m 0)[^]i[-]eps[<=]a k[*](t[*]p3m 0)[^]k ->
 a i[*]t[^]i[-]eps[<=]a k[*]t[^]k.
intros.
cut (t[*]p3m 0[=]t). intro.
AStepl (a i[*](t[*]p3m 0)[^]i[-]eps).
AStepr (a k[*](t[*]p3m 0)[^]k).
auto.

Step_final (t[*]One).
Qed.

Lemma Main_2 :
 forall (t : IR) (j k : nat),
 let r := t[*]p3m j in
 Zero[<=]t ->
 a k[*]t[^]k[=]a_0[-]eps ->
 (forall i : nat, 1 <= i -> i <= n -> a i[*]t[^]i[-]eps[<=]a k[*]t[^]k) ->
 forall i : nat, 1 <= i -> i <= n -> a i[*]r[^]i[<=]a_0.
intros.
unfold r in |- *.
apply leEq_transitive with (a i[*]t[^]i).
 AStepl (a i[*](t[^]i[*]p3m j[^]i)).
 RStepl (p3m j[^]i[*](a i[*]t[^]i)).
 AStepr (One[*](a i[*]t[^]i)).
 apply mult_resp_leEq_rht.
  AStepr (One[^]i:IR).
  apply nexp_resp_leEq.
   apply less_leEq; apply p3m_pos.
  apply p3m_small.
 AStepl (Zero[*]t[^]i).
 apply mult_resp_leEq_rht; auto.
 AStepl (Zero[^]i:IR).
 apply nexp_resp_leEq; auto.
 apply leEq_reflexive.
apply leEq_wdr with (eps[+]a k[*]t[^]k).
 apply shift_leEq_plus'; auto.
AStepl (eps[+](a_0[-]eps)); rational.
Qed.

Lemma Main_3a :
 forall (t : IR) (j k k_0 : nat),
 let r := t[*]p3m j in
 k_0 <= n ->
 a k_0[*]t[^]k_0[=]a_0[-]eps ->
 a k_0[*]r[^]k_0[-]eps[<=]a k[*]r[^]k ->
 p3m (j * n)[*]a_0[-]Two[*]eps[<=]a k[*]r[^]k.
intros.
unfold r in |- *.
RStepl (p3m (j * n)[*]a_0[-]eps[-]eps).
apply leEq_transitive with (a k_0[*](t[*]p3m j)[^]k_0[-]eps); auto.
apply minus_resp_leEq.
AStepr (a k_0[*](t[^]k_0[*]p3m j[^]k_0)).
AStepr (a k_0[*](t[^]k_0[*]p3m (j * k_0))).
RStepr (p3m (j * k_0)[*](a k_0[*]t[^]k_0)).
AStepr (p3m (j * k_0)[*](a_0[-]eps)).
AStepr (p3m (j * k_0)[*]a_0[-]p3m (j * k_0)[*]eps).
apply minus_resp_leEq_both.
 apply mult_resp_leEq_rht.
  apply p3m_mon'; auto with arith.
 apply less_leEq; apply a_0_pos.
AStepr (One[*]eps).
apply mult_resp_leEq_rht.
 apply p3m_small.
apply less_leEq; auto.
Qed.

Lemma Main_3 :
 forall (t : IR) (j k k_0 : nat),
 let r := t[*]p3m j in
 j < two_n ->
 k_0 <= n ->
 a k_0[*]t[^]k_0[=]a_0[-]eps ->
 a k_0[*]r[^]k_0[-]eps[<=]a k[*]r[^]k ->
 Smaller[*]a_0[-]Two[*]eps[<=]a k[*]r[^]k.
intros t j k k_0 r H H0 H1 H2.
unfold r in |- *.
apply leEq_transitive with (p3m (j * n)[*]a_0[-]Two[*]eps).
 apply minus_resp_leEq.
 apply mult_resp_leEq_rht.
  unfold Smaller in |- *.
  apply p3m_mon'.
  apply mult_le_compat_r; auto with arith.
 apply less_leEq; apply a_0_pos.
apply Main_3a with k_0; auto.
Qed.

Lemma Main :
 {r : IR | Zero[<=]r |
 {k : nat |
 1 <= k /\
 k <= n /\
 (let p_ := fun i : nat => a i[*]r[^]i in
  let p_k := a k[*]r[^]k in
  Sum 1 (pred k) p_[+]Sum (S k) n p_[<=](One[-]Small)[*]p_k[+]Three[^]n[*]eps /\
  r[^]n[<=]a_0 /\ Smaller[*]a_0[-]Two[*]eps[<=]p_k /\ p_k[<=]a_0)}}.
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
cut (Zero[<=]t[*]p3m (S j)). intro H14.
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
 AStepl (One[*](t[*]p3m (S j))[^]n).
 AStepl (a n[*](t[*]p3m (S j))[^]n).
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

End Main_Lemma.