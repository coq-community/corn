(* $Id$ *)

(** printing Smallest %\ensuremath{\frac13^{2n^2+n}}% *)
(** printing eta_0 %\ensuremath{\eta_0}% #&eta;<SUB>0</SUB># *)

Require Export NRootCC.
Require Export AbsCC.
Require Export MainLemma.

(** ** Kneser Lemma *)

Section Kneser_Lemma.

(**
%\begin{convention}% Let [b : nat->CC], [n : nat] and [c : IR]
such that [0 < n], [b_0 := b 0], [b_n := (b n) [=] One] and
[(AbsCC b_0) [<] c].
%\end{convention}%
*)

Variable b : nat -> CC.
Variable n : nat.
Hypothesis gt_n_0 : 0 < n.
(* begin hide *)
Let b_0 := b 0.
Let b_n := b n.
(* end hide *)
Hypothesis b_n_1 : b_n [=] One.
Variable c : IR.
Hypothesis b_0_lt_c : AbsCC b_0 [<] c.

(** 
%\begin{convention}% We define the following local abbreviations:
 - [two_n := 2 * n]
 - [Small := p3m n]
 - [Smaller := p3m (two_n * n)]
 - [Smallest := Small[*]Smaller]
 - [q := One[-]Smallest]
 - [a i := AbsCC (b i)]

%\end{convention}%
*)

(* begin hide *)
Let two_n := 2 * n.
Let Small := p3m n.
Let Smaller := p3m (two_n * n).
Let Smallest := Small[*]Smaller.
Let q := One[-]Smallest.
(* end hide *)

Lemma b_0'_exists : forall eta : IR, Zero [<] eta -> {b_0' : CC | AbsCC (b_0'[-]b_0) [<=] eta | b_0' [#] Zero}.
intros.
exact (Cexis_AFS_CC Zero b_0 eta X).
Qed.

Let eta_0 := ((c[-]AbsCC b_0) [/]FourNZ) [/]TwoNZ.

Lemma eta_0_pos : Zero [<] eta_0.
Proof.
unfold eta_0 in |- *.
apply pos_div_two.
apply pos_div_four.
apply shift_zero_less_minus.
assumption.
Qed.

Lemma eta_exists : {eta : IR | Zero [<] eta |
 {b_0' : CC | AbsCC (b_0'[-]b_0) [<=] eta | b_0' [#] Zero and AbsCC b_0'[+]Three[*]eta [<] c}}.
Proof.
exists eta_0.
 exact eta_0_pos.
generalize (b_0'_exists eta_0 eta_0_pos).
intro H.
elim H.
intros b_0' H0 H1.
exists b_0'.
assumption.
split. assumption.
apply leEq_less_trans with ((AbsCC b_0[+]c) [/]TwoNZ).
2: apply Average_less_Greatest; auto.
apply shift_plus_leEq.
apply leEq_wdl with (AbsCC (b_0'[-]b_0[+]b_0)).
 2: apply AbsCC_wd; rational.
apply leEq_transitive with (AbsCC (b_0'[-]b_0) [+]AbsCC b_0).
 apply triangle.
apply leEq_transitive with (eta_0[+]AbsCC b_0).
 apply plus_resp_leEq; auto.
apply eq_imp_leEq.
unfold eta_0 in |- *; rational.
Qed.

Lemma eps_exists_1 : forall eps x y : IR, Zero [<] eps -> Zero [<] x -> Zero [<] y ->
 {eps' : IR | Zero [<] eps' | eps' [<=] eps /\ x[*]eps' [<=] y}.
intros eps x y Heps Hx Hy.
cut (Zero [<] Half[*]eps). intro H2.
cut (x [#] Zero). intro H3.
2: apply pos_ap_zero; auto.
elim (less_cotransitive_unfolded _ _ _ H2 ((y[/] x[//]H3) [-]Half[*]eps)); intro H5.
 exists (Half[*]eps).
 auto.
 split. apply less_leEq; apply half_3. auto.
 astepr (x[*] (y[/] x[//]H3)).
 apply less_leEq.
 apply mult_resp_less_lft; auto.
 astepl (Zero[+]Half[*]eps).
 apply shift_plus_less; auto.
cut (Zero [<] (y[/] x[//]H3)). intro H4.
 2: apply div_resp_pos; auto.
exists (Half[*] (y[/] x[//]H3)).
apply mult_resp_pos. apply pos_half. auto.
split. apply leEq_transitive with (y[/] x[//]H3).
  apply less_leEq; apply half_3; auto.
 apply less_leEq.
 astepr (One[*]eps).
 astepr ((Half[+]Half) [*]eps).
 astepr (Half[*]eps[+]Half[*]eps).
 apply shift_less_plus'; auto.
rstepl (Half[*]y).
apply less_leEq; apply half_3; auto.
apply mult_resp_pos; auto.
apply pos_half.
Qed.

(* less_cotransitive_unfolded on 
  {Zero  [<]  y[/]x[//]H3[-]Half[*]eps} + 
  {y[/]x[//]H3[-]Half[*]eps  [<]  Half[*]eps}. *)

Lemma eps_exists : forall eta a_0 : IR, Zero [<] eta -> Zero [<] a_0 ->
 {eps : IR | Zero [<] eps | Two[*] (Three[^]n[+]One) [*]eps [<=] eta /\ Three[*]eps [<=] Smaller[*]a_0 /\ eps [<=] a_0}.
intros eta a_0 Heta Ha_0.
elim
 (eps_exists_1 ((Smaller[*]a_0) [/]ThreeNZ) (Three[^]n[+]One) (eta [/]TwoNZ)).
intros eps H H0.
elim H0; intros H1 H2.
exists eps.
auto.
split.
 astepl (Two[*] ((Three[^]n[+]One) [*]eps)).
 apply shift_mult_leEq' with (two_ap_zero IR); auto.
 apply pos_two.
split.
 apply shift_mult_leEq' with (three_ap_zero IR); auto.
 apply pos_three.
eapply leEq_transitive.
 apply H1.
apply shift_div_leEq'.
 apply pos_three.
apply mult_resp_leEq_rht.
 unfold Smaller in |- *; apply leEq_transitive with OneR. apply p3m_small.
 apply less_leEq; apply one_less_three.
apply less_leEq; auto.

apply pos_div_three.
apply mult_resp_pos; auto.
unfold Smaller in |- *; apply p3m_pos.

apply plus_resp_pos.
 apply nexp_resp_pos.
 apply pos_three.
apply pos_one.

apply pos_div_two; auto.
Qed.

(* begin hide *)
Let a (i : nat) : IR := AbsCC (b i).
(* end hide *)

Lemma z_exists : forall (b_0' : CC) (k : nat) (r eta : IR), let a_0 := AbsCC b_0' in
 Zero [<] a_0 -> Zero [<] a k -> 1 <= k -> k <= n -> Zero [<=] r -> Zero [<] eta ->
 AbsCC (b_0'[-]b_0) [<=] eta -> a k[*]r[^]k [<=] a_0 ->
 {z : CC | AbsCC z [=] r | AbsCC (b_0[+]b k[*]z[^]k) [<=] a_0[-]a k[*]r[^]k[+]eta}.
(* begin hide *)
intros b_0' k r eta a_0 H H0 H1 H2 H3 H4 H5 H6.
cut (AbsCC b_0' [#] Zero). intro H7.
 2: apply pos_ap_zero; auto.
cut (cc_IR (AbsCC b_0') [#] Zero). intro H8.
 2: astepr (cc_IR Zero); apply cc_IR_resp_ap; auto.
cut (a k [#] Zero). intro H9.
 2: apply pos_ap_zero; auto.
cut (b k [#] Zero). intro H10.
 2: apply AbsCC_ap_zero; apply ap_symmetric_unfolded; auto.
cut (0 < k). intro H11.
 2: auto with arith.
cut
 ( [--] ((cc_IR (a k) [/] cc_IR (AbsCC b_0') [//]H8) [*] (b_0'[/] b k[//]H10)) [#] 
  Zero). intro H12.
elim
 (CnrootCC
    [--] ((cc_IR (a k) [/] cc_IR (AbsCC b_0') [//]H8) [*] (b_0'[/] b k[//]H10))
    H12 k H11).
intros w H13.
cut (AbsCC w [=] One). intro H14.
exists (cc_IR r[*]w).
 astepl (AbsCC (cc_IR r) [*]AbsCC w).
 astepl (r[*]AbsCC w).
 Step_final (r[*]One).
apply
 leEq_transitive
  with (AbsCC (b_0'[+]b k[*] (cc_IR r[*]w) [^]k) [+]AbsCC (b_0[-]b_0')).
 apply leEq_wdl with (AbsCC (b_0'[+]b k[*] (cc_IR r[*]w) [^]k[+] (b_0[-]b_0'))).
  apply triangle.
 apply AbsCC_wd; rational.
apply leEq_wdl with (AbsCC b_0'[-]a k[*]r[^]k[+]AbsCC (b_0[-]b_0')).
 apply plus_resp_leEq_lft.
 astepl (AbsCC [--] (b_0[-]b_0')).
 apply leEq_wdl with (AbsCC (b_0'[-]b_0)); auto.
 apply AbsCC_wd; rational.
apply bin_op_wd_unfolded.
 2: Algebra.
apply
 eq_transitive_unfolded
  with
    (AbsCC
       ((b_0'[/] cc_IR (AbsCC b_0') [//]H8) [*]
        (cc_IR (AbsCC b_0') [-]cc_IR (a k) [*]cc_IR r[^]k))).
 astepl (One[*] (AbsCC b_0'[-]a k[*]r[^]k)).
 astepr
  (AbsCC (b_0'[/] cc_IR (AbsCC b_0') [//]H8) [*]
   AbsCC (cc_IR (AbsCC b_0') [-]cc_IR (a k) [*]cc_IR r[^]k)).
 apply bin_op_wd_unfolded.
  astepl (AbsCC b_0'[/] AbsCC b_0'[//]H7).
  apply eq_symmetric_unfolded.
  apply cc_div_abs'.
  apply AbsCC_nonneg.
 apply
  eq_transitive_unfolded
   with (AbsCC (cc_IR (AbsCC b_0') [-]cc_IR (a k) [*]cc_IR (r[^]k))).
  2: apply AbsCC_wd; Algebra.
 astepr (AbsCC (cc_IR (AbsCC b_0') [-]cc_IR (a k[*]r[^]k))).
 astepr (AbsCC (cc_IR (AbsCC b_0'[-]a k[*]r[^]k))).
 cut (Zero [<=] AbsCC b_0'[-]a k[*]r[^]k). Algebra.
 apply shift_leEq_lft; auto.
apply AbsCC_wd.
rstepl
 (b_0'[+]
  b k[*]
  (cc_IR r[^]k[*]
   [--] ((cc_IR (a k) [/] cc_IR (AbsCC b_0') [//]H8) [*] (b_0'[/] b k[//]H10)))).
apply bin_op_wd_unfolded. Algebra.
apply bin_op_wd_unfolded. Algebra.
Step_final (cc_IR r[^]k[*]w[^]k).

apply root_one with k; auto.
 apply AbsCC_nonneg.
astepl (AbsCC (w[^]k)).
astepl
 (AbsCC
    [--] ((cc_IR (a k) [/] cc_IR (AbsCC b_0') [//]H8) [*] (b_0'[/] b k[//]H10))).
astepl
 (AbsCC ((cc_IR (a k) [/] cc_IR (AbsCC b_0') [//]H8) [*] (b_0'[/] b k[//]H10))).
astepl
 (AbsCC (cc_IR (a k) [/] cc_IR (AbsCC b_0') [//]H8) [*]
  AbsCC (b_0'[/] b k[//]H10)).
astepl
 (AbsCC (cc_IR (a k) [/] cc_IR (AbsCC b_0') [//]H8) [*]
  AbsCC (b_0'[/] b k[//]H10)).
cut (Zero [<=] AbsCC b_0'). intro. 2: apply AbsCC_nonneg.
astepl
 ((AbsCC (cc_IR (a k)) [/] AbsCC b_0'[//]H7) [*]AbsCC (b_0'[/] b k[//]H10)).
astepl
 ((AbsCC (cc_IR (a k)) [/] AbsCC b_0'[//]H7) [*]AbsCC (b_0'[/] b k[//]H10)).
cut (Zero [<=] a k). intro. 2: apply less_leEq; auto.
astepl ((a k[/] AbsCC b_0'[//]H7) [*]AbsCC (b_0'[/] b k[//]H10)).
astepl ((a k[/] AbsCC b_0'[//]H7) [*] (AbsCC b_0'[/] AbsCC (b k) [//]H9)).
unfold a in |- *; rational.

apply
 ap_wdl_unfolded
  with (cc_IR [--] (a k[/] AbsCC b_0'[//]H7) [*] (b_0'[/] b k[//]H10)).
apply mult_resp_ap_zero.
astepr (cc_IR Zero).
apply cc_IR_resp_ap.
apply inv_resp_ap_zero.
apply div_resp_ap_zero_rev; auto.
apply div_resp_ap_zero_rev.
apply AbsCC_ap_zero.
apply ap_symmetric_unfolded; auto.
apply
 eq_transitive_unfolded
  with ( [--] (cc_IR (a k[/] AbsCC b_0'[//]H7)) [*] (b_0'[/] b k[//]H10)).
 apply mult_wdl.
 astepl (cc_IR (Zero[-] (a k[/] AbsCC b_0'[//]H7))). astepr (Zero[-]cc_IR (a k[/] AbsCC b_0'[//]H7)).
 Step_final (cc_IR Zero[-]cc_IR (a k[/] AbsCC b_0'[//]H7)).
astepl ((Zero[-]cc_IR (a k[/] AbsCC b_0'[//]H7)) [*] (b_0'[/] b k[//]H10)).
astepl
 ((cc_IR Zero[-]cc_IR (a k[/] AbsCC b_0'[//]H7)) [*] (b_0'[/] b k[//]H10)).
astepl
 (cc_IR Zero[*] (b_0'[/] b k[//]H10) [-]
  cc_IR (a k[/] AbsCC b_0'[//]H7) [*] (b_0'[/] b k[//]H10)).
astepl
 (Zero[*] (b_0'[/] b k[//]H10) [-]
  cc_IR (a k[/] AbsCC b_0'[//]H7) [*] (b_0'[/] b k[//]H10)).
astepl (Zero[-]cc_IR (a k[/] AbsCC b_0'[//]H7) [*] (b_0'[/] b k[//]H10)).
astepl ( [--] (cc_IR (a k[/] AbsCC b_0'[//]H7) [*] (b_0'[/] b k[//]H10))).
unfold cc_IR in |- *; simpl in |- *; split; simpl in |- *; rational.
Qed.
(* end hide *)

Lemma Kneser_1' : Half [<=] q.
Proof.
unfold q in |- *.
apply shift_leEq_minus.
astepl (Smallest[+]Half).
apply shift_plus_leEq.
unfold Half in |- *.
rstepr (One [/]TwoNZ:IR).
unfold Smallest, Small, Smaller in |- *.
generalize (p3m_smaller n gt_n_0).
intro Hn.
generalize (p3m_smaller (two_n * n)).
intro H2nn.
apply leEq_transitive with (Half[*] (Half:IR)).
 apply mult_resp_leEq_both; auto.
   apply less_leEq; apply p3m_pos.
  apply less_leEq; apply p3m_pos.
 apply H2nn.
 unfold two_n in |- *.
 elim gt_n_0. auto with arith.
 intros. simpl in |- *. auto with arith.
rstepr (One [/]TwoNZ[*]OneR).
apply less_leEq.
apply mult_resp_less_lft.
 exact (half_lt1 _).
exact (pos_half _).
Qed.

Lemma Kneser_1'' : q [<] One.
Proof.
unfold q in |- *.
apply shift_minus_less'.
rstepl (Zero[+]OneR).
apply plus_resp_less_rht.
unfold Smallest, Small, Smaller in |- *.
apply mult_resp_pos; apply p3m_pos.
Qed.

Lemma Kneser_1 : forall a_0 eta eps : IR, Zero [<] eta -> Zero [<] eps ->
 a_0[+]Three[*]eta [<] c -> Two[*] (Three[^]n[+]One) [*]eps [<=] eta -> q[*]a_0[+]Three[^]n[*]eps[+]eps[+]eta [<] q[*]c.
Proof.
intros.
cut
 (One [/]TwoNZ[*] (Two[*]Three[^]n[*]eps[+]Two[*]eps[+]Two[*]eta) [<=] 
  q[*] (Two[*]Three[^]n[*]eps[+]Two[*]eps[+]Two[*]eta)).
intro Hm.
apply
 leEq_less_trans
  with (q[*] (a_0[+]Two[*]Three[^]n[*]eps[+]Two[*]eps[+]Two[*]eta)).
 rstepr (q[*]a_0[+]q[*] (Two[*]Three[^]n[*]eps[+]Two[*]eps[+]Two[*]eta)).
 rstepl
  (q[*]a_0[+]One [/]TwoNZ[*] (Two[*]Three[^]n[*]eps[+]Two[*]eps[+]Two[*]eta)).
 apply plus_resp_leEq_lft; auto.
apply mult_resp_less_lft.
 apply leEq_less_trans with (a_0[+]Three[*]eta); auto.
 rstepl (a_0[+] (Two[*]Three[^]n[*]eps[+]Two[*]eps[+]Two[*]eta)).
 apply plus_resp_leEq_lft.
 rstepl (Two[*] (Three[^]n[+]One) [*]eps[+]Two[*]eta).
 rstepr (eta[+]Two[*]eta).
 apply plus_resp_leEq; auto.
apply less_leEq_trans with (Half:IR).
apply pos_half. exact Kneser_1'.

apply mult_resp_leEq_rht. exact Kneser_1'.
apply less_leEq.
apply less_leEq_trans with (Zero[+]Two[*]eta).
 rstepr (Two[*]eta).
 apply mult_resp_pos; auto.
 apply pos_two.
apply less_leEq.
apply plus_resp_less_rht.
apply less_transitive_unfolded with (Zero[+]Two[*]eps).
 rstepr (Two[*]eps).
 apply mult_resp_pos; auto.
 apply pos_two.
apply plus_resp_less_rht.
repeat apply mult_resp_pos; auto.
 apply pos_two.
apply nexp_resp_pos; apply pos_three.
Qed.

Lemma Kneser_2a : forall (R : CRing) (m n i : nat) (f : nat -> R), 1 <= i ->
 Sum m n f [=] f m[+]f i[+] (Sum (S m) (pred i) f[+]Sum (S i) n f).
intros.
astepl (f m[+]Sum (S m) n0 f).
astepl (f m[+] (Sum (S m) i f[+]Sum (S i) n0 f)).
astepl (f m[+] (Sum (S m) (pred i) f[+]f i[+]Sum (S i) n0 f)).
rational.
Qed.

Lemma Kneser_2b : forall (k : nat) (z : CC), 1 <= k ->
 let p_ := fun i => b i[*]z[^]i in
 Sum 0 n (fun i => b i[*]z[^]i) [=] b_0[+]b k[*]z[^]k[+] (Sum 1 (pred k) p_[+]Sum (S k) n p_).
(* begin hide *)
intros.
unfold p_ in |- *.
unfold b_0 in |- *.
apply
 eq_transitive_unfolded
  with (b 0[*]z[^]0[+]b k[*]z[^]k[+] (Sum 1 (pred k) p_[+]Sum (S k) n p_));
 unfold p_ in |- *.
apply Kneser_2a with (f := fun i : nat => b i[*]z[^]i).
auto.
rational.
Qed.
(* end hide *)

Lemma Kneser_2c : forall (m n : nat) (z : CC), m <= S n ->
 let r := AbsCC z in
 AbsCC (Sum m n (fun i => b i[*]z[^]i)) [<=] Sum m n (fun i => a i[*]r[^]i).
(* begin hide *)
intros.
unfold r in |- *.
apply leEq_wdr with (Sum m n0 (fun i : nat => AbsCC (b i[*]z[^]i))).
apply triangle_Sum with (z := fun i : nat => b i[*]z[^]i). auto.
apply Sum_wd.
intros.
unfold a in |- *.
Step_final (AbsCC (b i) [*]AbsCC (z[^]i)).
Qed.
(* end hide *)

Lemma Kneser_2 : forall (k : nat) (z : CC), 1 <= k -> k <= n ->
 let r := AbsCC z in let p_ := fun i => a i[*]r[^]i in
 AbsCC (Sum 0 n (fun i => b i[*]z[^]i)) [<=]
  AbsCC (b_0[+]b k[*]z[^]k) [+] (Sum 1 (pred k) p_[+]Sum (S k) n p_).
(* begin hide *)
intros.
unfold p_, r in |- *.
set (p_' := fun i : nat => b i[*]z[^]i) in *.
apply
 leEq_wdl
  with (AbsCC (b_0[+]b k[*]z[^]k[+] (Sum 1 (pred k) p_'[+]Sum (S k) n p_')));
 unfold p_' in |- *.
apply
 leEq_transitive
  with
    (AbsCC (b_0[+]b k[*]z[^]k) [+]AbsCC (Sum 1 (pred k) p_'[+]Sum (S k) n p_'));
 unfold p_' in |- *.
apply triangle.
apply plus_resp_leEq_lft.
apply
 leEq_transitive with (AbsCC (Sum 1 (pred k) p_') [+]AbsCC (Sum (S k) n p_'));
 unfold p_' in |- *.
apply triangle.
apply plus_resp_leEq_both.
apply Kneser_2c. auto with arith.
apply Kneser_2c. auto with arith.
apply AbsCC_wd.
apply eq_symmetric_unfolded.
apply Kneser_2b.
auto.
Qed.
(* end hide *)
Lemma Kneser_3 : {z : CC | AbsCC z[^]n [<=] c | AbsCC (Sum 0 n (fun i => b i[*]z[^]i)) [<] q[*]c}.
Proof.
elim eta_exists. intros eta H0 H1.
elim H1. intros b_0' H3 H4. elim H4. intros H5 H6.
clear H1 H4.
cut (Zero [<] AbsCC b_0'). intro H7.
 2: apply AbsCC_pos; auto.
elim (eps_exists eta (AbsCC b_0') H0 H7). intros eps H9 H10. elim H10. intros H11 H12. elim H12. intros H13 H14.
clear H10 H12.
cut (forall k : nat, Zero [<=] a k). intro H15.
 2: intro; unfold a in |- *; apply AbsCC_nonneg.
cut (a n [=] One). intro H16.
 2: unfold a in |- *; Step_final (AbsCC One).
elim (Main a n gt_n_0 eps H9 H15 H16 (AbsCC b_0') H14).
intro r. intros H18 H19.
elim H19. intros k H20.
elim H20. intros H21 H22. elim H22. intros H23 H24. elim H24. intros H25 H26.
elim H26. intros H27 H28. elim H28. intros H29 H30.
clear H19 H20 H22 H24 H26 H28.
cut (Zero [<] a k). intro H31.
elim (z_exists b_0' k r eta H7 H31 H21 H23 H18 H0 H3 H30). intro z. intros H33 H34.
exists z.
 astepl (r[^]n).
 apply leEq_transitive with (AbsCC b_0'); auto.
 apply leEq_transitive with (AbsCC b_0'[+]Three[*]eta).
  2: apply less_leEq; auto.
 astepl (AbsCC b_0'[+]Zero).
 apply plus_resp_leEq_lft.
 apply less_leEq.
 apply mult_resp_pos; auto.
 apply pos_three.
set (r' := AbsCC z) in *. unfold r' in H33, H34.
set (p_' := fun i : nat => a i[*]r'[^]i) in *.
apply leEq_less_trans with (eps[+] (q[*]AbsCC b_0'[+]Three[^]n[*]eps[+]eta)).
 2: rstepl (q[*]AbsCC b_0'[+]Three[^]n[*]eps[+]eps[+]eta); apply Kneser_1;
     auto.
apply
 leEq_transitive
  with (AbsCC (b_0[+]b k[*]z[^]k) [+] (Sum 1 (pred k) p_'[+]Sum (S k) n p_'));
 unfold p_', r' in |- *.
 apply Kneser_2; auto.
set (p_'' := fun i : nat => a i[*]r[^]i) in *.
apply
 leEq_wdl
  with (AbsCC (b_0[+]b k[*]z[^]k) [+] (Sum 1 (pred k) p_''[+]Sum (S k) n p_''));
 unfold p_'' in |- *.
 2: apply bin_op_wd_unfolded;
     [ Algebra | apply bin_op_wd_unfolded; apply Sum_wd; Algebra ].
apply
 leEq_transitive
  with
    (AbsCC (b_0[+]b k[*]z[^]k) [+]
     ((One[-]Small) [*] (a k[*]r[^]k) [+]Three[^]n[*]eps)).
 apply plus_resp_leEq_lft; auto.
apply
 leEq_transitive
  with
    (AbsCC b_0'[-]AbsCC (b k) [*]r[^]k[+]eta[+]
     ((One[-]Small) [*] (a k[*]r[^]k) [+]Three[^]n[*]eps)).
 apply plus_resp_leEq; auto.
unfold a in |- *.
rstepl (AbsCC b_0'[+]Three[^]n[*]eps[+]eta[-]Small[*] (AbsCC (b k) [*]r[^]k)).
apply
 leEq_transitive
  with
    (AbsCC b_0'[+]Three[^]n[*]eps[+]eta[-]
     Small[*] (Smaller[*]AbsCC b_0'[-]Two[*]eps)).
 apply minus_resp_leEq_rht.
 apply mult_resp_leEq_lft; auto.
 unfold Small in |- *.
 apply less_leEq; apply p3m_pos.
apply
 leEq_wdl with (Small[*]Two[*]eps[+] (q[*]AbsCC b_0'[+]Three[^]n[*]eps[+]eta)).
 2: unfold q, Smallest in |- *; rational.
apply plus_resp_leEq.
astepr (One[*]eps).
apply mult_resp_leEq_rht.
 2: apply less_leEq; auto.
astepr (Half[*] (Two:IR)).
apply mult_resp_leEq_rht.
 unfold Small in |- *; apply p3m_smaller; auto.
apply less_leEq; apply pos_two.

apply mult_cancel_pos_lft with (r[^]k).
 2: apply nexp_resp_nonneg; auto.
apply less_leEq_trans with eps; auto.
eapply leEq_transitive.
 2: apply H29. 
apply shift_leEq_minus.
rstepl (Three[*]eps). auto.
Qed.

End Kneser_Lemma.

Lemma Kneser : forall n : nat, 0 < n -> {q : IR | Zero [<=] q |
 q [<] One and (forall p : cpoly CC, monic n p -> forall c : IR,
  AbsCC p ! Zero [<] c -> {z : CC | AbsCC z[^]n [<=] c | AbsCC p ! z [<] q[*]c})}.
intros n H.
exists (One[-]p3m n[*]p3m (2 * n * n)).
 apply less_leEq.
 apply less_leEq_trans with (Half:IR).
  apply pos_half.
 apply Kneser_1'; auto.
split. apply Kneser_1''.
intros p H0 c H1.
elim H0. intros H2 H3.
cut (nth_coeff n p [=] One). intro H4.
 2: auto.
elim (Kneser_3 (fun i : nat => nth_coeff i p) n H H4 c). intros z H6 H7.
 2: astepl (AbsCC p ! Zero); auto.
exists z.
auto.
astepl (AbsCC (Sum 0 n (fun i : nat => nth_coeff i p[*]z[^]i))); auto.
Qed.
