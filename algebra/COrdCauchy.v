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
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; either version 2.1 of the License, or
 * (at your option) any later version.
 *
 * This work is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along
 * with this work; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 *)
Require Export CoRN.algebra.COrdAbs.
Set Automatic Introduction.

(* Begin_SpecReals *)

Section OrdField_Cauchy.

(**
** Cauchy sequences
%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)
Variable R : COrdField.

(* begin hide *)
Set Implicit Arguments.
Unset Strict Implicit.
(* end hide *)

Definition Cauchy_prop (g : nat -> R) : CProp := forall e : R,
 [0] [<] e -> {N : nat | forall m, N <= m -> AbsSmall e (g m[-]g N)}.

(* begin hide *)
Set Strict Implicit.
Unset Implicit Arguments.
(* end hide *)

(* Def. CauchyP, Build_CauchyP *)
(* Should be defined in terms of CauchyP *)

(**
Implicit arguments turned off, because Coq makes a mess of it in combination
with the coercions
*)

Record CauchySeq : Type :=
 {CS_seq   :> nat -> R;
  CS_proof :  Cauchy_prop CS_seq}.

Definition SeqLimit (seq : nat -> R) (lim : R) : CProp := forall e : R,
 [0] [<] e -> {N : nat | forall m, N <= m -> AbsSmall e (seq m[-]lim)}.

(* End_SpecReals *)

(**
We now prove that the property of being a Cauchy sequence is preserved
through the usual algebraic operations (addition, subtraction and
multiplication -- and division, provided some additional conditions
hold).

%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)

Theorem CS_seq_bounded : forall g : nat -> R, Cauchy_prop g ->
 {K : R | [0] [<] K | {N : nat | forall m, N <= m -> AbsSmall K (g m)}}.
Proof.
 intros g Hg.
 unfold Cauchy_prop in |- *.
 elim (Hg _ (pos_one _)).
 intros N H1.
 exists (g N[^]2[-]g N[+]Two).
  apply less_leEq_trans with (nring (R:=R) 7 [/]FourNZ).
   apply pos_div_four; apply nring_pos; auto with arith.
  astepl ([0][+]nring (R:=R) 7 [/]FourNZ).
  apply shift_plus_leEq.
  rstepr ((g N[-][1] [/]TwoNZ)[^]2).
  apply sqr_nonneg.
 exists N.
 intros m Hm.
 elim (H1 m Hm); intros.
 split.
  apply plus_cancel_leEq_rht with (z := [--](g N)).
  rstepr (g m[-]g N).
  rstepl ([--](g N[^]2[+]Two)).
  apply leEq_transitive with ([--]([1]:R)).
   apply inv_cancel_leEq.
   rstepl ([1]:R).
   rstepr (g N[^]2[+]Two).
   apply plus_cancel_leEq_rht with ([--][1]:R).
   rstepl ([0]:R).
   rstepr (g N[^]2[+][1]).
   apply leEq_transitive with (y := g N[^]2).
    apply sqr_nonneg.
   apply less_leEq; apply less_plusOne.
  assumption.
 apply plus_cancel_leEq_rht with (g N[-]Two).
 rstepr (g N[^]2).
 astepr (g N[*]g N).
 apply plus_cancel_leEq_rht with ([--](Two[*]g N)[+]Two).
 rstepl (g m[-]g N).
 rstepr (g N[*]g N[+][1][-]Two[*]g N[+][1]).
 apply leEq_transitive with (y := [1]:R).
  assumption.
 rstepl ([0][+]([1]:R)).
 apply plus_resp_leEq with (z := [1]:R).
 rstepr ((g N[-][1])[*](g N[-][1])).
 apply leEq_wdr with (y := (g N[-][1])[^]2).
  apply sqr_nonneg.
 algebra.
Qed.

Lemma CS_seq_const : forall c : R, Cauchy_prop (fun n => c).
Proof.
 exists 0.
 intros; astepr ([0]:R); apply zero_AbsSmall.
 apply less_leEq; auto.
Qed.

(**
%\begin{convention}% Assume [f] and [g] are Cauchy sequences on [R].
%\end{convention}%
*)

Variables f g : nat -> R.

Hypothesis Hf : Cauchy_prop f.
Hypothesis Hg : Cauchy_prop g.

Lemma CS_seq_plus : Cauchy_prop (fun m => f m[+]g m).
Proof.
 unfold Cauchy_prop in |- *.
 intros.
 set (e_div_4 := e [/]FourNZ) in *.
 cut ([0] [<] e_div_4); [ intro Heps | unfold e_div_4 in |- *; apply pos_div_four; auto ].
 unfold Cauchy_prop in Hf.
 unfold Cauchy_prop in Hg.
 elim (Hf e_div_4 Heps); intros N1 H21.
 elim (Hg e_div_4 Heps); intros N2 H31.
 exists (max N1 N2).
 intros.
 rstepl (e [/]TwoNZ[+]e [/]TwoNZ).
 rstepr (f m[-]f (max N1 N2)[+](g m[-]g (max N1 N2))).
 apply AbsSmall_plus.
  rstepr (f m[-]f N1[+](f N1[-]f (max N1 N2))).
  rstepl (e [/]FourNZ[+]e [/]FourNZ).
  apply AbsSmall_plus.
   apply H21; eauto with arith.
  apply AbsSmall_minus.
  apply H21; eauto with arith.
 rstepr (g m[-]g N2[+](g N2[-]g (max N1 N2))).
 rstepl (e [/]FourNZ[+]e [/]FourNZ).
 apply AbsSmall_plus.
  apply H31; eauto with arith.
 apply AbsSmall_minus.
 apply H31; eauto with arith.
Qed.

Lemma CS_seq_inv : Cauchy_prop (fun n => [--] (f n)).
Proof.
 red in |- *; intros e H.
 elim (Hf e H); intros N Hn.
 exists N; intros m Hm.
 apply AbsSmall_minus.
 rstepr (f m[-]f N).
 auto.
Qed.

Lemma CS_seq_mult : Cauchy_prop (fun n => f n[*]g n).
Proof.
 red in |- *; intros e He.
 elim (CS_seq_bounded f Hf); intros Mf HMf H.
 elim (CS_seq_bounded g Hg); intros Mg HMg H'.
 elim H; clear H; intros Nf HNf.
 elim H'; clear H'; intros Ng HNg.
 set (Mf_ap_zero := pos_ap_zero _ _ HMf) in *.
 set (Mg_ap_zero := pos_ap_zero _ _ HMg) in *.
 set (ef := e[/] _[//]mult_resp_ap_zero _ _ _ (twelve_ap_zero _) Mf_ap_zero) in *.
 set (eg := e[/] _[//]mult_resp_ap_zero _ _ _ (twelve_ap_zero _) Mg_ap_zero) in *.
 cut ([0] [<] ef); [ intro Hef
   | unfold ef in |- *; apply div_resp_pos; try apply mult_resp_pos; auto; apply pos_twelve ].
 cut ([0] [<] eg); [ intro Heg
   | unfold eg in |- *; apply div_resp_pos; try apply mult_resp_pos; auto; apply pos_twelve ].
 elim (Hf eg Heg); intros Pf HPf.
 elim (Hg ef Hef); intros Pg HPg.
 set (N := max (max Nf Pf) (max Ng Pg)) in *; exists N; intros m Hm.
 rstepr ((f m[-]f Pf[+][--](f N[-]f Pf))[*]g m[+] (g m[-]g Pg[+][--](g N[-]g Pg))[*]f N).
 apply AbsSmall_wdl_unfolded with (Three[*]((eg[+]eg)[*]Mg)[+]Three[*]((ef[+]ef)[*]Mf)).
  2: unfold eg, ef in |- *; rational.
 apply AbsSmall_plus; apply AbsSmall_mult; try apply AbsSmall_plus; try apply inv_resp_AbsSmall.
      apply HPf; apply le_trans with N; auto; unfold N in |- *; eauto with arith.
     apply HPf; apply le_trans with N; auto; unfold N in |- *; eauto with arith.
    apply HNg; auto; apply le_trans with N; auto; unfold N in |- *; eauto with arith.
   apply HPg; apply le_trans with N; auto; unfold N in |- *; eauto with arith.
  apply HPg; apply le_trans with N; auto; unfold N in |- *; eauto with arith.
 apply HNf; auto; apply le_trans with N; auto; unfold N in |- *; eauto with arith.
Qed.

(**
We now assume that [f] is, from some point onwards, greater than
some positive number.  The sequence of reciprocals is defined as
being constantly one up to that point, and the sequence of
reciprocals from then onwards.

%\begin{convention}%
Let [e] be a postive element of [R] and let [N:nat] be such that from
[N] onwards, [(f n) [#] [0]]
%\end{convention}%
*)

Variable e : R.
Hypothesis He : [0] [<] e.

Variable N : nat.
Hypothesis f_bnd : forall n : nat, N <= n -> e [<=] f n.

Lemma CS_seq_recip_def : forall n : nat, N <= n -> f n [#] [0].
Proof.
 intros.
 apply pos_ap_zero.
 apply less_leEq_trans with e; auto with arith.
Qed.

Definition CS_seq_recip_seq (n : nat) : R.
Proof.
 elim (lt_le_dec n N); intro Hdec.
  apply ([1]:R).
 apply ([1][/] _[//]CS_seq_recip_def n Hdec).
Defined.

Lemma CS_seq_recip : Cauchy_prop CS_seq_recip_seq.
Proof.
 red in |- *; intros d Hd.
 elim (Hf ((d[*]e[*]e) [/]TwoNZ));
   [ intros K HK | apply pos_div_two; repeat apply mult_resp_pos; auto ].
 exists (max K N); intros n Hn.
 apply AbsSmall_cancel_mult with (f (max K N)).
  apply less_leEq_trans with e; auto with arith.
 apply AbsSmall_cancel_mult with (f n).
  apply less_leEq_trans with e; eauto with arith.
 unfold CS_seq_recip_seq in |- *.
 elim lt_le_dec; intro; simpl in |- *.
  elimtype False; apply le_not_lt with N n; eauto with arith.
 elim lt_le_dec; intro; simpl in |- *.
  elimtype False; apply le_not_lt with N (max K N); eauto with arith.
 rstepr (f (max K N)[-]f n).
 apply AbsSmall_leEq_trans with (d[*]e[*]e).
  apply mult_resp_leEq_both.
     apply less_leEq; apply mult_resp_pos; auto.
    apply less_leEq; auto.
   apply mult_resp_leEq_lft.
    auto with arith.
   apply less_leEq; auto.
  auto with arith.
 auto with arith.
 rstepr (f (max K N)[-]f K[+](f K[-]f n)).
 apply AbsSmall_eps_div_two.
  auto with arith.
 apply AbsSmall_minus; apply HK.
 eauto with arith.
Qed.

End OrdField_Cauchy.

Arguments SeqLimit [R].

(**
The following lemma does not require the sequence to be Cauchy, but it fits
well here anyway.
*)

Lemma maj_upto_eps : forall (F : COrdField) (a : nat -> F) (n : nat) (eps : F),
 0 < n -> [0] [<] eps -> {k : nat | 1 <= k /\ k <= n /\ (forall i : nat, 1 <= i -> i <= n -> a i[-]eps [<=] a k)}.
Proof.
 intros F a n eps Hn Heps.
 induction  n as [| n Hrecn].
  elim (lt_irrefl _ Hn).
 clear Hrecn Hn.
 induction  n as [| n Hrecn].
  exists 1.
  repeat split. 1-2: reflexivity.
  intros.
  rewrite <- (le_antisym _ _ H H0).
  astepr (a 1[+][0]).
  unfold cg_minus in |- *.
  apply plus_resp_leEq_lft.
  astepr ([--]([0]:F)).
  apply less_leEq; apply inv_resp_less; auto.
 elim Hrecn; intros k Hk.
 cut (a (S (S n))[-]eps [<] a (S (S n))).
  intro H.
  elim (less_cotransitive_unfolded _ _ _ H (a k)); intro H4.
   exists k.
   elim Hk; intros H0 H2.
   elim H2; clear H2; intros H1 H2.
   repeat split.
     assumption.
    auto with arith.
   intros i H3 H5.
   elim (Cle_le_S_eq _ _ H5); intro H6.
    auto with arith.
   rewrite H6.
   apply less_leEq; assumption.
  exists (S (S n)).
  repeat split; auto with arith.
  intros i H0 H1.
  elim (Cle_le_S_eq _ _ H1); intro H2.
   apply leEq_transitive with (a k).
    elim Hk; intros H3 H5.
    elim H5; clear H5; intros H6 H7.
    auto with arith.
   apply less_leEq; assumption.
  rewrite H2; apply less_leEq; auto.
 rstepr (a (S (S n))[-][0]).
 apply minus_resp_less_rht.
 assumption.
Qed.

Section Mult_Continuous.

Variable R : COrdField.
(**
** Multiplication is continuous
%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)

Lemma smaller : forall x y : R,
 [0] [<] x -> [0] [<] y -> {z : R | [0] [<] z | z [<=] x /\ z [<=] y}.
Proof.
 intros x y H H0.
 elim (less_cotransitive_unfolded _ _ _ (half_3 _ _ H) y); intro.
  exists (Half[*]x).
   apply mult_resp_pos. apply pos_half. auto.
    split; apply less_leEq. apply half_3. auto. auto.
   cut (Half[*]y [<] y). intro. exists (Half[*]y).
  apply mult_resp_pos. apply pos_half. auto.
    split; apply less_leEq. apply less_transitive_unfolded with y. auto. auto.
   auto.
 apply half_3. auto.
Qed.

Lemma estimate_abs : forall x : R, {X : R | [0] [<] X | AbsSmall X x}.
Proof.
 intros.
 unfold AbsSmall in |- *.
 cut (x [<] x[+][1]). intro H.
  elim (less_cotransitive_unfolded _ x (x[+][1]) H [--]x); intro.
   exists ([--]x[+][1]).
    apply leEq_less_trans with ([--]x).
     2: apply less_plusOne.
    apply less_leEq; apply mult_cancel_less with (Two:R).
     apply pos_two.
    astepl ([0]:R); rstepr ([--]x[-]x).
    apply shift_less_minus.
    astepl x; auto.
   split; apply less_leEq.
    astepr ([--][--]x). apply inv_resp_less. apply less_plusOne.
    apply less_transitive_unfolded with ([--]x). auto. apply less_plusOne.
    exists (x[+][1]).
   apply less_leEq_trans with (([1]:R) [/]TwoNZ).
    apply pos_div_two; apply pos_one.
   apply shift_leEq_plus; rstepl (([--][1]:R) [/]TwoNZ).
   apply shift_div_leEq.
    apply pos_two.
   rstepr (x[+]x); apply shift_leEq_plus.
   unfold cg_minus in |- *; apply shift_plus_leEq'.
   rstepr (x[+][1]); apply less_leEq; auto.
  split; apply less_leEq.
   astepr ([--][--]x). apply inv_resp_less. auto. auto.
   apply less_plusOne.
Qed.

Lemma mult_contin : forall x y e : R, [0] [<] e ->
 {c : R | [0] [<] c | {d : R | [0] [<] d | forall x' y' : R,
 AbsSmall c (x[-]x') -> AbsSmall d (y[-]y') -> AbsSmall e (x[*]y[-]x'[*]y')}}.
Proof.
 intros x y e H.
 set (e2 := e [/]TwoNZ) in *.
 cut ([0] [<] e2). intro H0. 2: unfold e2 in |- *; apply pos_div_two; auto.
  elim (estimate_abs x). intro X. intros H1a H1b.
 elim (estimate_abs y). intro Y. intros H2 H3.
 cut (Y [#] [0]). intro H4.
  set (eY := e2[/] Y[//]H4) in *; exists eY.
   unfold eY in |- *. apply div_resp_pos. auto. auto.
   cut ([0] [<] X[+]eY). intro H5.
   cut (X[+]eY [#] [0]). intro H6.
    exists (e2[/] X[+]eY[//]H6).
     apply div_resp_pos. auto. auto.
      intros.
    apply AbsSmall_wdr_unfolded with ((x[-]x')[*]y[+]x'[*](y[-]y')).
     apply AbsSmall_eps_div_two.
      apply AbsSmall_wdl_unfolded with ((e [/]TwoNZ[/] Y[//]H4)[*]Y).
       apply mult_AbsSmall; auto.
      rational.
     apply AbsSmall_wdl_unfolded with ((X[+](e [/]TwoNZ[/] Y[//]H4))[*]
       (e [/]TwoNZ[/] X[+](e [/]TwoNZ[/] Y[//]H4)[//]H6)).
      apply mult_AbsSmall; auto.
      apply AbsSmall_wdr_unfolded with (x[+](x'[-]x)).
       apply AbsSmall_plus; auto. apply AbsSmall_minus. auto.
       rational.
     rational.
    rational.
   apply Greater_imp_ap. auto.
   apply plus_resp_pos; auto.
  unfold eY in |- *; apply div_resp_pos; auto.
 apply Greater_imp_ap. auto.
Qed.

(** Addition is also continuous. *)

Lemma plus_contin : forall (x y e : R), [0] [<] e ->
 {c : R | [0] [<] c | {d : R | [0] [<] d | forall x' y',
 AbsSmall c (x[-]x') -> AbsSmall d (y[-]y') -> AbsSmall e (x[+]y[-] (x'[+]y'))}}.
Proof.
 intros.
 cut ([0] [<] e [/]TwoNZ). intro.
  exists (e [/]TwoNZ). auto.
   exists (e [/]TwoNZ). auto.
   intros.
  apply AbsSmall_wdr_unfolded with (x[-]x'[+](y[-]y')).
   apply AbsSmall_eps_div_two; auto.
  rational.
 apply div_resp_pos. apply pos_two. auto.
Qed.

End Mult_Continuous.

Section Monotonous_functions.

(**
** Monotonous Functions

Finally, we study several properties of monotonous functions and
characterize them in some way.

%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)
Variable R : COrdField.

(**
We begin by characterizing the preservation of less (less or equal)
in terms of preservation of less or equal (less).
*)

Lemma resp_less_char' : forall (P : R -> CProp) (f : forall x, P x -> R) x y Hx Hy,
 (x [#] y -> f x Hx [#] f y Hy) -> (x [<=] y -> f x Hx [<=] f y Hy) ->
 x [<] y -> f x Hx [<] f y Hy.
Proof.
 intros.
 elim (ap_imp_less _ _ _ (X (less_imp_ap _ _ _ X0))); intros.
  auto.
 elimtype False.
 apply less_irreflexive_unfolded with (x := f x Hx).
 apply leEq_less_trans with (f y Hy); auto.
 apply H; apply less_leEq; auto.
Qed.

Lemma resp_less_char : forall (f : R -> R) x y,
 (x [#] y -> f x [#] f y) -> (x [<=] y -> f x [<=] f y) -> x [<] y -> f x [<] f y.
Proof.
 intros.
 set (f' := fun (x : R) (H : True) => f x) in *.
 change (f' x I [<] f' y I) in |- *.
 apply resp_less_char' with (P := fun x : R => True); auto.
Qed.

Lemma resp_leEq_char' : forall (P : R -> CProp) (f : forall x : R, P x -> R) x y Hx Hy,
 (x [=] y -> f x Hx [=] f y Hy) -> (x [<] y -> f x Hx [<] f y Hy) ->
 x [<=] y -> f x Hx [<=] f y Hy.
Proof.
 intros.
 rewrite -> leEq_def.
 intro.
 cut (Not (x [<] y) /\ ~ x [=] y); intros.
  inversion_clear H1.
  apply H3.
  apply leEq_imp_eq; firstorder using leEq_def.
 split; intro.
  apply less_irreflexive_unfolded with (x := f y Hy).
  apply less_transitive_unfolded with (f x Hx); auto.
 apply less_irreflexive_unfolded with (x := f y Hy).
 apply less_leEq_trans with (f x Hx); auto.
 apply eq_imp_leEq; auto.
Qed.

Lemma resp_leEq_char : forall (f : R -> R) x y,
 (x [=] y -> f x [=] f y) -> (x [<] y -> f x [<] f y) -> x [<=] y -> f x [<=] f y.
Proof.
 intros.
 set (f' := fun (x : R) (H : True) => f x) in *.
 change (f' x I [<=] f' y I) in |- *.
 apply resp_leEq_char' with (P := fun x : R => True); auto.
Qed.

(**
Next, we see different characterizations of monotonous functions from
some subset of the natural numbers into [R].  Mainly, these
amount (for different types of functions) to proving that a function
is monotonous iff [f(i) [<] f(i+1)] for every [i].

Also, strictly monotonous functions are injective.
*)

Lemma local_mon_imp_mon : forall f : nat -> R,
 (forall i, f i [<] f (S i)) -> forall i j, i < j -> f i [<] f j.
Proof.
 simple induction j.
  intros H0; elimtype False; inversion H0.
 clear j; intro j; intros H0 H1.
 elim (le_lt_eq_dec _ _ H1); intro.
  apply leEq_less_trans with (f j).
   apply less_leEq; apply H0; auto with arith.
  auto.
 rewrite <- b; apply X.
Qed.

Lemma local_mon_imp_mon' : forall f : nat -> R,
 (forall i, f i [<] f (S i)) -> forall i j, i <= j -> f i [<=] f j.
Proof.
 intros f H i j H0.
 elim (le_lt_eq_dec _ _ H0); intro.
  apply less_leEq; apply local_mon_imp_mon with (f := f); assumption.
 apply eq_imp_leEq; rewrite b; algebra.
Qed.

Lemma local_mon'_imp_mon' : forall f : nat -> R,
 (forall i, f i [<=] f (S i)) -> forall i j, i <= j -> f i [<=] f j.
Proof.
 intros; induction  j as [| j Hrecj].
  cut (i = 0); [ intro | auto with arith ].
  rewrite H1; apply leEq_reflexive.
 elim (le_lt_eq_dec _ _ H0); intro.
  apply leEq_transitive with (f j).
   apply Hrecj; auto with arith.
  apply H.
 rewrite b; apply leEq_reflexive.
Qed.

Lemma mon_imp_mon' : forall f : nat -> R,
 (forall i j, i < j -> f i [<] f j) -> forall i j, i <= j -> f i [<=] f j.
Proof.
 intros f H i j H0.
 elim (le_lt_eq_dec _ _ H0); intro.
  apply less_leEq; apply H; assumption.
 rewrite b; apply leEq_reflexive.
Qed.

Lemma mon_imp_inj : forall f : nat -> R,
 (forall i j, i < j -> f i [<] f j) -> forall i j, f i [=] f j -> i = j.
Proof.
 intros.
 cut (~ i <> j); [ omega | intro ].
 cut (i < j \/ j < i); [ intro | apply not_eq; auto ].
 inversion_clear H1; (elimtype False; cut (f i [#] f j); [ apply eq_imp_not_ap; assumption | idtac ]).
  apply less_imp_ap; apply X; assumption.
 apply Greater_imp_ap; apply X; assumption.
Qed.

Lemma local_mon_imp_mon_lt : forall n (f : forall i, i < n -> R),
 (forall i H H', f i H [<] f (S i) H') -> forall i j Hi Hj, i < j -> f i Hi [<] f j Hj.
Proof.
 simple induction j.
  intros Hi Hj H0; elimtype False; inversion H0.
 clear j; intro j; intros.
 elim (le_lt_eq_dec _ _ H); intro.
  cut (j < n); [ intro | auto with arith ].
  apply leEq_less_trans with (f j H0).
   apply less_leEq; apply X0; auto with arith.
  apply X.
 generalize Hj; rewrite <- b.
 intro; apply X.
Qed.

Lemma local_mon_imp_mon'_lt : forall n (f : forall i, i < n -> R),
 (forall i H H', f i H [<] f (S i) H') -> nat_less_n_fun f ->
 forall i j Hi Hj, i <= j -> f i Hi [<=] f j Hj.
Proof.
 intros.
 elim (le_lt_eq_dec _ _ H0); intros.
  apply less_leEq; apply local_mon_imp_mon_lt with n; auto.
 apply eq_imp_leEq; apply H; assumption.
Qed.

Lemma local_mon'_imp_mon'_lt : forall n (f : forall i, i < n -> R),
 (forall i H H', f i H [<=] f (S i) H') -> nat_less_n_fun f ->
 forall i j Hi Hj, i <= j -> f i Hi [<=] f j Hj.
Proof.
 simple induction j.
  intros.
  cut (i = 0); [ intro | auto with arith ].
  apply eq_imp_leEq; apply H0; auto.
 intro m; intros.
 elim (le_lt_eq_dec _ _ H2); intro.
  cut (m < n); [ intro | auto with arith ].
  apply leEq_transitive with (f m H3); auto.
  apply H1; auto with arith.
 apply eq_imp_leEq; apply H0; assumption.
Qed.

Lemma local_mon'_imp_mon'2_lt : forall n (f : forall i, i < n -> R),
 (forall i H H', f i H [<=] f (S i) H') -> forall i j Hi Hj, i < j -> f i Hi [<=] f j Hj.
Proof.
 intros; induction  j as [| j Hrecj].
  elimtype False; inversion H0.
 elim (le_lt_eq_dec _ _ H0); intro.
  cut (j < n); [ intro | auto with arith ].
  apply leEq_transitive with (f j H1).
   apply Hrecj; auto with arith.
  apply H.
 generalize Hj; rewrite <- b.
 intro; apply H.
Qed.

Lemma mon_imp_mon'_lt : forall n (f : forall i, i < n -> R), nat_less_n_fun f ->
 (forall i j Hi Hj, i < j -> f i Hi [<] f j Hj) -> forall i j Hi Hj, i <= j -> f i Hi [<=] f j Hj.
Proof.
 intros.
 elim (le_lt_eq_dec _ _ H0); intro.
  apply less_leEq; auto.
 apply eq_imp_leEq; auto.
Qed.

Lemma mon_imp_inj_lt : forall n (f : forall i, i < n -> R),
 (forall i j Hi Hj, i < j -> f i Hi [<] f j Hj) ->
 forall i j Hi Hj, f i Hi [=] f j Hj -> i = j.
Proof.
 intros.
 cut (~ i <> j); intro.
  clear X H Hj Hi; omega.
 cut (i < j \/ j < i); [ intro | apply not_eq; auto ].
 inversion_clear H1; (elimtype False; cut (f i Hi [#] f j Hj);
   [ apply eq_imp_not_ap; assumption | idtac ]).
  apply less_imp_ap; auto.
 apply Greater_imp_ap; auto.
Qed.

Lemma local_mon_imp_mon_le : forall n (f : forall i, i <= n -> R),
 (forall i H H', f i H [<] f (S i) H') -> forall i j Hi Hj, i < j -> f i Hi [<] f j Hj.
Proof.
 simple induction j.
  intros Hi Hj H0; elimtype False; inversion H0.
 clear j; intro j; intros.
 elim (le_lt_eq_dec _ _ H); intro.
  cut (j <= n); [ intro | auto with arith ].
  apply leEq_less_trans with (f j H0).
   apply less_leEq; auto with arith.
  apply X.
 generalize Hj; rewrite <- b.
 auto.
Qed.

Lemma local_mon_imp_mon'_le : forall n (f : forall i, i <= n -> R),
 (forall i H H', f i H [<] f (S i) H') -> nat_less_n_fun' f ->
 forall i j Hi Hj, i <= j -> f i Hi [<=] f j Hj.
Proof.
 intros.
 elim (le_lt_eq_dec _ _ H0); intros.
  apply less_leEq; apply local_mon_imp_mon_le with n; auto.
 apply eq_imp_leEq; auto.
Qed.

Lemma local_mon'_imp_mon'_le : forall n (f : forall i, i <= n -> R),
 (forall i H H', f i H [<=] f (S i) H') -> nat_less_n_fun' f ->
 forall i j Hi Hj, i <= j -> f i Hi [<=] f j Hj.
Proof.
 simple induction j.
  intros.
  cut (i = 0); [ intro | auto with arith ].
  apply eq_imp_leEq; apply H0; auto.
 intro m; intros.
 elim (le_lt_eq_dec _ _ H2); intro.
  cut (m <= n); [ intro | auto with arith ].
  apply leEq_transitive with (f m H3); auto.
  apply H1; auto with arith.
 apply eq_imp_leEq; apply H0; assumption.
Qed.

Lemma local_mon'_imp_mon'2_le : forall n (f : forall i, i <= n -> R),
 (forall i H H', f i H [<=] f (S i) H') -> forall i j Hi Hj, i < j -> f i Hi [<=] f j Hj.
Proof.
 intros; induction  j as [| j Hrecj].
  elimtype False; inversion H0.
 elim (le_lt_eq_dec _ _ H0); intro.
  cut (j <= n); [ intro | auto with arith ].
  apply leEq_transitive with (f j H1).
   apply Hrecj; auto with arith.
  apply H.
 generalize Hj; rewrite <- b.
 intro; apply H.
Qed.

Lemma mon_imp_mon'_le : forall n (f : forall i, i <= n -> R), nat_less_n_fun' f ->
 (forall i j Hi Hj, i < j -> f i Hi [<] f j Hj) -> forall i j Hi Hj, i <= j -> f i Hi [<=] f j Hj.
Proof.
 intros.
 elim (le_lt_eq_dec _ _ H0); intro.
  apply less_leEq; auto.
 apply eq_imp_leEq; auto.
Qed.

Lemma mon_imp_inj_le : forall n (f : forall i, i <= n -> R),
 (forall i j Hi Hj, i < j -> f i Hi [<] f j Hj) -> forall i j Hi Hj, f i Hi [=] f j Hj -> i = j.
Proof.
 intros.
 cut (~ i <> j); intro.
  clear H X Hj Hi; omega.
 cut (i < j \/ j < i); [ intro | apply not_eq; auto ].
 inversion_clear H1; (elimtype False; cut (f i Hi [#] f j Hj);
   [ apply eq_imp_not_ap; assumption | idtac ]).
  apply less_imp_ap; auto.
 apply Greater_imp_ap; auto.
Qed.

(**
A similar result for %{\em %partial%}% functions.
*)

Lemma part_mon_imp_mon' : forall F (I : R -> CProp), (forall x, I x -> Dom F x) ->
 (forall x y Hx Hy, I x -> I y -> x [<] y -> F x Hx [<] F y Hy) ->
 forall x y Hx Hy, I x -> I y -> x [<=] y -> F x Hx [<=] F y Hy.
Proof.
 intros.
 rewrite -> leEq_def.
 intro.
 cut (x [=] y); intros.
  apply (less_irreflexive_unfolded _ (F x Hx)).
  astepl (F y Hy); auto.
 apply leEq_imp_eq.
  firstorder using leEq_def.
 rewrite -> leEq_def.
 intro.
 apply (less_irreflexive_unfolded _ (F x Hx)).
 apply less_transitive_unfolded with (F y Hy); firstorder using leEq_def.
Qed.

End Monotonous_functions.
