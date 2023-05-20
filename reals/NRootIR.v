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

(** printing NRoot %\ensuremath{\sqrt[n]{\cdot}}% *)
(** printing sqrt %\ensuremath{\sqrt{\cdot}}% *)

Require Export CoRN.reals.OddPolyRootIR.
Import CRing_Homomorphisms.coercions.

(**
* Roots of Real Numbers *)

Section NRoot.
(**
** Existence of roots

%\begin{convention}% Let [n] be a natural number and [c] a nonnegative real.
[p] is the auxiliary polynomial [_X_[^]n[-] (_C_ c)].
%\end{convention}%
*)

Variable n : nat.
Hypothesis n_pos : 0 < n.
Variable c : IR.
Hypothesis c_nonneg : [0] [<=] c.

(* begin hide *)
Let p := _X_[^]n[-]_C_ c.
(* end hide *)

Lemma CnrootIR : {x : IR | [0] [<=] x | x[^]n [=] c}.
Proof.
 intros.
 cut (monic n p). intro.
  elim (Ccpoly_pos' _ p [0] n); auto.
  intro X. intros H0 H1.
  cut {x : IR | [0] [<=] x /\ x [<=] X /\ p ! x [=] [0]}. intro H2.
   elim H2. clear H2. intro. intro H2.
   elim H2. clear H2. intros H2 H3. elim H3. clear H3. intros.
   exists x. auto.
    apply cg_inv_unique_2.
   astepl (_X_ ! x[^]n[-] (_C_ c) ! x).
   astepl ((_X_[^]n) ! x[-] (_C_ c) ! x).
   Step_final (_X_[^]n[-]_C_ c) ! x.
  apply Civt_poly; auto.
   apply monic_apzero with n; auto.
  unfold p in |- *.
  astepl ((_X_[^]n) ! [0][-] (_C_ c) ! [0]).
  astepl (_X_ ! [0][^]n[-]c).
  astepl ([0][^]n[-]c).
  astepl ([0][-]c).
  astepl ( [--]c).
  astepr ( [--]ZeroR). apply inv_resp_leEq. auto.
  unfold p in |- *.
 apply monic_minus with 0.
   apply degree_le_c_.
  pattern n at 1 in |- *. replace n with (1 * n).
  apply monic_nexp.
   apply monic_x_.
  auto with arith.
 auto.
Qed.

End NRoot.

(** We define the root of order [n] for any nonnegative real number and
prove its main properties:
 - $\left(\sqrt[n]x\right)^n=x$#(sqrt(n) x)^n =x#;
 - $0\leq\sqrt[n]x$#0&le;sqrt(n)x#;
 - if [[0] [<] x] then $0<\sqrt[n]x$#0&lt;sqrt(n)x#;
 - $\sqrt[n]{x^n}=x$#sqrt(n) x^n =x#;
 - the nth root is monotonous;
 - in particular, if [x [<] [1]] then $\sqrt[n]x<1$#sqrt(n) x&lt;1#.

[(nroot ??)] will be written as [NRoot].
*)

Section Nth_Root.

Lemma nroot : forall x k, [0] [<=] x -> 0 < k -> {y : IR | [0] [<=] y | y[^]k [=] x}.
Proof.
 intros.
 elim (CnrootIR k H0 x H). intro y. intros.
 exists y; auto.
Qed.

Definition NRoot x n Hx Hn : IR := proj1_sig2T _ _ _ (nroot x n Hx Hn).

Lemma NRoot_power : forall x k Hx Hk, NRoot x k Hx Hk[^]k [=] x.
Proof.
 intros.
 unfold NRoot in |- *.
 apply proj2b_sig2T.
Qed.

Hint Resolve NRoot_power: algebra.

Lemma NRoot_nonneg : forall x k Hx Hk, [0] [<=] NRoot x k Hx Hk.
Proof.
 intros.
 unfold NRoot in |- *.
 apply proj2a_sig2T.
Qed.

Lemma NRoot_pos : forall x Hx k Hk, [0] [<] x -> [0] [<] NRoot x k Hx Hk.
Proof.
 intros. rename X into H.
 cut ([0] [<=] NRoot x k Hx Hk); intros.
  cut (NRoot x k Hx Hk [<] [0] or [0] [<] NRoot x k Hx Hk). intros H1.
   elim H1; clear H1; intro H1.
    rewrite -> leEq_def in H0; elim (H0 H1).
   auto.
  apply ap_imp_less.
  apply un_op_strext_unfolded with (nexp_op (R:=IR) k).
  astepl x; astepr ZeroR.
  apply pos_ap_zero; auto.
 apply NRoot_nonneg.
Qed.

Lemma NRoot_power' : forall x k Hx' Hk, [0] [<=] x -> NRoot (x[^]k) k Hx' Hk [=] x.
Proof.
 intros.
 apply root_unique with k; auto.
  apply NRoot_nonneg.
 apply NRoot_power.
Qed.

Lemma NRoot_pres_less : forall x Hx y Hy k Hk, x [<] y -> NRoot x k Hx Hk [<] NRoot y k Hy Hk.
Proof.
 intros.
 apply power_cancel_less with k.
  apply NRoot_nonneg.
 eapply less_wdl.
  2: apply eq_symmetric_unfolded; apply NRoot_power.
 eapply less_wdr.
  2: apply eq_symmetric_unfolded; apply NRoot_power.
 auto.
Qed.

Lemma NRoot_less_one : forall x Hx k Hk, x [<] [1] -> NRoot x k Hx Hk [<] [1].
Proof.
 intros.
 apply power_cancel_less with k.
  apply less_leEq; apply pos_one.
 eapply less_wdl.
  2: apply eq_symmetric_unfolded; apply NRoot_power.
 astepr OneR.
 assumption.
Qed.

Lemma NRoot_cancel : forall x Hx y Hy k Hk, NRoot x k Hx Hk [=] NRoot y k Hy Hk -> x [=] y.
Proof.
 intros.
 apply eq_transitive_unfolded with (NRoot x k Hx Hk[^]k).
  apply eq_symmetric_unfolded; apply NRoot_power.
 apply eq_transitive_unfolded with (NRoot y k Hy Hk[^]k).
  2: apply NRoot_power.
 apply nexp_wd; algebra.
Qed.

(** %\begin{convention}% Let [x,y] be nonnegative real numbers.
%\end{convention}% *)

Variables x y : IR.
Hypothesis Hx : [0] [<=] x.
Hypothesis Hy : [0] [<=] y.

Lemma NRoot_wd : forall k Hk Hk', x [=] y -> NRoot x k Hx Hk [=] NRoot y k Hy Hk'.
Proof.
 intros.
 apply root_unique with k; auto.
   apply NRoot_nonneg.
  apply NRoot_nonneg.
 eapply eq_transitive_unfolded.
  eapply eq_transitive_unfolded.
   2: apply H.
  apply NRoot_power.
 apply eq_symmetric_unfolded; apply NRoot_power.
Qed.

Lemma NRoot_unique : forall k Hk, [0] [<] x -> x[^]k [=] y -> x [=] NRoot y k Hy Hk.
Proof.
 intros. rename H into H0.
 apply root_unique with k; auto.
  apply NRoot_nonneg.
 eapply eq_transitive_unfolded.
  apply H0.
 apply eq_symmetric_unfolded; apply NRoot_power.
Qed.

End Nth_Root.

Arguments NRoot [x n].

#[global]
Hint Resolve NRoot_power NRoot_power': algebra.

Lemma NRoot_resp_leEq : forall x y xpos ypos k kpos,
 x [<=] y -> NRoot (x:=x) (n:=k) xpos kpos [<=] NRoot (x:=y) (n:=k) ypos kpos.
Proof.
 intros.
 rewrite -> leEq_def; intro H0.
 assert (NRoot ypos kpos[^]k [<=] NRoot xpos kpos[^]k).
  apply power_resp_leEq.
   apply NRoot_nonneg.
  apply less_leEq; auto.
 assert (x [=] y).
  apply leEq_imp_eq; auto.
  eapply leEq_wdl.
   eapply leEq_wdr.
    eexact H1.
   algebra.
  algebra.
 clear H H1.
 generalize (NRoot_wd _ _ xpos ypos k kpos kpos H2).
 intro.
 apply (less_irreflexive_unfolded _ (NRoot ypos kpos)).
 astepr (NRoot xpos kpos).
 auto.
Qed.

Lemma NRoot_cancel_less : forall x (Hx:[0][<=]x) y (Hy:[0][<=]y) k (Hk Hk':0<k), NRoot Hx Hk [<] NRoot Hy Hk' -> x [<] y.
Proof.
 intros x Hx y Hy k Hk Hk' H.
 astepl (NRoot Hx Hk[^]k).
 astepr (NRoot Hy Hk'[^]k).
 apply nexp_resp_less.
   auto with *.
  apply NRoot_nonneg.
 assumption.
Qed.

Lemma NRoot_str_ext : forall k (Hk Hk':0 < k) x y (Hx:[0][<=]x) (Hy:[0][<=]y), NRoot Hx Hk [#] NRoot Hy Hk' -> x[#]y.
Proof.
 intros k Hk Hk' x y Hx Hy H0.
 destruct (ap_imp_less _ _ _ H0) as [H1|H1].
  apply less_imp_ap.
  refine (NRoot_cancel_less _ _ _ _ _ _ _ H1).
 apply Greater_imp_ap.
 refine (NRoot_cancel_less _ _ _ _ _ _ _ H1).
Qed.

(*---------------------------------*)
Section Square_root.
(*---------------------------------*)

(**
** Square root *)

Definition sqrt x xpos : IR := NRoot (x:=x) (n:=2) xpos (Nat.lt_0_succ 1).

Lemma sqrt_sqr : forall x xpos, sqrt x xpos[^]2 [=] x.
Proof.
 intros.
 unfold sqrt in |- *.
 apply NRoot_power.
Qed.

Hint Resolve sqrt_sqr: algebra.

Lemma sqrt_nonneg : forall x xpos, [0] [<=] sqrt x xpos.
Proof.
 intros.
 unfold sqrt in |- *.
 apply NRoot_nonneg.
Qed.

Lemma sqrt_wd : forall x y xpos ypos, x [=] y -> sqrt x xpos [=] sqrt y ypos.
Proof.
 intros.
 unfold sqrt in |- *.
 apply NRoot_wd.
 auto.
Qed.

Hint Resolve sqrt_wd: algebra_c.

Lemma sqrt_to_nonneg : forall x, [0] [<=] x -> forall x2pos, sqrt (x[^]2) x2pos [=] x.
Proof.
 intros.
 apply root_unique with 2.
    apply sqrt_nonneg. auto. auto.
   Step_final (x[^]2).
Qed.

Lemma sqrt_to_nonpos : forall x, x [<=] [0] -> forall x2pos, sqrt (x[^]2) x2pos [=] [--]x.
Proof.
 intros.
 apply root_unique with 2.
    apply sqrt_nonneg.
   astepl ( [--]ZeroR). apply inv_resp_leEq. auto.
   auto.
 astepl (x[^]2). rational.
Qed.

Lemma sqrt_mult : forall x y xpos ypos xypos, sqrt (x[*]y) xypos [=] sqrt x xpos[*]sqrt y ypos.
Proof.
 intros.
 apply root_unique with 2.
    apply sqrt_nonneg.
   apply mult_resp_nonneg; apply sqrt_nonneg.
  auto.
 astepl (x[*]y).
 astepl (sqrt x xpos[^]2[*]sqrt y ypos[^]2).
 rational.
Qed.

Hint Resolve sqrt_mult: algebra.

Lemma sqrt_mult_wd : forall x y z xpos ypos zpos,
 z [=] x[*]y -> sqrt z zpos [=] sqrt x xpos[*]sqrt y ypos.
Proof.
 intros.
 cut ([0] [<=] x[*]y). intro.
  Step_final (sqrt (x[*]y) H0).
 apply mult_resp_nonneg; auto.
Qed.

Lemma sqrt_less : forall x y ypos, x[^]2 [<] y -> x [<] sqrt y ypos.
Proof.
 intros.
 apply power_cancel_less with 2.
  apply sqrt_nonneg.
 astepr y. auto.
Qed.

Lemma sqrt_less' : forall x y ypos, x[^]2 [<] y -> [--]x [<] sqrt y ypos.
Proof.
 intros.
 apply power_cancel_less with 2.
  apply sqrt_nonneg.
 rstepl (x[^]2). astepr y. auto.
Qed.

Lemma sqrt_resp_leEq : forall x y xpos ypos, x [<=] y -> sqrt x xpos [<=] sqrt y ypos.
Proof.
 intros.
 unfold sqrt in |- *.
 apply NRoot_resp_leEq.
 auto.
Qed.

Lemma sqrt_resp_less : forall x y xpos ypos, x [<] y -> sqrt x xpos [<] sqrt y ypos.
Proof.
 intros.
 unfold sqrt in |- *.
 apply NRoot_pres_less.
 auto.
Qed.

End Square_root.

#[global]
Hint Resolve sqrt_wd: algebra_c.
#[global]
Hint Resolve sqrt_sqr sqrt_mult: algebra.


Section Absolute_Props.

(**
** More on absolute value

With the help of square roots, we can prove some more properties of absolute
values in [IR].
*)

Lemma AbsIR_sqrt_sqr : forall x x2pos, AbsIR x [=] sqrt (x[^]2) x2pos.
Proof.
 intros x xxpos. unfold AbsIR in |- *. simpl in |- *. unfold ABSIR in |- *.
 apply equiv_imp_eq_max; intros.
   apply power_cancel_leEq with 2.
     auto.
    apply mult_cancel_leEq with (Two:IR). apply pos_two.
     rstepl (x[+][--]x).
    rstepr (y[+]y).
    apply plus_resp_leEq_both; auto.
   astepl ([1][*]x[*]x).
   rstepl (x[^]2[+][0]).
   apply shift_plus_leEq'.
   rstepr ((y[-]x) [*] (y[-][--]x)).
   apply mult_resp_nonneg.
    apply shift_zero_leEq_minus. auto.
    apply shift_zero_leEq_minus. auto.
   apply leEq_transitive with (sqrt (x[^]2) xxpos).
   apply power_cancel_leEq with 2. auto.
     apply sqrt_nonneg.
   astepr (x[^]2).
   apply leEq_reflexive.
  auto.
 apply leEq_transitive with (sqrt (x[^]2) xxpos).
  apply power_cancel_leEq with 2. auto.
    apply sqrt_nonneg.
  astepr (x[^]2).
  rstepl (x[^]2).
  apply leEq_reflexive.
 auto.
Qed.

Hint Resolve AbsIR_sqrt_sqr: algebra.

Lemma AbsIR_resp_mult : forall x y, AbsIR (x[*]y) [=] AbsIR x[*]AbsIR y.
Proof.
 intros.
 astepl (sqrt ((x[*]y) [^]2) (sqr_nonneg _ (x[*]y))).
 cut ([0] [<=] x[^]2[*]y[^]2). intro.
  astepl (sqrt (x[^]2[*]y[^]2) H).
  Step_final (sqrt (x[^]2) (sqr_nonneg _ x) [*]sqrt (y[^]2) (sqr_nonneg _ y)).
 apply mult_resp_nonneg; apply sqr_nonneg.
Qed.

Lemma AbsIR_mult_pos : forall x y, [0] [<=] y -> AbsIR (x[*]y) [=] AbsIR x[*]y.
Proof.
 intros.
 apply eq_transitive_unfolded with (AbsIR x[*]AbsIR y).
  apply AbsIR_resp_mult.
 apply bin_op_wd_unfolded.
  algebra.
 unfold AbsIR in |- *; simpl in |- *; unfold ABSIR in |- *.
 apply eq_transitive_unfolded with (Max [--]y y).
  apply Max_comm.
 apply leEq_imp_Max_is_rht.
 apply leEq_transitive with ZeroR.
  astepr ( [--]ZeroR).
  apply inv_resp_leEq; assumption.
 assumption.
Qed.

Lemma AbsIR_mult_pos' : forall x y, [0] [<=] x -> AbsIR (x[*]y) [=] x[*]AbsIR y.
Proof.
 intros.
 astepl (AbsIR (y[*]x)).
 eapply eq_transitive_unfolded.
  apply AbsIR_mult_pos; auto.
 algebra.
Qed.

Lemma AbsIR_nexp : forall x n, AbsIR (nexp _ n x) [=] nexp _ n (AbsIR x).
Proof.
 intros.
 induction  n as [| n Hrecn].
  simpl in |- *; apply AbsIR_eq_x; apply less_leEq; apply pos_one.
 simpl in |- *.
 eapply eq_transitive_unfolded.
  apply AbsIR_resp_mult.
 algebra.
Qed.

Lemma AbsIR_nexp_op : forall n x, AbsIR (x[^]n) [=] AbsIR x[^]n.
Proof.
 intros; simpl in |- *; apply AbsIR_nexp.
Qed.

Lemma AbsIR_less_square : forall x y, AbsIR x [<] y -> x[^]2 [<] y[^]2.
Proof.
 intros.
 eapply less_wdl.
  2: apply AbsIR_eq_x; apply sqr_nonneg.
 eapply less_wdl.
  2: apply eq_symmetric_unfolded; apply AbsIR_nexp_op.
 apply nexp_resp_less; auto.
 apply AbsIR_nonneg.
Qed.

Lemma AbsIR_leEq_square : forall x y, AbsIR x [<=] y -> x[^]2 [<=] y[^]2.
Proof.
 intros.
 eapply leEq_wdl.
  2: apply AbsIR_eq_x; apply sqr_nonneg.
 eapply leEq_wdl.
  2: apply eq_symmetric_unfolded; apply AbsIR_nexp_op.
 apply nexp_resp_leEq; auto.
 apply AbsIR_nonneg.
Qed.

Lemma AbsIR_division : forall x y y_ y__, AbsIR (x[/] y[//]y_) [=] (AbsIR x[/] AbsIR y[//]y__).
Proof.
 intros x y H Hy.
 rstepr (AbsIR x[*] ([1][/] AbsIR y[//]Hy)).
 apply eq_transitive_unfolded with (AbsIR (x[*] ([1][/] y[//]H))).
  apply un_op_wd_unfolded; rational.
 apply eq_transitive_unfolded with (AbsIR x[*]AbsIR ([1][/] y[//]H)).
  apply AbsIR_resp_mult.
 apply mult_wdr.
 cut (y [<] [0] or [0] [<] y).
  intros H0.
  elim H0.
   intros.
   apply eq_transitive_unfolded with ( [--] ([1][/] y[//]H)).
    apply AbsIR_eq_inv_x.
    rstepr ([0][/] [--]y[//]inv_resp_ap_zero _ _ H).
    apply shift_leEq_div.
     astepl ( [--]ZeroR).
     apply inv_resp_less; assumption.
    rstepl ( [--]OneR).
    astepr ( [--]ZeroR); apply inv_resp_leEq; apply less_leEq; apply pos_one.
   rstepl ([1][/] [--]y[//]inv_resp_ap_zero _ _ H).
   apply div_wd.
    algebra.
   apply eq_symmetric_unfolded; apply AbsIR_eq_inv_x.
   apply less_leEq; assumption.
  intros.
  apply eq_transitive_unfolded with ([1][/] y[//]H).
   apply AbsIR_eq_x.
   apply less_leEq; apply recip_resp_pos; assumption.
  apply div_wd; [ algebra
    | apply eq_symmetric_unfolded; apply AbsIR_eq_x; apply less_leEq; assumption ].
 apply ap_imp_less.
 assumption.
Qed.

(** Some special cases. *)

Lemma AbsIR_recip : forall x x_ x__, AbsIR ([1][/] x[//]x_) [=] ([1][/] AbsIR x[//]x__).
Proof.
 intros x H Ha.
 apply eq_transitive_unfolded with (AbsIR [1][/] AbsIR x[//]Ha).
  apply AbsIR_division.
 apply div_wd.
  2: algebra.
 apply AbsIR_eq_x; apply less_leEq; apply pos_one.
Qed.

Lemma AbsIR_div_two : forall x, AbsIR (x [/]TwoNZ) [=] AbsIR x [/]TwoNZ.
Proof.
 intros.
 apply eq_transitive_unfolded with (AbsIR x[/] AbsIR Two[//] AbsIR_resp_ap_zero _
   (ap_symmetric_unfolded _ _ _ (less_imp_ap _ _ _ (pos_two _)))).
  apply AbsIR_division.
 apply div_wd.
  algebra.
 apply AbsIR_eq_x; apply less_leEq; apply pos_two.
Qed.

(** Cauchy-Schwartz for IR and variants on that subject. *)

Lemma triangle_IR : forall x y, AbsIR (x[+]y) [<=] AbsIR x[+]AbsIR y.
Proof.
 intros.
 astepl (sqrt ((x[+]y) [^]2) (sqr_nonneg _ (x[+]y))).
 astepr (sqrt (x[^]2) (sqr_nonneg _ x) [+]sqrt (y[^]2) (sqr_nonneg _ y)).
 apply power_cancel_leEq with 2. auto.
   astepl ([0][+]ZeroR). apply plus_resp_leEq_both; apply sqrt_nonneg.
  astepl ((x[+]y) [^]2).
 rstepl (x[^]2[+]y[^]2[+]Two[*] (x[*]y)).
 rstepr (sqrt (x[^]2) (sqr_nonneg IR x) [^]2[+]sqrt (y[^]2) (sqr_nonneg IR y) [^]2[+]
   Two[*] (sqrt (x[^]2) (sqr_nonneg IR x) [*]sqrt (y[^]2) (sqr_nonneg IR y))).
 apply plus_resp_leEq_both.
  astepr (x[^]2[+]y[^]2). apply leEq_reflexive.
  apply mult_resp_leEq_lft.
  apply power_cancel_leEq with 2. auto.
    apply mult_resp_nonneg; apply sqrt_nonneg.
  rstepr (sqrt (x[^]2) (sqr_nonneg _ x) [^]2[*]sqrt (y[^]2) (sqr_nonneg _ y) [^]2).
  astepr (x[^]2[*]y[^]2).
  astepl (x[^]2[*]y[^]2).
  apply leEq_reflexive.
 apply less_leEq. apply pos_two.
Qed.

Lemma triangle_SumIR : forall k l s,
 k <= S l -> AbsIR (Sum k l s) [<=] Sum k l (fun i => AbsIR (s i)).
Proof.
 intros. induction  l as [| l Hrecl].
 generalize (toCle _ _ H); clear H; intro H.
  inversion H as [|m H0 H1].
   unfold Sum in |- *. unfold Sum1 in |- *. simpl in |- *.
   rstepr ZeroR.
   astepr (AbsIR [0]).
   apply eq_imp_leEq. apply AbsIR_wd. rational.
   inversion H0.
  unfold Sum in |- *. unfold Sum1 in |- *. simpl in |- *.
  rstepr (ABSIR (s 0)).
  apply eq_imp_leEq. apply AbsIR_wd. rational.
  elim (le_lt_eq_dec k (S (S l))); try intro y.
   apply leEq_wdl with (AbsIR (Sum k l s[+]s (S l))).
    apply leEq_wdr with (Sum k l (fun i : nat => AbsIR (s i)) [+]AbsIR (s (S l))).
     apply leEq_transitive with (AbsIR (Sum k l s) [+]AbsIR (s (S l))).
      apply triangle_IR.
     apply plus_resp_leEq. apply Hrecl. auto with arith.
     apply eq_symmetric_unfolded.
    apply Sum_last with (f := fun i : nat => AbsIR (s i)).
   apply AbsIR_wd.
   apply eq_symmetric_unfolded. apply Sum_last.
   rewrite y.
  unfold Sum in |- *. unfold Sum1 in |- *. simpl in |- *.
  rstepr ZeroR.
  astepr (AbsIR [0]).
  apply eq_imp_leEq. apply AbsIR_wd. rational.
  auto.
Qed.

Lemma triangle_IR_minus : forall x y, AbsIR (x[-]y) [<=] AbsIR x[+]AbsIR y.
Proof.
 intros.
 unfold cg_minus in |- *.
 apply leEq_wdr with (AbsIR x[+]AbsIR [--]y).
  apply triangle_IR.
 apply bin_op_wd_unfolded.
  algebra.
 unfold AbsIR in |- *; simpl in |- *; unfold ABSIR in |- *.
 apply eq_transitive_unfolded with (Max [--]y y).
  apply bin_op_wd_unfolded; algebra.
 apply Max_comm.
Qed.

Lemma weird_triangleIR : forall x y, AbsIR x[-]AbsIR (y[-]x) [<=] AbsIR y.
Proof.
 intros.
 apply shift_minus_leEq.
 simpl in |- *; unfold ABSIR in |- *; apply Max_leEq.
  rstepl (y[+][--] (y[-]x)).
  apply plus_resp_leEq_both; [ apply lft_leEq_Max | apply rht_leEq_Max ].
 rstepl ( [--]y[+] (y[-]x)).
 apply plus_resp_leEq_both; [ apply rht_leEq_Max | apply lft_leEq_Max ].
Qed.

Lemma triangle_IR_minus' : forall x y, AbsIR x[-]AbsIR y [<=] AbsIR (x[-]y).
Proof.
 intros.
 eapply leEq_wdr.
  2: apply AbsIR_minus.
 apply shift_minus_leEq; apply shift_leEq_plus'.
 apply weird_triangleIR.
Qed.

Lemma triangle_SumxIR : forall n (f : forall i, i < n -> IR),
 AbsIR (Sumx f) [<=] Sumx (fun i H => AbsIR (f i H)).
Proof.
 simple induction n.
  intros; simpl in |- *.
  apply eq_imp_leEq; apply AbsIRz_isz.
 clear n; intros.
 simpl in |- *; eapply leEq_transitive.
  apply triangle_IR.
 apply plus_resp_leEq.
 eapply leEq_wdr.
  apply H.
 apply Sumx_wd.
 intros; algebra.
Qed.

Lemma triangle_Sum2IR : forall m n (f : forall i, m <= i -> i <= n -> IR),
 m <= S n -> AbsIR (Sum2 f) [<=] Sum2 (fun i Hm Hn => AbsIR (f i Hm Hn)).
Proof.
 intros.
 unfold Sum2 in |- *.
 eapply leEq_wdr.
  apply triangle_SumIR.
  assumption.
 apply Sum_wd'.
  assumption.
 intros.
 elim (le_lt_dec m i); intro;
   [ simpl in |- * | exfalso; apply (Nat.le_ngt m i); auto with arith ].
 elim (le_lt_dec i n); intro;
   [ simpl in |- * | exfalso; apply (Nat.le_ngt i n); auto with arith ].
 algebra.
Qed.

Lemma AbsIR_str_bnd_AbsIR : forall a b e, AbsIR (a[-]b) [<] e -> AbsIR b [<] AbsIR a[+]e.
Proof.
 do 3 intro. intro H.
 apply shift_less_plus'.
 eapply leEq_less_trans.
  apply triangle_IR_minus'.
 eapply less_wdl; [ apply H | apply AbsIR_minus ].
Qed.

Lemma AbsIR_bnd_AbsIR : forall a b e, AbsIR (a[-]b) [<=] e -> AbsIR b [<=] AbsIR a[+]e.
Proof.
 intros.
 apply shift_leEq_plus'.
 eapply leEq_transitive.
  apply triangle_IR_minus'.
 eapply leEq_wdl; [ apply H | apply AbsIR_minus ].
Qed.

End Absolute_Props.

Section Consequences.

(**
** Cauchy sequences

With these results, we can also prove that the sequence of reciprocals of a
Cauchy sequence that is never zero and whose Limit is not zero is also a
Cauchy sequence.
*)

Lemma Cauchy_Lim_recip : forall seq y, Cauchy_Lim_prop2 seq y ->
 forall seq_ y_, Cauchy_Lim_prop2 (fun n : nat => [1][/] seq n[//]seq_ n) ([1][/] y[//]y_).
Proof.
 intros seq y H Hn Hy.
 red in |- *; red in H.
 intros eps He.
 cut {n0 : nat | forall n : nat, n0 <= n -> AbsIR y [/]TwoNZ [<=] AbsIR (seq n)}.
  intro H0.
  elim H0; clear H0; intros n0 Hn0.
  cut ([0] [<] eps [/]TwoNZ[*] (AbsIR y[*]AbsIR y)).
   intro H0.
   elim (H _ H0); clear H.
   intros N HN.
   exists (Nat.max N n0).
   intros.
   apply AbsIR_imp_AbsSmall.
   apply leEq_wdl with (([1][/] _[//]AbsIR_resp_ap_zero _ (Hn m)) [*]
     ([1][/] _[//]AbsIR_resp_ap_zero _ Hy) [*]AbsIR (seq m[-]y)).
    rstepr ((Two[/] _[//]AbsIR_resp_ap_zero _ Hy) [*] ([1][/] _[//]AbsIR_resp_ap_zero _ Hy) [*]
      (eps [/]TwoNZ[*] (AbsIR y[*]AbsIR y))).
    apply mult_resp_leEq_both.
       astepl (ZeroR[*][0]); apply mult_resp_leEq_both; try apply leEq_reflexive.
        apply less_leEq; apply recip_resp_pos; apply AbsIR_pos; apply Hn.
       apply less_leEq; apply recip_resp_pos; apply AbsIR_pos; apply Hy.
      apply AbsIR_nonneg.
     apply mult_resp_leEq_rht.
      rstepr ([1][/] _[//] div_resp_ap_zero_rev _ _ _ (two_ap_zero _) (AbsIR_resp_ap_zero _ Hy)).
      apply recip_resp_leEq.
       apply pos_div_two; apply AbsIR_pos; apply Hy.
      apply Hn0.
      apply Nat.le_trans with (Nat.max N n0); auto with arith.
     apply less_leEq; apply recip_resp_pos; apply AbsIR_pos; apply Hy.
    apply AbsSmall_imp_AbsIR.
    apply HN.
    apply Nat.le_trans with (Nat.max N n0); auto with arith.
   apply eq_transitive_unfolded with
     (AbsIR ([1][/] _[//]Hn m) [*]AbsIR ([1][/] _[//]Hy) [*]AbsIR (y[-]seq m)).
    repeat apply mult_wd; apply eq_symmetric_unfolded.
      apply AbsIR_recip.
     apply AbsIR_recip.
    apply AbsIR_minus.
   apply eq_transitive_unfolded with (AbsIR (([1][/] _[//]Hn m) [*] ([1][/] _[//]Hy) [*] (y[-]seq m))).
    eapply eq_transitive_unfolded.
     2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
    apply mult_wdl.
    apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
   apply AbsIR_wd.
   rational.
  astepl (ZeroR[*][0]); apply mult_resp_less_both; try apply leEq_reflexive.
   apply pos_div_two; assumption.
  astepl (ZeroR[*][0]); apply mult_resp_less_both; try apply leEq_reflexive;
    apply AbsIR_pos; apply Hy.
 cut {n0 : nat | forall n : nat, n0 <= n -> AbsSmall (AbsIR y [/]TwoNZ) (seq n[-]y)}.
  2: apply H.
  2: eapply less_wdr.
   3: apply AbsIR_div_two.
  2: apply AbsIR_pos.
  2: apply div_resp_ap_zero_rev; apply Hy.
 intro H0.
 elim H0; intros n0 Hn0; clear H0; exists n0; intros.
 apply leEq_transitive with (AbsIR y[-]AbsIR (seq n[-]y)).
  apply shift_leEq_minus; apply shift_plus_leEq'.
  rstepr (AbsIR y [/]TwoNZ).
  apply AbsSmall_imp_AbsIR.
  apply Hn0; assumption.
 apply weird_triangleIR.
Qed.

Lemma Cauchy_recip : forall seq seq_, Lim seq [#] ([0]:IR) ->
 Cauchy_prop (fun n => [1][/] seq n[//]seq_ n).
Proof.
 intros seq Hn Hy.
 apply Cauchy_prop2_prop.
 exists ([1][/] _[//]Hy).
 apply Cauchy_Lim_recip.
 apply Cauchy_complete.
Qed.

Lemma Lim_recip : forall seq seq_ seq__,
 Lim (Build_CauchySeq _ _ (Cauchy_recip seq seq_ seq__)) [=] ([1][/] _[//]seq__).
Proof.
 intros.
 apply eq_symmetric_unfolded; apply Limits_unique.
 simpl in |- *; apply Cauchy_Lim_recip.
 apply Cauchy_complete.
Qed.

End Consequences.

Section Part_Function_NRoot.

(** *** Functional Operators

%\begin{convention}%
Let [F:PartIR] and denote by [P] its domain, which must be entirely nonnegative.
%\end{convention}%
*)

Variables F : PartIR.

Let P := Dom F.

Let R := extend P (fun x Hx => [0][<=]F x Hx).

Let Ext2R := ext2 (P:=P) (R:=fun x Hx => [0][<=]F x Hx).

Variable n : nat.

Hypothesis Hn : 0 < n.

Lemma part_function_NRoot_strext : forall x y Hx Hy,
 NRoot (Ext2R x Hx) Hn [#] NRoot (Ext2R y Hy) Hn -> x [#] y.
Proof.
 intros x y Hx Hy H.
 refine (pfstrx _ _ _ _ _ _ (NRoot_str_ext _ _ _ _ _ _ _ H)).
Qed.

Lemma part_function_NRoot_pred_wd : pred_wd _ R.
Proof.
 intros x y H H0.
 elim H.
 intros H1 H2.
 split.
  apply (dom_wd _ F x y H1 H0).
 intros H3.
 astepr (F x H1).
 auto.
Qed.

Definition FNRoot := Build_PartFunct IR _ part_function_NRoot_pred_wd
 (fun x Hx => NRoot (Ext2R x Hx) Hn) part_function_NRoot_strext.

Section Included.

Variable S:IR -> CProp.

Lemma included_FNRoot : included S P ->
 (forall x, S x -> forall Hx, [0][<=]F x Hx) -> included S (Dom FNRoot).
Proof.
 intros H H0.
 simpl in |- *.
 unfold extend in |- *.
 split.
  apply H; assumption.
 intros; apply H0; assumption.
Qed.

Lemma included_FNRoot' : included S (Dom FNRoot) -> included S P.
Proof.
 intro H; simpl in H; eapply included_extend; unfold R in *; apply H.
Qed.

End Included.

End Part_Function_NRoot.

#[global]
Hint Resolve included_FNRoot included_FNRoot' : included.
