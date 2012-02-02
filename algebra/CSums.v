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

(** printing Sum0 %\ensuremath{\sum_0}% #&sum;<sub>0</sub># *)
(** printing Sum1 %\ensuremath{\sum_1}% #&sum;<sub>1</sub># *)
(** printing Sum2 %\ensuremath{\sum_2}% #&sum;<sub>2</sub># *)
(** printing Sum %\ensuremath{\sum}% #&sum;# *)
(** printing Sumx %\ensuremath{\sum'}% #&sum;'&*)

Require Export CAbGroups.
Require Export Peano_dec.

(**
* Sums

%\begin{convention}% Let [G] be an abelian group.
%\end{convention}%
*)

Section Sums.

Variable G : CAbGroup. (* Sum1 and Sum use subtraction *)

Fixpoint Sumlist (l : list G) : G :=
  match l with
  | nil      => [0]:G
  | cons x k => x[+]Sumlist k
  end.

Fixpoint Sumx n : (forall i : nat, i < n -> G) -> G :=
  match n return ((forall i : nat, i < n -> G) -> G) with
  | O   => fun _ => [0]:G
  | S m => fun f => Sumx m (fun i l => f i (lt_S _ _ l)) [+]f m (lt_n_Sn m)
  end.

(**
It is sometimes useful to view a function defined on $\{0,\ldots,i-1\}$
#{0, ... i-1}# as a function on the natural numbers which evaluates to
[Zero] when the input is greater than or equal to [i].
*)

Definition part_tot_nat_fun n (f : forall i, i < n -> G) : nat -> G.
Proof.
 intros i.
 elim (le_lt_dec n i).
  intro a; apply ([0]:G).
 intro b; apply (f i b).
Defined.

Lemma part_tot_nat_fun_ch1 : forall n (f : forall i, i < n -> G),
 nat_less_n_fun f -> forall i Hi, part_tot_nat_fun n f i [=] f i Hi.
Proof.
 intros n f Hf i Hi.
 unfold part_tot_nat_fun in |- *.
 elim le_lt_dec; intro.
  elimtype False; apply (le_not_lt n i); auto.
 simpl in |- *; apply Hf; auto.
Qed.

Lemma part_tot_nat_fun_ch2 : forall n (f : forall i, i < n -> G) i,
 n <= i -> part_tot_nat_fun n f i [=] [0].
Proof.
 intros n f i Hi.
 unfold part_tot_nat_fun in |- *.
 elim le_lt_dec; intro.
  simpl in |- *; algebra.
 elimtype False; apply (le_not_lt n i); auto.
Qed.

(** [Sum0] defines the sum for [i=0..(n-1)] *)

Fixpoint Sum0 (n:nat) (f : nat -> G) {struct n} : G :=
  match n with
  | O   => [0]:G
  | S m => Sum0 m f[+]f m
  end.

(** [Sum1] defines the sum for [i=m..(n-1)] *)

Definition Sum1 m n f := Sum0 n f[-]Sum0 m f.

Definition Sum m n : (nat -> G) -> G := Sum1 m (S n).
(* Sum i=m..n *)

(** [Sum2] is similar to [Sum1], but does not require the summand to be
defined outside where it is being added. *)

Definition Sum2 m n (h : forall i : nat, m <= i -> i <= n -> G) : G.
Proof.
 apply (Sum m n).
 intro i.
 elim (le_lt_dec m i); intro H.
  elim (le_lt_dec i n); intro H0.
   apply (h i H H0).
  apply ([0]:G).
 apply ([0]:G).
Defined.

Lemma Sum_one : forall n f, Sum n n f [=] f n.
Proof.
 intros n f.
 unfold Sum in |- *.
 unfold Sum1 in |- *.
 simpl in |- *.
 Step_final (f n[+]Sum0 n f[-]Sum0 n f).
Qed.

Hint Resolve Sum_one: algebra.

Lemma Sum_empty : forall n f, 0 < n -> Sum n (pred n) f [=] [0].
Proof.
 intros n f H.
 unfold Sum in |- *.
 rewrite <- (S_pred _ _ H).
 unfold Sum1 in |- *; algebra.
Qed.

Hint Resolve Sum_empty: algebra.

Lemma Sum_Sum : forall l m n f, Sum l m f[+]Sum (S m) n f [=] Sum l n f.
Proof.
 intros l m n f.
 unfold Sum in |- *.
 unfold Sum1 in |- *.
 astepl (Sum0 (S n) f[-]Sum0 (S m) f[+] (Sum0 (S m) f[-]Sum0 l f)).
 astepl (Sum0 (S n) f[-]Sum0 (S m) f[+]Sum0 (S m) f[-]Sum0 l f).
 astepl (Sum0 (S n) f[-] (Sum0 (S m) f[-]Sum0 (S m) f) [-]Sum0 l f).
 astepl (Sum0 (S n) f[-][0][-]Sum0 l f).
 astepl (Sum0 (S n) f[+] [--][0][-]Sum0 l f).
 Step_final (Sum0 (S n) f[+][0][-]Sum0 l f).
Qed.

Hint Resolve Sum_Sum: algebra.

Lemma Sum_first : forall m n f, Sum m n f [=] f m[+]Sum (S m) n f.
Proof.
 intros m n f.
 unfold Sum in |- *.
 unfold Sum1 in |- *.
 astepr (f m[+]Sum0 (S n) f[-]Sum0 (S m) f).
 astepr (Sum0 (S n) f[+]f m[-]Sum0 (S m) f).
 astepr (Sum0 (S n) f[+] (f m[-]Sum0 (S m) f)).
 unfold cg_minus in |- *.
 apply bin_op_wd_unfolded.
  algebra.
 simpl in |- *.
 astepr (f m[+] [--] (f m[+]Sum0 m f)).
 astepr (f m[+] ([--] (f m) [+] [--] (Sum0 m f))).
 astepr (f m[+] [--] (f m) [+] [--] (Sum0 m f)).
 astepr ([0][+] [--] (Sum0 m f)).
 algebra.
Qed.

Lemma Sum_last : forall m n f, Sum m (S n) f [=] Sum m n f[+]f (S n).
Proof.
 intros m n f.
 unfold Sum in |- *.
 unfold Sum1 in |- *.
 simpl in |- *.
 unfold cg_minus in |- *.
 astepl (Sum0 n f[+]f n[+] (f (S n) [+] [--] (Sum0 m f))).
 astepr (Sum0 n f[+]f n[+] ([--] (Sum0 m f) [+]f (S n))).
 algebra.
Qed.

Hint Resolve Sum_last: algebra.

Lemma Sum_last' : forall m n f, 0 < n -> Sum m n f [=] Sum m (pred n) f[+]f n.
Proof.
 intros m n f H. induction  n as [| n Hrecn].
 elim (lt_irrefl 0 H).
 apply Sum_last.
Qed.

(**
We add some extensionality results which will be quite useful
when working with integration.
*)

Lemma Sum0_strext : forall f g n, Sum0 n f [#] Sum0 n g -> {i:nat | i < n | f i [#] g i}.
Proof.
 intros f g n H.
 induction  n as [| n Hrecn].
  simpl in H.
  elim (ap_irreflexive_unfolded _ _ H).
 simpl in H.
 cut ({i : nat | i < n | f i [#] g i} or f n [#] g n).
  intro H0.
  elim H0; intro H1.
   elim H1; intros i H2 H3; exists i; auto with arith.
  exists n; auto with arith.
 cut (Sum0 n f [#] Sum0 n g or f n [#] g n).
  intro H0; elim H0; intro H1.
   left; apply Hrecn; assumption.
  auto.
 apply bin_op_strext_unfolded with (csg_op (c:=G)).
 assumption.
Qed.

Lemma Sum_strext : forall f g m n, m <= S n ->
 Sum m n f [#] Sum m n g -> {i : nat | m <= i /\ i <= n | f i [#] g i}.
Proof.
 intros f g m n H H0.
 induction  n as [| n Hrecn].
  elim (le_lt_eq_dec _ _ H); intro H2.
   cut (m = 0).
    intro H1.
    rewrite H1; exists 0; auto.
    rewrite H1 in H0.
    astepl (Sum 0 0 f); astepr (Sum 0 0 g); assumption.
   inversion H2; [ auto | inversion H3 ].
  elimtype False.
  cut (0 = pred 1); [ intro H3 | auto ].
  rewrite H3 in H0.
  rewrite H2 in H0.
  apply (ap_irreflexive_unfolded G [0]).
  eapply ap_wdl_unfolded.
   eapply ap_wdr_unfolded.
    apply H0.
   apply Sum_empty; auto.
  apply Sum_empty; auto.
 elim (le_lt_eq_dec _ _ H); intro Hmn.
  cut (Sum m n f [#] Sum m n g or f (S n) [#] g (S n)).
   intro H1; elim H1; intro H2.
    cut {i : nat | m <= i /\ i <= n | f i [#] g i}.
     intro H3; elim H3; intros i H4 H5; elim H4; intros H6 H7; clear H1 H4.
     exists i; try split; auto with arith.
    apply Hrecn; auto with arith.
   exists (S n); try split; auto with arith.
  apply bin_op_strext_unfolded with (csg_op (c:=G)).
  astepl (Sum m (S n) f); astepr (Sum m (S n) g); assumption.
 clear Hrecn.
 elimtype False.
 cut (S n = pred (S (S n))); [ intro H1 | auto ].
 rewrite H1 in H0.
 rewrite Hmn in H0.
 apply (ap_irreflexive_unfolded G [0]).
 eapply ap_wdl_unfolded.
  eapply ap_wdr_unfolded.
   apply H0.
  apply Sum_empty; auto with arith.
 apply Sum_empty; auto with arith.
Qed.

Lemma Sumx_strext : forall n f g, nat_less_n_fun f -> nat_less_n_fun g ->
 Sumx _ f [#] Sumx _ g -> {N : nat | {HN : N < n | f N HN [#] g N HN}}.
Proof.
 intro n; induction  n as [| n Hrecn].
  intros f g H H0 H1.
  elim (ap_irreflexive_unfolded _ _ H1).
 intros f g H H0 H1.
 simpl in H1.
 elim (bin_op_strext_unfolded _ _ _ _ _ _ H1); clear H1; intro H1.
  cut (nat_less_n_fun (fun (i : nat) (l : i < n) => f i (lt_S _ _ l)));
    [ intro H2 | red in |- *; intros; apply H; assumption ].
  cut (nat_less_n_fun (fun (i : nat) (l : i < n) => g i (lt_S _ _ l)));
    [ intro H3 | red in |- *; intros; apply H0; assumption ].
  elim (Hrecn _ _ H2 H3 H1); intros N HN.
  elim HN; clear HN; intros HN H'.
  exists N. exists (lt_S _ _ HN).
  eapply ap_wdl_unfolded.
   eapply ap_wdr_unfolded.
    apply H'.
   algebra.
  algebra.
 exists n. exists (lt_n_Sn n).
 eapply ap_wdl_unfolded.
  eapply ap_wdr_unfolded.
   apply H1.
  algebra.
 algebra.
Qed.

Lemma Sum0_strext' : forall f g n, Sum0 n f [#] Sum0 n g -> {i : nat | f i [#] g i}.
Proof.
 intros f g n H.
 elim (Sum0_strext _ _ _ H); intros i Hi Hi'; exists i; auto.
Qed.

Lemma Sum_strext' : forall f g m n, Sum m n f [#] Sum m n g -> {i : nat | f i [#] g i}.
Proof.
 intros f g m n H.
 unfold Sum, Sum1 in H.
 elim (cg_minus_strext _ _ _ _ _ H); intro H1; elim (Sum0_strext _ _ _ H1);
   intros i Hi Hi'; exists i; assumption.
Qed.

Lemma Sum0_wd : forall m f f', (forall i, f i [=] f' i) -> Sum0 m f [=] Sum0 m f'.
Proof.
 intros m f f' H.
 elim m; simpl in |- *; algebra.
Qed.

Lemma Sum_wd : forall m n f f', (forall i, f i [=] f' i) -> Sum m n f [=] Sum m n f'.
Proof.
 intros m n f f' H.
 unfold Sum in |- *.
 unfold Sum1 in |- *.
 unfold cg_minus in |- *.
 apply bin_op_wd_unfolded.
  apply Sum0_wd; exact H.
 apply un_op_wd_unfolded.
 apply Sum0_wd; exact H.
Qed.

Lemma Sumx_wd : forall n f g, (forall i H, f i H [=] g i H) -> Sumx n f [=] Sumx n g.
Proof.
 intro n; elim n; intros; simpl in |- *; algebra.
Qed.

Lemma Sum_wd' : forall m n, m <= S n -> forall f f',
 (forall i, m <= i -> i <= n -> f i [=] f' i) -> Sum m n f [=] Sum m n f'.
Proof.
 intros m n. induction  n as [| n Hrecn]; intros H f f' H0.
 inversion H.
   unfold Sum in |- *. unfold Sum1 in |- *. Step_final ([0]:G).
   inversion H2. astepl (f 0). astepr (f' 0). auto.
  elim (le_lt_eq_dec m (S (S n)) H); intro H1.
  astepl (Sum m n f[+]f (S n)).
  astepr (Sum m n f'[+]f' (S n)).
  apply bin_op_wd_unfolded; auto with arith.
 rewrite H1.
 unfold Sum in |- *. unfold Sum1 in |- *. Step_final ([0]:G).
Qed.

Lemma Sum2_wd : forall m n, m <= S n -> forall f g,
 (forall i Hm Hn, f i Hm Hn [=] g i Hm Hn) -> Sum2 m n f [=] Sum2 m n g.
Proof.
 intros m n H f g H0.
 unfold Sum2 in |- *.
 apply Sum_wd'.
  assumption.
 intros i H1 H2.
 elim le_lt_dec; intro H3; [ simpl in |- * | elimtype False; apply (le_not_lt i n); auto ].
 elim le_lt_dec; intro H4; [ simpl in |- * | elimtype False; apply (le_not_lt m i); auto ].
 algebra.
Qed.

Lemma Sum0_plus_Sum0 : forall f g m, Sum0 m (fun i => f i[+]g i) [=] Sum0 m f[+]Sum0 m g.
Proof.
 intros f g m.
 elim m.
  simpl in |- *; algebra.
 intros n H.
 simpl in |- *.
 astepl (Sum0 n f[+]Sum0 n g[+] (f n[+]g n)).
 astepl (Sum0 n f[+] (Sum0 n g[+] (f n[+]g n))).
 astepl (Sum0 n f[+] (Sum0 n g[+]f n[+]g n)).
 astepl (Sum0 n f[+] (f n[+]Sum0 n g[+]g n)).
 astepl (Sum0 n f[+] (f n[+]Sum0 n g) [+]g n).
 Step_final (Sum0 n f[+]f n[+]Sum0 n g[+]g n).
Qed.
Hint Resolve Sum0_plus_Sum0: algebra.

Lemma Sum_plus_Sum : forall f g m n, Sum m n (fun i => f i[+]g i) [=] Sum m n f[+]Sum m n g.
Proof.
 intros f g m n.
 unfold Sum in |- *.
 unfold Sum1 in |- *.
 astepl (Sum0 (S n) f[+]Sum0 (S n) g[-] (Sum0 m f[+]Sum0 m g)).
 astepl (Sum0 (S n) f[+]Sum0 (S n) g[-]Sum0 m f[-]Sum0 m g).
 unfold cg_minus in |- *.
 astepr (Sum0 (S n) f[+] [--] (Sum0 m f) [+]Sum0 (S n) g[+] [--] (Sum0 m g)).
 apply bin_op_wd_unfolded.
  astepl (Sum0 (S n) f[+] (Sum0 (S n) g[+] [--] (Sum0 m f))).
  astepl (Sum0 (S n) f[+] ([--] (Sum0 m f) [+]Sum0 (S n) g)).
  algebra.
 algebra.
Qed.

Lemma Sumx_plus_Sumx : forall n f g, Sumx n f[+]Sumx n g [=] Sumx n (fun i Hi => f i Hi[+]g i Hi).
Proof.
 intro n; induction  n as [| n Hrecn].
  intros; simpl in |- *; algebra.
 intros f g; simpl in |- *.
 apply eq_transitive_unfolded with (Sumx _ (fun (i : nat) (l : i < n) => f i (lt_S i n l)) [+]
   Sumx _ (fun (i : nat) (l : i < n) => g i (lt_S i n l)) [+] (f n (lt_n_Sn n) [+]g n (lt_n_Sn n))).
  set (Sf := Sumx _ (fun (i : nat) (l : i < n) => f i (lt_S i n l))) in *.
  set (Sg := Sumx _ (fun (i : nat) (l : i < n) => g i (lt_S i n l))) in *.
  set (fn := f n (lt_n_Sn n)) in *; set (gn := g n (lt_n_Sn n)) in *.
  astepl (Sf[+]fn[+]Sg[+]gn).
  astepl (Sf[+] (fn[+]Sg) [+]gn).
  astepl (Sf[+] (Sg[+]fn) [+]gn).
  Step_final (Sf[+]Sg[+]fn[+]gn).
 apply bin_op_wd_unfolded; algebra.
(* useless since V8.1:
apply
 Hrecn
  with
    (f := fun (i : nat) (l : i < n) => f i (lt_S i n l))
    (g := fun (i : nat) (l : i < n) => g i (lt_S i n l)).
*)
Qed.

Lemma Sum2_plus_Sum2 : forall m n, m <= S n -> forall f g,
 Sum2 m n f[+]Sum2 m n g [=] Sum2 _ _ (fun i Hm Hn => f i Hm Hn[+]g i Hm Hn).
Proof.
 intros m n H f g.
 unfold Sum2 in |- *; simpl in |- *.
 apply eq_symmetric_unfolded.
 eapply eq_transitive_unfolded.
  2: apply Sum_plus_Sum.
 apply Sum_wd; intro i.
 elim le_lt_dec; intro H0; simpl in |- *; elim le_lt_dec; intro H1; simpl in |- *; algebra.
Qed.

Lemma inv_Sum0 : forall f n, Sum0 n (fun i => [--] (f i)) [=] [--] (Sum0 n f).
Proof.
 intros f n.
 induction  n as [| n Hrecn].
  simpl in |- *; algebra.
 simpl in |- *.
 Step_final ([--] (Sum0 n f) [+] [--] (f n)).
Qed.

Hint Resolve inv_Sum0: algebra.

Lemma inv_Sum : forall f m n, Sum m n (fun i => [--] (f i)) [=] [--] (Sum m n f).
Proof.
 intros f a b.
 unfold Sum in |- *.
 unfold Sum1 in |- *.
 astepl ([--] (Sum0 (S b) f) [-][--] (Sum0 a f)).
 astepl ([--] (Sum0 (S b) f) [+] [--][--] (Sum0 a f)).
 Step_final ([--] (Sum0 (S b) f[+] [--] (Sum0 a f))).
Qed.

Hint Resolve inv_Sum: algebra.

Lemma inv_Sumx : forall n f, [--] (Sumx n f) [=] Sumx _ (fun i Hi => [--] (f i Hi)).
Proof.
 intro n; induction  n as [| n Hrecn].
  simpl in |- *; algebra.
 intro f; simpl in |- *.
 astepl ([--] (Sumx _ (fun i (l : i < n) => f i (lt_S i n l))) [+] [--] (f n (lt_n_Sn n))).
 apply bin_op_wd_unfolded.
  apply Hrecn with (f := fun i (l : i < n) => f i (lt_S i n l)).
 algebra.
Qed.

Lemma inv_Sum2 : forall m n : nat, m <= S n -> forall f,
 [--] (Sum2 m n f) [=] Sum2 _ _ (fun i Hm Hn => [--] (f i Hm Hn)).
Proof.
 intros m n H f.
 unfold Sum2 in |- *; simpl in |- *.
 apply eq_symmetric_unfolded.
 eapply eq_transitive_unfolded.
  2: apply inv_Sum.
 apply Sum_wd; intro i.
 elim le_lt_dec; intro; simpl in |- *; elim le_lt_dec; intro; simpl in |- *; algebra.
Qed.

Lemma Sum_minus_Sum : forall f g m n, Sum m n (fun i => f i[-]g i) [=] Sum m n f[-]Sum m n g.
Proof.
 (* WHAT A MISERY TO PROVE THIS *)
 intros f g a b.
 astepl (Sum a b (fun i : nat => f i[+] [--] (g i))).
 cut (Sum a b (fun i : nat => f i[+] (fun j : nat => [--] (g j)) i) [=]
   Sum a b f[+]Sum a b (fun j : nat => [--] (g j))).
  intro H.
  astepl (Sum a b f[+]Sum a b (fun j : nat => [--] (g j))).
  Step_final (Sum a b f[+] [--] (Sum a b g)).
 change (Sum a b (fun i : nat => f i[+] (fun j : nat => [--] (g j)) i) [=]
   Sum a b f[+]Sum a b (fun j : nat => [--] (g j))) in |- *.
 apply Sum_plus_Sum.
Qed.

Hint Resolve Sum_minus_Sum: algebra.

Lemma Sumx_minus_Sumx : forall n f g,
 Sumx n f[-]Sumx n g [=] Sumx _ (fun i Hi => f i Hi[-]g i Hi).
Proof.
 intros n f g; unfold cg_minus in |- *.
 eapply eq_transitive_unfolded.
  2: apply Sumx_plus_Sumx with (f := f) (g := fun i (Hi : i < n) => [--] (g i Hi)).
 apply bin_op_wd_unfolded; algebra.
 apply inv_Sumx.
Qed.

Lemma Sum2_minus_Sum2 : forall m n, m <= S n -> forall f g,
 Sum2 m n f[-]Sum2 m n g [=] Sum2 _ _ (fun i Hm Hn => f i Hm Hn[-]g i Hm Hn).
Proof.
 intros m n H f g; unfold cg_minus in |- *.
 eapply eq_transitive_unfolded.
  2: apply Sum2_plus_Sum2 with (f := f) (g := fun i (Hm : m <= i) (Hn : i <= n) => [--] (g i Hm Hn));
    assumption.
 apply bin_op_wd_unfolded.
  algebra.
 apply inv_Sum2; assumption.
Qed.

Lemma Sum_apzero : forall f m n,
 m <= n -> Sum m n f [#] [0] -> {i : nat | m <= i /\ i <= n | f i [#] [0]}.
Proof.
 intros a k l H H0. induction  l as [| l Hrecl].
 exists 0. split; auto. cut (k = 0).
   intro H'. rewrite H' in H0.
   astepl (Sum 0 0 a). auto.
   inversion H. auto.
  elim (le_lt_eq_dec k (S l) H); intro HH.
  cut (Sum k l a [#] [0] or a (S l) [#] [0]). intro H1.
   elim H1; clear H1; intro H1.
    elim Hrecl; auto with arith.
    intro i. intros H2 H6. exists i; auto.
    elim H2; intros H3 H4; auto.
   exists (S l); try split; auto with arith.
  apply cg_add_ap_zero.
  apply ap_wdl_unfolded with (Sum k (S l) a). auto.
   apply Sum_last.
 rewrite HH in H0.
 exists (S l); auto.
 astepl (Sum (S l) (S l) a). auto.
Qed.

Lemma Sum_zero : forall f m n, m <= S n ->
 (forall i, m <= i -> i <= n -> f i [=] [0]) -> Sum m n f [=] [0].
Proof.
 intros a k l H H0. induction  l as [| l Hrecl].
 elim (le_lt_eq_dec _ _ H); clear H; intro H.
   replace k with 0. astepl (a 0). apply H0. auto.
    auto with arith. auto. inversion H. auto. inversion H2.
    rewrite H.
  unfold Sum in |- *. unfold Sum1 in |- *. algebra.
  elim (le_lt_eq_dec k (S (S l)) H); intro HH.
  astepl (Sum k l a[+]a (S l)).
  astepr ([0][+] ([0]:G)).
  apply bin_op_wd_unfolded.
   apply Hrecl; auto with arith.
  apply H0; auto with arith.
 rewrite HH.
 unfold Sum in |- *. unfold Sum1 in |- *. algebra.
Qed.

Lemma Sum_term : forall f m i n, m <= i -> i <= n ->
 (forall j, m <= j -> j <> i -> j <= n -> f j [=] [0]) -> Sum m n f [=] f i.
Proof.
 intros a k i0 l H H0 H1.
 astepl (Sum k i0 a[+]Sum (S i0) l a).
 astepr (a i0[+][0]).
 apply bin_op_wd_unfolded.
  elim (O_or_S i0); intro H2.
   elim H2; intros m Hm.
   rewrite <- Hm.
   astepl (Sum k m a[+]a (S m)).
   astepr ([0][+]a (S m)).
   apply bin_op_wd_unfolded.
    apply Sum_zero. rewrite Hm; auto.
     intros i H3 H4. apply H1. auto. omega. omega.
    algebra.
  rewrite <- H2 in H. rewrite <- H2.
  inversion H. algebra.
  apply Sum_zero. auto with arith.
  intros. apply H1. omega. omega. auto.
Qed.

Lemma Sum0_shift : forall f g n, (forall i, f i [=] g (S i)) -> g 0[+]Sum0 n f [=] Sum0 (S n) g.
Proof.
 intros a b l H. induction  l as [| l Hrecl].
 simpl in |- *; algebra.
 simpl in |- *.
 astepl (b 0[+]Sum0 l a[+]a l).
 Step_final (Sum0 (S l) b[+]a l).
Qed.

Hint Resolve Sum0_shift: algebra.

Lemma Sum_shift : forall f g m n,
 (forall i, f i [=] g (S i)) -> Sum m n f [=] Sum (S m) (S n) g.
Proof.
 unfold Sum in |- *. unfold Sum1 in |- *. intros a b k l H.
 astepl (Sum0 (S l) a[+]b 0[-]b 0[-]Sum0 k a).
 astepl (Sum0 (S l) a[+]b 0[-] (b 0[+]Sum0 k a)).
 Step_final (b 0[+]Sum0 (S l) a[-] (b 0[+]Sum0 k a)).
Qed.

Lemma Sum_big_shift : forall f g k m n, (forall j, m <= j -> f j [=] g (j + k)) ->
 m <= S n -> Sum m n f [=] Sum (m + k) (n + k) g.
Proof.
 do 3 intro; generalize f g; clear f g.
 induction  k as [| k Hreck].
  intros f g n m. repeat rewrite <- plus_n_O.
  intros H H0.
  apply: Sum_wd'. auto.
   intros. set (Hi:= H i). rewrite <- (plus_n_O i) in Hi. apply: Hi. auto.
  intros; repeat rewrite <- plus_n_Sm.
 apply eq_transitive_unfolded with (Sum (m + k) (n + k) (fun n : nat => g (S n))).
  2: apply Sum_shift; algebra.
 apply Hreck.
  intros; rewrite plus_n_Sm; apply H; auto with arith.
 auto.
Qed.

Lemma Sumx_Sum0 : forall n f g,
 (forall i Hi, f i Hi [=] g i) -> Sumx n f [=] Sum0 n g.
Proof.
 intro; induction  n as [| n Hrecn]; simpl in |- *; algebra.
Qed.

End Sums.

Implicit Arguments Sum [G].
Implicit Arguments Sum0 [G].
Implicit Arguments Sumx [G n].
Implicit Arguments Sum2 [G m n].

(**
The next results are useful for calculating some special sums,
often referred to as ``Mengolli Sums''.
%\begin{convention}% Let [G] be an abelian group.
%\end{convention}%
*)

Section More_Sums.

Variable G : CAbGroup.

Lemma Mengolli_Sum : forall n (f : forall i, i <= n -> G) (g : forall i, i < n -> G),
 nat_less_n_fun' f -> (forall i H, g i H [=] f (S i) H[-]f i (lt_le_weak _ _ H)) ->
 Sumx g [=] f n (le_n n) [-]f 0 (le_O_n n).
Proof.
 intro n; induction  n as [| n Hrecn]; intros f g Hf H; simpl in |- *.
  astepl (f 0 (le_n 0) [-]f 0 (le_n 0)).
  apply cg_minus_wd; algebra.
 apply eq_transitive_unfolded with (f _ (le_n (S n)) [-]f _ (le_S _ _ (le_n n)) [+]
   (f _ (le_S _ _ (le_n n)) [-]f 0 (le_O_n (S n)))).
  eapply eq_transitive_unfolded.
   apply cag_commutes_unfolded.
  apply bin_op_wd_unfolded.
   eapply eq_transitive_unfolded.
    apply H.
   apply cg_minus_wd; apply Hf; algebra.
  set (f' := fun i (H : i <= n) => f i (le_S _ _ H)) in *.
  set (g' := fun i (H : i < n) => g i (lt_S _ _ H)) in *.
  apply eq_transitive_unfolded with (f' n (le_n n) [-]f' 0 (le_O_n n)).
   apply Hrecn.
    red in |- *; intros; unfold f' in |- *; apply Hf; algebra.
   intros i Hi.
   unfold f' in |- *; unfold g' in |- *.
   eapply eq_transitive_unfolded.
    apply H.
   apply cg_minus_wd; apply Hf; algebra.
  unfold f' in |- *; apply cg_minus_wd; apply Hf; algebra.
 astepr (f (S n) (le_n (S n)) [+][0][-]f 0 (le_O_n (S n))).
 astepr (f (S n) (le_n (S n)) [+] ([--] (f n (le_S _ _ (le_n n))) [+]f n (le_S _ _ (le_n n))) [-]
   f 0 (le_O_n (S n))).
 Step_final (f (S n) (le_n (S n)) [+] [--] (f n (le_S _ _ (le_n n))) [+]
   f n (le_S _ _ (le_n n)) [-]f 0 (le_O_n (S n))).
Qed.

Lemma Mengolli_Sum_gen : forall f g : nat -> G, (forall n, g n [=] f (S n) [-]f n) ->
 forall m n, m <= S n -> Sum m n g [=] f (S n) [-]f m.
Proof.
 intros f g H m n; induction  n as [| n Hrecn]; intro Hmn.
  elim (le_lt_eq_dec _ _ Hmn); intro H0.
   cut (m = 0); [ intro H1 | inversion H0; auto with arith; inversion H2 ].
   rewrite H1.
   eapply eq_transitive_unfolded; [ apply Sum_one | apply H ].
  cut (0 = pred 1); [ intro H1 | auto ].
  rewrite H0; astepr ([0]:G); rewrite H1; apply Sum_empty.
  auto with arith.
 simpl in Hmn; elim (le_lt_eq_dec _ _ Hmn); intro H0.
  apply eq_transitive_unfolded with (f (S (S n)) [-]f (S n) [+] (f (S n) [-]f m)).
   eapply eq_transitive_unfolded.
    apply Sum_last.
   eapply eq_transitive_unfolded.
    apply cag_commutes_unfolded.
   apply bin_op_wd_unfolded; [ apply H | apply Hrecn ].
   auto with arith.
  astepr (f (S (S n)) [+][0][-]f m).
  astepr (f (S (S n)) [+] ([--] (f (S n)) [+]f (S n)) [-]f m).
  Step_final (f (S (S n)) [+] [--] (f (S n)) [+]f (S n) [-]f m).
 rewrite H0.
 astepr ([0]:G).
 cut (S n = pred (S (S n))); [ intro H2 | auto ].
 rewrite H2; apply Sum_empty.
 auto with arith.
Qed.

Lemma str_Mengolli_Sum_gen : forall (f g : nat -> G) m n, m <= S n ->
 (forall i, m <= i -> i <= n -> g i [=] f (S i) [-]f i) -> Sum m n g [=] f (S n) [-]f m.
Proof.
 intros f g m n H H0.
 apply eq_transitive_unfolded with (Sum m n (fun i : nat => f (S i) [-]f i)).
  apply Sum_wd'; assumption.
 apply Mengolli_Sum_gen; [ intro; algebra | assumption ].
Qed.

Lemma Sumx_to_Sum : forall n, 0 < n -> forall f, nat_less_n_fun f ->
 Sumx f [=] Sum 0 (pred n) (part_tot_nat_fun G n f).
Proof.
 intro n; induction  n as [| n Hrecn]; intros H f Hf.
  elimtype False; inversion H.
 cut (0 <= n); [ intro H0 | auto with arith ].
 elim (le_lt_eq_dec _ _ H0); clear H H0; intro H.
  simpl in |- *.
  pattern n at 6 in |- *; rewrite -> (S_pred _ _ H).
  eapply eq_transitive_unfolded.
   2: apply eq_symmetric_unfolded; apply Sum_last.
  apply bin_op_wd_unfolded.
   eapply eq_transitive_unfolded.
    apply Hrecn; auto.
    red in |- *; intros; apply Hf; auto.
   apply Sum_wd'.
    auto with arith.
   intros i H1 H2.
   cut (i < n); [ intro | omega ].
   eapply eq_transitive_unfolded.
    apply part_tot_nat_fun_ch1 with (Hi := H0).
    red in |- *; intros; apply Hf; auto.
   apply eq_symmetric_unfolded.
   eapply eq_transitive_unfolded.
    apply part_tot_nat_fun_ch1 with (Hi := lt_S _ _ H0).
    red in |- *; intros; apply Hf; auto.
   algebra.
  rewrite <- (S_pred _ _ H).
  apply eq_symmetric_unfolded; apply part_tot_nat_fun_ch1; auto.
 generalize f Hf; clear Hf f; rewrite <- H.
 simpl in |- *; intros f Hf.
 eapply eq_transitive_unfolded.
  2: apply eq_symmetric_unfolded; apply Sum_one.
 astepl (f 0 (lt_n_Sn 0)).
 apply eq_symmetric_unfolded; apply part_tot_nat_fun_ch1; auto.
Qed.

End More_Sums.

Hint Resolve Sum_one Sum_Sum Sum_first Sum_last Sum_last' Sum_wd
  Sum_plus_Sum: algebra.
Hint Resolve Sum_minus_Sum inv_Sum inv_Sum0: algebra.
