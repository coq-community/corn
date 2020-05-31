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

(** printing sqrt_Half %\ensuremath{\sqrt{\frac12}}% *)
(** printing sqrt_I %\ensuremath{\sqrt{\imath}}% *)
(** printing nroot_I %\ensuremath{\sqrt[n]{\imath}}% *)
(** printing nroot_minus_I %\ensuremath{\sqrt[n]{-\imath}}% *)

Require Export CoRN.complex.CComplex.
Require Export Coq.Arith.Wf_nat.
Require Export Coq.setoid_ring.ArithRing.
Import CRing_Homomorphisms.coercions.

(**
* Roots of Complex Numbers

Properties of non-zero complex numbers
*)

Section CC_ap_zero.

Lemma cc_ap_zero : forall P : CC -> Prop,
 (forall a b, a [#] [0] -> P (a[+I*]b)) -> (forall a b, b [#] [0] -> P (a[+I*]b)) -> forall c, c [#] [0] -> P c.
Proof.
 intros ????.
 elim c. intros a b H1.
 elim H1; intros H2; auto.
Qed.

Lemma C_cc_ap_zero : forall P : CC -> CProp,
 (forall a b, a [#] [0] -> P (a[+I*]b)) -> (forall a b, b [#] [0] -> P (a[+I*]b)) -> forall c, c [#] [0] -> P c.
Proof.
 intro. intros H H0 c.
 elim c. intros a b. intro H1.
 elim H1; intros H2;auto.
Qed.

End CC_ap_zero.

(** Weird lemma. *)

Section Imag_to_Real.

Lemma imag_to_real : forall a b a' b', a'[+I*]b' [=] (a[+I*]b) [*]II -> a [#] [0] -> b' [#] [0].
Proof.
 intros ????? H0.
 cut (b' [=] a); intros.
  (* astepl a. *)
  now apply ap_wdl with a.
  apply eq_transitive with (Im (a'[+I*]b')).
  apply eq_reflexive.
 (* astepl (Im a[+I*]b[*]II). *)
 apply eq_transitive with (Im ((a[+I*]b) [*]II)).
  now apply Im_wd. 
  (* Step_final (Im ( [--]b) [+I*]a). *)
  apply eq_transitive with (Im ( [--]b[+I*]a)).
  apply Im_wd. apply mult_I.
  apply eq_reflexive.
Qed.

End Imag_to_Real.

(**
** Roots of the imaginary unit *)

Section NRootI.

Definition sqrt_Half := sqrt Half (less_leEq _ _ _ (pos_half IR)).
Definition sqrt_I := sqrt_Half[+I*]sqrt_Half.

Lemma sqrt_I_nexp : sqrt_I[^]2 [=] II.
Proof.
 (* astepl sqrt_I[*]sqrt_I. *)
 apply eq_transitive with (sqrt_I[*]sqrt_I).
  apply nexp_two.
 unfold sqrt_I in |- *.
 (* astepl (sqrt_Half[*]sqrt_Half[-]sqrt_Half[*]sqrt_Half) [+I*]
   (sqrt_Half[*]sqrt_Half[+]sqrt_Half[*]sqrt_Half). *)
 apply eq_transitive with ((sqrt_Half[*]sqrt_Half[-]sqrt_Half[*]sqrt_Half) [+I*]
   (sqrt_Half[*]sqrt_Half[+]sqrt_Half[*]sqrt_Half)).
  apply eq_reflexive_unfolded.
 cut (sqrt_Half[*]sqrt_Half [=] Half); intros.
  (* astepl [0][+I*] (Half[+]Half). *)
  apply eq_transitive with ([0][+I*] (Half[+]Half)).
   apply I_wd. apply cg_minus_correct. apply bin_op_wd_unfolded. exact H.
    exact H.
  (* Step_final [0][+I*][1]. *)
  apply eq_transitive with ([0][+I*][1]).
   apply I_wd. apply eq_reflexive. apply half_2.
    apply eq_reflexive.
 (* astepl sqrt_Half[^] (2). *)
 apply eq_transitive with (sqrt_Half[^]2).
  apply eq_symmetric. apply nexp_two.
 apply sqrt_sqr.
Qed.

Lemma nroot_I_nexp_aux : forall n, odd n -> {m : nat | n * n = 4 * m + 1}.
Proof.
 intros n on.
 elim (odd_S2n n); try assumption.
 intros n' H.
 rewrite H.
 exists (n' * n' + n').
 unfold double in |- *.
 ring.
Qed.

Definition nroot_I (n : nat) (n_ : odd n) : CC := II[^]n.

Lemma nroot_I_nexp : forall n n_, nroot_I n n_[^]n [=] II.
Proof.
 intros n on.
 unfold nroot_I in |- *.
 (* astepl II[^] (mult n n). *)
 apply eq_transitive with (II[^] (n * n)).
  apply nexp_mult.
 elim (nroot_I_nexp_aux n); try assumption.
 intros m H.
 rewrite H.
 (* astepl II[^] (mult (4) m) [*]II[^] (1). *)
 apply eq_transitive with (II[^] (4 * m) [*]II[^]1).
  apply eq_symmetric. apply nexp_plus.
  (* astepl (II[^] (4)) [^]m[*]II. *)
  apply eq_transitive with ((II[^]4) [^]m[*]II).
  apply bin_op_wd_unfolded. apply eq_symmetric. apply nexp_mult.
   apply nexp_one.
 cut (II[^]4 [=] [1]); intros.
  (* astepl [1][^]m[*]II. *)
  apply eq_transitive_unfolded with ([1][^]m[*]II).
   apply bin_op_wd_unfolded. apply un_op_wd_unfolded. exact H0.
    apply eq_reflexive_unfolded.
  (* Step_final [1][*]II. *)
  apply eq_transitive_unfolded with ([1][*]II).
   apply bin_op_wd_unfolded. apply one_nexp. apply eq_reflexive_unfolded.
    apply one_mult.
 replace 4 with (2 * 2).
  (* astepl (II[^] (2)) [^] (2). *)
  apply eq_transitive_unfolded with ((II[^]2) [^]2).
   apply eq_symmetric_unfolded. apply nexp_mult.
   (* astepl ( [--] ([1]::CC)) [^] (2). *)
   apply eq_transitive_unfolded with ( [--] ([1]:CC) [^]2).
   apply un_op_wd_unfolded. exact I_square'.
   (* Step_final ([1]::CC) [^] (2). *)
   apply eq_transitive_unfolded with (([1]:CC) [^]2).
   apply inv_nexp_two.
  apply one_nexp.
 auto with arith.
Qed.
Hint Resolve nroot_I_nexp: algebra.

Definition nroot_minus_I (n : nat) (n_ : odd n) : CC := [--] (nroot_I n n_).

Lemma nroot_minus_I_nexp : forall n n_, nroot_minus_I n n_[^]n [=] [--]II.
Proof.
 intros n on.
 unfold nroot_minus_I in |- *.
 (* Step_final [--] ((nroot_I n on) [^]n). *)
 apply eq_transitive_unfolded with ( [--] (nroot_I n on[^]n)).
  apply inv_nexp_odd. exact on.
  apply un_op_wd_unfolded. apply nroot_I_nexp.
Qed.

End NRootI.

(**
** Roots of complex numbers *)

Section NRootCC_1.

(** We define the nth root of a complex number with a non zero imaginary part.
*)

Section NRootCC_1_ap_real.

(**
%\begin{convention}% Let [a,b : IR] and [b_ : (b [#] [0])].
Define [c2 := a[^]2[+]b[^]2], [c := sqrt c2], [a'2 := (c[+]a) [*]Half],
[a' := sqrt a'2], [b'2 := (c[-]a) [*]Half] and [b' := sqrt b'2].
%\end{convention}%
*)
Variables a b : IR.
Hypothesis b_ : b [#] [0].

(* begin hide *)
Let c2 := a[^]2[+]b[^]2.
(* end hide *)

Lemma nrCC1_c2pos : [0] [<] c2.
Proof.
 unfold c2 in |- *.
 apply plus_resp_nonneg_pos.
  apply sqr_nonneg.
 apply pos_square.
 assumption.
Qed.

(* begin hide *)
Let c := sqrt c2 (less_leEq _ _ _ nrCC1_c2pos).
Let a'2 := (c[+]a) [*]Half.
(* end hide *)

Lemma nrCC1_a'2pos : [0] [<] a'2.
Proof.
 unfold a'2 in |- *.
 apply (mult_resp_pos IR).
  rstepr (c[-][--]a).
  apply shift_zero_less_minus.
  unfold c in |- *.
  apply sqrt_less'.
  unfold c2 in |- *.
  apply (Ccsr_wdl _ (cof_less (c:=IR)) (a[^]2[+][0]) (a[^]2[+]b[^]2)).
   apply plus_resp_less_lft.
   change ([0] [<] b[^]2) in |- *.
   apply pos_square. assumption.
   (* algebra. *)
   apply cm_rht_unit_unfolded.
 apply pos_half.
Qed.

(* begin hide *)
Let a' := sqrt a'2 (less_leEq _ _ _ nrCC1_a'2pos).
Let b'2 := (c[-]a) [*]Half.
(* end hide *)

Lemma nrCC1_b'2pos : [0] [<] b'2.
Proof.
 unfold b'2 in |- *.
 apply (mult_resp_pos IR).
  change ([0] [<] c[-]a) in |- *.
  apply shift_zero_less_minus.
  unfold c in |- *.
  apply sqrt_less.
  unfold c2 in |- *.
  rstepl (a[^]2[+][0]).
  apply plus_resp_less_lft.
  change ([0] [<] b[^]2) in |- *.
  apply pos_square. assumption.
  apply pos_half.
Qed.

(* begin hide *)
Let b' := sqrt b'2 (less_leEq _ _ _ nrCC1_b'2pos).
(* end hide *)

Lemma nrCC1_a3 : a'[^]2[-]b'[^]2 [=] a.
Proof.
 unfold a', b' in |- *.
 (* astepl a'2[-]b'2. *)
 apply eq_transitive_unfolded with (a'2[-]b'2).
  apply cg_minus_wd. apply sqrt_sqr. apply sqrt_sqr.
   unfold a'2, b'2 in |- *.
 unfold Half in |- *.
 rational.
Qed.

Lemma nrCC1_a4 : (c[+]a) [*] (c[-]a) [=] b[^]2.
Proof.
 (* astepl c[^] (2) [-]a[^] (2). *)
 apply eq_transitive_unfolded with (c[^]2[-]a[^]2).
  apply nexp_funny.
 unfold c in |- *.
 (* astepl c2[-]a[^] (2). *)
 apply eq_transitive_unfolded with (c2[-]a[^]2).
  apply cg_minus_wd. apply sqrt_sqr. apply eq_reflexive_unfolded.
   unfold c2 in |- *.
 (* astepl (a[^] (2) [+]b[^] (2)) [+][--] (a[^] (2)). *)
 apply eq_transitive_unfolded with (a[^]2[+]b[^]2[+][--] (a[^]2)).
  apply eq_reflexive_unfolded.
 (* astepl (b[^] (2) [+]a[^] (2)) [+][--] (a[^] (2)). *)
 apply eq_transitive_unfolded with (b[^]2[+]a[^]2[+][--] (a[^]2)).
  apply bin_op_wd_unfolded. apply cag_commutes_unfolded.
   apply eq_reflexive_unfolded.
 (* astepl b[^] (2) [+] (a[^] (2) [+][--] (a[^] (2))). *)
 apply eq_transitive_unfolded with (b[^]2[+] (a[^]2[+][--] (a[^]2))).
  apply eq_symmetric_unfolded. apply plus_assoc_unfolded.
  (* Step_final b[^] (2) [+][0]. *)
  apply eq_transitive_unfolded with (b[^]2[+][0]).
  apply bin_op_wd_unfolded. apply eq_reflexive_unfolded.
   apply cg_rht_inv_unfolded.
 apply cm_rht_unit_unfolded.
Qed.
Hint Resolve nrCC1_a4: algebra.

Lemma nrCC1_a5 : a'2[*]b'2 [=] (b[*]Half) [^]2.
Proof.
 unfold a'2, b'2 in |- *.
 (* astepl (c[+]a) [*] (Half[*] ((c[-]a) [*]Half)). *)
 apply eq_transitive_unfolded with ((c[+]a) [*] (Half[*] ((c[-]a) [*]Half))).
  apply eq_symmetric_unfolded. apply mult_assoc_unfolded.
  (* astepl (c[+]a) [*] (((c[-]a) [*]Half) [*]Half). *)
  apply eq_transitive_unfolded with ((c[+]a) [*] ((c[-]a) [*]Half[*]Half)).
  apply bin_op_wd_unfolded. apply eq_reflexive_unfolded. apply mult_commutes.
   (* astepl (c[+]a) [*] ((c[-]a) [*] (Half[*]Half)). *)
   apply eq_transitive_unfolded with ((c[+]a) [*] ((c[-]a) [*] (Half[*]Half))).
  apply bin_op_wd_unfolded. apply eq_reflexive_unfolded.
   apply eq_symmetric_unfolded. apply mult_assoc_unfolded.
  (* astepl ((c[+]a) [*] (c[-]a)) [*] (Half[*]Half). *)
  apply eq_transitive_unfolded with ((c[+]a) [*] (c[-]a) [*] (Half[*]Half)).
  apply mult_assoc_unfolded.
 (* astepl b[^] (2) [*] (Half[*]Half). *)
 apply eq_transitive_unfolded with (b[^]2[*] (Half[*]Half)).
  apply bin_op_wd_unfolded. exact nrCC1_a4. apply eq_reflexive_unfolded.
   (* astepl (b[*]b) [*] (Half[*]Half). *)
   apply eq_transitive_unfolded with (b[*]b[*] (Half[*]Half)).
  apply bin_op_wd_unfolded. apply nexp_two. apply eq_reflexive_unfolded.
   (* astepl ((b[*]b) [*]Half) [*]Half. *)
   apply eq_transitive_unfolded with (b[*]b[*]Half[*]Half).
  apply mult_assoc_unfolded.
 (* astepl (b[*] (b[*]Half)) [*]Half. *)
 apply eq_transitive_unfolded with (b[*] (b[*]Half) [*]Half).
  apply bin_op_wd_unfolded. apply eq_symmetric_unfolded.
   apply mult_assoc_unfolded. apply eq_reflexive_unfolded.
  (* astepl ((b[*]Half) [*]b) [*]Half. *)
  apply eq_transitive_unfolded with (b[*]Half[*]b[*]Half).
  apply bin_op_wd_unfolded. apply mult_commutes. apply eq_reflexive_unfolded.
   (* Step_final (b[*]Half) [*] (b[*]Half). *)
   apply eq_transitive_unfolded with (b[*]Half[*] (b[*]Half)).
  apply eq_symmetric_unfolded. apply mult_assoc_unfolded.
  apply eq_symmetric_unfolded. apply nexp_two.
Qed.

Lemma nrCC1_a6 : [0] [<] a'2[*]b'2.
Proof.
 apply (mult_resp_pos IR).
  apply nrCC1_a'2pos.
 apply nrCC1_b'2pos.
Qed.

Lemma nrCC1_a6' : [0] [<] (b[*]Half) [^]2.
Proof.
 apply pos_square.
 (* astepr [0][*]Half. *)
 apply ap_wdr_unfolded with (ZeroR[*]Half).
  2: apply cring_mult_zero_op.
 apply mult_rht_resp_ap; try assumption.
 apply pos_ap_zero.
 apply pos_half.
Qed.
Hint Resolve nrCC1_a5: algebra.

Lemma nrCC1_a7_upper : [0] [<] b -> a'[*]b' [=] b[*]Half.
Proof.
 intros.
 unfold a', b' in |- *.
 (* astepl (sqrt a'2[*]b'2 (less_leEq ? ? ? nrCC1_a6)). *)
 apply eq_transitive_unfolded with (sqrt (a'2[*]b'2) (less_leEq _ _ _ nrCC1_a6)).
  apply eq_symmetric_unfolded. apply NRootIR.sqrt_mult.
  (* astepl (sqrt (b[*]Half) [^] (2) nrCC1_a6'). *)
  apply eq_transitive_unfolded with (sqrt ((b[*]Half) [^]2) (less_leEq _ _ _ nrCC1_a6')).
  apply sqrt_wd. exact nrCC1_a5.
  apply sqrt_to_nonneg.
 apply less_leEq.
 rstepl (ZeroR[*]Half).
 apply mult_resp_less. assumption.
  apply pos_half.
Qed.

Lemma nrCC1_a7_lower : b [<] [0] -> a'[*][--]b' [=] b[*]Half.
Proof.
 intros.
 (* astepl [--] (a'[*]b'). *)
 apply eq_transitive_unfolded with ( [--] (a'[*]b')).
  apply cring_inv_mult_lft.
 cut (a'[*]b' [=] [--] (b[*]Half)); intros. rename H into H0. rename X into H.
  (* Step_final [--][--] (b[*]Half). *)
  apply eq_transitive_unfolded with ( [--][--] (b[*]Half)).
   apply un_op_wd_unfolded. exact H0.
   apply cg_inv_inv.
 unfold a', b' in |- *.
 (* astepl (sqrt a'2[*]b'2 (less_leEq ? ? ? nrCC1_a6)). *)
 apply eq_transitive_unfolded with (sqrt (a'2[*]b'2) (less_leEq _ _ _ nrCC1_a6)).
  apply eq_symmetric_unfolded. apply NRootIR.sqrt_mult.
  (* astepl (sqrt (b[*]Half) [^] (2) (less_leEq ? ? ? nrCC1_a6')). *)
  apply eq_transitive_unfolded with (sqrt ((b[*]Half) [^]2) (less_leEq _ _ _ nrCC1_a6')).
  apply sqrt_wd. exact nrCC1_a5.
  apply sqrt_to_nonpos.
 apply less_leEq.
 rstepr (ZeroR[*]Half).
 apply mult_resp_less. assumption.
  apply pos_half.
Qed.
Hint Resolve nrCC1_a3 nrCC1_a7_upper nrCC1_a7_lower: algebra.

Lemma nrootCC_1_upper : [0] [<] b -> (a'[+I*]b') [^]2 [=] a[+I*]b.
Proof.
 intros.
 (* astepl (a'[^] (2) [-]b'[^] (2)) [+I*] ((a'[*]b') [*]Two). *)
 apply eq_transitive_unfolded with ((a'[^]2[-]b'[^]2) [+I*]a'[*]b'[*]Two).
  apply cc_calculate_square.
 cut (a'[*]b'[*]Two [=] b); intros.
  (* Step_final a[+I*]b. *)
  apply eq_transitive_unfolded with (a[+I*]b).
   apply I_wd. exact nrCC1_a3. rename H into H0. exact H0.
    apply eq_reflexive_unfolded.
 (* astepl (b[*]Half) [*]Two. *)
 apply eq_transitive_unfolded with (b[*]Half[*]Two).
  apply bin_op_wd_unfolded. apply nrCC1_a7_upper. rename X into H. exact H.
   apply eq_reflexive_unfolded.
 (* algebra. *)
 apply half_1'.
Qed.

Lemma nrootCC_1_lower : b [<] [0] -> (a'[+I*][--]b') [^]2 [=] a[+I*]b.
Proof.
 intros.
 cut (a'[^]2[-][--]b'[^]2 [=] a); intros.
  cut (a'[*][--]b'[*]Two [=] b); intros.
   (* Step_final (a'[^] (2) [-] ( [--]b') [^] (2)) [+I*] ((a'[*][--]b') [*]Two). *)
   apply eq_transitive_unfolded with ((a'[^]2[-][--]b'[^]2) [+I*]a'[*][--]b'[*]Two).
    apply cc_calculate_square.
   apply I_wd. rename H0 into H1. rename H into H0. rename X into H. exact H0.
    rename H0 into H1. rename H into H0. rename X into H.  exact H1.
   (* astepl (b[*]Half) [*]Two. *)
   apply eq_transitive_unfolded with (b[*]Half[*]Two).
   apply bin_op_wd_unfolded. apply nrCC1_a7_lower.
    rename H into H0. rename X into H.  exact H.
    apply eq_reflexive_unfolded.
  (* algebra. *)
  apply half_1'.
 (* Step_final a'[^] (2) [-]b'[^] (2). *)
 apply eq_transitive_unfolded with (a'[^]2[-]b'[^]2).
  apply cg_minus_wd. apply eq_reflexive_unfolded. apply inv_nexp_two.
   exact nrCC1_a3.
Qed.

Lemma nrootCC_1_ap_real : {z : CC | z[^]2 [=] a[+I*]b}.
Proof.
 elim (ap_imp_less _ b [0]).
   intro H.
   exists (a'[+I*][--]b'). apply nrootCC_1_lower. assumption.
   intro H.
  exists (a'[+I*]b'). apply nrootCC_1_upper. assumption.
  assumption.
Qed.

End NRootCC_1_ap_real.

(** We now define the nth root of a complex number with a non zero real part.
*)

Section NRootCC_1_ap_imag.

(**
%\begin{convention}% Let [a,b : IR] and [a_ : (a [#] [0])] and define
[c' := (a[+I*]b) [*][--]II := a'[+I*]b'].
%\end{convention}%
*)
Variables a b : IR.
Hypothesis a_ : a [#] [0].

(* begin hide *)
Let c' := (a[+I*]b) [*][--]II.
Let a' := Re c'.
Let b' := Im c'.
(* end hide *)

Lemma nrootCC_1_ap_imag : {z : CC | z[^]2 [=] a[+I*]b}.
Proof.
 elim (nrootCC_1_ap_real a' b').
  intros x H.
  exists (x[*]sqrt_I).
  (* astepl x[^] (2) [*]sqrt_I[^] (2). *)
  apply eq_transitive_unfolded with (x[^]2[*]sqrt_I[^]2).
   apply mult_nexp.
  Hint Resolve sqrt_I_nexp: algebra.
  (* astepl (a'[+I*]b') [*]II. *)
  apply eq_transitive_unfolded with ((a'[+I*]b') [*]II).
   apply bin_op_wd_unfolded. exact H. exact sqrt_I_nexp.
    (* astepl ((a[+I*]b) [*][--]II) [*]II. *)
    apply eq_transitive_unfolded with ((a[+I*]b) [*][--]II[*]II).
   apply eq_reflexive_unfolded.
  (* astepl (a[+I*]b) [*] ( [--]II[*]II). *)
  apply eq_transitive_unfolded with ((a[+I*]b) [*] ( [--]II[*]II)).
   apply eq_symmetric_unfolded. apply mult_assoc_unfolded.
   (* Step_final (a[+I*]b) [*][1]. *)
   apply eq_transitive_unfolded with ((a[+I*]b) [*][1]).
   apply bin_op_wd_unfolded. apply eq_reflexive_unfolded. exact I_recip_lft.
    apply mult_one.
 cut (b[+I*][--]a [=] c'); intros.
  (* astepl (Im c'). *)
  apply ap_wdl_unfolded with (Im c').
   2: apply eq_reflexive_unfolded.
  (* astepl (Im b[+I*][--]a). *)
  apply ap_wdl_unfolded with (Im (b[+I*][--]a)).
   2: apply Im_wd. 2: exact H.
   (* astepl [--]a. *)
   apply ap_wdl_unfolded with ( [--]a).
   apply zero_minus_apart. apply minus_ap_zero. apply inv_resp_ap_zero.
   exact a_.
  apply eq_reflexive_unfolded.
 (* astepl ( [--][--]b) [+I*][--]a. *)
 apply eq_transitive_unfolded with ( [--][--]b[+I*][--]a).
  apply I_wd. apply eq_symmetric_unfolded. apply cg_inv_inv.
   apply eq_reflexive_unfolded.
 (* astepl [--] (( [--]b) [+I*]a). *)
 apply eq_transitive_unfolded with ( [--] ( [--]b[+I*]a)).
  apply eq_reflexive_unfolded.
 (* astepl [--] ((a[+I*]b) [*]II). *)
 apply eq_transitive_unfolded with ( [--] ((a[+I*]b) [*]II)).
  apply un_op_wd_unfolded. apply eq_symmetric_unfolded. apply mult_I.
  (* Step_final (a[+I*]b) [*][--]II. *)
  apply eq_transitive_unfolded with ((a[+I*]b) [*][--]II).
  apply eq_symmetric_unfolded. apply cring_inv_mult_lft.
  apply eq_reflexive_unfolded.
Qed.

End NRootCC_1_ap_imag.

(** We now define the roots of arbitrary non zero complex numbers. *)

Lemma nrootCC_1 : forall c : CC, c [#] [0] -> {z : CC | z[^]2 [=] c}.
Proof.
 intros.
 pattern c in |- *.
 apply C_cc_ap_zero; try assumption; intros.
  apply nrootCC_1_ap_imag. assumption.
  apply nrootCC_1_ap_real. assumption.
Qed.

End NRootCC_1.

Section NRootCC_2.

(**
%\begin{convention}% Let [n : nat] and [c,z : CC] and [c_:(c [#] [0])].
%\end{convention}%
*)
Variable n : nat.
Variables c z : CC.
Hypothesis c_ : c [#] [0].

Lemma nrootCC_2' : (z[*]CC_conj z) [^]n [=] c[*]CC_conj c ->
 z[^]n[*]CC_conj c[-]CC_conj z[^]n[*]c [=] [0] -> (z[^]n) [^]2 [=] c[^]2.
Proof.
 intros.
 cut (z[^]n[*]CC_conj c [=] CC_conj z[^]n[*]c); intros.
  apply (mult_cancel_rht _ ((z[^]n) [^]2) (c[^]2) (CC_conj c)).
   apply CC_conj_strext.
   (* astepl c. *)
   apply ap_wdl_unfolded with c.
    2: apply eq_symmetric_unfolded. 2: apply CC_conj_conj.
    (* astepr ([0]::CC). *)
    apply ap_wdr_unfolded with ([0]:CC).
    exact c_.
   apply eq_symmetric_unfolded. exact CC_conj_zero.
   (* astepl (z[^]n[*]z[^]n) [*] (CC_conj c). *)
   apply eq_transitive_unfolded with (z[^]n[*]z[^]n[*]CC_conj c).
   apply bin_op_wd_unfolded. apply nexp_two. apply eq_reflexive_unfolded.
    (* astepl z[^]n[*] (z[^]n[*] (CC_conj c)). *)
    apply eq_transitive_unfolded with (z[^]n[*] (z[^]n[*]CC_conj c)).
   apply eq_symmetric_unfolded. apply mult_assoc_unfolded.
   (* astepl z[^]n[*] ((CC_conj z) [^]n[*]c). *)
   apply eq_transitive_unfolded with (z[^]n[*] (CC_conj z[^]n[*]c)).
   apply bin_op_wd_unfolded. apply eq_reflexive_unfolded. exact H1.
    (* astepl (z[^]n[*] (CC_conj z) [^]n) [*]c. *)
    apply eq_transitive_unfolded with (z[^]n[*]CC_conj z[^]n[*]c).
   apply mult_assoc_unfolded.
  (* astepl ((z[*] (CC_conj z)) [^]n) [*]c. *)
  apply eq_transitive_unfolded with ((z[*]CC_conj z) [^]n[*]c).
   apply bin_op_wd_unfolded. apply eq_symmetric_unfolded. apply mult_nexp.
    apply eq_reflexive_unfolded.
  (* astepl (c[*] (CC_conj c)) [*]c. *)
  apply eq_transitive_unfolded with (c[*]CC_conj c[*]c).
   apply bin_op_wd_unfolded. exact H. apply eq_reflexive_unfolded.
    (* astepl c[*] (c[*] (CC_conj c)). *)
    apply eq_transitive_unfolded with (c[*] (c[*]CC_conj c)).
   apply mult_commutes.
  (* Step_final (c[*]c) [*] (CC_conj c). *)
  apply eq_transitive_unfolded with (c[*]c[*]CC_conj c).
   apply mult_assoc_unfolded.
  apply bin_op_wd_unfolded. apply eq_symmetric_unfolded. apply nexp_two.
   apply eq_reflexive_unfolded.
 cut (forall (G : CGroup) (x y : G), x[-]y [=] [0] -> x [=] y); intros.
  apply H1. assumption.
  (* astepl x[+][0]. *)
  apply eq_transitive_unfolded with (x[+][0]).
  apply eq_symmetric_unfolded. apply cm_rht_unit_unfolded.
  (* astepl x[+] ( [--]y[+]y). *)
  apply eq_transitive_unfolded with (x[+] ( [--]y[+]y)).
  apply bin_op_wd_unfolded. apply eq_reflexive_unfolded.
   apply eq_symmetric_unfolded. apply cg_lft_inv_unfolded.
  (* astepl (x[+][--]y) [+]y. *)
  apply eq_transitive_unfolded with (x[+][--]y[+]y).
  apply plus_assoc_unfolded.
 (* Step_final [0][+]y. *)
 apply eq_transitive_unfolded with ([0][+]y).
  apply bin_op_wd_unfolded. exact H1. apply eq_reflexive_unfolded.
   apply cm_lft_unit_unfolded.
Qed.

Lemma nrootCC_2 : (z[*]CC_conj z) [^]n [=] c[*]CC_conj c ->
 z[^]n[*]CC_conj c[-]CC_conj z[^]n[*]c [=] [0] -> z[^]n [=] c or z[^]n [=] [--]c.
Proof.
 intros.
 apply cond_square_eq; try assumption.
  exact TwoCC_ap_zero.
 apply nrootCC_2'; assumption.
Qed.

End NRootCC_2.

Section NRootCC_3.

Fixpoint Im_poly (p : cpoly CC) : cpoly IR :=
  match p with
  | cpoly_zero _       => cpoly_zero IR
  | cpoly_linear _ c p1 => cpoly_linear IR (Im c) (Im_poly p1)
  end.

Lemma nrCC3_a1 : forall p r, (Im_poly p) ! r [=] Im p ! (cc_IR r).
Proof.
 intros.
 elim p; intros.
  unfold Im_poly in |- *.
  (* astepl ([0]::IR). *)
  apply eq_transitive_unfolded with ZeroR.
   apply eq_reflexive_unfolded.
  (* Step_final (Im ([0]::CC)). *)
  apply eq_transitive_unfolded with (Im ([0]:CC)); apply eq_reflexive_unfolded.
 (* astepl (cpoly_linear ? (Im s) (Im_poly c))!r. *)
 apply eq_transitive_unfolded with (cpoly_linear _ (Im s) (Im_poly c)) ! r.
  apply eq_reflexive_unfolded.
 (* astepl (Im s) [+]r[*] ((Im_poly c)!r). *)
 apply eq_transitive_unfolded with (Im s[+]r[*] (Im_poly c) ! r).
  apply eq_reflexive_unfolded.
 (* astepl (Im s) [+]r[*] (Im (c!(cc_IR r))). *)
 apply eq_transitive_unfolded with (Im s[+]r[*]Im c ! (cc_IR r)).
  apply bin_op_wd_unfolded. apply eq_reflexive_unfolded. apply bin_op_wd_unfolded.
   apply eq_reflexive_unfolded. exact H.
  cut (forall (r : IR) (c : CC), r[*]Im c [=] Im (cc_IR r[*]c)); intros.
  (* astepl (Im s) [+] (Im (cc_IR r) [*] (c!(cc_IR r))). *)
  apply eq_transitive_unfolded with (Im s[+]Im (cc_IR r[*]c ! (cc_IR r))).
   apply bin_op_wd_unfolded. apply eq_reflexive_unfolded. apply H0.
    (* Step_final (Im s[+] (cc_IR r) [*] (c!(cc_IR r))). *)
    apply eq_transitive_unfolded with (Im (s[+]cc_IR r[*]c ! (cc_IR r))).
   apply eq_reflexive_unfolded.
  apply eq_reflexive_unfolded.
 (* astepl r0[*] (Im c0) [+][0]. *)
 apply eq_transitive_unfolded with (r0[*]Im c0[+][0]).
  apply eq_symmetric_unfolded. apply cm_rht_unit_unfolded.
  (* astepl r0[*] (Im c0) [+][0][*] (Re c0). *)
  apply eq_transitive_unfolded with (r0[*]Im c0[+][0][*]Re c0).
  apply bin_op_wd_unfolded. apply eq_reflexive_unfolded.
   apply eq_symmetric_unfolded. apply cring_mult_zero_op.
  (* astepl (Im (r0[+I*][0]) [*] ((Re c0) [+I*] (Im c0))). *)
  apply eq_transitive_unfolded with (Im ((r0[+I*][0]) [*] (Re c0[+I*]Im c0))).
  apply eq_reflexive_unfolded.
 (* Step_final (Im (cc_IR r0) [*] ((Re c0) [+I*] (Im c0))). *)
 apply eq_transitive_unfolded with (Im (cc_IR r0[*] (Re c0[+I*]Im c0))).
  apply eq_reflexive_unfolded.
 apply eq_reflexive_unfolded.
Qed.

Lemma nrCC3_a2 : forall p n, nth_coeff n (Im_poly p) [=] Im (nth_coeff n p).
Proof.
 intro.
 elim p; intros.
  unfold Im_poly in |- *.
  (* astepl ([0]::IR). *)
  apply eq_transitive_unfolded with ZeroR.
   apply eq_reflexive_unfolded.
  (* Step_final (Im ([0]::CC)). *)
  apply eq_transitive_unfolded with (Im ([0]:CC)).
   apply eq_reflexive_unfolded.
  apply eq_reflexive_unfolded.
 elim n; intros.
  (* Step_final (Im s). *)
  apply eq_transitive_unfolded with (Im s).
   apply eq_reflexive_unfolded.
  apply eq_reflexive_unfolded.
 (* astepl (nth_coeff ? n0 (Im_poly c)). *)
 apply eq_transitive_unfolded with (nth_coeff n0 (Im_poly c)).
  apply eq_reflexive_unfolded.
 (* Step_final (Im (nth_coeff CC n0 c)). *)
 apply eq_transitive_unfolded with (Im (nth_coeff (R:=CC) n0 c)).
  apply H.
 apply eq_reflexive_unfolded.
Qed.

(**
%\begin{convention}% Let [a,b : IR], [b_ : (b [#] [0])] and [n : nat].
%\end{convention}%
*)

Variables a b : IR.
Hypothesis b_ : b [#] [0].
Variable n : nat.

Definition nrCC3_poly'' := (_X_[+]_C_ II) [^]n.

Lemma nrCC3_a3 : forall r : IR, nrCC3_poly'' ! (cc_IR r) [=] (r[+I*][1]) [^]n.
Proof.
 intros.
 unfold nrCC3_poly'' in |- *.
 (* astepl ((_X_[+] (_C_ II))!(cc_IR r)) [^]n. *)
 apply eq_transitive_unfolded with ((_X_[+]_C_ II) ! (cc_IR r) [^]n).
  apply nexp_apply.
 (* astepl ((_X_!(cc_IR r)) [+] ((_C_) II)!(cc_IR r)) [^]n. *)
 apply eq_transitive_unfolded with ((_X_ ! (cc_IR r) [+] (_C_ II) ! (cc_IR r)) [^]n).
  apply un_op_wd_unfolded. apply plus_apply.
  cut (forall c x : CC, _X_ ! x[+] (_C_ c) ! x [=] x[+]c); intros.
  (* astepl ((cc_IR r) [+]II) [^]n. *)
  apply eq_transitive_unfolded with ((cc_IR r[+]II) [^]n).
   apply un_op_wd_unfolded. apply H.
   (* astepl ((r[+I*][0]) [+] ([0][+I*][1])) [^]n. *)
   apply eq_transitive_unfolded with ((r[+I*][0][+][0][+I*][1]) [^]n).
   apply eq_reflexive_unfolded.
  (* Step_final ((r[+][0]) [+I*] ([0][+][1])) [^]n. *)
  apply eq_transitive_unfolded with (((r[+][0]) [+I*] ([0][+][1])) [^]n).
   apply eq_reflexive_unfolded.
  apply un_op_wd_unfolded. apply I_wd. apply cm_rht_unit_unfolded.
  apply cm_lft_unit_unfolded.
 (* algebra. *)
 apply bin_op_wd_unfolded. apply x_apply. apply c_apply.
Qed.

Lemma nrCC3_a4 : degree_le 1 (_X_[+]_C_ II).
Proof.
 apply degree_imp_degree_le.
 cut (degree 1 (_C_ II[+]_X_)); intros.
  apply (degree_wd _ (_C_ II[+]_X_)).
   (* algebra. *)
   apply cag_commutes_unfolded.
  (* algebra. *)
  rename X into H.  exact H.
  apply (degree_plus_rht _ (_C_ II) _X_ 0 1).
   apply degree_le_c_.
  apply degree_x_.
 auto with arith.
Qed.

Lemma nrCC3_a5 : degree_le n nrCC3_poly''.
Proof.
 replace n with (1 * n).
  unfold nrCC3_poly'' in |- *.
  apply degree_le_nexp.
  exact nrCC3_a4.
 unfold mult in |- *.
 auto with arith.
Qed.

Lemma nrCC3_a6 : nth_coeff n nrCC3_poly'' [=] [1].
Proof.
 cut (monic n nrCC3_poly''); intros.
  unfold monic in H.
  elim H; intros; assumption.
 replace n with (1 * n).
  unfold nrCC3_poly'' in |- *.
  apply monic_nexp.
  unfold monic in |- *; split.
   (* algebra. *)
   apply eq_reflexive_unfolded.
  exact nrCC3_a4.
 unfold mult in |- *.
 auto with arith.
Qed.

Definition nrCC3_poly' := nrCC3_poly''[*]_C_ (a[+I*][--]b).

Lemma nrCC3_a7 : forall r : IR, nrCC3_poly' ! (cc_IR r) [=] (r[+I*][1]) [^]n[*] (a[+I*][--]b).
Proof.
 intros.
 unfold nrCC3_poly' in |- *.
 (* astepl (nrCC3_poly''!(cc_IR r)) [*] ((_C_ a[+I*][--]b)!(cc_IR r)). *)
 apply eq_transitive_unfolded with (nrCC3_poly'' ! (cc_IR r) [*] (_C_ (a[+I*][--]b)) ! (cc_IR r)).
  apply mult_apply.
 Hint Resolve nrCC3_a3: algebra.
 (* Step_final (nrCC3_poly''!(cc_IR r)) [*] (a[+I*][--]b). *)
 apply eq_transitive_unfolded with (nrCC3_poly'' ! (cc_IR r) [*] (a[+I*][--]b)).
  apply bin_op_wd_unfolded. apply eq_reflexive_unfolded. apply c_apply.
   apply bin_op_wd_unfolded. apply nrCC3_a3. apply eq_reflexive_unfolded.
Qed.

Lemma nrCC3_a8 : degree_le n nrCC3_poly'.
Proof.
 replace n with (n + 0).
  unfold nrCC3_poly' in |- *.
  apply degree_le_mult.
   exact nrCC3_a5.
  apply degree_le_c_.
 auto with arith.
Qed.

Lemma nrCC3_a9 : nth_coeff n nrCC3_poly' [=] a[+I*][--]b.
Proof.
 unfold nrCC3_poly' in |- *.
 Hint Resolve nth_coeff_p_mult_c_: algebra.
 (* astepl (nth_coeff n nrCC3_poly'') [*] (a[+I*][--]b). *)
 apply eq_transitive_unfolded with (nth_coeff n nrCC3_poly''[*] (a[+I*][--]b)).
  apply nth_coeff_p_mult_c_.
 Hint Resolve nrCC3_a6: algebra.
 (* Step_final [1][*] (a[+I*][--]b). *)
 apply eq_transitive_unfolded with ([1][*] (a[+I*][--]b)).
  apply bin_op_wd_unfolded. exact nrCC3_a6. apply eq_reflexive_unfolded.
   apply one_mult.
Qed.

Definition nrootCC_3_poly := Im_poly nrCC3_poly'.

Lemma nrootCC_3_ : forall r : IR, nrootCC_3_poly ! r [=] Im ((r[+I*][1]) [^]n[*] (a[+I*][--]b)).
Proof.
 intros.
 unfold nrootCC_3_poly in |- *.
 Hint Resolve nrCC3_a1 nrCC3_a7: algebra.
 (* Step_final (Im (nrCC3_poly'!(cc_IR r))). *)
 apply eq_transitive_unfolded with (Im nrCC3_poly' ! (cc_IR r)).
  apply nrCC3_a1.
 apply Im_wd. apply nrCC3_a7.
Qed.

Lemma nrootCC_3 : forall r : IR,
 cc_IR nrootCC_3_poly ! r[*] (Two[*]II) [=] (r[+I*][1]) [^]n[*] (a[+I*][--]b) [-] (r[+I*][--][1]) [^]n[*] (a[+I*]b).
Proof.
 intros.
 cut (CC_conj ((r[+I*][1]) [^]n[*] (a[+I*][--]b)) [=] (r[+I*][--][1]) [^]n[*] (a[+I*]b)); intros.
  Hint Resolve nrootCC_3_: algebra.
  (* astepl (cc_IR (Im (r[+I*][1]) [^]n[*] (a[+I*][--]b))) [*] (Two[*]II). *)
  apply eq_transitive_unfolded with (cc_IR (Im ((r[+I*][1]) [^]n[*] (a[+I*][--]b))) [*] (Two[*]II)).
   apply bin_op_wd_unfolded. apply cc_IR_wd. apply nrootCC_3_.
    apply eq_reflexive_unfolded.
  Hint Resolve calculate_Im: algebra.
  (* Step_final (r[+I*][1]) [^]n[*] (a[+I*][--]b) [-] (CC_conj (r[+I*][1]) [^]n[*] (a[+I*][--]b)).
  *)
  apply eq_transitive_unfolded with ((r[+I*][1]) [^]n[*] (a[+I*][--]b) [-]
    CC_conj ((r[+I*][1]) [^]n[*] (a[+I*][--]b))).
   apply calculate_Im.
  apply cg_minus_wd. apply eq_reflexive_unfolded. exact H.
   (* astepl (CC_conj (r[+I*][1]) [^]n) [*] (CC_conj a[+I*][--]b). *)
   apply eq_transitive_unfolded with (CC_conj ((r[+I*][1]) [^]n) [*]CC_conj (a[+I*][--]b)).
  apply CC_conj_mult.
 (* Step_final (CC_conj r[+I*][1]) [^]n[*]a[+I*][--][--]b. *)
 apply eq_transitive_unfolded with (CC_conj (r[+I*][1]) [^]n[*] (a[+I*][--][--]b)).
  apply bin_op_wd_unfolded. apply CC_conj_nexp. apply eq_reflexive_unfolded.
   apply bin_op_wd_unfolded. apply eq_reflexive_unfolded. apply I_wd.
  apply eq_reflexive_unfolded. apply cg_inv_inv.
Qed.

Lemma nrootCC_3_degree : degree n nrootCC_3_poly.
Proof.
 unfold degree in |- *.
 split.
  cut (nth_coeff n nrootCC_3_poly [=] [--]b); intros.
   (* astepl [--]b. *)
   apply ap_wdl_unfolded with ( [--]b).
    apply zero_minus_apart. apply minus_ap_zero. apply inv_resp_ap_zero.
    exact b_.
   apply eq_symmetric_unfolded. exact H.
   unfold nrootCC_3_poly in |- *.
  Hint Resolve nrCC3_a2: algebra.
  (* astepl (Im (nth_coeff n nrCC3_poly')). *)
  apply eq_transitive_unfolded with (Im (nth_coeff n nrCC3_poly')).
   apply nrCC3_a2.
  Hint Resolve nrCC3_a9: algebra.
  (* Step_final (Im a[+I*][--]b). *)
  apply eq_transitive_unfolded with (Im (a[+I*][--]b)).
   apply Im_wd. exact nrCC3_a9.
   apply eq_reflexive_unfolded.
 cut (forall (p : cpoly CC) (n : nat), degree_le n p -> degree_le n (Im_poly p)); intros.
  unfold nrootCC_3_poly in |- *.
  apply H.
  exact nrCC3_a8.
 unfold degree_le in |- *.
 unfold degree_le in H.
 intros.
 (* astepl (Im (nth_coeff m p)). *)
 apply eq_transitive_unfolded with (Im (nth_coeff m p)).
  apply nrCC3_a2.
 (* Step_final (Im ([0]::CC)). *)
 apply eq_transitive_unfolded with (Im ([0]:CC)).
  apply Im_wd. apply H. exact H0.
  apply eq_reflexive_unfolded.
Qed.

End NRootCC_3.

Section NRootCC_3'.

(**
%\begin{convention}% Let [c:IR], [n:nat] and [n_:(lt (0) n)].
%\end{convention}%
*)

Variable c : IR.
Variable n : nat.
Hypothesis n_ : 0 < n.

Definition nrootCC_3'_poly := _X_[^]n[-]_C_ c.

Lemma nrootCC_3' : forall x : IR, nrootCC_3'_poly ! x [=] x[^]n[-]c.
Proof.
 intros.
 unfold nrootCC_3'_poly in |- *.
 cut ((_X_[^]n) ! x [=] x[^]n). intros.
  (* Step_final (_X_[^]n)!x[-] (_C_ c)!x. *)
  apply eq_transitive_unfolded with ((_X_[^]n) ! x[-] (_C_ c) ! x).
   apply minus_apply.
  apply cg_minus_wd. exact H. apply c_apply.
   (* Step_final (_X_!x) [^]n. *)
   apply eq_transitive_unfolded with (_X_ ! x[^]n).
  apply nexp_apply.
 apply un_op_wd_unfolded. apply x_apply.
Qed.

Lemma nrootCC_3'_degree : degree n nrootCC_3'_poly.
Proof.
 unfold nrootCC_3'_poly in |- *.
 apply (degree_minus_lft _ (_C_ c) (_X_[^]n) 0 n).
   apply degree_le_c_.
  (* Replace (degree IR n) with (degree IR (mult (1) n)). *)
  pattern n at 1 in |- *; replace n with (1 * n).
   apply degree_nexp.
   apply degree_x_.
  replace (1 * n) with n; auto.
  unfold mult in |- *.
  auto with arith.
 assumption.
Qed.

End NRootCC_3'.

Section NRootCC_4.

Section NRootCC_4_ap_real.

(**
%\begin{convention}% Let [a,b : IR], [b_ : (b [#] [0])], [n : nat] and
[n_:(odd n)]; define [c := a[+I*]b].
%\end{convention}%
*)

Variables a b : IR.
Hypothesis b_ : b [#] [0].
Variable n : nat.
Hypothesis n_ : odd n.

(* begin hide *)
Let c := a[+I*]b.
(* end hide *)

Section NRootCC_4_solutions.

Lemma nrCC4_a1 : {r : IR | (r[+I*][1]) [^]n[*]CC_conj c[-] (r[+I*][--][1]) [^]n[*]c [=] [0]}.
Proof.
 elim (realpolyn_oddhaszero (nrootCC_3_poly a b n)).
  intro r. intro H.
  exists r.
  (* astepl (r[+I*][1]) [^]n[*] (a[+I*][--]b) [-] (r[+I*][--][1]) [^]n[*] (a[+I*]b). *)
  apply eq_transitive_unfolded
    with ((r[+I*][1]) [^]n[*] (a[+I*][--]b) [-] (r[+I*][--][1]) [^]n[*] (a[+I*]b)).
   apply eq_reflexive_unfolded.
  Hint Resolve nrootCC_3: algebra.
  (* astepl (cc_IR ((nrootCC_3_poly a b n)!r)) [*] (Two[*]II). *)
  apply eq_transitive_unfolded with (cc_IR (nrootCC_3_poly a b n) ! r[*] (Two[*]II)).
   apply eq_symmetric_unfolded. apply nrootCC_3.
   (* astepl (cc_IR [0]) [*] (Two[*]II). *)
   apply eq_transitive_unfolded with (cc_IR [0][*] (Two[*]II)).
   apply bin_op_wd_unfolded. apply cc_IR_wd. exact H. apply eq_reflexive_unfolded.
    (* Step_final [0][*] (Two[*]II). *)
    apply eq_transitive_unfolded with ([0][*] (Two[*]II)).
   apply eq_reflexive_unfolded.
  apply cring_mult_zero_op.
 unfold odd_cpoly in |- *.
 exists n.
  apply to_Codd.
  assumption.
 apply (nrootCC_3_degree a b b_ n).
Qed.

(**
%\begin{convention}% Let [r2',c2 : IR] and [r2'_ : (r2' [#] [0])].
%\end{convention}%
*)

Variables r2' c2 : IR.
Hypothesis r2'_ : r2' [#] [0].

Lemma nrCC4_a1' : {y2 : IR | (y2[*]r2') [^]n [=] c2}.
Proof.
 elim (realpolyn_oddhaszero (nrootCC_3'_poly c2 n)).
  intro y2r2'. intros.
  exists (y2r2'[/] r2'[//]r2'_).
  (* astepl y2r2'[^]n. *)
  apply eq_transitive_unfolded with (y2r2'[^]n).
   apply un_op_wd_unfolded. apply div_1.
   (* astepl y2r2'[^]n[+][0]. *)
   apply eq_transitive_unfolded with (y2r2'[^]n[+][0]).
   apply eq_symmetric_unfolded. apply cm_rht_unit_unfolded.
   (* astepl y2r2'[^]n[+] ( [--]c2[+]c2). *)
   apply eq_transitive_unfolded with (y2r2'[^]n[+] ( [--]c2[+]c2)).
   apply bin_op_wd_unfolded. apply eq_reflexive_unfolded.
    apply eq_symmetric_unfolded. apply cg_lft_inv_unfolded.
   (* astepl (y2r2'[^]n[+][--]c2) [+]c2. *)
   apply eq_transitive_unfolded with (y2r2'[^]n[+][--]c2[+]c2).
   apply plus_assoc_unfolded.
  (* astepl (y2r2'[^]n[-]c2) [+]c2. *)
  apply eq_transitive_unfolded with (y2r2'[^]n[-]c2[+]c2).
   apply eq_reflexive_unfolded.
  Hint Resolve nrootCC_3': algebra.
  (* astepl (nrootCC_3'_poly c2 n)!y2r2'[+]c2. *)
  apply eq_transitive_unfolded with ((nrootCC_3'_poly c2 n) ! y2r2'[+]c2).
   apply bin_op_wd_unfolded. apply eq_symmetric_unfolded. apply nrootCC_3'.
    apply eq_reflexive_unfolded.
  (* Step_final [0][+]c2. *)
  apply eq_transitive_unfolded with ([0][+]c2).
   apply bin_op_wd_unfolded. assumption. apply eq_reflexive_unfolded.
    apply cm_lft_unit_unfolded.
 unfold odd_cpoly in |- *.
 exists n.
  apply to_Codd.
  assumption.
 apply nrootCC_3'_degree.
 rewrite (odd_double n). auto with arith.
  assumption.
Qed.

End NRootCC_4_solutions.

Section NRootCC_4_equations.

(**
%\begin{convention}% Let [r,y2 : IR] be such that
[(r[+I*][1]) [^]n[*] (CC_conj c) [-] (r[+I*][--][1]) [^]n[*]c [=] [0]]
and [(y2[*] (r[^] (2) [+][1])) [^]n [=] a[^] (2) [+]b[^] (2)].
%\end{convention}%
*)
Variable r : IR.
Hypothesis r_property : (r[+I*][1]) [^]n[*]CC_conj c[-] (r[+I*][--][1]) [^]n[*]c [=] [0].

Variable y2 : IR.
Hypothesis y2_property : (y2[*] (r[^]2[+][1])) [^]n [=] a[^]2[+]b[^]2.

Lemma nrCC4_a2 : [0] [<] a[^]2[+]b[^]2.
Proof.
 apply plus_resp_nonneg_pos.
  apply sqr_nonneg.
 apply pos_square.
 assumption.
Qed.

Lemma nrCC4_a3 : [0] [<] r[^]2[+][1].
Proof.
 apply plus_resp_nonneg_pos.
  apply sqr_nonneg.
 apply pos_one.
Qed.

Lemma nrCC4_a4 : [0] [<] y2.
Proof.
 apply mult_cancel_pos_lft with (r[^]2[+][1]).
  apply odd_power_cancel_pos with n.
   assumption.
  apply (pos_wd _ _ _ y2_property).
  apply nrCC4_a2.
 apply less_leEq; apply nrCC4_a3.
Qed.

Definition nrCC4_y := sqrt y2 (less_leEq _ _ _ nrCC4_a4).

Let y := nrCC4_y.

Definition nrCC4_x := y[*]r.

Let x := nrCC4_x.

Lemma nrCC4_a5 : x [=] y[*]r.
Proof.
 unfold x in |- *. unfold nrCC4_x in |- *.
 (* algebra. *)
 apply eq_reflexive_unfolded.
Qed.

Lemma nrCC4_a6 : (x[^]2[+]y[^]2) [^]n [=] a[^]2[+]b[^]2.
Proof.
 unfold x in |- *. unfold nrCC4_x in |- *.
 cut ((y[*]r) [^]2[+]y[^]2 [=] y[^]2[*] (r[^]2[+][1])). intro.
  (* astepl (y[^] (2) [*] (r[^] (2) [+][1])) [^]n. *)
  apply eq_transitive_unfolded with ((y[^]2[*] (r[^]2[+][1])) [^]n).
   apply un_op_wd_unfolded. exact H.
   cut (y[^]2 [=] y2). intro.
   (* Step_final (y2[*] (r[^] (2) [+][1])) [^]n. *)
   apply eq_transitive_unfolded with ((y2[*] (r[^]2[+][1])) [^]n).
    apply un_op_wd_unfolded. apply bin_op_wd_unfolded. exact H0.
    apply eq_reflexive_unfolded.
   exact y2_property.
  unfold y in |- *. unfold nrCC4_y in |- *.
  apply sqrt_sqr.
 (* Step_final y[^] (2) [*]r[^] (2) [+]y[^] (2) [*][1]. *)
 apply eq_transitive_unfolded with (y[^]2[*]r[^]2[+]y[^]2[*][1]).
  apply bin_op_wd_unfolded. apply mult_nexp. apply eq_symmetric_unfolded.
   apply mult_one.
 apply eq_symmetric_unfolded. apply ring_dist_unfolded.
Qed.

Definition nrCC4_z := x[+I*]y.

Let z := nrCC4_z.

Lemma nrCC4_a7 : z[^]n[*]CC_conj c[-]CC_conj z[^]n[*]c [=] [0].
Proof.
 unfold z in |- *. unfold nrCC4_z in |- *.
 (* astepl (x[+I*]y) [^]n[*] (CC_conj c) [-] (x[+I*][--]y) [^]n[*]c. *)
 apply eq_transitive_unfolded with ((x[+I*]y) [^]n[*]CC_conj c[-] (x[+I*][--]y) [^]n[*]c).
  apply eq_reflexive_unfolded.
 unfold x in |- *. unfold nrCC4_x in |- *.
 cut ((y[*]r[+I*]y) [^]n[*]CC_conj c [=] cc_IR y[^]n[*] ((r[+I*][1]) [^]n[*]CC_conj c)). intro.
  cut ((y[*]r[+I*][--]y) [^]n[*]c [=] cc_IR y[^]n[*] ((r[+I*][--][1]) [^]n[*]c)). intro.
   (* astepl (cc_IR y) [^]n[*] ((r[+I*][1]) [^]n[*] (CC_conj c)) [-]
     (cc_IR y) [^]n[*] ((r[+I*][--][1]) [^]n[*]c). *)
   apply eq_transitive_unfolded with (cc_IR y[^]n[*] ((r[+I*][1]) [^]n[*]CC_conj c) [-]
     cc_IR y[^]n[*] ((r[+I*][--][1]) [^]n[*]c)).
    apply cg_minus_wd. exact H. exact H0.
     (* astepl (cc_IR y) [^]n[*] (((r[+I*][1]) [^]n[*] (CC_conj c)) [-] ((r[+I*][--][1]) [^]n[*]c)). *)
     apply eq_transitive_unfolded with
       (cc_IR y[^]n[*] ((r[+I*][1]) [^]n[*]CC_conj c[-] (r[+I*][--][1]) [^]n[*]c)).
    apply eq_symmetric_unfolded. apply dist_2a.
    (* Step_final (cc_IR y) [^]n[*][0]. *)
    apply eq_transitive_unfolded with (cc_IR y[^]n[*][0]).
    apply bin_op_wd_unfolded. apply eq_reflexive_unfolded. exact r_property.
     apply cring_mult_zero.
  cut ((y[*]r[+I*][--]y) [^]n [=] cc_IR y[^]n[*] (r[+I*][--][1]) [^]n). intro.
   (* Step_final ((cc_IR y) [^]n[*] (r[+I*][--][1]) [^]n) [*]c. *)
   apply eq_transitive_unfolded with (cc_IR y[^]n[*] (r[+I*][--][1]) [^]n[*]c).
    apply bin_op_wd_unfolded. exact H0. apply eq_reflexive_unfolded.
     apply eq_symmetric_unfolded. apply mult_assoc_unfolded.
   cut (y[*]r[+I*][--]y [=] cc_IR y[*] (r[+I*][--][1])). intro.
   (* Step_final ((cc_IR y) [*] (r[+I*][--][1])) [^]n. *)
   apply eq_transitive_unfolded with ((cc_IR y[*] (r[+I*][--][1])) [^]n).
    apply un_op_wd_unfolded. exact H0.
    apply mult_nexp.
  cut ( [--]y [=] y[*][--][1]). intro.
   (* Step_final (y[*]r) [+I*] (y[*][--][1]). *)
   apply eq_transitive_unfolded with (y[*]r[+I*]y[*][--][1]).
    apply I_wd. apply eq_reflexive_unfolded. exact H0.
     apply eq_symmetric_unfolded. apply cc_IR_mult_rht.
   (* Step_final [--] (y[*][1]). *)
   apply eq_transitive_unfolded with ( [--] (y[*][1])).
   apply un_op_wd_unfolded. apply eq_symmetric_unfolded. apply mult_one.
   apply eq_symmetric_unfolded. apply cring_inv_mult_lft.
  cut ((y[*]r[+I*]y) [^]n [=] cc_IR y[^]n[*] (r[+I*][1]) [^]n). intro.
  (* Step_final ((cc_IR y) [^]n[*] (r[+I*][1]) [^]n) [*] (CC_conj c). *)
  apply eq_transitive_unfolded with (cc_IR y[^]n[*] (r[+I*][1]) [^]n[*]CC_conj c).
   apply bin_op_wd_unfolded. exact H. apply eq_reflexive_unfolded.
    apply eq_symmetric_unfolded. apply mult_assoc_unfolded.
  cut (y[*]r[+I*]y [=] cc_IR y[*] (r[+I*][1])). intro.
  (* Step_final ((cc_IR y) [*] (r[+I*][1])) [^]n. *)
  apply eq_transitive_unfolded with ((cc_IR y[*] (r[+I*][1])) [^]n).
   apply un_op_wd_unfolded. exact H.
   apply mult_nexp.
 (* Step_final (y[*]r) [+I*] (y[*][1]). *)
 apply eq_transitive_unfolded with (y[*]r[+I*]y[*][1]).
  apply I_wd. apply eq_reflexive_unfolded. apply eq_symmetric_unfolded.
   apply mult_one.
 apply eq_symmetric_unfolded. apply cc_IR_mult_rht.
Qed.

Lemma nrCC4_a8 : (z[*]CC_conj z) [^]n [=] c[*]CC_conj c.
Proof.
 unfold z in |- *.
 unfold nrCC4_z in |- *.
 unfold c in |- *.
 (* astepl (cc_IR x[^] (2) [+]y[^] (2)) [^]n. *)
 apply eq_transitive_unfolded with (cc_IR (x[^]2[+]y[^]2) [^]n).
  apply un_op_wd_unfolded. apply calculate_norm.
  (* astepl (cc_IR (x[^] (2) [+]y[^] (2)) [^]n). *)
  apply eq_transitive_unfolded with (cc_IR ((x[^]2[+]y[^]2) [^]n)).
  apply cc_IR_nexp.
 Hint Resolve nrCC4_a6: algebra.
 (* Step_final (cc_IR (a[^] (2) [+]b[^] (2))). *)
 apply eq_transitive_unfolded with (cc_IR (a[^]2[+]b[^]2)).
  apply cc_IR_wd. exact nrCC4_a6.
  apply eq_symmetric_unfolded. apply calculate_norm.
Qed.

Lemma nrCC4_a9 : z[^]n [=] c or z[^]n [=] [--]c.
Proof.
 apply nrootCC_2.
   right.
   (* astepl b. *)
   apply ap_wdl_unfolded with b.
    exact b_.
   apply eq_reflexive_unfolded.
  apply nrCC4_a8.
 apply nrCC4_a7.
Qed.

End NRootCC_4_equations.

Lemma nrCC4_a10 : forall c, {z : CC | z[^]n [=] c or z[^]n [=] [--]c} -> {z : CC | z[^]n [=] c}.
Proof.
 intros c0 H.
 elim H. intros x H0.
 elim H0; intro H1.
  exists x. assumption.
  exists ( [--]x).
 (* astepl [--] (x[^]n). *)
 apply eq_transitive_unfolded with ( [--] (x[^]n)).
  apply inv_nexp_odd. assumption.
  (* Step_final [--][--]c0. *)
  apply eq_transitive_unfolded with ( [--][--]c0).
  apply un_op_wd_unfolded. exact H1.
  apply cg_inv_inv.
Qed.

Lemma nrootCC_4_ap_real : {z : CC | z[^]n [=] c}.
Proof.
 apply nrCC4_a10.
 elim nrCC4_a1. intro r. intro H.
 elim (nrCC4_a1' (r[^]2[+][1]) (a[^]2[+]b[^]2)). intro y2. intro H0.
  exists (nrCC4_z r y2 H0).
  apply nrCC4_a9. assumption.
  change (r[^]2[+][1] [#] [0]) in |- *.
 apply pos_ap_zero.
 apply nrCC4_a3.
Qed.

End NRootCC_4_ap_real.

Section NRootCC_4_ap_imag.

(**
%\begin{convention}% Let [a,b : IR] and [n : nat] with [a [#] [0]]
and [(odd n)]; define [c' := (a[+I*]b) [*]II := a'[+I*]b'].
%\end{convention}%
*)
Variables a b : IR.
Hypothesis a_ : a [#] [0].
Variable n : nat.
Hypothesis n_ : odd n.

(* begin hide *)
Let c' := (a[+I*]b) [*]II.
Let a' := Re c'.
Let b' := Im c'.
(* end hide *)

Lemma nrootCC_4_ap_real' : {z' : CC | z'[^]n [=] a'[+I*]b'}.
Proof.
 apply nrootCC_4_ap_real; try assumption.
 apply (imag_to_real a b a' b').
  (* algebra. *)
  apply eq_reflexive_unfolded.
 (* algebra. *)
 exact a_.
Qed.

Lemma nrootCC_4_ap_imag : {z : CC | z[^]n [=] a[+I*]b}.
Proof.
 elim nrootCC_4_ap_real'.
 intro z'.
 intro H.
 exists (z'[*]nroot_minus_I n n_).
 (* astepl z'[^]n[*] (nroot_minus_I n on) [^]n. *)
 apply eq_transitive_unfolded with (z'[^]n[*]nroot_minus_I n n_[^]n).
  apply mult_nexp.
 Hint Resolve nroot_minus_I_nexp: algebra.
 (* astepl (a'[+I*]b') [*][--]II. *)
 apply eq_transitive_unfolded with ((a'[+I*]b') [*][--]II).
  apply bin_op_wd_unfolded. exact H. apply nroot_minus_I_nexp.
   (* astepl ((a[+I*]b) [*]II) [*][--]II. *)
   apply eq_transitive_unfolded with ((a[+I*]b) [*]II[*][--]II).
  apply eq_reflexive_unfolded.
 (* astepl (a[+I*]b) [*] (II[*][--]II). *)
 apply eq_transitive_unfolded with ((a[+I*]b) [*] (II[*][--]II)).
  apply eq_symmetric_unfolded. apply mult_assoc_unfolded.
  (* Step_final (a[+I*]b) [*][1]. *)
  apply eq_transitive_unfolded with ((a[+I*]b) [*][1]).
  apply bin_op_wd_unfolded. apply eq_reflexive_unfolded. exact I_recip_rht.
   apply mult_one.
Qed.

End NRootCC_4_ap_imag.

Lemma nrootCC_4 : forall c, c [#] [0] -> forall n, odd n -> {z : CC | z[^]n [=] c}.
Proof.
 intros.
 pattern c in |- *.
 apply C_cc_ap_zero; try assumption; intros.
  apply nrootCC_4_ap_imag; try assumption.
 apply nrootCC_4_ap_real; try assumption.
Qed.

End NRootCC_4.

(** Finally, the general definition of nth root. *)

Section NRootCC_5.

Lemma nrCC_5a2 : forall n : nat, double n = 2 * n.
Proof.
 intros.
 unfold double in |- *.
 unfold mult in |- *.
 auto with arith.
Qed.

Lemma nrCC_5a3 : forall (n : nat) (z : CC), (z[^]2) [^]n [=] z[^]double n.
Proof.
 intros.
 (* astepl z[^] (mult (2) n). *)
 apply eq_transitive_unfolded with (z[^] (2 * n)).
  apply nexp_mult.
 rewrite <- nrCC_5a2.
 (* algebra. *)
 apply eq_reflexive_unfolded.
Qed.
Hint Resolve nrCC_5a3: algebra.

(**
%\begin{convention}% Let [c : CC] with [c [#] [0]].
%\end{convention}%
*)
Variable c : CC.
Hypothesis c_ : c [#] [0].

Lemma nrCC_5a4 : forall n, 0 < n -> {z : CC | z[^]n [=] c} -> {z : CC | z[^]double n [=] c}.
Proof.
 intros n H H0.
 elim H0. intros x H1.
 elim (nrootCC_1 x). intros x0 H2.
  exists x0.
  (* astepl (x0[^] (2)) [^]n. *)
  apply eq_transitive_unfolded with ((x0[^]2) [^]n).
   apply eq_symmetric_unfolded. apply nrCC_5a3.
   (* Step_final x[^]n. *)
   apply eq_transitive_unfolded with (x[^]n).
   apply un_op_wd_unfolded. exact H2.
   exact H1.
 apply (cs_un_op_strext _ (nexp_op (R:=CC) n)).
 (* astepl c. *)
 apply ap_wdl_unfolded with c.
  2: apply eq_symmetric_unfolded. 2: exact H1.
  (* astepr ([0]::CC). *)
  apply ap_wdr_unfolded with ([0]:CC).
  exact c_.
 apply eq_symmetric_unfolded. apply zero_nexp. exact H.
Qed.

Lemma nrootCC_5 : forall n : nat, 0 < n -> {z : CC | z[^]n [=] c}.
Proof.
 intros.
 pattern n in |- *.
 apply odd_double_ind.
   exact (nrootCC_4 c c_).
  exact nrCC_5a4.
 assumption.
Qed.

End NRootCC_5.

(** Final definition *)

Definition CnrootCC : forall c, c [#] [0] -> forall n, 0 < n -> {z : CC | z[^]n [=] c} := nrootCC_5.
