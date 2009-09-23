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
(* file        : least_upper_bound_principle.v                     *)
(* version     : 1.50 -	03/05/2001                                 *)
(* version     : 1.00 - 27/02/2001                                 *)
(* author      : Milad Niqui                                       *)
(* language    : coq 7.0beta26feb                                  *)
(* dependency  : iso_CReals.v , Expon.v                            *)
(* description : proof of the Bridges' least upper bound principle *)



Require Export iso_CReals.
Require Import Expon.

Section LUBP.

Variable R1 : CReals.

(* SUBSECTION ON GENRAL DEFINITIONS *)
Section lub_definitions.

Variable OF : COrdField.
Variable SS : OF -> CProp.

Definition member (H : {x : OF | SS x}) := let (N, _) := H in N.
Definition Pmember (H : {x : OF | SS x}) := projT2 H.

Definition is_upper_bound (b : OF) :=
  forall x : OF, SS x -> forall z : OF, z[<]x -> z[<]b.



Definition l_u_b :=
  {b : OF |
  is_upper_bound b and (forall b' : OF, b'[<]b -> {s : OF | SS s and b'[<]s})}.
Definition supremum (H : l_u_b) := let (N, _) := H in N.
Definition Psupremum (H : l_u_b) := projT2 H.


          (* the following definitions are not used in *)
          (* this file but later we will need them     *)
Definition is_lower_bound (c : OF) :=
  forall x : OF, SS x -> forall z : OF, z[<]c -> z[<]x.

Definition g_l_b :=
  {c : OF |
  is_lower_bound c and (forall c' : OF, c[<]c' -> {s : OF | SS s and s[<]c'})}.

Definition infimum (H : g_l_b) := let (N, _) := H in N.
Definition Pinfimum (H : g_l_b) := projT2 H.

End lub_definitions.

(* MAIN SECTION *)
Section upper_bound_sequence.

Variable A : R1 -> CProp.
Hypothesis is_inhabitted : {x : R1 | A x}.
Hypothesis bounded_above : {b : R1 | is_upper_bound R1 A b}.
Hypothesis
  located :
    forall x y : R1, x[<]y -> is_upper_bound R1 A y or {s : R1 | A s | x[<]s}.

Let s := member R1 A is_inhabitted.
Let Ps := Pmember R1 A is_inhabitted.

Let b0 := let (N, _) := bounded_above in N.
Let Pb0 := projT2 bounded_above.

Lemma b0_is_upper_bound : is_upper_bound R1 A b0.
Proof.
 exact Pb0.
Qed.

Lemma s_inhabits_A : A s.
Proof.
 exact Ps.
Qed.

Let dstart_l := s[-]One.
Let dstart_r := b0[+]One.

Lemma dl_less_dr : dstart_l[<]dstart_r.
Proof.
 apply less_transitive_unfolded with (y := b0).
  unfold is_upper_bound in bounded_above.
  cut (forall x : R1, A x -> forall z : R1, z[<]x -> z[<]b0).
   intro H.
   cut (forall z : R1, z[<]s -> z[<]b0).
    intro H0.
    apply H0.
    unfold dstart_l in |- *.
    apply shift_minus_less.
    apply less_plusOne.
   intros.
   apply H with (z := z) (x := s).
    apply Ps.
   assumption.
  exact Pb0.
 unfold dstart_r in |- *.
 apply less_plusOne.
Qed.

Lemma shrink23d :
 forall r1 r2 : R1,
 r1[<]r2 -> r1[+](r2[-]r1) [/]ThreeNZ[<]r2[-](r2[-]r1) [/]ThreeNZ.
Proof.
 intros.
 apply plus_cancel_less with (z := (r2[-]r1) [/]ThreeNZ).
 rstepl (r2[-](r2[-]r1) [/]ThreeNZ).
 rstepr r2.
 apply plus_cancel_less with (z := [--]r2).
 rstepr ([--](Zero:R1)).
 rstepl ([--]((r2[-]r1) [/]ThreeNZ)).
 apply inv_resp_less.
 apply mult_cancel_less with (z := Three:R1).
  apply pos_nring_S.
 rstepl (Zero:R1).
 rstepr (r2[-]r1).
 apply shift_zero_less_minus.
 assumption.
Qed.


Lemma shrink13d :
 forall r1 r2 : R1, r1[<]r2 -> r1[<]r2[-](r2[-]r1) [/]ThreeNZ.
Proof.
 intros.
 apply less_transitive_unfolded with (y := r1[+](r2[-]r1) [/]ThreeNZ).
  astepl (r1[+]Zero).
  apply plus_resp_less_lft.
  apply div_resp_pos.
   apply pos_three.
  apply shift_zero_less_minus.
  assumption.
 apply shrink23d.
 assumption.
Qed.

Lemma shrink24d :
 forall r1 r2 : R1, r1[<]r2 -> r1[+](r2[-]r1) [/]ThreeNZ[<]r2.
Proof.
 intros.
 apply less_transitive_unfolded with (y := r2[-](r2[-]r1) [/]ThreeNZ).
  apply shrink23d.
  assumption.
 astepl (r2[+][--]((r2[-]r1) [/]ThreeNZ)).
 astepr (r2[+]Zero).
 apply plus_resp_less_lft.
 apply inv_cancel_less.
 rstepl (Zero:R1).
 rstepr ((r2[-]r1) [/]ThreeNZ).
 apply div_resp_pos.
  apply pos_three.
 apply shift_zero_less_minus.
 assumption.
Qed.

Definition Real_Interval := Interval R1.

Definition dcotrans_analyze : forall r1 r2 : R1, r1[<]r2 -> R1.
Proof.
 intros.
 case (located (r1[+](r2[-]r1) [/]ThreeNZ) (r2[-](r2[-]r1) [/]ThreeNZ)).
   apply shrink23d.
   assumption.
  intro.
  exact (r2[-](r2[-]r1) [/]ThreeNZ).
 intro.
 exact (r1[+](r2[-]r1) [/]ThreeNZ).
Defined.

Lemma dcotrans_analyze_strong :
 forall (r1 r2 : R1) (H : r1[<]r2),
 {s : R1 | A s | r1[+](r2[-]r1) [/]ThreeNZ[<]s}
 and dcotrans_analyze r1 r2 H[=]r1[+](r2[-]r1) [/]ThreeNZ
 or is_upper_bound R1 A (r2[-](r2[-]r1) [/]ThreeNZ)
    and dcotrans_analyze r1 r2 H[=]r2[-](r2[-]r1) [/]ThreeNZ.
Proof.
 intros.
 unfold dcotrans_analyze in |- *.
 elim (located (r1[+](r2[-]r1) [/]ThreeNZ) (r2[-](r2[-]r1) [/]ThreeNZ) (shrink23d _ _ H)).
  intro.
  right.
  split.
   assumption.
  apply eq_reflexive_unfolded.
 intro.
 left.
 split.
  assumption.
 apply eq_reflexive_unfolded.
Qed.

Notation "( p , q )" := (pairT p q).

Definition dif_cotrans : forall I1 : Real_Interval, Real_Interval.
Proof.
 intros.
 case I1.
 intros i pi.
 elim (dcotrans_analyze_strong (fstT i) (sndT i) pi).
  intro.
  exact (Build_Interval _ (fstT i[+](sndT i[-]fstT i) [/]ThreeNZ, sndT i)
    (shrink24d (fstT i) (sndT i) pi)).
 intro.
 exact (Build_Interval _ (fstT i, sndT i[-](sndT i[-]fstT i) [/]ThreeNZ)
   (shrink13d (fstT i) (sndT i) pi)).
Defined.


Lemma dif_cotrans_strong :
 forall I1 : Real_Interval,
 {s : R1 | A s | fstT I1[+](sndT I1[-]fstT I1) [/]ThreeNZ[<]s}
 and dif_cotrans I1 =
     Build_Interval _ (fstT I1[+](sndT I1[-]fstT I1) [/]ThreeNZ, sndT I1)
       (shrink24d (fstT I1) (sndT I1) (is_interval _ I1))
 or is_upper_bound R1 A (sndT I1[-](sndT I1[-]fstT I1) [/]ThreeNZ)
    and dif_cotrans I1 =
        Build_Interval _ (fstT I1, sndT I1[-](sndT I1[-]fstT I1) [/]ThreeNZ)
          (shrink13d (fstT I1) (sndT I1) (is_interval _ I1)).
Proof.
 intros.
 case I1.
 intros i pi.
 elim (dcotrans_analyze_strong _ _ pi).
  intro y.
  left.
  elim y.
  intros H H0.
  split.
   exact H.
  cut (dif_cotrans (Build_Interval _ i pi) =
    Build_Interval _ (fstT i[+](sndT i[-]fstT i) [/]ThreeNZ, sndT i) (shrink24d (fstT i) (sndT i) pi)).
   intro H1.
   rewrite H1.
   simpl in |- *.
   apply refl_equal.
  unfold dif_cotrans in |- *.
  apply not_r_cor_rect.
  apply or_not_and.
  right.
  apply ap_imp_neq.
  astepl (fstT i[+](sndT i[-]fstT i) [/]ThreeNZ).
  apply less_imp_ap.
  apply shrink23d.
  assumption.
 intro y.
 elim y.
 intros H H0.
 right.
 split.
  exact H.
 cut (dif_cotrans (Build_Interval R1 i pi) =
   Build_Interval R1 (fstT i, sndT i[-](sndT i[-]fstT i) [/]ThreeNZ)
     (shrink13d (fstT i) (sndT i) pi)).
  intro.
  rewrite H1.
  simpl in |- *.
  reflexivity.
 unfold dif_cotrans in |- *.
 apply not_l_cor_rect.
 apply or_not_and.
 right.
 apply ap_imp_neq.
 astepl (sndT i[-](sndT i[-]fstT i) [/]ThreeNZ).
 apply Greater_imp_ap.
 apply shrink23d.
 assumption.
Qed.


Fixpoint dIntrvl (n : nat) : Real_Interval :=
  match n with
  | O => Build_Interval _ (dstart_l, dstart_r) dl_less_dr
  | S p => dif_cotrans (dIntrvl p)
  end.

Let U (n : nat) := (fstT (dIntrvl n)[+]sndT (dIntrvl n)) [/]TwoNZ.
Let V (n : nat) := fstT (dIntrvl n).
Let W (n : nat) := sndT (dIntrvl n).

Lemma delta_dIntrvl :
 forall n : nat,
 Length _ (dIntrvl (S n))[=]Two [/]ThreeNZ[*]Length _ (dIntrvl n).
Proof.
 intros.
 case (dif_cotrans_strong (dIntrvl n)).
  intro a.
  elim a.
  intros H H0.
  simpl in |- *.
  rewrite H0.
  unfold Length in |- *.
  simpl in |- *.
  rational.
 intro a.
 elim a.
 intros H H0.
 simpl in |- *.
 rewrite H0.
 unfold Length in |- *.
 simpl in |- *.
 rational.
Qed.

Lemma Length_dIntrvl :
 forall n : nat,
 Length _ (dIntrvl n)[=](Two [/]ThreeNZ)[^]n[*](dstart_r[-]dstart_l).
Proof.
 intros.
 induction  n as [| n Hrecn].
  (* n=0 *)
  unfold Length in |- *.
  simpl in |- *.
  rational.
 (* n=(S n0) & induction hypothesis *)
 astepr (Two [/]ThreeNZ[*]((Two [/]ThreeNZ)[^]n[*](dstart_r[-]dstart_l))).
  astepr (Two [/]ThreeNZ[*]Length _ (dIntrvl n)).
  apply delta_dIntrvl.
 astepr ((Two [/]ThreeNZ)[^]n[*]Two [/]ThreeNZ[*](dstart_r[-]dstart_l)).
 rational.
Qed.


Lemma dIntrvl_inside_l_n :
 forall m n : nat, m <= n -> fstT (dIntrvl m)[<=]fstT (dIntrvl n).
Proof.
 intros.
 induction  n as [| n Hrecn].
  (* n=0 *)
  cut (m = 0).
   intro.
   rewrite H0.
   simpl in |- *.
   apply leEq_reflexive.
  symmetry  in |- *.
  apply le_n_O_eq.
  assumption.
 (* n=(S n0) *)
 cut ({m = S n} + {m <= n}).
  intro H0.
  case H0.
   intro H1.
   rewrite H1.
   apply leEq_reflexive.
  intro H2.
  apply leEq_transitive with (y := fstT (dIntrvl n)).
   apply Hrecn.
   assumption.
  case (dif_cotrans_strong (dIntrvl n)).
   intro a.
   elim a.
   intros H3 H4.
   change (fstT (dIntrvl n)[<=]fstT (dif_cotrans (dIntrvl n))) in |- *.
   rewrite H4.
   simpl in |- *.
   astepl (fstT (dIntrvl n)[+]Zero).
   apply plus_resp_leEq_both with (b := (sndT (dIntrvl n)[-]fstT (dIntrvl n)) [/]ThreeNZ).
    apply leEq_reflexive.
   apply less_leEq.
   apply div_resp_pos.
    apply pos_three.
   apply shift_zero_less_minus.
   apply is_interval.
  intro a.
  elim a.
  intros H3 H4.
  change (fstT (dIntrvl n)[<=]fstT (dif_cotrans (dIntrvl n))) in |- *.
  rewrite H4.
  simpl in |- *.
  apply leEq_reflexive.
 case (le_lt_eq_dec m (S n) H).
  intro.
  right.
  apply lt_n_Sm_le.
  assumption.
 intro.
 left.
 assumption.
Qed.

Lemma dIntrvl_inside_r_n :
 forall m n : nat, m <= n -> sndT (dIntrvl n)[<=]sndT (dIntrvl m).
Proof.
 intros.
 induction  n as [| n Hrecn].
  (* n=0 *)
  cut (m = 0).
   intro H0.
   rewrite H0.
   simpl in |- *.
   apply leEq_reflexive.
  symmetry  in |- *.
  apply le_n_O_eq.
  assumption.
 (* n=(S n0) *)
 cut ({m = S n} + {m <= n}).
  intro H0.
  case H0.
   intro H1.
   rewrite H1.
   apply leEq_reflexive.
  intro H2.
  apply leEq_transitive with (y := sndT (dIntrvl n)).
   case (dif_cotrans_strong (dIntrvl n)).
    intro a.
    elim a.
    intros H3 H4.
    change (sndT (dif_cotrans (dIntrvl n))[<=]sndT (dIntrvl n)) in |- *.
    rewrite H4.
    simpl in |- *.
    apply leEq_reflexive.
   intro a.
   elim a.
   intros H3 H4.
   change (sndT (dif_cotrans (dIntrvl n))[<=]sndT (dIntrvl n)) in |- *.
   rewrite H4.
   simpl in |- *.
   astepr (sndT (dIntrvl n)[+]Zero).
   astepl (sndT (dIntrvl n)[+][--]((sndT (dIntrvl n)[-]fstT (dIntrvl n)) [/]ThreeNZ)).
   apply plus_resp_leEq_both.
    apply leEq_reflexive.
   apply inv_cancel_leEq.
   astepl (Zero:R1).
   astepr ((sndT (dIntrvl n)[-]fstT (dIntrvl n)) [/]ThreeNZ).
   apply less_leEq.
   apply div_resp_pos.
    apply pos_three.
   apply shift_zero_less_minus.
   apply is_interval.
  apply Hrecn.
  assumption.
 case (le_lt_eq_dec m (S n) H).
  intro.
  right.
  apply lt_n_Sm_le.
  assumption.
 intro.
 left.
 assumption.
Qed.

Lemma V_increase : forall m n : nat, m <= n -> V m[<=]V n.
Proof.
 intros.
 unfold V in |- *.
 apply dIntrvl_inside_l_n.
 assumption.
Qed.

Lemma W_decrease : forall m n : nat, m <= n -> W n[<=]W m.
Proof.
 intros.
 unfold W in |- *.
 apply dIntrvl_inside_r_n.
 assumption.
Qed.


Lemma U_m_n_V : forall m n : nat, m <= n -> V m[<]U n.
Proof.
 intros.
 unfold U in |- *.
 apply leEq_less_trans with (y := V n).
  apply V_increase.
  assumption.
 unfold V in |- *.
 apply Smallest_less_Average.
 apply is_interval.
Qed.

Lemma U_m_n_W : forall m n : nat, m <= n -> U n[<]W m.
Proof.
 intros.
 unfold U in |- *.
 apply less_leEq_trans with (y := W n).
  unfold W in |- *.
  apply Average_less_Greatest.
  apply is_interval.
 apply W_decrease.
 assumption.
Qed.

(*  These lemma are *very* similar to those in  *)
(*  Cauchy_rationals_approach_reals.v           *)
Lemma a_familiar_simple_inequality :
 forall m : nat,
 4 <= m ->
 (Two [/]ThreeNZ)[^]m[<]((One:R1)[/] nring (S m)[//]nringS_ap_zero _ m).
Proof.
 intros.
 induction  m as [| m Hrecm].
  apply False_rect.
  generalize H.
  change (~ 4 <= 0) in |- *.
  apply le_Sn_O.
 case (le_lt_eq_dec 4 (S m) H).
  intro.
  apply less_transitive_unfolded with
    (y := Two [/]ThreeNZ[*]((One:R1)[/] nring (S m)[//]nringS_ap_zero _ m)).
   astepl (((Two:R1) [/]ThreeNZ)[^]m[*]Two [/]ThreeNZ).
   astepl ((Two:R1) [/]ThreeNZ[*](Two [/]ThreeNZ)[^]m).
   apply mult_resp_less_lft.
    apply Hrecm.
    apply lt_n_Sm_le.
    assumption.
   apply div_resp_pos.
    apply pos_three.
   apply pos_two.
  apply mult_cancel_less with (z := (Three:R1)[*]nring (S m)[*]nring (S (S m))).
   apply mult_resp_pos.
    apply mult_resp_pos.
     apply pos_three.
    apply pos_nring_S.
   apply pos_nring_S.
  rstepl ((Two:R1)[*]nring (S (S m))).
  rstepr ((Three:R1)[*]nring (S m)).
  astepl ((Two:R1)[*](nring m[+]Two)).
   astepr ((Three:R1)[*](nring m[+]One)).
   apply plus_cancel_less with (z := [--]((Two:R1)[*]nring m[+]Three)).
   rstepl (One:R1).
   rstepr (nring (R:=R1) m).
   astepl (nring (R:=R1) 1).
    apply nring_less.
    apply lt_trans with (m := 3).
     constructor.
     constructor.
    apply lt_S_n.
    assumption.
   simpl in |- *.
   algebra.
  apply bin_op_wd_unfolded.
   apply eq_reflexive_unfolded.
  simpl in |- *.
  rational.
 intro H0.
 rewrite <- H0.
 apply mult_cancel_less with (z := nring (R:=R1) 5[*]Three[^]4).
  apply mult_resp_pos.
   apply pos_nring_S.
  rstepr (Three[^]2[*](Three[^]2:R1)).
  apply mult_resp_pos.
   apply pos_square.
   apply nringS_ap_zero.
  apply pos_square.
  apply nringS_ap_zero.
 rstepl (Two[^]4[*]nring (R:=R1) 5).
 rstepr (Three[^]4:R1).
 rstepl (nring (R:=R1) 80).
 rstepr (nring (R:=R1) 81).
 apply nring_less.
 constructor.
Qed.

Lemma U_conversion_rate2 :
 forall m n : nat,
 4 <= m ->
 m <= n ->
 AbsSmall (dstart_r[-]dstart_l[/] nring (S m)[//]nringS_ap_zero _ m)
   (U m[-]U n).
Proof.
 intros.
 apply AbsSmall_leEq_trans with (e1 := Length _ (dIntrvl m)).
  apply less_leEq.
  astepl ((Two [/]ThreeNZ)[^]m[*](dstart_r[-]dstart_l)).
   rstepr ((One[/] nring (S m)[//]nringS_ap_zero _ m)[*](dstart_r[-]dstart_l)).
   apply mult_resp_less.
    apply a_familiar_simple_inequality.
    assumption.
   apply shift_zero_less_minus.
   apply dl_less_dr.
  apply eq_symmetric_unfolded.
  apply Length_dIntrvl.
 unfold Length in |- *.
 apply AbsSmall_subinterval; apply less_leEq.
    change (V m[<]U m) in |- *.
    apply U_m_n_V.
    constructor.
   change (V m[<]U n) in |- *.
   apply U_m_n_V.
   assumption.
  change (U m[<]W m) in |- *.
  apply U_m_n_W.
  constructor.
 change (U n[<]W m) in |- *.
 apply U_m_n_W.
 assumption.
Qed.


Lemma CS_seq_U : Cauchy_prop (fun m : nat => U m).
Proof.
 intros.
 unfold Cauchy_prop in |- *.
 intros e H.
 cut {n : nat | (dstart_r[-]dstart_l[/] e[//]Greater_imp_ap _ e Zero H)[<]nring n}.
  intro H0.
  case H0.
  intro N.
  intro.
  exists (S (N + 3)).
  intros.
  apply AbsSmall_minus.
  apply AbsSmall_leEq_trans with (e1 := dstart_r[-]dstart_l[/] nring (S (S (N + 3)))[//]
    nringS_ap_zero R1 (S (N + 3))).
   apply less_leEq.
   apply swap_div with (z_ := Greater_imp_ap _ e Zero H).
     apply pos_nring_S.
    assumption.
   apply less_transitive_unfolded with (y := nring (R:=R1) N).
    assumption.
   apply nring_less.
   apply le_lt_n_Sm.
   constructor.
   apply le_plus_l.
  apply U_conversion_rate2 with (m := S (N + 3)).
   apply le_n_S.
   apply le_plus_r.
  assumption.
 apply Archimedes'.  (* Note the use of Archimedean Property of R1 *)
Qed.

Definition U_as_CauchySeq := Build_CauchySeq R1 (fun m : nat => U m) CS_seq_U.

Let B := Lim U_as_CauchySeq.

Lemma U_minus_V : forall n : nat, U n[-]V n[=]Length _ (dIntrvl n) [/]TwoNZ.
Proof.
 intros.
 unfold U in |- *.
 unfold V in |- *.
 unfold Length in |- *.
 rational.
Qed.

Lemma U_minus_W : forall n : nat, W n[-]U n[=]Length _ (dIntrvl n) [/]TwoNZ.
Proof.
 intros.
 unfold U in |- *.
 unfold W in |- *.
 unfold Length in |- *.
 rational.
Qed.

Lemma U_V_upper :
 forall n : nat, U n[-]V n[<](Two [/]ThreeNZ)[^]n[*](dstart_r[-]dstart_l).
Proof.
 intro.
 apply less_wdr with (y := Length _ (dIntrvl n)).
  apply less_wdl with (x := Length _ (dIntrvl n) [/]TwoNZ).
   apply plus_cancel_less with (z := [--](Length R1 (dIntrvl n) [/]TwoNZ)).
   rstepl (Zero:R1).
   rstepr (Length R1 (dIntrvl n) [/]TwoNZ).
   apply pos_div_two.
   unfold Length in |- *.
   apply shift_zero_less_minus.
   apply is_interval.
  apply eq_symmetric_unfolded.
  apply U_minus_V.
 apply Length_dIntrvl.
Qed.

Lemma U_W_lower :
 forall n : nat, W n[-]U n[<](Two [/]ThreeNZ)[^]n[*](dstart_r[-]dstart_l).
Proof.
 intro.
 apply less_wdr with (y := Length _ (dIntrvl n)).
  apply less_wdl with (x := Length _ (dIntrvl n) [/]TwoNZ).
   apply plus_cancel_less with (z := [--](Length R1 (dIntrvl n) [/]TwoNZ)).
   rstepl (Zero:R1).
   rstepr (Length R1 (dIntrvl n) [/]TwoNZ).
   apply pos_div_two.
   unfold Length in |- *.
   apply shift_zero_less_minus.
   apply is_interval.
  apply eq_symmetric_unfolded.
  apply U_minus_W.
 apply Length_dIntrvl.
Qed.

Lemma AbsSmall_U_V :
 forall n : nat,
 AbsSmall ((Two [/]ThreeNZ)[^]n[*](dstart_r[-]dstart_l)) (U n[-]V n).
Proof.
 intros.
 split; apply less_leEq.
  apply less_wdr with (y := Length R1 (dIntrvl n) [/]TwoNZ).
   apply less_wdl with (x := [--](Length R1 (dIntrvl n))).
    apply plus_cancel_less with (z := Length R1 (dIntrvl n)).
    rstepl (Zero:R1).
    apply plus_resp_pos.
     apply pos_div_two.
     unfold Length in |- *.
     apply shift_zero_less_minus.
     apply is_interval.
    unfold Length in |- *.
    apply shift_zero_less_minus.
    apply is_interval.
   apply un_op_wd_unfolded.
   apply Length_dIntrvl.
  apply eq_symmetric_unfolded.
  apply U_minus_V.
 apply U_V_upper.
Qed.

Lemma AbsSmall_U_W :
 forall n : nat,
 AbsSmall ((Two [/]ThreeNZ)[^]n[*](dstart_r[-]dstart_l)) (W n[-]U n).
Proof.
 intro.
 split; apply less_leEq.
  apply less_wdr with (y := Length R1 (dIntrvl n) [/]TwoNZ).
   apply less_wdl with (x := [--](Length R1 (dIntrvl n))).
    apply plus_cancel_less with (z := Length R1 (dIntrvl n)).
    rstepl (Zero:R1).
    apply plus_resp_pos.
     apply pos_div_two.
     unfold Length in |- *.
     apply shift_zero_less_minus.
     apply is_interval.
    unfold Length in |- *.
    apply shift_zero_less_minus.
    apply is_interval.
   apply un_op_wd_unfolded.
   apply Length_dIntrvl.
  apply eq_symmetric_unfolded.
  apply U_minus_W.
 apply U_W_lower.
Qed.

(* Two properties of exponentiation in COrdFields *)

Lemma nexp_resp_great_One :
 forall (OF : COrdField) (x : OF), One[<]x -> forall n : nat, One[<=]x[^]n.
Proof.
 intros.
 change (x[^]0[<=]x[^]n) in |- *.
 apply great_nexp_resp_le.
  apply less_leEq; assumption.
 apply le_O_n.
Qed.


Lemma very_weak_binomial :
 forall (OF : COrdField) (x : OF) (n : nat),
 Zero[<]x -> 1 < n -> One[+]nring n[*]x[<](x[+]One)[^]n.
Proof.
 do 3 intro.  intros H H0.
 induction  n as [| n Hrecn].
  apply False_rect.
  apply (lt_n_O 0).
  apply lt_trans with (m := 1).
   apply lt_O_Sn.
  assumption.
 case (le_lt_eq_dec 2 (S n) (lt_le_S 1 (S n) H0)).
  intro.
  cut (One[+]nring n[*]x[<](x[+]One)[^]n).
   intro.
   apply less_wdr with (y := (x[+]One)[^]n[*](x[+]One)).
    apply less_transitive_unfolded with (y := One[+]nring (S n)[*]x[+]nring n[*]x[^]2).
     apply plus_cancel_less with (z := [--](One[+]nring (S n)[*]x)).
     rstepl (Zero:OF).
     rstepr (nring n[*]x[^]2).
     apply mult_resp_pos.
      change (nring (R:=OF) 0[<]nring n) in |- *.
      apply nring_less.
      apply lt_S_n.
      assumption.
     apply pos_square.
     apply Greater_imp_ap.
     assumption.
    apply less_wdl with (x := (One[+]nring n[*]x)[*](x[+]One)).
     apply mult_resp_less.
      assumption.
     apply less_transitive_unfolded with (y := x).
      assumption.
     apply less_plusOne.
    simpl in |- *.
    rational.
   simpl in |- *.
   apply eq_reflexive_unfolded.
  apply Hrecn.
  apply lt_S_n.
  assumption.
 intro H1.
 rewrite <- H1.
 apply less_wdr with (y := One[+]Two[*]x[+]x[^]2).
  apply plus_cancel_less with (z := [--](One[+]Two[*]x)).
  astepl (Zero:OF).
  apply less_wdr with (y := x[^]2).
   apply pos_square.
   apply Greater_imp_ap.
   assumption.
  rational.
 simpl in |- *.
 rational.
Qed.

(* A consequence of Archimedean property -         *)
(* the every basis of definition of e=lim(1+1/n)^n *)

Lemma nexp_resp_Two : forall x : R1, One[<]x -> {M : nat | Two[<]x[^]M}.
Proof.
 intros.
 cut (x[-]One[#]Zero).
  intro H0.
  cut {N : nat | (One[/] x[-]One[//]H0)[<]nring N}.
   intro H1.
   case H1.
   intro N.
   intro.
   exists (S N).
   apply less_transitive_unfolded
     with (y := ((One[/] nring (S N)[//]nringS_ap_zero _ N)[+](One:R1))[^]S N).
    apply less_wdl with (x := (One:R1)[+] nring (S N)[*](One[/] nring (S N)[//]nringS_ap_zero _ N)).
     apply very_weak_binomial.
      apply recip_resp_pos.
      apply pos_nring_S.
     apply lt_n_S.
     apply neq_O_lt.
     apply (nring_ap_zero_imp R1).
     apply Greater_imp_ap.
     apply less_transitive_unfolded with (y := One[/] x[-]One[//]H0).
      apply recip_resp_pos.
      apply shift_zero_less_minus.
      assumption.
     assumption.
    rational.
   apply nexp_resp_less.
     apply le_n_S.
     apply le_O_n.
    apply less_leEq.
    apply less_transitive_unfolded with (y := One:R1).
     apply pos_one.
    apply plus_cancel_less with (z := [--](One:R1)).
    astepl (Zero:R1).
    rstepr ((One:R1)[/] nring (S N)[//]nringS_ap_zero R1 N).
    apply recip_resp_pos.
    apply pos_nring_S.
   apply plus_cancel_less with (z := [--](One:R1)).
   rstepl (One[/] nring (S N)[//]nringS_ap_zero R1 N).
   astepr (x[-]One).
   apply swap_div with (z_ := H0).
     apply pos_nring_S.
    apply shift_zero_less_minus.
    assumption.
   apply less_transitive_unfolded with (y := nring (R:=R1) N).
    assumption.
   apply nring_less_succ.
  apply Archimedes'.         (* Note the use of Archimedean property *)
 apply Greater_imp_ap.
 apply shift_zero_less_minus.
 assumption.
Qed.

Lemma twisted_archimedean :
 forall (n : nat) (x : R1), One[<]x -> {M : nat | nring n[<]x[^]M}.
Proof.
 intros n x H.
 induction  n as [| n Hrecn].
  exists 0.
  simpl in |- *.
  apply pos_one.
 case Hrecn.
 intro M1.
 intros.
 case (nexp_resp_Two x H).
 intro M2.
 intros.
 exists (M1 + M2).
 apply less_transitive_unfolded with (y := x[^]M1[+]One).
  simpl in |- *.
  apply plus_resp_less_leEq.
   assumption.
  apply leEq_reflexive.
 apply less_wdr with (y := x[^]M1[*]x[^]M2).
  apply plus_cancel_less with (z := [--](x[^]M1)).
  apply less_wdl with (x := One:R1).
   apply less_wdr with (y := x[^]M1[*](x[^]M2[-]One)).
    apply leEq_less_trans with (y := x[^]M1[*]One).
     astepr (x[^]M1).
     apply nexp_resp_great_One.
     assumption.
    apply mult_resp_less_lft.
     apply shift_less_minus.
     rstepl (Two:R1).
     assumption.
    apply leEq_less_trans with (y := nring (R:=R1) n).
     change (nring (R:=R1) 0[<=]nring n) in |- *.
     apply nring_leEq.
     apply le_O_n.
    assumption.
   rational.
  rational.
 apply nexp_plus.
Qed.

Lemma B_limit_V :
 forall e : R1,
 Zero[<]e -> {N : nat | forall m : nat, N <= m -> AbsSmall e (V m[-]B)}.
Proof.
 intros e H.
 cut {N : nat | forall m : nat, N <= m -> AbsSmall (e [/]TwoNZ) (V m[-]U m)}.
  intro H0.
  cut {N : nat | forall m : nat, N <= m -> AbsSmall (e [/]TwoNZ) (U m[-]B)}.
   intro H1.
   case H0.
   intro N1.
   intro H2.
   case H1.
   intro N2.
   intro H3.
   exists (N1 + N2).
   intros.
   rstepr (V m[-]U m[+](U m[-]B)).
   rstepl (e [/]TwoNZ[+]e [/]TwoNZ).
   apply AbsSmall_plus.
    apply H2.
    apply le_trans with (m := N1 + N2).
     apply le_plus_l.
    assumption.
   apply H3.
   apply le_trans with (m := N1 + N2).
    apply le_plus_r.
   assumption.
  unfold B in |- *.
  cut (SeqLimit U_as_CauchySeq (Lim U_as_CauchySeq)).
   intro H1.
   red in H1.
   apply H1.
   apply pos_div_two.
   assumption.
  apply Lim_Cauchy.
 (* The Core of the Proof *)
 cut {n : nat | (Two[*](dstart_r[-]dstart_l)[/] e[//]Greater_imp_ap _ e Zero H)[<]nring n}.
  intro H0.
  case H0.
  intro N.
  intros.
  case (twisted_archimedean N (Three [/]TwoNZ)).
   apply mult_cancel_less with (z := Two:R1).
    apply pos_two.
   astepl (Two:R1).
   rstepr (Three:R1).
   apply two_less_three.
  intro M.
  intros.
  exists M.
  intros.
  apply AbsSmall_leEq_trans with (e1 := (Two [/]ThreeNZ)[^]m[*](dstart_r[-]dstart_l)).
   apply less_leEq.
   apply mult_cancel_less with (z := ((Three:R1) [/]TwoNZ)[^]m).
    apply less_leEq_trans with (y := ((Three:R1) [/]TwoNZ)[^]0).
     simpl in |- *.
     apply pos_one.
    apply great_nexp_resp_le.
     apply less_leEq.
     apply mult_cancel_less with (z := Two:R1).
      apply pos_two.
     rstepl (Two:R1).
     rstepr (Three:R1).
     apply two_less_three.
    apply le_O_n.
   apply less_wdl with (x := (Two[^]m[/] Three[^]m[//]nexp_resp_ap_zero m (three_ap_zero R1))[*]
     (dstart_r[-]dstart_l)[*] (Three[^]m[/] Two[^]m[//]nexp_resp_ap_zero m (two_ap_zero R1))).
    rstepl (dstart_r[-]dstart_l).
    apply mult_cancel_less with (z := Two[/] e[//]Greater_imp_ap _ e Zero H).
     apply div_resp_pos.
      assumption.
     apply pos_two.
    apply less_wdl with (x := Two[*](dstart_r[-]dstart_l)[/] e[//]Greater_imp_ap _ e Zero H).
     rstepr (((Three:R1) [/]TwoNZ)[^]m).
     apply less_transitive_unfolded with (y := nring (R:=R1) N).
      assumption.
     apply less_leEq_trans with (y := ((Three:R1) [/]TwoNZ)[^]M).
      assumption.
     apply great_nexp_resp_le.
      apply less_leEq.
      apply mult_cancel_less with (z := Two:R1).
       apply pos_two.
      rstepl (Two:R1).
      astepr (Three:R1).
      apply two_less_three.
     assumption.
    rational.
   apply bin_op_wd_unfolded.
    apply bin_op_wd_unfolded.
     apply eq_symmetric_unfolded.
     apply nexp_distr_div'.
    apply eq_reflexive_unfolded.
   apply eq_symmetric_unfolded.
   apply nexp_distr_div'.
  apply AbsSmall_minus.
  apply AbsSmall_U_V.
 apply Archimedes'.
Qed.


Lemma B_limit_W :
 forall e : R1,
 Zero[<]e -> {N : nat | forall m : nat, N <= m -> AbsSmall e (W m[-]B)}.
Proof.
 intros e H.
 cut {N : nat | forall m : nat, N <= m -> AbsSmall (e [/]TwoNZ) (W m[-]U m)}.
  intro H0.
  cut {N : nat | forall m : nat, N <= m -> AbsSmall (e [/]TwoNZ) (U m[-]B)}.
   intro H1.
   case H0.
   intro N1.
   intros.
   case H1.
   intro N2.
   intros.
   exists (N1 + N2).
   intros.
   rstepr (W m[-]U m[+](U m[-]B)).
   rstepl (e [/]TwoNZ[+]e [/]TwoNZ).
   apply AbsSmall_plus.
    apply a.
    apply le_trans with (m := N1 + N2).
     apply le_plus_l.
    assumption.
   apply a0.
   apply le_trans with (m := N1 + N2).
    apply le_plus_r.
   assumption.
  unfold B in |- *.
  cut (SeqLimit U_as_CauchySeq (Lim U_as_CauchySeq)).
   intro H1.
   red in H1.
   apply H1.
   apply pos_div_two.
   assumption.
  apply Lim_Cauchy.
 (* The Core of the Proof *)
 cut {n : nat | (Two[*](dstart_r[-]dstart_l)[/] e[//]Greater_imp_ap _ e Zero H)[<]nring n}.
  intro H0.
  case H0.
  intro N.
  intros.
  case (twisted_archimedean N (Three [/]TwoNZ)).
   apply mult_cancel_less with (z := Two:R1).
    apply pos_two.
   astepl (Two:R1).
   rstepr (Three:R1).
   apply two_less_three.
  intro M.
  intros.
  exists M.
  intros.
  apply AbsSmall_leEq_trans with (e1 := (Two [/]ThreeNZ)[^]m[*](dstart_r[-]dstart_l)).
   apply less_leEq.
   apply mult_cancel_less with (z := ((Three:R1) [/]TwoNZ)[^]m).
    apply less_leEq_trans with (y := ((Three:R1) [/]TwoNZ)[^]0).
     simpl in |- *.
     apply pos_one.
    apply great_nexp_resp_le.
     apply less_leEq.
     apply mult_cancel_less with (z := Two:R1).
      apply pos_two.
     rstepl (Two:R1).
     rstepr (Three:R1).
     apply two_less_three.
    apply le_O_n.
   apply less_wdl with (x := (Two[^]m[/] Three[^]m[//]nexp_resp_ap_zero m (three_ap_zero R1))[*]
     (dstart_r[-]dstart_l)[*] (Three[^]m[/] Two[^]m[//]nexp_resp_ap_zero m (two_ap_zero R1))).
    rstepl (dstart_r[-]dstart_l).
    apply mult_cancel_less with (z := Two[/] e[//]Greater_imp_ap _ e Zero H).
     apply div_resp_pos.
      assumption.
     apply pos_two.
    apply less_wdl with (x := Two[*](dstart_r[-]dstart_l)[/] e[//]Greater_imp_ap _ e Zero H).
     rstepr (((Three:R1) [/]TwoNZ)[^]m).
     apply less_transitive_unfolded with (y := nring (R:=R1) N).
      assumption.
     apply less_leEq_trans with (y := ((Three:R1) [/]TwoNZ)[^]M).
      assumption.
     apply great_nexp_resp_le.
      apply less_leEq.
      apply mult_cancel_less with (z := Two:R1).
       apply pos_two.
      rstepl (Two:R1).
      astepr (Three:R1).
      apply two_less_three.
     assumption.
    rational.
   apply bin_op_wd_unfolded.
    apply bin_op_wd_unfolded.
     apply eq_symmetric_unfolded.
     apply nexp_distr_div'.
    apply eq_reflexive_unfolded.
   apply eq_symmetric_unfolded.
   apply nexp_distr_div'.
  apply AbsSmall_U_W.
 apply Archimedes'.
Qed.

Lemma W_n_is_upper : forall n : nat, is_upper_bound R1 A (W n).
Proof.
 intros.
 induction  n as [| n Hrecn].
  (* n=O *)
  unfold W in |- *.
  simpl in |- *.
  unfold dstart_r in |- *.
  red in |- *.
  intros x H z H0.
  cut (is_upper_bound R1 A b0).
   intros H1.
   red in H1.
   apply less_transitive_unfolded with (y := b0).
    apply (H1 x H z).
    assumption.
   apply less_plusOne.
  exact Pb0.
 (* n=(S n0) *)
 case (dif_cotrans_strong (dIntrvl n)).
  intro a.
  elim a.
  intros H H0.
  unfold W in |- *.
  simpl in |- *.
  rewrite H0.
  simpl in |- *.
  exact Hrecn.
 intro a.
 elim a.
 intros.
 unfold W in |- *.
 simpl in |- *.
 rewrite b.
 simpl in |- *.
 exact a0.
Qed.

Lemma A_bounds_V_n : forall n : nat, {s' : R1 | A s' | V n[<]s'}.
Proof.
 intro.
 induction  n as [| n Hrecn].
  (* n=0 *)
  unfold V in |- *.
  simpl in |- *.
  exists s.
   apply s_inhabits_A.
  unfold dstart_l in |- *.
  apply shift_minus_less.
  apply less_plusOne.
 (* n=(S n0) *)
 case (dif_cotrans_strong (dIntrvl n)).
  intro a.
  elim a.
  intros H H0.
  unfold V in |- *.
  simpl in |- *.
  rewrite H0.
  simpl in |- *.
  exact H.
 intro a.
 elim a.
 intros H H0.
 unfold V in |- *.
 simpl in |- *.
 rewrite H0.
 simpl in |- *.
 exact Hrecn.
Qed.

Theorem cauchy_gives_lub : l_u_b R1 A.
Proof.
 intros.
 unfold l_u_b in |- *.
 exists B.
 split.
  (* to prove the first condition of l.u.b *)
  red in |- *.
  intros t At.
  intros.
  case (B_limit_W ((t[-]z) [/]TwoNZ)).
   apply pos_div_two.
   apply shift_zero_less_minus.
   assumption.
  intro N.
  intro H0.
  cut (AbsSmall ((t[-]z) [/]TwoNZ) (W N[-]B)).
   intro H1.
   apply plus_cancel_less with (z := (t[-]z) [/]TwoNZ).
   apply less_leEq_trans with (y := W N).
    rstepl (t[-](t[-]z) [/]TwoNZ).
    cut (is_upper_bound R1 A (W N)).
     intro H2.
     red in H2.
     apply (H2 t At).
     apply plus_cancel_less with (z := (t[-]z) [/]TwoNZ[-]t).
     rstepl (Zero:R1).
     rstepr ((t[-]z) [/]TwoNZ).
     apply pos_div_two.
     apply shift_zero_less_minus.
     assumption.
    apply W_n_is_upper.
   apply plus_cancel_leEq_rht with (z := [--]B).
   astepl (W N[-]B).
   rstepr ((t[-]z) [/]TwoNZ).
   elim H1.
   intros H2 H3.
   assumption.
  apply H0.
  constructor.
 (* to prove the second condition of a l.u.b. *)
 intros b' H.
 case (B_limit_V ((B[-]b') [/]TwoNZ)).
  apply pos_div_two.
  apply shift_zero_less_minus.
  assumption.
 intro N.
 intro H0.
 cut (AbsSmall ((B[-]b') [/]TwoNZ) (V N[-]B)).
  intros.
  case (A_bounds_V_n N).
  intro s'.
  set (H2 := True) in *. (* dummy *)
  intros.
  exists s'.
  split.
   assumption.
  apply less_transitive_unfolded with (y := V N).
   apply less_leEq_trans with (y := B[-](B[-]b') [/]TwoNZ).
    apply plus_cancel_less with (z := [--]b').
    astepl (Zero:R1).
    rstepr ((B[-]b') [/]TwoNZ).
    apply pos_div_two.
    apply shift_zero_less_minus.
    assumption.
   apply plus_cancel_leEq_rht with (z := [--]B).
   astepr (V N[-]B).
   rstepl ([--]((B[-]b') [/]TwoNZ)).
   elim H1.
   intros.
   assumption.
  assumption.
 apply H0.
 constructor.
Qed.

End upper_bound_sequence.

End LUBP.
(* end hide *)
