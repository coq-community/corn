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
(* begin hide *)
Require Export CoRN.reals.Q_in_CReals.


(*----- Opaque_algebra.v will be loaded in line 151 -----*)

Lemma or_not_and :
 forall (A : CProp) (B : Prop), Not A \/ ~ B -> Not (A and B).
Proof.
 intros.
 intro H0.
 elim H0.
 intros.
 case H.
  intro H3.
  apply H3.
  assumption.
 intro H3.
 apply H3.
 assumption.
Qed.

Section Interval_definition.
 Variable OF : COrdField.

 Record Interval : Type :=
   {pair_crr :> prodT OF OF; is_interval : fstT pair_crr[<]sndT pair_crr}.

Definition Length (I1 : Interval) : OF := sndT I1[-]fstT I1.

End Interval_definition.

Definition Rat_Interval := Interval Q_as_COrdField.

(* we have this in Q_COrdField... *)
Lemma Qlt_eq_gt_dec' :
 forall q1 q2 : Q_as_COrdField, ((q1[<]q2) or (q2[<]q1)) or (q1[=]q2).
Proof.
 intros.
 case (Q_dec q1 q2); intuition.
Qed.

(*
Lemma ex_informative_on_Q:(P:Q_as_COrdField->Prop)(Ex [q:Q_as_COrdField](P q))
                             ->{q:Q_as_COrdField | (P q)}.
Proof.
 Intro.
 Intro.
 Apply ex_informative.
 Assumption.
Qed.
*)

Section COrdField_extra.


Variable OF : COrdField.




Lemma AbsSmall_pos_reflexive : forall x : OF, ([0][<=]x) -> AbsSmall x x.
Proof.
 intros.
 split.
  apply leEq_transitive with (y := [0]:OF).
   apply inv_cancel_leEq.
   rstepl ([0]:OF).
   rstepr x.
   assumption.
  assumption.
 apply leEq_reflexive.
Qed.

Lemma AbsSmall_neg_reflexive : forall x : OF, ([0][<=]x) -> AbsSmall x [--]x.
Proof.
 intros.
 split.
  apply leEq_reflexive.
 apply leEq_transitive with (y := [0]:OF).
  apply inv_cancel_leEq.
  rstepl ([0]:OF).
  rstepr x.
  assumption.
 assumption.
Qed.


Lemma AbsSmall_subinterval :
 forall a b x y : OF,
 (a[<=]x) -> (a[<=]y) -> (x[<=]b) -> (y[<=]b) -> AbsSmall (b[-]a) (x[-]y).
Proof.
 intros.
 split.
  rstepl (a[+][--]b).
  rstepr (x[+][--]y).
  apply plus_resp_leEq_both.
   assumption.
  apply inv_resp_leEq.
  assumption.
 rstepl (x[+][--]y).
 rstepr (b[+][--]a).
 apply plus_resp_leEq_both.
  assumption.
 apply inv_resp_leEq.
 assumption.
Qed.


End COrdField_extra.


Section Rational_sequence.
Load "Opaque_algebra".  (* WARNING: A file is being loaded *)
Variable R1 : CReals.

Definition start_l (x : R1) := let (N, _) := start_of_sequence _ x in N.


Lemma start_of_sequence2 :
 forall x : R1,
 {q2 : Q_as_COrdField | inj_Q R1 (start_l x)[<]x | x[<]inj_Q R1 q2}.
Proof.
 intro.
 apply (ProjT2 (start_of_sequence _ x)).
Qed.

Definition start_r (x : R1) := let (N, _, _) := start_of_sequence2 x in N.

Lemma start_of_sequence_property :
 forall x : R1, (inj_Q R1 (start_l x)[<]x) and (x[<]inj_Q R1 (start_r x)).
Proof.
 intro.
 unfold start_l, start_r in |- *.
 elim start_of_sequence2; auto.
Qed.


Lemma l_less_r : forall x : R1, start_l x[<]start_r x.
Proof.
 intro.
 apply less_inj_Q with (R1 := R1).
 elim (start_of_sequence_property x).
 apply less_transitive_unfolded.
Qed.


Lemma shrink23 :
 forall q1 q2 : Q_as_COrdField,
 (q1[<]q2) -> q1[+](q2[-]q1) [/]ThreeNZ[<]q2[-](q2[-]q1) [/]ThreeNZ.
Proof.
 intros.
 apply plus_cancel_less with (R := Q_as_COrdField) (z := (q2[-]q1) [/]ThreeNZ).
 rstepl (q2[-](q2[-]q1) [/]ThreeNZ).
 rstepr q2.
 apply plus_cancel_less with (R := Q_as_COrdField) (z := [--]q2).
 rstepr [--]([0]:Q_as_COrdField).
 rstepl [--]((q2[-]q1) [/]ThreeNZ).
 apply inv_resp_less.
 apply mult_cancel_less with (R := Q_as_COrdField) (z := Three:Q_as_COrdField).
  apply pos_nring_S.
 rstepl ([0]:Q_as_COrdField).
 rstepr (q2[-]q1).
 apply shift_zero_less_minus.
 assumption.
Qed.


Lemma shrink13 :
 forall q1 q2 : Q_as_COrdField, (q1[<]q2) -> q1[<]q2[-](q2[-]q1) [/]ThreeNZ.
Proof.
 intros.
 apply less_transitive_unfolded with (q1[+](q2[-]q1) [/]ThreeNZ).
  astepl (q1[+][0]).
  apply plus_resp_less_lft.
  apply div_resp_pos.
   apply pos_three.
  apply shift_zero_less_minus.
  assumption.
 apply shrink23.
 assumption.
Qed.

Lemma shrink24 :
 forall q1 q2 : Q_as_COrdField, (q1[<]q2) -> q1[+](q2[-]q1) [/]ThreeNZ[<]q2.
Proof.
 intros.
 apply less_transitive_unfolded with (q2[-](q2[-]q1) [/]ThreeNZ).
  apply shrink23.
  assumption.
 astepl (q2[+][--]((q2[-]q1) [/]ThreeNZ)).
 astepr (q2[+][0]).
 apply plus_resp_less_lft.
 apply inv_cancel_less.
 rstepl ([0]:Q_as_COrdField).
 rstepr ((q2[-]q1) [/]ThreeNZ).
 apply div_resp_pos.
  apply pos_three.
 apply shift_zero_less_minus.
 assumption.
Qed.


Definition cotrans_analyze :
  forall (x : R1) (q1 q2 : Q_as_COrdField), (q1[<]q2) -> Q_as_COrdField.
Proof.
 intros.
 cut (inj_Q R1 q1[<]inj_Q R1 q2).
  intro H0.
  case (less_cotransitive_unfolded R1 (inj_Q R1 q1) (inj_Q R1 q2) H0 x).
   intro.
   exact q1.
  intro.
  exact q2.
 apply inj_Q_less.
 assumption.
Defined.



Lemma cotrans_analyze_strong :
 forall (q1 q2 : Q_as_COrdField) (x : R1) (H : q1[<]q2),
 ((inj_Q R1 q1[<]x) and (cotrans_analyze x q1 q2 H[=]q1))
 or (x[<]inj_Q R1 q2) and (cotrans_analyze x q1 q2 H[=]q2).
Proof.
 intros.
 unfold cotrans_analyze in |- *.
 elim (less_cotransitive_unfolded R1 (inj_Q R1 q1) (inj_Q R1 q2) (inj_Q_less R1 q1 q2 H) x).
  intros.
  left.
  split.
   assumption.
  algebra.
 intros.
 right.
 split.
  assumption.
 algebra.
Qed.


Definition trichotomy :
  R1 -> Q_as_COrdField -> Q_as_COrdField -> Q_as_COrdField.
Proof.
 intros x q1 q2.
 case (Qlt_eq_gt_dec' q1 q2).
  intro s.
  elim s.
   intro a.
   exact (cotrans_analyze x (q1[+](q2[-]q1) [/]ThreeNZ) (q2[-](q2[-]q1) [/]ThreeNZ) (shrink23 q1 q2 a)).
  intro.
  exact [0].
 intro.
 exact q1.
Defined.


Lemma trichotomy_strong1 :
 forall (q1 q2 : Q_as_COrdField) (x : R1) (H : q1[<]q2),
 ((inj_Q R1 (q1[+](q2[-]q1) [/]ThreeNZ)[<]x)
  and (trichotomy x q1 q2[=]q1[+](q2[-]q1) [/]ThreeNZ))
 or (x[<]inj_Q R1 (q2[-](q2[-]q1) [/]ThreeNZ))
    and (trichotomy x q1 q2[=]q2[-](q2[-]q1) [/]ThreeNZ).
Proof.
 intros.
 unfold trichotomy in |- *.
 elim (Qlt_eq_gt_dec' q1 q2).
  intro y.
  elim y.
   intro y0.
   simpl in |- *.
   apply cotrans_analyze_strong.
  intro.
  apply False_rect.
  generalize b.
  change (Not (q2[<]q1)) in |- *.
  apply less_antisymmetric_unfolded.
  assumption.
 intro.
 elimtype False.
 generalize b.
 change (q1[~=]q2) in |- *.
 apply ap_imp_neq.
 apply less_imp_ap.
 assumption.
Qed.

Notation "( A , B )" := (pairT A B).
Definition if_cotrans : forall (x : R1) (I1 : Rat_Interval), Rat_Interval.
Proof.
 intros.
 case I1.
 intros i pi.
 elim (trichotomy_strong1 (fstT i) (sndT i) x pi).
  intro.
  exact (Build_Interval _ (fstT i[+](sndT i[-]fstT i) [/]ThreeNZ, sndT i)
    (shrink24 (fstT i) (sndT i) pi)).
 intro.
 exact (Build_Interval _ (fstT i, sndT i[-](sndT i[-]fstT i) [/]ThreeNZ)
   (shrink13 (fstT i) (sndT i) pi)).
Defined.



Lemma if_cotrans_strong :
 forall (x : R1) (I1 : Rat_Interval),
 ((inj_Q R1 (fstT I1[+](sndT I1[-]fstT I1) [/]ThreeNZ)[<]x)
  and if_cotrans x I1 =
      Build_Interval _ (fstT I1[+](sndT I1[-]fstT I1) [/]ThreeNZ, sndT I1)
        (shrink24 (fstT I1) (sndT I1) (is_interval _ I1)))
 or (x[<]inj_Q R1 (sndT I1[-](sndT I1[-]fstT I1) [/]ThreeNZ))
    and if_cotrans x I1 =
        Build_Interval _ (fstT I1, sndT I1[-](sndT I1[-]fstT I1) [/]ThreeNZ)
          (shrink13 (fstT I1) (sndT I1) (is_interval _ I1)).
Proof.
 intros.
 case I1.
 intros i pi.
 elim (trichotomy_strong1 (fstT i) (sndT i) x pi).
  intro y.
  elim y.
  intros H H0.
  left.
  split.
   exact H.
  cut (if_cotrans x (Build_Interval Q_as_COrdField i pi) = Build_Interval Q_as_COrdField
    (fstT i[+](sndT i[-]fstT i) [/]ThreeNZ, sndT i) (shrink24 (fstT i) (sndT i) pi)).
   intro H1.
   rewrite H1.
   simpl in |- *.
   reflexivity.
  unfold if_cotrans in |- *.
  apply not_r_cor_rect.
  apply or_not_and.
  right.
  change (trichotomy x (fstT i) (sndT i)[~=]sndT i[-](sndT i[-]fstT i) [/]ThreeNZ) in |- *.
  apply ap_imp_neq.
  astepl (fstT i[+](sndT i[-]fstT i) [/]ThreeNZ).
  apply less_imp_ap.
  apply shrink23.
  assumption.
 intro.
 elim b.
 intros H H0.
 right.
 split.
  exact H.
 cut (if_cotrans x (Build_Interval Q_as_COrdField i pi) = Build_Interval Q_as_COrdField
   (fstT i, sndT i[-](sndT i[-]fstT i) [/]ThreeNZ) (shrink13 (fstT i) (sndT i) pi)).
  intro H1.
  rewrite H1.
  simpl in |- *.
  reflexivity.
 unfold if_cotrans in |- *.
 apply not_l_cor_rect.
 apply or_not_and.
 right.
 change (trichotomy x (fstT i) (sndT i)[~=] (fstT i)[+]((sndT i[-]fstT i) [/]ThreeNZ)) in |- *.
 apply ap_imp_neq.
 astepl (sndT i[-](sndT i[-]fstT i) [/]ThreeNZ).
 apply Greater_imp_ap.
 apply shrink23.
 assumption.
Qed.

Fixpoint Intrvl (x : R1) (n : nat) {struct n} : Rat_Interval :=
  match n with
  | O => Build_Interval _ (start_l x, start_r x) (l_less_r x)
  | S p => if_cotrans x (Intrvl x p)
  end.


Definition G (x : R1) (n : nat) :=
  (fstT (Intrvl x n)[+]sndT (Intrvl x n)) [/]TwoNZ.

Opaque Q_as_CField.

Lemma delta_Intrvl :
 forall (x : R1) (n : nat),
 Length _ (Intrvl x (S n))[=]Two [/]ThreeNZ[*]Length _ (Intrvl x n).
Proof.
 intros.
 case (if_cotrans_strong x (Intrvl x n)).
  intro H.
  elim H.
  intros H0 H1.
  simpl in |- *.
  rewrite H1.
  unfold Length in |- *.
  simpl in |- *.
  rational.
 intro H.
 elim H.
 intros H0 H1.
 simpl in |- *.
 rewrite H1.
 unfold Length in |- *.
 simpl in |- *.
 rational.
Qed.

Lemma Length_Intrvl :
 forall (x : R1) (n : nat),
 Length _ (Intrvl x n)[=](Two [/]ThreeNZ)[^]n[*](start_r x[-]start_l x).
Proof.
 intros.
 induction  n as [| n Hrecn].
  (* n=0 *)
  unfold Length in |- *.
  simpl in |- *.
  rational.
 (* n=(S n0) & induction hypothesis *)
 astepr (Two [/]ThreeNZ[*]((Two [/]ThreeNZ)[^]n[*](start_r x[-]start_l x))).
  astepr (Two [/]ThreeNZ[*]Length Q_as_COrdField (Intrvl x n)).
  apply delta_Intrvl.
 astepr ((Two [/]ThreeNZ)[^]n[*]Two [/]ThreeNZ[*](start_r x[-]start_l x)).
 rational.
Qed.


Lemma Intrvl_inside_l_n :
 forall (x : R1) (m n : nat),
 m <= n -> fstT (Intrvl x m)[<=]fstT (Intrvl x n).
Proof.
 intros.
 induction  n as [| n Hrecn].
  (* n=0 *)
  cut (m = 0).
   intro.
   rewrite H0.
   apply leEq_reflexive.
  symmetry  in |- *.
  apply le_n_O_eq.
  assumption.
 (* n=(S n0) *)
 cut ({m = S n} + {m <= n}).
  intro.
  case H0.
   intro H1.
   rewrite H1.
   apply leEq_reflexive.
  intro.
  apply leEq_transitive with (fstT (Intrvl x n)).
   apply Hrecn.
   assumption.
  case (if_cotrans_strong x (Intrvl x n)).
   intro H2.
   elim H2.
   intros H3 H4.
   change (fstT (Intrvl x n)[<=]fstT (if_cotrans x (Intrvl x n))) in |- *.
   rewrite H4.
   astepl (fstT (Intrvl x n)[+][0]).
   simpl.
   apply (plus_resp_leEq_both Q_as_COrdField).
    apply leEq_reflexive.
   apply less_leEq.
   apply (div_resp_pos Q_as_COrdField).
    apply (pos_three Q_as_COrdField).
   apply (shift_zero_less_minus Q_as_COrdField).
   apply (is_interval Q_as_COrdField).
  intro H2.
  elim H2.
  intros H3 H4.
  change (fstT (Intrvl x n)[<=]fstT (if_cotrans x (Intrvl x n))) in |- *.
  rewrite H4.
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

Lemma Intrvl_inside_r_n :
 forall (x : R1) (m n : nat),
 m <= n -> sndT (Intrvl x n)[<=]sndT (Intrvl x m).
Proof.
 intros.
 induction  n as [| n Hrecn].
  (* n=0 *)
  cut (m = 0).
   intro.
   rewrite H0.
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
  intro.
  apply leEq_transitive with (sndT (Intrvl x n)).
   case (if_cotrans_strong x (Intrvl x n)).
    intro H2.
    elim H2.
    intros H3 H4.
    change (sndT (if_cotrans x (Intrvl x n))[<=]sndT (Intrvl x n)) in |- *.
    rewrite H4.
    apply leEq_reflexive.
   intro H2.
   elim H2.
   intros H3 H4.
   change (sndT (if_cotrans x (Intrvl x n))[<=]sndT (Intrvl x n)) in |- *.
   rewrite H4.
   astepr (sndT (Intrvl x n)[+][0]).
   astepl (sndT (Intrvl x n)[+] [--]((sndT (Intrvl x n)[-]fstT (Intrvl x n)) [/]ThreeNZ)).
   apply plus_resp_leEq_both.
    apply leEq_reflexive.
   apply inv_cancel_leEq.
   astepl ([0]:Q_as_COrdField).
   astepr ((sndT (Intrvl x n)[-]fstT (Intrvl x n)) [/]ThreeNZ).
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


Lemma G_m_n_lower :
 forall (x : R1) (m n : nat), m <= n -> fstT (Intrvl x m)[<]G x n.
Proof.
 intros.
 unfold G in |- *.
 apply leEq_less_trans with (fstT (Intrvl x n)).
  apply Intrvl_inside_l_n.
  assumption.
 apply Smallest_less_Average.
 apply is_interval.
Qed.

Lemma G_m_n_upper :
 forall (x : R1) (m n : nat), m <= n -> G x n[<]sndT (Intrvl x m).
Proof.
 intros.
 unfold G in |- *.
 apply less_leEq_trans with (sndT (Intrvl x n)).
  apply Average_less_Greatest.
  apply is_interval.
 apply Intrvl_inside_r_n.
 assumption.
Qed.

Opaque Q_as_COrdField.

Lemma a_simple_inequality :
 forall m : nat,
 4 <= m ->
 (Two [/]ThreeNZ)[^]m[<]
 (([1]:Q_as_COrdField)[/] nring (S m)[//]nringS_ap_zero _ m).
Proof.
 intros.
 induction  m as [| m Hrecm].
  apply False_rect.
  generalize H.
  change (~ 4 <= 0) in |- *.
  apply le_Sn_O.
 case (le_lt_eq_dec 4 (S m) H).
  intro.
  apply less_transitive_unfolded with (Two [/]ThreeNZ[*]
    (([1]:Q_as_COrdField)[/] nring (S m)[//]nringS_ap_zero _ m)).
   astepl (((Two:Q_as_COrdField) [/]ThreeNZ)[^]m[*]Two [/]ThreeNZ).
   astepl ((Two:Q_as_COrdField) [/]ThreeNZ[*](Two [/]ThreeNZ)[^]m).
   apply mult_resp_less_lft.
    apply Hrecm.
    apply lt_n_Sm_le.
    assumption.
   apply div_resp_pos.
    apply pos_three.
   apply pos_two.
  (* astepl ((Two::Q_as_COrdField)[/]ThreeNZ)[*](Two[/]ThreeNZ)[^]m.
  Apply nexp_Sn with ((Two::Q_as_COrdField)[/]ThreeNZ). *)
  apply mult_cancel_less with ((Three:Q_as_COrdField)[*]nring (S m)[*]nring (S (S m))).
   apply mult_resp_pos.
    apply mult_resp_pos.
     apply pos_three.
    apply pos_nring_S.
   apply pos_nring_S.
  rstepl ((Two:Q_as_COrdField)[*]nring (S (S m))).
  rstepr ((Three:Q_as_COrdField)[*]nring (S m)).
  astepl ((Two:Q_as_COrdField)[*](nring m[+]Two)).
   astepr ((Three:Q_as_COrdField)[*](nring m[+][1])).
   apply plus_cancel_less with ([--]((Two:Q_as_COrdField)[*]nring m[+]Three)).
   rstepl ([1]:Q_as_COrdField).
   rstepr (nring (R:=Q_as_COrdField) m).
   astepl (nring (R:=Q_as_COrdField) 1).
   apply nring_less.
   apply lt_trans with (m := 3).
    constructor.
    constructor.
   apply lt_S_n.
   assumption.
  simpl in |- *.
  rational.
 intro.
 rewrite <- e.
 apply mult_cancel_less with (nring (R:=Q_as_COrdField) 5[*]Three[^]4).
  apply mult_resp_pos.
   apply pos_nring_S.
  rstepr (Three[^]2[*]Three[^]2:Q_as_COrdField).
  apply mult_resp_pos.
   apply pos_square.
   apply nringS_ap_zero.
  apply pos_square.
  apply nringS_ap_zero.
 rstepl (Two[^]4[*]nring (R:=Q_as_COrdField) 5).
 rstepr (Three[^]4:Q_as_COrdField).
 rstepl (nring (R:=Q_as_COrdField) 80).
 rstepr (nring (R:=Q_as_COrdField) 81).
 apply nring_less.
 constructor.
Qed.

Lemma G_conversion_rate2 :
 forall (x : R1) (m n : nat),
 4 <= m ->
 m <= n ->
 AbsSmall (start_r x[-]start_l x[/] nring (S m)[//]nringS_ap_zero _ m)
   (G x m[-]G x n).
Proof.
 intros.
 apply AbsSmall_leEq_trans with (Length _ (Intrvl x m)).
  astepl ((Two [/]ThreeNZ)[^]m[*](start_r x[-]start_l x)).
   rstepr (([1][/] nring (S m)[//]nringS_ap_zero _ m)[*](start_r x[-]start_l x)).
   apply less_leEq.
   apply mult_resp_less.
    apply a_simple_inequality.
    assumption.
   apply shift_zero_less_minus.
   apply l_less_r.
  apply eq_symmetric_unfolded.
  apply Length_Intrvl.
 unfold Length in |- *.
 apply AbsSmall_subinterval; apply less_leEq.
    apply G_m_n_lower.
    constructor.
   apply G_m_n_lower.
   assumption.
  apply G_m_n_upper.
  constructor.
 apply G_m_n_upper.
 assumption.
Qed.

Lemma CS_seq_G : forall x : R1, Cauchy_prop (fun m : nat => G x m).
Proof.
 intros.
 unfold Cauchy_prop in |- *.
 intros e H.
 cut {n : nat | (start_r x[-]start_l x[/] e[//]Greater_imp_ap _ e [0] H)[<]nring n}.
  intro H0.
  case H0.
  intro N.
  intro.
  exists (S (N + 3)).
  intros.
  apply AbsSmall_minus.
  apply AbsSmall_leEq_trans with (start_r x[-]start_l x[/] nring (S (S (N + 3)))[//]
    nringS_ap_zero Q_as_COrdField (S (N + 3))).
   apply less_leEq.
   apply swap_div with (z_ := Greater_imp_ap _ e [0] H).
     apply pos_nring_S.
    assumption.
   apply less_transitive_unfolded with (nring (R:=Q_as_COrdField) N).
    assumption.
   apply nring_less.
   apply le_lt_n_Sm.
   constructor.
   apply le_plus_l.
  apply G_conversion_rate2 with (m := S (N + 3)).
   apply le_n_S.
   apply le_plus_r.
  assumption.
 apply Q_is_archemaedian.  (* Note the use of Q_is_archemaedian *)
Qed.

Definition G_as_CauchySeq (x : R1) :=
  Build_CauchySeq Q_as_COrdField (fun m : nat => G x m) (CS_seq_G x).



Lemma CS_seq_inj_Q_G :
 forall x : R1, Cauchy_prop (fun m : nat => inj_Q R1 (G x m)).
Proof.
 intro.
 change (Cauchy_prop (fun m : nat => inj_Q R1 (CS_seq _ (G_as_CauchySeq x) m))) in |- *.
 apply inj_Q_Cauchy.
Qed.

Definition inj_Q_G_as_CauchySeq (x : R1) :=
  Build_CauchySeq _ (fun m : nat => inj_Q R1 (G x m)) (CS_seq_inj_Q_G x).


Lemma x_in_Intrvl_l :
 forall (x : R1) (n : nat), inj_Q R1 (fstT (Intrvl x n))[<]x.
Proof.
 intros.
 induction  n as [| n Hrecn].
  (* n=0 *)
  simpl in |- *.
  cut ((inj_Q R1 (start_l x)[<]x) and (x[<]inj_Q R1 (start_r x))).
   intro H.
   elim H.
   intros.
   assumption.
  apply start_of_sequence_property.
 (* n= (S n0) *)
 case (if_cotrans_strong x (Intrvl x n)).
  intro H.
  elim H.
  intros H0 H1.
  change (inj_Q R1 (fstT (if_cotrans x (Intrvl x n)))[<]x) in |- *.
  rewrite H1.
  simpl in |- *.
  assumption.
 intro H.
 elim H.
 intros H0 H1.
 change (inj_Q R1 (fstT (if_cotrans x (Intrvl x n)))[<]x) in |- *.
 rewrite H1.
 simpl in |- *.
 assumption.
Qed.

Lemma x_in_Intrvl_r :
 forall (x : R1) (n : nat), x[<]inj_Q R1 (sndT (Intrvl x n)).
Proof.
 intros.
 induction  n as [| n Hrecn].
  (* n=0 *)
  simpl in |- *.
  cut ((inj_Q R1 (start_l x)[<]x) and (x[<]inj_Q R1 (start_r x))).
   intro H.
   elim H.
   intros.
   assumption.
  apply start_of_sequence_property.
 (* n= (S n0) *)
 case (if_cotrans_strong x (Intrvl x n)).
  intro H.
  elim H.
  intros H0 H1.
  change (x[<]inj_Q R1 (sndT (if_cotrans x (Intrvl x n)))) in |- *.
  rewrite H1.
  simpl in |- *.
  assumption.
 intro H.
 elim H.
 intros H0 H1.
 change (x[<]inj_Q R1 (sndT (if_cotrans x (Intrvl x n)))) in |- *.
 rewrite H1.
 simpl in |- *.
 assumption.
Qed.



Lemma G_conversion_rate_resp_x :
 forall (x : R1) (m : nat),
 4 <= m ->
 AbsSmall
   (inj_Q R1 (start_r x[-]start_l x[/] nring (S m)[//]nringS_ap_zero _ m))
   (inj_Q R1 (G x m)[-]x).
Proof.
 intros.
 apply AbsSmall_leEq_trans with (e1 := inj_Q R1 (Length _ (Intrvl x m))).
  apply less_leEq.
  apply inj_Q_less.
  astepl ((Two [/]ThreeNZ)[^]m[*](start_r x[-]start_l x)).
   rstepr (([1][/] nring (S m)[//]nringS_ap_zero _ m)[*](start_r x[-]start_l x)).
   apply mult_resp_less.
    apply a_simple_inequality.
    assumption.
   apply shift_zero_less_minus.
   apply l_less_r.
  apply eq_symmetric_unfolded.
  apply Length_Intrvl.
 unfold Length in |- *.
 astepl (inj_Q R1 (sndT (Intrvl x m))[-]inj_Q R1 (fstT (Intrvl x m))).
 apply AbsSmall_subinterval; apply less_leEq.
    apply inj_Q_less.
    apply G_m_n_lower.
    constructor.
   apply x_in_Intrvl_l.
  apply inj_Q_less.
  apply G_m_n_upper.
  constructor.
 apply x_in_Intrvl_r.
Qed.

Lemma x_is_SeqLimit_G : forall x : R1, SeqLimit (inj_Q_G_as_CauchySeq x) x.
Proof.
 intros.
 unfold SeqLimit in |- *.
 intros e H.
 unfold inj_Q_G_as_CauchySeq in |- *.
 unfold CS_seq in |- *.
 cut {n : nat | (inj_Q R1 (start_r x[-]start_l x)[/] e[//]Greater_imp_ap _ e [0] H)[<] nring n}.
  intro H0.
  case H0.
  intro N.
  intro.
  exists (S (N + 3)).
  intros.
  apply AbsSmall_leEq_trans with (e1 := inj_Q R1 ((start_r x[-]start_l x)[/]nring (S (S (N + 3)))[//]
    nringS_ap_zero Q_as_COrdField (S (N + 3)))).
   apply less_leEq.
   apply less_transitive_unfolded with (y := inj_Q R1
     ((start_r x[-]start_l x)[/]nring (R:=Q_as_COrdField) (S N)[//] nringS_ap_zero _ N)).
    apply inj_Q_less.
    apply mult_cancel_less with (nring (R:=Q_as_COrdField) (S (S (N + 3)))[*]nring (S N)).
     apply mult_resp_pos.
      apply pos_nring_S.
     apply pos_nring_S.
    rstepl ((start_r x[-]start_l x)[*]nring (S N)).
    rstepr ((start_r x[-]start_l x)[*]nring (S (S (N + 3)))).
    apply mult_resp_less_lft.
     apply nring_less.
     apply lt_n_S.
     apply le_lt_n_Sm.
     apply le_plus_l.
    apply shift_zero_less_minus.
    apply l_less_r.
   astepl (inj_Q R1 (start_r x[-]start_l x)[/]nring (S N)[//]nringS_ap_zero R1 N).
    apply swap_div with (z_ := Greater_imp_ap _ e [0] H).
      apply pos_nring_S.
     assumption.
    apply less_transitive_unfolded with (y := nring (R:=R1) N).
     assumption.
    apply nring_less.
    apply le_lt_n_Sm.
    constructor.
   apply mult_cancel_lft with (z := nring (R:=R1) (S N)).
    apply nringS_ap_zero.
   rstepl (inj_Q R1 (start_r x[-]start_l x)).
   astepr (inj_Q R1 (nring (S N))[*] inj_Q R1 ((start_r x[-]start_l x)[/]nring (S N)[//]
     nringS_ap_zero Q_as_COrdField N)).
   astepr (inj_Q R1 (nring (S N)[*] ((start_r x[-]start_l x)[/]nring (S N)[//]
     nringS_ap_zero Q_as_COrdField N))).
   apply inj_Q_wd.
   rational.
  apply AbsSmall_leEq_trans with (e1 := inj_Q R1 ((start_r x[-]start_l x)[/]nring (S m)[//]
    nringS_ap_zero Q_as_COrdField m)).
   apply inj_Q_leEq.
   apply mult_cancel_leEq with (nring (R:=Q_as_COrdField) (S (S (N + 3)))[*]nring (S m)).
    apply mult_resp_pos.
     apply pos_nring_S.
    apply pos_nring_S.
   rstepl ((start_r x[-]start_l x)[*]nring (S (S (N + 3)))).
   rstepr ((start_r x[-]start_l x)[*]nring (S m)).
   apply mult_resp_leEq_lft.
    apply nring_leEq.
    apply le_n_S.
    assumption.
   apply less_leEq.
   apply shift_zero_less_minus.
   apply l_less_r.
  apply G_conversion_rate_resp_x.
  apply le_trans with (m := S (N + 3)).
   apply le_n_S.
   apply le_plus_r.
  assumption.
 apply Archimedes'.
Qed.

End Rational_sequence.

(* end hide *)
