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

Require Export Differentiability.
Set Automatic Introduction.

Section Nth_Derivative.

(**
* Nth Derivative

We now study higher order differentiability.

%\begin{convention}% Throughout this section:
 - [a, b] will be real numbers with [a [<] b];
 - [I] will denote the compact interval [[a,b]];
 - [F, G, H] will denote partial functions.

%\end{convention}%

** Definitions

We first define what we mean by the derivative of order [n] of a function.
*)

Variables a b : IR.
Hypothesis Hab' : a[<]b.

(* begin hide *)
Let Hab := less_leEq _ _ _ Hab'.
Let I := Compact Hab.
(* end hide *)

Fixpoint Derivative_I_n (n : nat) (F Fn : PartIR) {struct n} : CProp :=
  match n with
  | O   => Feq I F Fn
  | S p => {f' : CSetoid_fun (subset (Compact Hab)) IR |
      Derivative_I Hab' F (PartInt f') | Derivative_I_n p (PartInt f') Fn}
  end.

(**
Unlike first order differentiability, for our definition to be
workable it is better to define directly what it means for a function
to be [n] times differentiable instead of quantifying over the
[Derivative_I_n] relation.
*)

Fixpoint Diffble_I_n (n : nat) (F : PartIR) {struct n} : CProp :=
  match n with
  | O   => included I (Dom F)
  | S p => {H : Diffble_I Hab' F | Diffble_I_n p (PartInt (ProjT1 H))}
  end.

End Nth_Derivative.

Implicit Arguments Derivative_I_n [a b].
Implicit Arguments Diffble_I_n [a b].

Section Trivia.

(**
** Trivia

These are the expected extensionality and uniqueness results.
*)

Variables a b : IR.
Hypothesis Hab' : a[<]b.

(* begin hide *)
Let Hab := less_leEq _ _ _ Hab'.
Let I := Compact Hab.
(* end hide *)

Lemma Diffble_I_n_wd : forall n F G,
 Feq I F G -> Diffble_I_n Hab' n F -> Diffble_I_n Hab' n G.
Proof.
 intro.
 induction  n as [| n Hrecn].
  simpl in |- *; unfold Feq in |- *; tauto.
 intros F G H H0.
 elim H0; intros H1 H2; clear H0.
 cut (Diffble_I Hab' G).
  2: apply Diffble_I_wd with F; assumption.
 intro H0.
 exists H0.
 eapply Hrecn.
  2: apply H2.
 unfold I, Hab in |- *; apply Derivative_I_unique with F.
  apply projT2.
 apply Derivative_I_wdl with G.
  apply Feq_symmetric; assumption.
 apply projT2.
Qed.

Lemma Derivative_I_n_wdr : forall n F G H,
 Feq I G H -> Derivative_I_n Hab' n F G -> Derivative_I_n Hab' n F H.
Proof.
 intro.
 induction  n as [| n Hrecn]; intros F G H H0 H1.
  simpl in |- *; simpl in H1.
  apply Feq_transitive with G; assumption.
 elim H1; intros f' H2 H3.
 exists f'; auto.
 apply Hrecn with G; assumption.
Qed.

Lemma Derivative_I_n_wdl : forall n F G H,
 Feq I F G -> Derivative_I_n Hab' n F H -> Derivative_I_n Hab' n G H.
Proof.
 intro.
 induction  n as [| n Hrecn]; intros F G H H0 H1.
  simpl in |- *; simpl in H1.
  apply Feq_transitive with F.
   apply Feq_symmetric; assumption.
  auto.
 elim H1; intros f' H2 H3.
 exists f'; auto.
 apply Derivative_I_wdl with F; assumption.
Qed.

Lemma Derivative_I_n_unique : forall n F G H,
 Derivative_I_n Hab' n F G -> Derivative_I_n Hab' n F H -> Feq I G H.
Proof.
 intro.
 induction  n as [| n Hrecn]; intros F G H H0 H1.
  simpl in H0, H1.
  unfold I in |- *; apply Feq_transitive with F.
   apply Feq_symmetric; assumption.
  auto.
 elim H0; intros g' H2 H3.
 elim H1; intros h' H4 H5.
 apply Hrecn with (PartInt g').
  assumption.
 apply Derivative_I_n_wdl with (PartInt h').
  2: assumption.
 unfold I, Hab in |- *; apply Derivative_I_unique with F; assumption.
Qed.

End Trivia.

Section Basic_Results.

(**
** Basic Results

We now explore the concept of [n] times differentiability.  Notice
that, unlike the first order case, we do not pay so much attention to
the relation of [n] times derivative, but focus rather on the
definition of [Diffble_I_n].
*)

Variables a b : IR.
Hypothesis Hab' : a[<]b.

(* begin hide *)
Let Hab := less_leEq _ _ _ Hab'.
Let I := Compact Hab.
(* end hide *)

(**
We begin by showing that having a higher order derivative implies being differentiable.
*)

Lemma Diffble_I_n_imp_diffble : forall n : nat,
 0 < n -> forall F : PartIR, Diffble_I_n Hab' n F -> Diffble_I Hab' F.
Proof.
 intros n H F.
 rewrite (S_pred n 0);auto. simpl. intro H0. simpl in H0.
 inversion_clear H0; assumption.
Qed.

Lemma deriv_n_imp_diffble : forall n : nat, 0 < n ->
 forall F F' : PartIR, Derivative_I_n Hab' n F F' -> Diffble_I Hab' F.
Proof.
 simple destruct n.
  intros; elimtype False; inversion H.
 clear n; intros n H F F' H0.
 elim H0; clear H0; intros f'' H0 H1.
 exists f''; assumption.
Qed.

(**
If a function is [n] times differentiable then it is also [m] times differentiable for every [m] less or equal than [n].
*)

Lemma le_imp_Diffble_I : forall m n : nat, m <= n ->
 forall F, Diffble_I_n Hab' n F -> Diffble_I_n Hab' m F.
Proof.
 intros m n H F H0.
 induction  n as [| n Hrecn].
  cut (m = 0); [ intro | auto with arith ].
  rewrite H1; simpl in |- *; tauto.
 elim (le_lt_eq_dec _ _ H); intro H2.
  2: rewrite H2; assumption.
 apply Hrecn.
  auto with arith.
 elim H0; intros Hf Hf'.
 clear Hf' Hf H2 Hrecn H.
 generalize H0.
 generalize F.
 clear H0 F; induction  n as [| n Hrecn]; intros.
  simpl in |- *; apply diffble_imp_inc.
  exact (Diffble_I_n_imp_diffble _ (lt_n_Sn 0) F H0).
 simpl in |- *.
 elim H0; intros Hf Hf'.
 exists Hf.
 apply Hrecn.
 assumption.
Qed.

(**
The next result consolidates our intuition that a function is [n]
times differentiable if we can build from it a chain of [n]
derivatives.
*)

Lemma Diffble_I_imp_le : forall n, 0 < n -> forall F F',
 Diffble_I_n Hab' n F -> Derivative_I Hab' F F' -> Diffble_I_n Hab' (pred n) F'.
Proof.
 simple destruct n.
  intros; elimtype False; inversion H.
 clear n; intros n H F F' H0 H1.
 elim H0; intros f'' Hf''.
 simpl in |- *.
 eapply Diffble_I_n_wd.
  2: apply Hf''.
 apply Derivative_I_unique with F.
  apply projT2.
 assumption.
Qed.

(**
As expected, an [n] times differentiable in [[a,b]] function must be
defined in that interval.
*)

Lemma Diffble_I_n_imp_inc : forall n F,
 Diffble_I_n Hab' n F -> included (Compact Hab) (Dom F).
Proof.
 intros n F H; induction  n as [| n Hrecn].
  simpl in H; Included.
 apply Hrecn.
 exact (le_imp_Diffble_I _ _ (le_n_Sn n) _ H).
Qed.

(**
Also, the notions of derivative and differentiability are related as expected.
*)

Lemma Diffble_I_n_imp_deriv_n : forall n F, Diffble_I_n Hab' n F ->
 {f' : CSetoid_fun (subset (Compact Hab)) IR | Derivative_I_n Hab' n F (PartInt f')}.
Proof.
 intro; induction  n as [| n Hrecn].
  intros F H.
  exists (IntPartIR (Diffble_I_n_imp_inc _ _ H)).
  simpl in |- *; simpl in H.
  FEQ.
 intros F H.
 elim H; intros H1 H2.
 elim (Hrecn _ H2); intros f' Hf'.
 exists f'.
 simpl in |- *.
 exists (ProjT1 H1).
  apply projT2.
 assumption.
Qed.

Lemma deriv_n_imp_Diffble_I_n : forall n F F',
 Derivative_I_n Hab' n F F' -> Diffble_I_n Hab' n F.
Proof.
 intro; induction  n as [| n Hrecn]; intros F F' H.
  simpl in |- *; simpl in H.
  elim H; intros.
  elim b0; auto.
 simpl in |- *.
 elim H; intros f' H0 H1.
 cut (Diffble_I Hab' F); [ intro H2 | exists f'; assumption ].
 exists H2.
 apply Hrecn with F'.
 eapply Derivative_I_n_wdl.
  2: apply H1.
 apply Derivative_I_unique with F.
  assumption.
 apply projT2.
Qed.

(**
From this we can prove that if [F] has an nth order derivative in
[[a,b]] then both [F] and its derivative are defined in that interval.
*)

Lemma Derivative_I_n_imp_inc : forall n F F',
 Derivative_I_n Hab' n F F' -> included I (Dom F).
Proof.
 intros; apply Diffble_I_n_imp_inc with n.
 apply deriv_n_imp_Diffble_I_n with F'; assumption.
Qed.

Lemma Derivative_I_n_imp_inc' : forall n F F',
 Derivative_I_n Hab' n F F' -> included I (Dom F').
Proof.
 intro; induction  n as [| n Hrecn]; intros F F' H.
  simpl in |- *; simpl in H.
  elim H; intros H0 H1; elim H1; auto.
 elim H; intros f' H0 H1.
 apply Hrecn with (PartInt f').
 assumption.
Qed.

Section aux.

(**
First order differentiability is just a special case.
*)

(* begin show *)
Variable F : PartIR.
Hypothesis diffF : Diffble_I Hab' F.
Hypothesis diffFn : Diffble_I_n Hab' 1 F.
(* end show *)

Lemma deriv_1_deriv : Feq I
 (PartInt (ProjT1 diffF)) (PartInt (ProjT1 (Diffble_I_n_imp_deriv_n _ _ diffFn))).
Proof.
 intros.
 simpl in |- *.
 unfold I, Hab in |- *; apply Derivative_I_unique with F.
  apply projT2.
 cut (Derivative_I_n Hab' 1 F (PartInt (ProjT1 (Diffble_I_n_imp_deriv_n 1 F diffFn)))).
  2: apply projT2.
 intro H.
 elim H; intros f' H0 H1.
 apply Derivative_I_wdr with (PartInt f'); assumption.
Qed.

Lemma deriv_1_deriv' : forall (x : subset I),
 ProjT1 diffF x [=] ProjT1 (Diffble_I_n_imp_deriv_n _ _ diffFn) x.
Proof.
 intros.
 elim deriv_1_deriv; intros H H1.
 elim H1; intros H0 H2.
 simpl in H2. clear H0 H1.
 generalize (H2 (scs_elem _ _ x) (scs_prf _ _ x) (scs_prf _ _ x) (scs_prf _ _ x)).
 intro H0.
 eapply eq_transitive_unfolded.
  eapply eq_transitive_unfolded.
   2: apply H0.
  apply csf_wd_unfolded.
  cut (scs_elem _ _ x [=] scs_elem _ _ x).
   case x; simpl in |- *; auto.
  algebra.
 apply csf_wd_unfolded.
 cut (scs_elem _ _ x [=] scs_elem _ _ x).
  case x; simpl in |- *; auto.
 algebra.
Qed.

End aux.

(**
As usual, nth order derivability is preserved by shrinking the interval.
*)

Lemma included_imp_deriv_n : forall n c d Hcd F F',
 included (Compact (less_leEq _ c d Hcd)) (Compact (less_leEq _ a b Hab')) ->
 Derivative_I_n Hab' n F F' -> Derivative_I_n Hcd n F F'.
Proof.
 intro; induction  n as [| n Hrecn]; simpl in |- *; intros c d Hcd F F' H H0.
  apply included_Feq with (Compact (less_leEq _ _ _ Hab')); auto.
 elim H0; intros f' H1 H2.
 exists (IntPartIR (F:=(Frestr (F:=PartInt f') (compact_wd _ _ _) H)) (included_refl _ _)).
  apply Derivative_I_wdr with (PartInt f').
   FEQ.
   simpl in |- *; apply csf_wd_unfolded; simpl in |- *; algebra.
  apply included_imp_deriv with (Hab := Hab'); auto.
 apply Derivative_I_n_wdl with (PartInt f').
  FEQ.
  simpl in |- *; apply csf_wd_unfolded; simpl in |- *; algebra.
 auto.
Qed.

Lemma included_imp_diffble_n : forall n c d Hcd F,
 included (Compact (less_leEq _ c d Hcd)) (Compact (less_leEq _ a b Hab')) ->
 Diffble_I_n Hab' n F -> Diffble_I_n Hcd n F.
Proof.
 intro; induction  n as [| n Hrecn]; simpl in |- *; intros c d Hcd F H H0.
  apply included_trans with (Compact (less_leEq _ _ _ Hab')); Included.
 elim H0; intros f' HF.
 exists (included_imp_diffble _ _ _ _ _ _ _ H f').
 apply Diffble_I_n_wd with (PartInt (ProjT1 f')).
  apply Derivative_I_unique with F.
   apply included_imp_deriv with (Hab := Hab').
    auto.
   apply projT2.
  apply projT2.
 auto.
Qed.

(**
And finally we have an addition rule for the order of the derivative.
*)

Lemma Derivative_I_n_plus : forall n m k F G H, Derivative_I_n Hab' m F G ->
 Derivative_I_n Hab' n G H -> k = m + n -> Derivative_I_n Hab' k F H.
Proof.
 do 2 intro.
 induction  m as [| m Hrecm]; intros k F G H H0 H1 H2; rewrite H2.
  simpl in |- *.
  apply Derivative_I_n_wdl with G.
   elim H0; clear H0; intros H3 H4.
   elim H4; clear H4; intros H0 H5.
   apply Derivative_I_n_unique with 0 G.
    simpl in |- *; apply Feq_reflexive; auto.
   simpl in |- *; FEQ; algebra.
  auto.
 elim H0; intros F' H3 H4.
 exists F'; auto.
 apply Hrecm with G; auto.
Qed.

End Basic_Results.

Section More_Results.

Variables a b : IR.
Hypothesis Hab' : a[<]b.

(* begin hide *)
Let Hab := less_leEq _ _ _ Hab'.
Let I := Compact Hab.
(* end hide *)

(**
** The Nth Derivative

We now define an operator that returns an nth order derivative of an
n-times differentiable function.  This is analogous to the quantifier
elimination which we would get if we had defined nth differentiability
as an existential quantification of the nth derivative relation.
*)

Definition n_deriv_I n F (H : Diffble_I_n Hab' n F) : PartIR.
Proof.
 revert F H; induction  n as [| n Hrecn].
  intros.
  simpl in H.
  apply (FRestr H).
 intros F H.
 cut (Diffble_I Hab' F). intro H0.
  set (f' := ProjT1 H0) in *.
  cut (Diffble_I_n Hab' n (PartInt f')).
   intro H1.
   apply (Hrecn _ H1).
  cut (n = pred (S n)); [ intro | simpl in |- *; reflexivity ].
  rewrite H1.
  apply Diffble_I_imp_le with F.
    apply lt_O_Sn.
   assumption.
  unfold f' in |- *; apply projT2.
 apply Diffble_I_n_imp_diffble with (S n).
  apply lt_O_Sn.
 assumption.
Defined.

(**
This operator is well defined and works as expected.
*)

Lemma n_deriv_I_wd : forall n F G Hf Hg,
 Feq I F G -> Feq I (n_deriv_I n F Hf) (n_deriv_I n G Hg).
Proof.
 intro; induction  n as [| n Hrecn]; intros F G Hf Hg H.
  elim H; clear H; intros H H0.
  elim H0; clear H0; intros H2 H1.
  unfold I in |- *; simpl in |- *; FEQ.
  simpl in |- *; apply H1; auto.
 simpl in |- *.
 apply Hrecn.
 unfold I, Hab in |- *; apply Derivative_I_unique with F.
  apply projT2.
 apply Derivative_I_wdl with G.
  apply Feq_symmetric; assumption.
 apply projT2.
Qed.

Lemma n_deriv_lemma : forall n F H, Derivative_I_n Hab' n F (n_deriv_I n F H).
Proof.
 intro; induction  n as [| n Hrecn]; intros.
  simpl in |- *; simpl in H; FEQ.
 elim H; intros Hf Hf'.
 exists (ProjT1 Hf).
  apply projT2.
 simpl in |- *.
 cut (Diffble_I_n Hab' n (PartInt (ProjT1 Hf))). intro H0.
  apply Derivative_I_n_wdr with (n_deriv_I _ _ H0).
   2: apply Hrecn.
  apply n_deriv_I_wd.
  unfold I, Hab in |- *; apply Derivative_I_unique with F.
   apply projT2.
  apply projT2.
 elim H; intros.
 eapply Diffble_I_n_wd.
  2: apply p.
 apply Derivative_I_unique with F; apply projT2.
Qed.

Lemma n_deriv_inc : forall n F H, included (Compact Hab) (Dom (n_deriv_I n F H)).
Proof.
 intros; simpl in |- *.
 unfold I, Hab in |- *; apply Derivative_I_n_imp_inc' with n F.
 apply n_deriv_lemma.
Qed.

Lemma n_deriv_inc' : forall n Hab F H, included (Dom (n_deriv_I n F H)) (compact a b Hab).
Proof.
 intro; induction  n as [| n Hrecn]; intros; simpl in |- *; Included.
Qed.

(**
Some basic properties of this operation.
*)

Lemma n_Sn_deriv : forall n F H HS,
 Derivative_I Hab' (n_deriv_I n F H) (n_deriv_I (S n) F HS).
Proof.
 intro; induction  n as [| n Hrecn].
  intros.
  apply Derivative_I_wdl with F.
   FEQ.
  apply Derivative_I_wdr with (PartInt (ProjT1 (Diffble_I_n_imp_diffble _ _ _ _ (lt_O_Sn 0) _ HS))).
   apply eq_imp_Feq.
     Included.
    Included.
   intros; simpl in |- *; apply csf_wd_unfolded; simpl in |- *; algebra.
  apply projT2.
 intro.
 cut {p : nat | p = S n}.
  intro H; elim H; intros p H0.
  pattern (S n) at 2 4 in |- *; rewrite <- H0.
  intros.
  elim H1; intros H0' H0''; clear H1.
  elim HS; intros H1' H1''; clear HS.
  cut (Diffble_I_n Hab' n (PartInt (ProjT1 H1'))).
   intro H1'''.
   apply Derivative_I_wdl with (n_deriv_I _ _ H1''').
    2: apply Derivative_I_wdr with (n_deriv_I _ _ H1'').
     simpl in |- *; apply n_deriv_I_wd.
     unfold I, Hab in |- *; apply Derivative_I_unique with F.
      apply projT2.
     apply projT2.
    simpl in |- *; apply n_deriv_I_wd.
    unfold I, Hab in |- *; apply Derivative_I_unique with F.
     apply projT2.
    apply projT2.
   generalize H1''.
   rewrite H0.
   intro.
   apply Hrecn.
  generalize H1''; clear H1''.
  rewrite H0; intro.
  apply le_imp_Diffble_I with (S n); [ auto with arith | assumption ].
 exists (S n); auto.
Qed.

Lemma n_deriv_plus : forall m n F H H',
 Derivative_I_n Hab' m (n_deriv_I n F H) (n_deriv_I (m + n) F H').
Proof.
 intro; induction  m as [| m Hrecm].
  simpl in |- *.
  intros.
  apply n_deriv_I_wd.
  unfold I in |- *; apply Feq_reflexive.
  exact (Diffble_I_n_imp_inc _ _ _ _ _ H).
 intros.
 simpl in |- *.
 cut (Diffble_I_n Hab' (S n) F).
  intro H0.
  exists (IntPartIR (n_deriv_inc _ _ H0)).
   eapply Derivative_I_wdr.
    2: apply n_Sn_deriv with (HS := H0).
   FEQ.
   apply n_deriv_inc.
  cut (Diffble_I_n Hab' (m + n)
    (PartInt (ProjT1 (Diffble_I_n_imp_diffble _ _ _ (S n) (lt_O_Sn n) F H0)))).
   intro H1.
   eapply Derivative_I_n_wdr.
    2: eapply Derivative_I_n_wdl.
     3: apply Hrecm with (H' := H1).
    apply n_deriv_I_wd.
    unfold I, Hab in |- *; apply Derivative_I_unique with F.
     apply projT2.
    apply projT2.
   FEQ.
    apply n_deriv_inc.
   simpl in |- *; algebra.
  elim H'; intros.
  eapply Diffble_I_n_wd.
   2: apply p.
  apply Derivative_I_unique with F.
   apply projT2.
  apply projT2.
 apply le_imp_Diffble_I with (S m + n).
  simpl in |- *; rewrite plus_comm; auto with arith.
 assumption.
Qed.

End More_Results.

Section More_on_n_deriv.

(**
Some not so basic properties of this operation (needed in rather specific situations).
*)

Lemma n_deriv_I_wd' : forall n a b Hab a' b' Hab' F H H' x y, x [=] y ->
 Compact (less_leEq _ _ _ Hab) x -> Compact (less_leEq _ _ _ Hab') y ->
 Diffble_I_n (Min_less_Max _ _ a' b' Hab) n F -> forall Hx Hy,
 n_deriv_I a b Hab n F H x Hx [=] n_deriv_I a' b' Hab' n F H' y Hy.
Proof.
 intros n a b Hab a' b' Hab' F H H' x y H0 H1 H2 H3 Hx Hy.
 cut (included (Compact (less_leEq _ _ _ Hab)) (Dom (n_deriv_I _ _ _ _ _ H3))).
  intro H4.
  cut (included (Compact (less_leEq _ _ _ Hab')) (Dom (n_deriv_I _ _ _ _ _ H3))).
   intro H5.
   apply eq_transitive_unfolded with (Part (FRestr H5) y H2).
    apply eq_transitive_unfolded with (Part (FRestr H4) x H1).
     apply Feq_imp_eq with (Compact (less_leEq _ _ _ Hab)).
      apply Derivative_I_n_unique with n F.
       apply n_deriv_lemma.
      apply Derivative_I_n_wdr with (n_deriv_I _ _ _ _ _ H3).
       FEQ.
      apply included_imp_deriv_n with (Hab' := Min_less_Max a b a' b' Hab).
       intros x0 H6.
       elim H6; clear H6; intros H7 H8; split.
        apply leEq_transitive with a.
         apply Min_leEq_lft.
        auto.
       apply leEq_transitive with b.
        auto.
       apply lft_leEq_Max.
      apply n_deriv_lemma.
     auto.
    simpl in |- *; algebra.
   apply eq_symmetric_unfolded.
   apply Feq_imp_eq with (Compact (less_leEq _ _ _ Hab')).
    apply Derivative_I_n_unique with n F.
     apply n_deriv_lemma.
    apply Derivative_I_n_wdr with (n_deriv_I _ _ _ _ _ H3).
     FEQ.
    apply included_imp_deriv_n with (Hab' := Min_less_Max a b a' b' Hab).
     intros x0 H6.
     elim H6; clear H6; intros H7 H8; split.
      apply leEq_transitive with a'.
       apply Min_leEq_rht.
      auto.
     apply leEq_transitive with b'.
      auto.
     apply rht_leEq_Max.
    apply n_deriv_lemma.
   auto.
  intros x0 H5.
  apply n_deriv_inc.
  elim H5; clear H5; intros H6 H7; split.
   apply leEq_transitive with a'.
    apply Min_leEq_rht.
   auto.
  apply leEq_transitive with b'.
   auto.
  apply rht_leEq_Max.
 intros x0 H4.
 apply n_deriv_inc.
 elim H4; clear H4; intros H5 H6; split.
  apply leEq_transitive with a.
   apply Min_leEq_lft.
  auto.
 apply leEq_transitive with b.
  auto.
 apply lft_leEq_Max.
Qed.

Lemma n_deriv_I_wd'' : forall n a b Hab Hab' F H H' x y, x [=] y ->
 Compact (less_leEq _ _ _ Hab) x -> Compact (less_leEq _ _ _ Hab) y ->
 forall Hx Hy, n_deriv_I a b Hab n F H x Hx [=] n_deriv_I a b Hab' n F H' y Hy.
Proof.
 intros n a b Hab Hab' F H H' x y H0 H1 H2 Hx Hy.
 apply n_deriv_I_wd'.
    algebra.
   auto.
  auto.
 apply included_imp_diffble_n with (Hab' := Hab).
  2: auto.
 intros x0 H3.
 elim H3; clear H3; intros H4 H5; split.
  eapply leEq_wdl.
   apply H4.
  apply Min_id.
 eapply leEq_wdr.
  apply H5.
 apply Max_id.
Qed.

Lemma n_deriv_I_strext' : forall n a b Hab a' b' Hab' F H H' x y,
 Compact (less_leEq _ _ _ Hab) x -> Compact (less_leEq _ _ _ Hab') y ->
 Diffble_I_n (Min_less_Max _ _ a' b' Hab) n F -> (forall Hx Hy,
 n_deriv_I a b Hab n F H x Hx [#] n_deriv_I a' b' Hab' n F H' y Hy) -> x [#] y.
Proof.
 intros n a b Hab a' b' Hab' F H H' x y H0 H1 H2 H3.
 cut (Compact (less_leEq _ _ _ (Min_less_Max a b a' b' Hab)) x). intro H4.
  cut (Compact (less_leEq _ _ _ (Min_less_Max a b a' b' Hab)) y). intro H5.
   apply pfstrx with (n_deriv_I _ _ _ _ _ H2) (n_deriv_inc _ _ _ _ _ H2 _ H4)
     (n_deriv_inc _ _ _ _ _ H2 _ H5).
   apply ap_wdr_unfolded with (Part (n_deriv_I _ _ _ _ _ H') y (n_deriv_inc _ _ _ _ _ H' y H1)).
    apply ap_wdl_unfolded with (Part (n_deriv_I _ _ _ _ _ H) x (n_deriv_inc _ _ _ _ _ H x H0)).
     auto.
    apply Feq_imp_eq with (Compact (less_leEq _ _ _ Hab)).
     apply Derivative_I_n_unique with n F.
      apply n_deriv_lemma.
     apply included_imp_deriv_n with (Hab' := Min_less_Max a b a' b' Hab).
      intros x0 H6.
      elim H6; clear H6; intros H7 H8; split.
       apply leEq_transitive with a.
        apply Min_leEq_lft.
       auto.
      apply leEq_transitive with b.
       auto.
      apply lft_leEq_Max.
     apply n_deriv_lemma.
    auto.
   apply Feq_imp_eq with (Compact (less_leEq _ _ _ Hab')).
    apply Derivative_I_n_unique with n F.
     apply n_deriv_lemma.
    apply included_imp_deriv_n with (Hab' := Min_less_Max a b a' b' Hab).
     intros x0 H6.
     elim H6; clear H6; intros H7 H8; split.
      apply leEq_transitive with a'.
       apply Min_leEq_rht.
      auto.
     apply leEq_transitive with b'.
      auto.
     apply rht_leEq_Max.
    apply n_deriv_lemma.
   auto.
  elim H1; clear H1; intros H7 H8; split.
   apply leEq_transitive with a'.
    apply Min_leEq_rht.
   auto.
  apply leEq_transitive with b'.
   auto.
  apply rht_leEq_Max.
 red in |- *; intros.
 inversion_clear H0; split.
  apply leEq_transitive with a.
   apply Min_leEq_lft.
  auto.
 apply leEq_transitive with b.
  auto.
 apply lft_leEq_Max.
Qed.

End More_on_n_deriv.
