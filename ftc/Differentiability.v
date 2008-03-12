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

Require Export PartInterval.
Require Export DerivativeOps.

Section Definitions.

(**
* Differentiability

We will now use our work on derivatives to define a notion of
differentiable function and prove its main properties.

%\begin{convention}% Throughout this section, [a,b] will be real
numbers with [a [<] b], [I] will denote the interval [[a,b]]
and [F,G,H] will be differentiable functions.
%\end{convention}%

Usually a function [F] is said to be differentiable in a proper
compact interval [[a,b]] if there exists another function [F']
such that [F'] is a derivative of [F] in that interval.  There is a
problem in formalizing this definition, as we pointed out earlier on,
which is that if we simply write it down as is we are not able to get
such a function [F'] from a hypothesis that [F] is differentiable.

However, it turns out that this is not altogether the best definition
for the following reason: if we say that [F] is differentiable in
[[a,b]], we mean that there is a partial function [F'] which is
defined in [[a,b]] and satisfies a certain condition in that
interval but nothing is required of the behaviour of the function
outside [[a,b]].  Thus we can argue that, from a mathematical
point of view, the [F'] that we get eliminating a hypothesis of
differentiability should be defined exactly on that interval.  If we
do this, we can quantify over the set of setoid functions in that
interval and eliminate the existencial quantifier without any
problems.
*)

Definition Diffble_I (a b : IR) (Hab : a [<] b) (F : PartIR) :=
 {f' : CSetoid_fun (subset (Compact (less_leEq _ _ _ Hab))) IR |
  Derivative_I Hab F (PartInt f')}.

End Definitions.

Implicit Arguments Diffble_I [a b].

Section Local_Properties.

(**
From this point on, we just prove results analogous to the ones for derivability.

A function differentiable in [[a,b]] is differentiable in every proper compact subinterval of [[a,b]].
*)

Lemma included_imp_diffble : forall a b Hab c d Hcd F,
 included (compact c d (less_leEq _ _ _ Hcd)) (compact a b (less_leEq _ _ _ Hab)) ->
 Diffble_I Hab F -> Diffble_I Hcd F.
intros a b Hab c d Hcd F H H0.
elim H0; clear H0; intros f' derF.
exists
 (IntPartIR (F:=(Frestr (F:=PartInt f') (compact_wd _ _ _) H))
    (included_refl _ _)).
apply Derivative_I_wdr with (PartInt f').
FEQ.
simpl in |- *; apply csf_wd_unfolded; simpl in |- *; algebra.
exact (included_imp_deriv _ _ _ _ _ _ _ _ H derF).
Qed.

(**
A function differentiable in an interval is everywhere defined in that interval.
*)

Variables a b : IR.
Hypothesis Hab' : a [<] b.

(* begin hide *)
Let Hab := less_leEq _ _ _ Hab'.
Let I := Compact Hab.
(* end hide *)

Lemma diffble_imp_inc : forall F, Diffble_I Hab' F -> included I (Dom F).
intros F H.
inversion_clear H.
unfold I, Hab in |- *; Included.
Qed.

(**
If a function has a derivative in an interval then it is differentiable in that interval.
*)

Lemma deriv_imp_Diffble_I : forall F F', Derivative_I Hab' F F' -> Diffble_I Hab' F.
intros F F' H.
exists (IntPartIR (derivative_imp_inc' _ _ _ _ _ H)).
apply Derivative_I_wdr with F'.
apply int_part_int.
assumption.
Qed.

End Local_Properties.

Hint Resolve diffble_imp_inc: included.

Section Operations.

(**
All the algebraic results carry on.
*)

Variables a b : IR.
Hypothesis Hab' : a [<] b.

(* begin hide *)
Let Hab := less_leEq _ _ _ Hab'.
Let I := Compact Hab.
(* end hide *)

Section Constants.

Lemma Diffble_I_const : forall c : IR, Diffble_I Hab' [-C-]c.
intros.
exists (IConst (Hab:=Hab) Zero).
apply Derivative_I_wdr with ( [-C-]Zero:PartIR).
apply part_int_const.
Deriv.
Qed.

Lemma Diffble_I_id : Diffble_I Hab' FId.
exists (IConst (Hab:=Hab) One).
apply Derivative_I_wdr with ( [-C-]One:PartIR).
apply part_int_const.
Deriv.
Qed.

End Constants.

Section Well_Definedness.

Variables F H : PartIR.

Hypothesis diffF : Diffble_I Hab' F.

Lemma Diffble_I_wd : Feq (Compact Hab) F H -> Diffble_I Hab' H.
intro H0.
exists (ProjT1 diffF).
eapply Derivative_I_wdl.
apply H0.
apply projT2.
Qed.

End Well_Definedness.

Variables F G : PartIR.

Hypothesis diffF : Diffble_I Hab' F.
Hypothesis diffG : Diffble_I Hab' G.

Lemma Diffble_I_plus : Diffble_I Hab' (F{+}G).
elim diffF; intros F' derF.
elim diffG; intros G' derG.
exists (IPlus F' G').
eapply Derivative_I_wdr.
apply part_int_plus with (F := PartInt F') (G := PartInt G').
apply Feq_reflexive; Included.
apply Feq_reflexive; Included.
Deriv.
Qed.

Lemma Diffble_I_inv : Diffble_I Hab' {--}F.
elim diffF; intros F' derF.
exists (IInv F').
eapply Derivative_I_wdr.
apply part_int_inv with (F := PartInt F').
apply Feq_reflexive; Included.
Deriv.
Qed.

Lemma Diffble_I_mult : Diffble_I Hab' (F{*}G).
elim diffF; intros F' derF.
elim diffG; intros G' derG.
exists
 (IPlus (IMult (IntPartIR (diffble_imp_inc _ _ _ _ diffF)) G')
    (IMult F' (IntPartIR (diffble_imp_inc _ _ _ _ diffG)))).
eapply Derivative_I_wdr.
apply
 part_int_plus
  with
    (F := PartInt (IMult (IntPartIR (diffble_imp_inc _ _ _ _ diffF)) G'))
    (G := PartInt (IMult F' (IntPartIR (diffble_imp_inc _ _ _ _ diffG)))).
apply Feq_reflexive; Included.
apply Feq_reflexive; Included.
eapply Derivative_I_wdr.
apply Feq_plus with (F := F{*}PartInt G') (G := PartInt F'{*}G).
apply part_int_mult.
FEQ.
apply Feq_reflexive; Included.
apply part_int_mult.
apply Feq_reflexive; Included.
FEQ.
Deriv.
Qed.

(* begin show *)
Hypothesis Gbnd : bnd_away_zero I G.
(* end show *)

Lemma Diffble_I_recip : Diffble_I Hab' {1/}G.
elim diffG; intros G' derG.
cut (included I (Dom G)); [ intro Hg' | unfold I, Hab in |- *; Included ].
unfold I in Hg';
 cut (forall x : subset I, IMult (IntPartIR Hg') (IntPartIR Hg') x [#] Zero). intro H.
exists (IInv (IDiv G' _ H)).
eapply Derivative_I_wdr.
apply part_int_inv with (F := PartInt (IDiv G' _ H)).
apply Feq_reflexive; Included.
eapply Derivative_I_wdr.
apply
 Feq_inv
  with (F := PartInt G'{/}PartInt (IMult (IntPartIR Hg') (IntPartIR Hg'))).
apply part_int_div.
apply Feq_reflexive; Included.
apply Feq_reflexive; simpl in |- *; Included.
red in |- *; intros.
split.
simpl in |- *; Included.
elim Gbnd; intros Hinc c.
elim c; clear c; intros c H0 H1.
exists (c[*]c).
apply mult_resp_pos; assumption.
intros.
simpl in |- *.
eapply leEq_wdr.
2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
apply mult_resp_leEq_both; auto; apply less_leEq; assumption.
eapply Derivative_I_wdr.
apply Feq_inv with (F := PartInt G'{/}G{*}G).
apply Feq_div.
Included.
apply Feq_reflexive; Included.
apply part_int_mult.
FEQ.
FEQ.
Deriv.
intro x.
simpl in |- *.
apply mult_resp_ap_zero; apply bnd_imp_ap_zero with I; auto; apply scs_prf.
Qed.

End Operations.

Section Corollaries.

Variables a b : IR.
Hypothesis Hab' : a [<] b.

(* begin hide *)
Let Hab := less_leEq _ _ _ Hab'.
Let I := Compact Hab.
(* end hide *)

Variables F G : PartIR.

Hypothesis diffF : Diffble_I Hab' F.
Hypothesis diffG : Diffble_I Hab' G.

Lemma Diffble_I_minus : Diffble_I Hab' (F{-}G).
apply Diffble_I_wd with (F{+}{--}G).
apply Diffble_I_plus.
assumption.
apply Diffble_I_inv; assumption.
FEQ.
Qed.

Lemma Diffble_I_scal : forall c : IR, Diffble_I Hab' (c{**}F).
intro.
unfold Fscalmult in |- *.
apply Diffble_I_mult.
apply Diffble_I_const.
assumption.
Qed.

Lemma Diffble_I_nth : forall n : nat, Diffble_I Hab' (F{^}n).
intro.
induction  n as [| n Hrecn].
eapply Diffble_I_wd.
2: apply FNth_zero'; Included.
apply Diffble_I_const.
eapply Diffble_I_wd.
2: apply FNth_mult'; Included.
apply Diffble_I_mult; assumption.
Qed.

Hypothesis Gbnd : bnd_away_zero I G.

Lemma Diffble_I_div : Diffble_I Hab' (F{/}G).
apply Diffble_I_wd with (F{*}{1/}G).
apply Diffble_I_mult.
assumption.
apply Diffble_I_recip; assumption.
FEQ.
Qed.

End Corollaries.

Section Other_Properties.

(**
Differentiability of families of functions is proved by
induction using the constant and addition rules.
*)

Variables a b : IR.
Hypothesis Hab' : a [<] b.

Lemma Diffble_I_Sum0 : forall (f : nat -> PartIR),
 (forall n, Diffble_I Hab' (f n)) -> forall n, Diffble_I Hab' (FSum0 n f).
intros f diffF.
induction  n as [| n Hrecn].
apply Diffble_I_wd with (Fconst (S:=IR) Zero).
apply Diffble_I_const.
FEQ.
red in |- *; simpl in |- *; intros.
apply (diffble_imp_inc _ _ _ _ (diffF n)); assumption.
apply Diffble_I_wd with (FSum0 n f{+}f n).
apply Diffble_I_plus.
auto.
auto.
FEQ.
simpl in |- *; red in |- *; intros.
apply (diffble_imp_inc _ _ _ _ (diffF n0)); assumption.
simpl in |- *.
apply bin_op_wd_unfolded; try apply Sum0_wd; intros; rational.
Qed.

Lemma Diffble_I_Sumx : forall n (f : forall i, i < n -> PartIR),
 (forall i Hi, Diffble_I Hab' (f i Hi)) -> Diffble_I Hab' (FSumx n f).
intro; induction  n as [| n Hrecn]; intros.
simpl in |- *; apply Diffble_I_const.
simpl in |- *.
apply Diffble_I_plus; auto.
Qed.

Lemma Diffble_I_Sum : forall (f : nat -> PartIR),
 (forall n, Diffble_I Hab' (f n)) -> forall m n, Diffble_I Hab' (FSum m n f).
intros.
eapply Diffble_I_wd.
2: apply Feq_symmetric; apply FSum_FSum0'; Included.
apply Diffble_I_minus; apply Diffble_I_Sum0; auto.
Qed.

End Other_Properties.

(**
Finally, a differentiable function is continuous.

%\begin{convention}% Let [F] be a partial function with derivative [F'] on [I].
%\end{convention}%
*)

Lemma diffble_imp_contin_I : forall a b (Hab' : a [<] b) (Hab : a [<=] b) F,
 Diffble_I Hab' F -> Continuous_I Hab F.
intros a b Hab' Hab F H.
apply deriv_imp_contin_I with Hab' (PartInt (ProjT1 H)).
apply projT2.
Qed.

Hint Immediate included_imp_contin deriv_imp_contin_I deriv_imp_contin'_I
  diffble_imp_contin_I: continuous.

Hint Immediate included_imp_deriv: derivate.
