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
(* file        : bridges_gives_our.v                               *)
(* version     : 1.50 - 09/05/2001                                 *)
(* version     : 1.00 - 09/03/2001                                 *)
(* author      : Milad Niqui                                       *)
(* language    : coq7.0bet26feb                                    *)
(* dependency  : least_upper_bound_principle                       *)
(* description : Bridges' proof of Cauchy completeness in TCS-219  *)


Require Import Bridges_LUB.


(* This lemma comes from lemmas.v of Martijn Oostdijk *)
Lemma le_witness_informative :
 forall m n : nat, m <= n -> {k : nat | n = m + k}.
Proof.
 intros.
 induction  n as [| n Hrecn].
  exists 0.
  rewrite <- (plus_n_O m).
  apply le_n_O_eq.
  assumption.
 case (le_lt_eq_dec m (S n)).
   assumption.
  intro.
  case Hrecn.
   apply lt_n_Sm_le.
   assumption.
  intro k.
  intros.
  exists (S k).
  rewrite <- (plus_Snm_nSm m k).
  simpl in |- *.
  apply eq_S.
  assumption.
 intro.
 exists 0.
 rewrite <- (plus_n_O m).
 symmetry  in |- *.
 assumption.
Qed.

Section bridges_axioms_imply_ours.

Variable OF : COrdField.
Hypothesis
  lubp :
    forall X : OF -> CProp,
    {x : OF | X x} ->
    {b : OF | is_upper_bound OF X b} ->
    (forall x y : OF,
     x[<]y -> is_upper_bound OF X y or {s : OF | X s | x[<]s}) ->
    l_u_b OF X.

Hypothesis is_Archimedes : forall x : OF, {n : nat | x[<=]nring n}.

Lemma is_Archimedes' : forall x : OF, {n : nat | x[<]nring n}.
Proof.
 intro x.
 elim (is_Archimedes (x[+][1])); intros n Hn.
 exists n.
 apply less_leEq_trans with (x[+][1]).
  apply less_plusOne.
 auto.
Qed.

Section proofs_in_TCS.

Lemma leEq_geEq :
 forall x y : OF,
 (forall t : OF, t[<]x -> t[<]y) -> forall z : OF, y[<]z -> x[<]z.
Proof.
 intros x y H z H0.
 apply plus_cancel_less with (z := [--](z[-]y)).
 rstepr y.
 apply H.
 apply shift_plus_less.
 apply plus_cancel_less with (z := [--]x).
 rstepr (z[-]y).
 astepl ([0]:OF).
 apply shift_zero_less_minus.
 assumption.
Qed.


Theorem glbp :
 forall X : OF -> CProp,
 {x : OF | X x} ->
 {l : OF | is_lower_bound OF X l} ->
 (forall x y : OF, x[=]y -> X x -> X y) ->
 (forall x y : OF, x[<]y -> is_lower_bound OF X x or {s : OF | X s | s[<]y}) ->
 g_l_b OF X.
Proof.
 intros X H H0 strong_extensionality_of_X.
 intros.
 red in |- *.
 cut (l_u_b OF (fun x : OF => X [--]x)).
  intro H2.
  red in H2.
  case H2.
  intro b.
  intros a.
  exists ([--]b).
  elim a.
  intros H3 H4.
  split.
   red in |- *.
   intros x H5 z H6.
   red in H3.
   case (less_cotransitive_unfolded OF z [--]b H6 x).
    trivial.
   intro.
   elimtype False.
   apply (less_irreflexive_unfolded _ b).
   apply H3 with (x := [--]x) (z := b).
    apply (strong_extensionality_of_X x [--][--]x).
     algebra.
    assumption.
   apply inv_cancel_less.
   astepl x.
   assumption.
  intros.
  case (H4 [--]c').
   apply inv_cancel_less.
   astepr c'.
   assumption.
  intro s.
  intros H6.
  elim H6.
  intros.
  exists ([--]s).
  split.
   assumption.
  apply inv_cancel_less.
  astepr s.
  assumption.
 (* * * * * * * *)
 apply (lubp (fun x : OF => X [--]x)).
   case H.
   intro x.
   intro.
   exists ([--]x).
   apply (strong_extensionality_of_X x [--][--]x).
    algebra.
   assumption.
  case H0.
  intro l.
  intros.
  exists ([--]l).
  red in |- *.
  red in i.
  intros.
  apply inv_cancel_less.
  astepl l.
  apply (leEq_geEq l [--]x).
   intros.
   apply i with (x := [--]x).
    assumption.
   assumption.
  apply inv_resp_less.
  assumption.
 rename X0 into H1. intros x y H2.
 case (H1 [--]y [--]x).
   apply inv_resp_less.
   assumption.
  intro.
  left.
  red in |- *.
  red in i.
  intros.
  apply inv_cancel_less.
  apply (leEq_geEq [--]y [--]x0).
   intros.
   apply i with (x := [--]x0).
    assumption.
   assumption.
  apply inv_resp_less.
  assumption.
 intro e.
 right.
 case e.
 intro s.
 intros.
 exists ([--]s).
  apply (strong_extensionality_of_X s [--][--]s).
   algebra.
  assumption.
 apply inv_cancel_less.
 rstepl s.
 assumption.
Qed.




Section supremum.
Variable P : OF -> CProp.



Lemma inequality1 : forall x : OF, x[<]x[^]2[-]x[+]Two.
Proof.
 intros.
 apply plus_cancel_less with (z := [--]x).
 astepl ([0]:OF).
 simpl in |- *.
 rstepr ((x[-][1])[*](x[-][1])[+][1]).
 apply less_wdr with (y := (x[-][1])[^]2[+]([1]:OF)).
  apply less_leEq_trans with (y := [1]:OF).
   apply pos_one.
  apply plus_cancel_leEq_rht with (z := [--]([1]:OF)).
  astepl ([0]:OF).
  rstepr ((x[-]([1]:OF))[^]2).
  apply sqr_nonneg.
 simpl in |- *.
 rational.
Qed.

Lemma inequality2 : forall x : OF, ([0]:OF)[<]x[^]2[-]x[+]Two.
Proof.
 intros.
 apply less_wdr with (y := (x[-][1] [/]TwoNZ)[^]2[+](Three [/]FourNZ[+][1])).
  apply less_leEq_trans with (y := Three [/]FourNZ[+]([1]:OF)).
   apply plus_resp_pos.
    apply div_resp_pos.
     apply pos_four.
    apply pos_three.
   apply pos_one.
  apply plus_cancel_leEq_rht with (z := [--](Three [/]FourNZ[+]([1]:OF))).
  astepl ([0]:OF).
  rstepr ((x[-]([1]:OF) [/]TwoNZ)[^]2).
  apply sqr_nonneg.
 simpl in |- *.
 rational.
Qed.

Lemma inequality3 : forall x : OF, [--](x[^]2)[-]x[-]Two[<]x.
Proof.
 intros.
 apply inv_cancel_less.
 apply plus_cancel_less with (z := x).
 simpl in |- *.
 rstepr ((x[+][1])[*](x[+][1])[+][1]).
 astepl ([0]:OF).
 apply less_wdr with (y := (x[+][1])[^]2[+]([1]:OF)).
  apply less_leEq_trans with (y := [1]:OF).
   apply pos_one.
  apply plus_cancel_leEq_rht with (z := [--]([1]:OF)).
  astepl ([0]:OF).
  rstepr ((x[+]([1]:OF))[^]2).
  apply sqr_nonneg.
 simpl in |- *.
 rational.
Qed.

Lemma inequality4 : forall x : OF, [--](x[^]2)[-]x[-]Two[<]([0]:OF).
Proof.
 intros.
 apply inv_cancel_less.
 astepl ([0]:OF).
 apply less_wdr with (y := (x[+][1] [/]TwoNZ)[^]2[+](Three [/]FourNZ[+][1])).
  apply less_leEq_trans with (y := Three [/]FourNZ[+]([1]:OF)).
   apply plus_resp_pos.
    apply div_resp_pos.
     apply pos_four.
    apply pos_three.
   apply pos_one.
  apply plus_cancel_leEq_rht with (z := [--](Three [/]FourNZ[+]([1]:OF))).
  astepl ([0]:OF).
  rstepr ((x[+]([1]:OF) [/]TwoNZ)[^]2).
  apply sqr_nonneg.
 simpl in |- *.
 rational.
Qed.


Fixpoint Hum (r : nat -> OF) (n : nat) {struct n} : OF :=
  match n with
  | O => r 0
  | S p => r (S p)[+]Hum r p
  end.

Lemma bound_tk1 :
 forall (n : nat) (g : nat -> OF),
 (forall m : nat, m <= n -> ([0]:OF)[<]g m) -> ([0]:OF)[<]Hum g n.
Proof.
 intros n g H.
 induction  n as [| n Hrecn].
  simpl in |- *.
  apply H.
  constructor.
 (* n=(S n0) *)
 simpl in |- *.
 apply plus_resp_pos.
  apply H.
  apply le_n.
 apply Hrecn.
 intros.
 apply H.
 apply le_trans with (m := n).
  assumption.
 apply le_n_Sn.
Qed.

Lemma bound_tk2 :
 forall (n : nat) (g : nat -> OF),
 (forall m : nat, m <= n -> g m[<]([0]:OF)) -> Hum g n[<][0].
Proof.
 intros n g H.
 induction  n as [| n Hrecn].
  simpl in |- *.
  apply H.
  constructor.
 (* n=(S n0) *)
 simpl in |- *.
 astepr ([0][+]([0]:OF)).
 apply plus_resp_less_both.
  apply H.
  apply le_n.
 apply Hrecn.
 intros.
 apply H.
 apply le_trans with (m := n).
  assumption.
 apply le_n_Sn.
Qed.


Lemma trick :
 forall (n : nat) (r g : nat -> OF),
 (forall m : nat, m <= n -> ([0]:OF)[<]g m) ->
 (forall m : nat, m <= n -> r m[<]g m) ->
 forall m : nat, m <= n -> r m[<]Hum g n.
Proof.
 intros n r g H H0 m H1.
 induction  n as [| n Hrecn].
  (* n=O *)
  simpl in |- *.
  rewrite <- (le_n_O_eq m H1).
  apply H0.
  constructor.
 (* n=(S n0) *)
 simpl in |- *.
 case (le_lt_eq_dec m (S n)).
   assumption.
  intro.
  cut (m <= n).
   intro.
   astepl (([0]:OF)[+]r m).
   apply plus_resp_less_both.
    apply H.
    apply le_n.
   apply Hrecn.
     intros.
     apply H.
     apply le_trans with (m := n).
      assumption.
     apply le_n_Sn.
    intros.
    apply H0.
    apply le_trans with (m := n).
     assumption.
    apply le_n_Sn.
   assumption.
  apply lt_n_Sm_le.
  assumption.
 intros.
 rewrite e.
 astepl (r (S n)[+]([0]:OF)).
 apply plus_resp_less_both.
  apply H0.
  apply le_n.
 apply bound_tk1.
 intros.
 apply H.
 apply le_trans with (m := n).
  assumption.
 apply le_n_Sn.
Qed.


Lemma trick' :
 forall (n : nat) (r g : nat -> OF),
 (forall m : nat, m <= n -> g m[<][0]) ->
 (forall m : nat, m <= n -> g m[<]r m) ->
 forall m : nat, m <= n -> Hum g n[<]r m.
Proof.
 intros n r g H H0 m H1.
 induction  n as [| n Hrecn].
  (* n=O *)
  simpl in |- *.
  rewrite <- (le_n_O_eq m H1).
  apply H0.
  constructor.
 (* n=(S n0) *)
 simpl in |- *.
 case (le_lt_eq_dec m (S n)).
   assumption.
  intro.
  cut (m <= n).
   intro.
   astepr (([0]:OF)[+]r m).
   apply plus_resp_less_both.
    apply H.
    apply le_n.
   apply Hrecn.
     intros.
     apply H.
     apply le_trans with (m := n).
      assumption.
     apply le_n_Sn.
    intros.
    apply H0.
    apply le_trans with (m := n).
     assumption.
    apply le_n_Sn.
   assumption.
  apply lt_n_Sm_le.
  assumption.
 intro H2.
 rewrite H2.
 astepr (r (S n)[+]([0]:OF)).
 apply plus_resp_less_both.
  apply H0.
  apply le_n.
 apply bound_tk2.
 intros.
 apply H.
 apply le_trans with (m := n).
  assumption.
 apply le_n_Sn.
Qed.

Theorem up_bound_for_n_element :
 forall (n : nat) (r : nat -> OF),
 {b : OF | forall m : nat, m <= n -> r m[<]b}.
Proof.
 intros.
 exists (Hum (fun p : nat => r p[^]2[-]r p[+]Two) n).
 intros.
 apply trick.
   intros.
   apply inequality2.
  intros.
  apply inequality1.
 assumption.
Qed.

Lemma low_bound_for_n_element :
 forall (n : nat) (r : nat -> OF),
 {l : OF | forall m : nat, m <= n -> l[<]r m}.
Proof.
 intros.
 exists (Hum (fun p : nat => [--](r p[^]2)[-]r p[-]Two) n).
 intros.
 apply trick'.
   intros.
   apply inequality4.
  intros.
  apply inequality3.
 assumption.
Qed.

Definition saghf (r : nat -> OF) (n : nat) :=
  let (N, _) := up_bound_for_n_element n r in N.

Lemma Psaghf : forall (r : nat -> OF) (n m : nat), m <= n -> r m[<]saghf r n.
Proof.
 intros r n.
 unfold saghf in |- *.
 elim up_bound_for_n_element; auto.
Qed.

Definition kaf (r : nat -> OF) (n : nat) :=
  let (N, _) := low_bound_for_n_element n r in N.


Lemma Pkaf : forall (r : nat -> OF) (n m : nat), m <= n -> kaf r n[<]r m.
Proof.
 intros r n.
 unfold kaf in |- *. elim low_bound_for_n_element; auto.
Qed.


Hypothesis
  is_finite_P :
    {n : nat |
    {r : nat -> OF | forall y : OF, P y -> {m : nat | m <= n | r m[=]y}}}.

Definition card := let (N, _) := is_finite_P in N.


Lemma Pcard1 :
 {r : nat -> OF | forall y : OF, P y -> {m : nat | m <= card | r m[=]y}}.
Proof.
 intros.
 unfold card in |- *. elim is_finite_P; auto.
Defined.

Definition seq := let (N, _) := Pcard1 in N.

Definition Pseq1 := projT2 Pcard1.

Lemma Pseq1_unfolded :
 forall y : OF, P y -> {m : nat | m <= card | seq m[=]y}.
Proof.
 exact Pseq1.
Qed.

Definition indeks (y : OF) (H : P y) :=
  let (N, _, _) := Pseq1_unfolded y H in N.

Lemma Pindeks :
 forall (y : OF) (H : P y), indeks y H <= card /\ seq (indeks y H)[=]y.
Proof.
 intros.
 unfold indeks in |- *.  elim Pseq1_unfolded; auto.
Qed.

Hypothesis is_onto_seq_P : forall t : nat, t <= card -> P (seq t).

Lemma P_is_inhabited : {x : OF | P x}.
Proof.
 intros.
 exists (seq 0).
 apply is_onto_seq_P.
 apply le_O_n.
Qed.

(*
Lemma bounded_quantifier:(N:nat;phi,psi:nat->Prop)
                 ((m:nat)(le m N)->(phi m)\/(psi m))->
        ((m:nat)(le m N)->(phi m))\/(Ex [j:nat](le j N)/\(psi j)).
Proof.
 Intros.
 Induction N.
 Cut (phi O)\/(psi O).
 Intro.
 Case H0.
 Intros.
 Left.
 Intros.
 Rewrite <- (le_n_O_eq m H2).
 Assumption.
 Intro.
 Right.
 Exists O.
 Split.
 Constructor.
 Assumption.
 Apply H.
 Constructor.*)
 (* n=(S n0) *)
(* Case HrecN.
 Intros.
 Apply H.
 Apply le_trans with m:=N.
 Assumption.
 Apply le_n_Sn.
 Intro.
 Case (H (S N)).
 Apply le_n.
 Intros.
 Left.
 Intros.
 Case (le_lt_eq_dec m (S N)).
 Assumption.
 Intros.
 Apply H0.
 Apply (lt_n_Sm_le m N).
 Assumption.
 Intro.
 Rewrite e.
 Assumption.
 Intro.
 Right.
 Exists (S N).
 Split.
 Apply le_n.
 Assumption.
 Intro.
 Right.
 Case H0.
 Intro j.
 Intros.
 Exists j.
 Elim H1.
 Intros.
 Split.
 Apply le_trans with m:=N.
 Assumption.
 Apply le_n_Sn.
 Assumption.
Qed.
*)

Lemma bounded_quantifier_informative :
 forall (N : nat) (phi psi : nat -> CProp),
 (forall m : nat, m <= N -> phi m or psi m) ->
 (forall m : nat, m <= N -> phi m) or {j : nat | Cle j N | psi j}.
Proof.
 do 3 intro.  intro H.
 induction  N as [| N HrecN].
  cut (phi 0 or psi 0).
   intro H0.
   case H0.
    intros.
    left.
    intros.
    rewrite <- (le_n_O_eq m H1).
    assumption.
   intro.
   right.
   exists 0.
    constructor.
   assumption.
  apply H.
  constructor.
 (* n=(S n0) *)
 case HrecN.
   intros.
   apply H.
   apply le_trans with (m := N).
    assumption.
   apply le_n_Sn.
  intro.
  case (H (S N)).
    apply le_n.
   intros.
   left.
   intros.
   case (le_lt_eq_dec m (S N)).
     assumption.
    intros.
    apply p.
    apply (lt_n_Sm_le m N).
    assumption.
   intro.
   rewrite e.
   assumption.
  intro.
  right.
  exists (S N).
   apply toCle.
   apply le_n.
  assumption.
 intro.
 right.
 case s.
 intro j.
 intros.
 exists j.
  apply toCle.
  apply le_trans with (m := N).
   apply Cle_to.
   assumption.
  apply le_n_Sn.
 assumption.
Qed.

Lemma bridges_lemma1a : l_u_b OF P.
Proof.
 apply (lubp P P_is_inhabited).
  case is_finite_P.
  intro N.
  intros.
  case s.
  intro r.
  intro.
  exists (saghf r N).
  red in |- *.
  intros x H z H0.
  apply less_transitive_unfolded with (y := x).
   assumption.
  case (s0 x H).
  intro m.
  intros H1 H2.
  apply less_wdl with (x := r m).
   apply Psaghf.
   assumption.
  assumption.
 (* Start of Bridges' 3-line proof *)
 intros.
 cut ((forall k : nat, k <= card -> seq k[<]y) or {j : nat | P (seq j) | x[<]seq j}).
  intro H0.
  case H0.
   intro c.
   left.
   red in |- *.
   intros x0 H1 z H2.
   apply less_transitive_unfolded with (y := x0).
    assumption.
   elim (Pindeks x0 H1).
   intros.
   apply less_wdl with (x := seq (indeks x0 H1)).
    apply c.
    assumption.
   assumption.
  intro e.
  right.
  case e.
  intro j.
  intros H2 H3.
  exists (seq j).
   assumption.
  assumption.
 (* proof of the claim that we cut above *)
 case (bounded_quantifier_informative card)
   with (phi := fun k : nat => seq k[<]y) (psi := fun k : nat => x[<]seq k).
   intros.
   cut (x[<]seq m or seq m[<]y).
    intro H1.
    case H1.
     intro.
     right.
     assumption.
    intro.
    left.
    assumption.
   apply less_cotransitive_unfolded.
   assumption.
  intros.
  left.
  assumption.
 intro e.
 right.
 case e.
 intro j.
 intros.
 exists j.
  apply is_onto_seq_P.
  apply Cle_to.
  assumption.
 assumption.
Qed.

Hypothesis P_is_strongly_extensional : forall x y : OF, x[=]y -> P x -> P y.


Lemma bridges_lemma1b : g_l_b OF P.
Proof.
 intros.
 red in |- *.
 cut (l_u_b OF (fun x : OF => P [--]x)).
  intro H.
  red in H.
  case H.
  intro b.
  intros p.
  elim p.
  intros H0 H1.
  exists ([--]b).
  split.
   red in |- *.
   red in H0.
   intros x H2 z H3.
   case (less_cotransitive_unfolded OF z [--]b H3 x).
    trivial.
   intro.
   elim (less_irreflexive_unfolded _ b).
   apply H0 with (x := [--]x) (z := b).
    apply (P_is_strongly_extensional x [--][--]x).
     algebra.
    assumption.
   apply inv_cancel_less.
   astepl x.
   assumption.
  intros.
  case (H1 [--]c').
   apply inv_cancel_less.
   astepr c'.
   assumption.
  intro s.
  intros H3.
  elim H3.
  intros.
  exists ([--]s).
  split.
   assumption.
  apply inv_cancel_less.
  astepr s.
  assumption.
 (* * * * * * * *  *)
 apply (lubp (fun x : OF => P [--]x)).
   case P_is_inhabited.
   intro x.
   intro.
   exists ([--]x).
   apply (P_is_strongly_extensional x [--][--]x).
    algebra.
   assumption.
  case is_finite_P.
  intro N.
  intros.
  case s.
  intro r.
  intro.
  exists (saghf (fun n : nat => [--](r n)) N).
  red in |- *.
  intros x H z H0.
  apply less_transitive_unfolded with (y := x).
   assumption.
  case (s0 [--]x H).
  intro m.
  intros H1 H2.
  apply less_wdl with (x := [--](r m)).
   apply (Psaghf (fun m : nat => [--](r m))).
   assumption.
  rstepl (([0]:OF)[-]r m).
  rstepr (([0]:OF)[-][--]x).
  apply cg_minus_wd.
   apply eq_reflexive_unfolded.
  assumption.
 (* Start of Bridges' 3-line proof *)
 intros x y H.
 cut ((forall k : nat, k <= card -> [--](seq k)[<]y) or {j : nat | P (seq j) | x[<][--](seq j)}).
  intro H0.
  case H0.
   intro c.
   left.
   red in |- *.
   intros x0 H1 z H2.
   apply less_transitive_unfolded with (y := x0).
    assumption.
   elim (Pindeks [--]x0 H1).
   intros.
   apply less_wdl with (x := [--](seq (indeks [--]x0 H1))).
    apply c.
    assumption.
   rstepl (([0]:OF)[-]seq (indeks [--]x0 H1)).
   rstepr (([0]:OF)[-][--]x0).
   apply cg_minus_wd.
    apply eq_reflexive_unfolded.
   assumption.
  intro e.
  right.
  case e.
  intro j.
  intros H2 H3.
  exists ([--](seq j)).
   apply (P_is_strongly_extensional (seq j) [--][--](seq j)).
    algebra.
   assumption.
  assumption.
 (* proof of the claim that we cut above *)
 case (bounded_quantifier_informative card) with (phi := fun k : nat => [--](seq k)[<]y)
   (psi := fun k : nat => x[<][--](seq k)).
   intros.
   cut (x[<][--](seq m) or [--](seq m)[<]y).
    intro H1.
    case H1.
     intro.
     right.
     assumption.
    intro.
    left.
    assumption.
   apply less_cotransitive_unfolded.
   assumption.
  intros.
  left.
  assumption.
 intro e.
 right.
 case e.
 intro j.
 intros.
 exists j.
  apply is_onto_seq_P.
  apply Cle_to.
  assumption.
 assumption.
Qed.


End supremum.

(*---------------------------------*)
(*---------------------------------*)
(*---------------------------------*)
(*---------------------------------*)
Section Every_Cauchy_Sequence_is_bounded.

Definition seq2set (g : CauchySeq OF) (x : OF) : CProp :=
  {n : nat | x[=]CS_seq _ g n}.

Variable g : CauchySeq OF.

Let g_ := CS_seq _ g.
Let pg := CS_proof _ g.


Let P (BOUND : nat) (x : OF) := {n : nat | n <= BOUND | x[=]g_ n}.


Lemma fin_is_fin :
 forall BOUND : nat,
 {n : nat |
 {r : nat -> OF | forall y : OF, P BOUND y -> {m : nat | m <= n | r m[=]y}}}.
Proof.
 intros.
 exists BOUND.
 exists g_.
 intros y H.
 red in H.
 case H.
 intro n.
 intros.
 exists n.
  assumption.
 apply eq_symmetric_unfolded.
 assumption.
Defined.

Lemma card_fin :
 forall BOUND : nat, card (P BOUND) (fin_is_fin BOUND) = BOUND.
Proof.
 unfold card in |- *.
 unfold fin_is_fin in |- *.
 reflexivity.
Qed.

Lemma finite_seq :
 forall BOUND t : nat, seq (P BOUND) (fin_is_fin BOUND) t[=]g_ t.
Proof.
 intros.
 unfold seq in |- *.
 unfold fin_is_fin in |- *.
 unfold Pcard1 in |- *.
 unfold Pcard1 in |- *.
 change (g_ t[=]g_ t) in |- *.
 apply eq_reflexive_unfolded.
Qed.

Lemma bridges_lemma2a : l_u_b OF (seq2set g).
Proof.
 intros.
 apply (lubp (seq2set g)).
   (* it is inhabited *)
   exists (g_ 0).
   red in |- *.
   exists 0.
   apply eq_reflexive_unfolded.
  (* it is bounded above *)
  cut {N : nat | forall m : nat, N <= m -> AbsSmall [1] (g_ m[-]g_ N)}.
   intro H.
   case H.
   intro N.
   intro.
   exists (saghf g_ N[+][1]).
   red in |- *.
   intros x H0 y H1.
   red in H0.
   case H0.
   intro n.
   intro c.
   apply less_transitive_unfolded with (y := x).
    assumption.
   apply less_wdl with (x := g_ n).
    case (le_ge_dec N n).
     intro H2.
     apply leEq_less_trans with (y := g_ N[+][1]).
      apply shift_leEq_plus'.
      cut (AbsSmall [1] (g_ n[-]g_ N)).
       intro.
       elim H3.
       intros H4 H5.
       assumption.
      apply a.
      assumption.
     apply plus_resp_less_rht.
     apply Psaghf.
     apply le_n.
    intro H2.
    apply less_transitive_unfolded with (y := saghf g_ N).
     apply Psaghf.
     assumption.
    apply less_plusOne.
   apply eq_symmetric_unfolded.
   exact c.
  apply (pg [1]).
  apply pos_one.
 (* This is the proof of Proposition 1 of Bridges *)
 intros a b.
 intro.
 cut {N : nat | forall m : nat, N <= m -> AbsSmall ((b[-]a) [/]TwoNZ) (g_ m[-]g_ N)}.
  intro H0.
  case H0.
  intro N.
  intros.
  cut (l_u_b OF (fun x : OF => {n : nat | n <= N | x[=]g_ n})).
   intro H1.
   red in H1.
   case H1.
   intro sigma.
   intros p.
   elim p.
   intros.
   cut (a[<](a[+]b) [/]TwoNZ).
    intro H2.
    case (less_cotransitive_unfolded _ a ((a[+]b) [/]TwoNZ) H2 sigma).
     intro c.
     right.
     case (b0 a c).
     intro xj.
     intro H5.
     exists xj.
      elim H5.
      intros H6 H7.
      case H6.
      intro j.
      intros H9 H10.
      red in |- *.
      exists j.
      simpl in |- *.
      assumption.
     elim H5.
     intros.
     assumption.
    intro.
    left.
    red in |- *.
    intros x H3 z H4.
    red in H3.
    case H3.
    intro n.
    intros.
    case (le_ge_dec N n).
     intro H7.
     rstepr (a[+](b[-]a)).
     apply less_transitive_unfolded with (y := sigma[+](b[-]a) [/]TwoNZ).
      apply shift_less_plus.
      apply (a1 (g_ N)).
       exists N.
        apply le_n.
       apply eq_reflexive_unfolded.
      apply shift_minus_less.
      apply less_leEq_trans with (y := x).
       assumption.
      apply leEq_wdl with (x := g_ n).
       apply shift_leEq_plus'.
       cut (AbsSmall ((b[-]a) [/]TwoNZ) (g_ n[-]g_ N)).
        intro H8.
        elim H8.
        intros H9 H10.
        assumption.
       apply a0.
       assumption.
      apply eq_symmetric_unfolded.
      assumption.
     apply shift_plus_less.
     rstepr ((a[+]b) [/]TwoNZ).
     assumption.
    intro.
    rstepr (a[+](b[-]a)).
    apply less_transitive_unfolded with (y := sigma[+](b[-]a) [/]TwoNZ).
     apply shift_less_plus.
     apply (a1 x).
      exists n.
       assumption.
      assumption.
     apply shift_minus_less.
     apply less_transitive_unfolded with (y := x).
      assumption.
     apply shift_less_plus'.
     astepl ([0]:OF).
     apply pos_div_two.
     apply shift_zero_less_minus.
     assumption.
    apply shift_plus_less.
    rstepr ((a[+]b) [/]TwoNZ).
    assumption.
   apply plus_cancel_less with (z := [--]a).
   rstepl ([0]:OF).
   rstepr ((b[-]a) [/]TwoNZ).
   apply pos_div_two.
   apply shift_zero_less_minus.
   assumption.
  apply bridges_lemma1a with (P := P N) (is_finite_P := fin_is_fin N).
  intros.
  unfold P in |- *.
  exists t.
   rewrite <- (card_fin N).
   assumption.
  apply (finite_seq N).
 apply (pg ((b[-]a) [/]TwoNZ)).
 apply pos_div_two.
 apply shift_zero_less_minus.
 assumption.
Qed.

Definition sup := let (N, _) := bridges_lemma2a in N.


Definition Psup := projT2 bridges_lemma2a.

Lemma Psup_proj1 : is_upper_bound OF (seq2set g) sup.
Proof.
 unfold sup in |- *.
 elim Psup.
 auto.
Qed.

Lemma Psup_unfolded1 :
 forall x : OF, seq2set g x -> forall z : OF, z[<]x -> z[<]sup.
Proof.
 change (is_upper_bound OF (seq2set g) sup) in |- *.
 exact Psup_proj1.
Qed.

Lemma Psup_unfolded2 :
 forall b' : OF, b'[<]sup -> {s : OF | seq2set g s | b'[<]s}.
Proof.
 unfold sup in |- *.
 elim Psup.
 simpl in |- *.
 intros.  rename X into H.
 elim (b b' H); intros x p; elim p; exists x; auto.
Qed.



Lemma bridges_lemma2b : g_l_b OF (seq2set g).
Proof.
 intros.
 apply (glbp (seq2set g)).
    (* it is inhabited *)
    exists (g_ 0).
    red in |- *.
    exists 0.
    apply eq_reflexive_unfolded.
   (* it is bounded below *)
   cut {N : nat | forall m : nat, N <= m -> AbsSmall [1] (g_ m[-]g_ N)}.
    intro H.
    case H.
    intro N.
    intros.
    exists (kaf g_ N[-][1]).
    red in |- *.
    intros x H0 z H1.
    case H0.
    intro n.
    intros c.
    apply less_wdr with (y := g_ n).
     case (le_ge_dec N n).
      intro.
      apply less_leEq_trans with (y := g_ N[-][1]).
       apply less_transitive_unfolded with (y := kaf g_ N[-][1]).
        assumption.
       apply minus_resp_less.
       apply Pkaf.
       apply le_n.
      apply plus_cancel_leEq_rht with (z := [--](g_ N)).
      rstepl ([--]([1]:OF)).
      astepr (g_ n[-]g_ N).
      cut (AbsSmall [1] (g_ n[-]g_ N)).
       intro.
       elim H2.
       intros.
       assumption.
      apply a.
      assumption.
     intro.
     apply less_transitive_unfolded with (y := kaf g_ N[-][1]).
      assumption.
     apply less_transitive_unfolded with (y := kaf g_ N).
      apply plus_cancel_less with (z := [1]:OF).
      astepl (kaf g_ N).
      apply less_plusOne.
     apply Pkaf.
     assumption.
    apply eq_symmetric_unfolded.
    exact c.
   (* Here we are using ex_informative *)
   apply (pg [1]).
   apply pos_one.
  (* it is strongly extensional *)
  intros x y H H0.
  red in |- *.
  red in H0.
  case H0.
  intro n.
  intros.
  exists n.
  apply eq_transitive_unfolded with (y := x).
   apply eq_symmetric_unfolded.
   assumption.
  assumption.
 (* This is the proof of Proposition 1 of Bridges for infimum *)
 intros a b.
 intro.
 cut {N : nat | forall m : nat, N <= m -> AbsSmall ((b[-]a) [/]TwoNZ) (g_ m[-]g_ N)}.
  intro H0.
  case H0.
  intro N.
  intros.
  cut (g_l_b OF (fun x : OF => {n : nat | n <= N | x[=]g_ n})).
   intro H1.
   red in H1.
   case H1.
   intro tau.
   intros p.
   elim p.
   intros.
   cut ((a[+]b) [/]TwoNZ[<]b).
    intro H2.
    case (less_cotransitive_unfolded _ ((a[+]b) [/]TwoNZ) b H2 tau).
     intro.
     left.
     red in |- *.
     intros x H3 z H4.
     red in H3.
     case H3.
     intro n.
     intros H7.
     case (le_ge_dec N n).
      intro.
      red in a1.
      apply less_wdr with (y := g_ n).
       apply less_leEq_trans with (y := g_ N[-](b[-]a) [/]TwoNZ).
        apply shift_less_minus.
        apply (a1 (g_ N)).
         exists N.
          apply le_n.
         apply eq_reflexive_unfolded.
        apply less_transitive_unfolded with (y := (a[+]b) [/]TwoNZ).
         apply shift_plus_less.
         rstepr a.
         assumption.
        assumption.
       cut (AbsSmall ((b[-]a) [/]TwoNZ) (g_ n[-]g_ N)).
        intro H8.
        elim H8.
        intros H9 H10.
        apply shift_minus_leEq.
        apply shift_leEq_plus'.
        apply inv_cancel_leEq.
        rstepr (g_ n[-]g_ N).
        assumption.
       apply a0.
       assumption.
      apply eq_symmetric_unfolded.
      assumption.
     intro.
     apply less_transitive_unfolded with (y := z[+](b[-]a) [/]TwoNZ).
      apply plus_cancel_less with (z := [--]z).
      rstepl ([0]:OF).
      rstepr ((b[-]a) [/]TwoNZ).
      apply pos_div_two.
      apply shift_zero_less_minus.
      assumption.
     apply (a1 x).
      exists n.
       assumption.
      assumption.
     apply less_transitive_unfolded with (y := (a[+]b) [/]TwoNZ).
      apply shift_plus_less.
      rstepr a.
      assumption.
     assumption.
    right.
    case (b0 b c).
    intro xj.
    intro p0.
    exists xj.
     elim p0.
     intros H6 H7.
     case H6.
     intro j.
     intros H9 H10.
     red in |- *.
     exists j.
     simpl in |- *.
     assumption.
    elim p0.
    intros.
    assumption.
   apply plus_cancel_less with (z := [--]((a[+]b) [/]TwoNZ)).
   rstepl ([0]:OF).
   rstepr ((b[-]a) [/]TwoNZ).
   apply pos_div_two.
   apply shift_zero_less_minus.
   assumption.
  apply bridges_lemma1b with (P := P N) (is_finite_P := fin_is_fin N).
   intros.
   unfold P in |- *.
   exists t.
    rewrite <- (card_fin N).
    assumption.
   apply (finite_seq N).
  unfold P in |- *.
  intros x H1 z H2.
  case H2.
  intro n.
  intros.
  exists n.
   intros.
   assumption.
  apply eq_transitive_unfolded with (y := x).
   apply eq_symmetric_unfolded.
   assumption.
  assumption.
 apply (pg ((b[-]a) [/]TwoNZ)).
 apply pos_div_two.
 apply shift_zero_less_minus.
 assumption.
Qed.



Definition inf := let (N, _) := bridges_lemma2b in N.


Definition Pinf := ProjT2 bridges_lemma2b.

Lemma Pinf_proj1 : is_lower_bound OF (seq2set g) inf.
Proof.
 unfold inf in |- *.
 elim Pinf.
 auto.
Qed.

Lemma Pinf_unfolded1 :
 forall x : OF, seq2set g x -> forall z : OF, z[<]inf -> z[<]x.
Proof.
 change (is_lower_bound OF (seq2set g) inf) in |- *.
 exact Pinf_proj1.
Qed.

Lemma Pinf_unfolded2 :
 forall c' : OF, inf[<]c' -> {s : OF | seq2set g s | s[<]c'}.
Proof.
 unfold inf in |- *.
 elim Pinf.
 simpl in |- *.
 intros.  rename X into H.
 elim (b c' H); intros x p; elim p; exists x; auto.
Qed.


(* I tried very much not to mention this lemma! *)
Lemma sup_leEq : forall n : nat, g_ n[<=]sup.
Proof.
 intros.
 rewrite -> leEq_def; intro.
 apply (less_irreflexive_unfolded _ sup).
 apply (Psup_unfolded1 (g_ n)).
  red in |- *.
  exists n.
  apply eq_reflexive_unfolded.
 assumption.
Qed.

Lemma inf_geEq : forall n : nat, inf[<=]g_ n.
Proof.
 intros.
 rewrite -> leEq_def; intro.
 apply (less_irreflexive_unfolded _ (g_ n)).
 apply (Pinf_unfolded1 (g_ n)).
  red in |- *.
  exists n.
  apply eq_reflexive_unfolded.
 assumption.
Qed.

Lemma tail_is_Cauchy :
 forall n : nat, Cauchy_prop (fun m : nat => g_ (n + m)).
Proof.
 intros.
 red in |- *.
 intros.
 case (pg (e [/]TwoNZ)).
  apply pos_div_two.
  assumption.
 intro N.
 intros.
 exists N.
 intros.
 rstepr (g_ (n + m)[-]g_ N[+](g_ N[-]g_ (n + N))).
 rstepl (e [/]TwoNZ[+]e [/]TwoNZ).
 apply AbsSmall_plus.
  apply a.
  apply le_trans with (m := m).
   assumption.
  apply le_plus_r.
 apply AbsSmall_minus.
 apply a.
 apply le_plus_r.
Qed.


Definition tail_seq (n : nat) :=
  Build_CauchySeq OF (fun m : nat => g_ (n + m)) (tail_is_Cauchy n).

End Every_Cauchy_Sequence_is_bounded.



Variable g : CauchySeq OF.

Let g_ := CS_seq _ g.
Let pg := CS_proof _ g.

Let sup_tail (n : nat) := sup (tail_seq g n).




Lemma sup_tail_leEq : forall N m : nat, N <= m -> g_ m[<=]sup_tail N.
Proof.
 intros.
 unfold sup_tail in |- *.
 case (le_witness_informative N m H).
 intro k.
 intro.
 apply leEq_wdl with (x := tail_seq g N k).
  apply sup_leEq.
 simpl in |- *.
 rewrite e.
 apply eq_reflexive_unfolded.
Qed.


Lemma sup_tail_is_Cauchy : Cauchy_prop (fun m : nat => sup_tail m).
Proof.
 red in |- *.
 intros.
 cut {N : nat | forall m : nat, N <= m -> AbsSmall (e [/]TwoNZ) (g_ m[-]g_ N)}.
  intros H0.
  case H0.
  intro N.
  intros.
  exists N.
  intros.
  split.
   (* I *)
   apply inv_cancel_leEq.
   rstepl (sup_tail N[-]sup_tail m).
   rstepr e.
   rewrite -> leEq_def; intro.
   apply (less_irreflexive_unfolded _ e).
   case (Psup_unfolded2 (tail_seq g N) (sup_tail m[+]e)).
    change (sup_tail m[+]e[<]sup_tail N) in |- *.
    apply shift_plus_less'.
    assumption.
   intro xj.
   intros H4 H5.
   red in H4.
   case H4.
   intro j.
   intros.
   apply less_leEq_trans with (y := g_ (N + j)[-]g_ m).
    apply shift_less_minus.
    apply shift_plus_less'.
    apply leEq_less_trans with (y := sup_tail m).
     apply sup_tail_leEq.
     apply le_n.
    apply shift_less_minus.
    apply less_wdr with (y := xj).
     assumption.
    assumption.
   cut (AbsSmall e (g_ (N + j)[-]g_ m)).
    intro H7.
    elim H7.
    intros H8 H9.
    assumption.
   rstepr (g_ (N + j)[-]g_ N[+](g_ N[-]g_ m)).
   rstepl (e [/]TwoNZ[+]e [/]TwoNZ).
   apply AbsSmall_plus.
    apply a.
    apply le_plus_l.
   apply AbsSmall_minus.
   apply a.
   assumption.
  (* II *)
  apply less_leEq.
  apply leEq_less_trans with (y := e [/]TwoNZ).
   rewrite -> leEq_def.
   intro.
   apply (less_irreflexive_unfolded _ (e [/]TwoNZ)).
   case (Psup_unfolded2 (tail_seq g m) (sup_tail N[+]e [/]TwoNZ)).
    change (sup_tail N[+]e [/]TwoNZ[<]sup_tail m) in |- *.
    apply shift_plus_less'.
    assumption.
   intro xj.
   intros H4 H5.
   red in H4.
   case H4.
   intro j.
   intros.
   apply less_leEq_trans with (y := g_ (m + j)[-]g_ N).
    apply shift_less_minus.
    apply shift_plus_less'.
    apply leEq_less_trans with (y := sup_tail N).
     apply sup_tail_leEq.
     apply le_n.
    apply shift_less_minus.
    apply less_wdr with (y := xj).
     assumption.
    assumption.
   cut (AbsSmall (e [/]TwoNZ) (g_ (m + j)[-]g_ N)).
    intro H7.
    elim H7.
    intros.
    assumption.
   apply a.
   apply le_trans with (m := m).
    assumption.
   apply le_plus_l.
  apply pos_div_two'.
  assumption.
 apply pg.
 apply pos_div_two.
 assumption.
Qed.

Definition sup_tail_as_Cauchy :=
  Build_CauchySeq OF (fun m : nat => sup_tail m) sup_tail_is_Cauchy.

Let L := inf sup_tail_as_Cauchy.


Lemma sup_tail_decrease :
 forall m n : nat, m <= n -> sup_tail n[<=]sup_tail m.
Proof.
 intros.
 rewrite -> leEq_def; intro.
 case (Psup_unfolded2 (tail_seq g n) (sup_tail m)).
  assumption.
 intro xj.
 intros H2 H3.
 red in H2.
 case H2.
 intro j.
 intros.
 apply (less_irreflexive_unfolded _ xj).
 apply leEq_less_trans with (y := sup_tail m).
  apply leEq_wdl with (x := CS_seq OF (tail_seq g n) j).
   simpl in |- *.
   apply sup_tail_leEq.
   apply le_trans with (m := n).
    assumption.
   apply le_plus_l.
  apply eq_symmetric_unfolded.
  assumption.
 assumption.
Qed.

Lemma L_less_sup_n : forall n : nat, L[<=]sup_tail n.
Proof.
 intros.
 unfold L in |- *.
 change (inf sup_tail_as_Cauchy[<=]CS_seq OF sup_tail_as_Cauchy n) in |- *.
 apply inf_geEq.
Qed.

Lemma Psup_unfolded2_informative :
 forall (h : CauchySeq OF) (b' : OF),
 b'[<]sup h -> {s : OF | seq2set h s | b'[<]s}.
Proof.
 intros.
 apply Psup_unfolded2.
 assumption.
Qed.


Lemma Pinf_unfolded2_informative :
 forall (h : CauchySeq OF) (c' : OF),
 inf h[<]c' -> {s : OF | seq2set h s | s[<]c'}.
Proof.
 intros.
 apply Pinf_unfolded2.
 assumption.
Qed.


Lemma convergent_subseq :
 forall k : nat,
 {N_k : nat | k <= N_k | AbsSmall (one_div_succ k) (g_ N_k[-]L)}.
Proof.
 intros.
 case (Pinf_unfolded2_informative sup_tail_as_Cauchy (L[+]one_div_succ k)).
  change (L[<]L[+]one_div_succ k) in |- *.
  apply shift_less_plus'.
  rstepl ([0]:OF).
  apply one_div_succ_pos.
 intro sN.
 intros.
 red in s.
 case s.
 intro N.
 intros c0.
 case (Psup_unfolded2_informative (tail_seq g (k + N)) (L[-]one_div_succ k)).
  apply less_leEq_trans with (y := L).
   apply shift_minus_less.
   apply shift_less_plus'.
   rstepl ([0]:OF).
   apply one_div_succ_pos.
  change (L[<=]sup_tail (k + N)) in |- *.
  apply L_less_sup_n.
 intro xj.
 intros.
 case s0.
 intro j.
 intros.
 exists (k + N + j).
  apply le_trans with (m := k + N).
   apply le_plus_l.
  apply le_plus_l.
 split.
  apply shift_leEq_minus.
  rstepl (L[-]one_div_succ k).
  apply leEq_wdr with (y := xj).
   apply less_leEq; assumption.
  assumption.
 apply shift_minus_leEq.
 apply leEq_transitive with (y := sN).
  change (CS_seq OF (tail_seq g (k + N)) j[<=]sN) in |- *.
  apply leEq_transitive with (y := sup (tail_seq g (k + N))).
   apply sup_leEq.
  apply leEq_wdr with (y := sup (tail_seq g N)).
   change (sup_tail (k + N)[<=]sup_tail N) in |- *.
   apply sup_tail_decrease.
   apply le_plus_r.
  apply eq_symmetric_unfolded.
  assumption.
 apply less_leEq.
 astepr (L[+]one_div_succ k); auto.
Qed.





(* very elegant proof almost as short as text version! *)
Theorem lubp_gives_Cauchy : SeqLimit g L.
Proof.
 red in |- *.
 intros e H.
 case (is_Archimedes' ((Two[/] e[//]Greater_imp_ap _ e [0] H)[-][1])).
 intro k.
 intros.
 case (pg (e [/]FourNZ)).
  apply div_resp_pos.
   apply pos_four.
  assumption.
 intro N1.
 intros.
 case (convergent_subseq (N1 + k)).
 intro Nk.
 intros.
 elim a0.
 intros.
 exists Nk.
 intros.
 change (AbsSmall e (g_ m[-]L)) in |- *.
 rstepl (e [/]TwoNZ[+]e [/]TwoNZ).
 rstepr (g_ m[-]g_ Nk[+](g_ Nk[-]L)).
 apply AbsSmall_plus.
  rstepl (e [/]FourNZ[+]e [/]FourNZ).
  rstepr (g_ m[-]g_ N1[+](g_ N1[-]g_ Nk)).
  apply AbsSmall_plus.
   apply a.
   apply le_trans with (m := Nk).
    apply le_trans with (m := N1 + k).
     apply le_plus_l.
    assumption.
   assumption.
  apply AbsSmall_minus.
  apply a.
  apply le_trans with (m := N1 + k).
   apply le_plus_l.
  assumption.
 apply AbsSmall_leEq_trans with (e1 := one_div_succ (R:=OF) (N1 + k)).
  unfold one_div_succ in |- *.
  unfold Snring in |- *.
  apply shift_div_leEq.
   apply pos_nring_S.
  cut (e [/]TwoNZ[#][0]).
   intro H3.
   apply shift_leEq_mult' with H3.
    apply pos_div_two.
    assumption.
   rstepl (Two[/] e[//]Greater_imp_ap _ e [0] H).
   change ((Two[/] e[//]Greater_imp_ap OF e [0] H)[<=]nring (N1 + k)[+][1]) in |- *.
   apply shift_leEq_plus.
   apply leEq_transitive with (y := nring (R:=OF) k).
    apply less_leEq; assumption.
   apply nring_leEq.
   apply le_plus_r.
  apply Greater_imp_ap.
  apply pos_div_two.
  assumption.
 assumption.
Qed.

End proofs_in_TCS.

Definition Bridges_R_is_CReals :=
  Build_is_CReals OF (fun g : CauchySeq OF => inf (sup_tail_as_Cauchy g))
    lubp_gives_Cauchy is_Archimedes.

Definition Bridges_R_as_CReals :=
  Build_CReals OF (fun g : CauchySeq OF => inf (sup_tail_as_Cauchy g))
    Bridges_R_is_CReals.


End bridges_axioms_imply_ours.
(* end hide *)
(** remove printing Q *)
