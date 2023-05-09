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

Require Export CoRN.algebra.CSetoidInc.
Require Export CoRN.reals.RealLists.
Set Automatic Introduction.

Section Intervals.

(**
* Intervals
In this section we define (compact) intervals of the real line and
some useful functions to work with them.

** Definitions

We start by defining the compact interval [[a,b]] as being the set of
points less or equal than [b] and greater or equal than [a].  We
require [a [<=] b], as we want to work only in nonempty intervals.
*)

Definition compact (a b : IR) (Hab : a [<=] b) (x : IR) := a [<=] x and x [<=] b.

(**
%\begin{convention}% Let [a,b : IR] and [Hab : a [<=] b].
%\end{convention}%

As expected, both [a] and [b] are members of [[a,b]].  Also they are
members of the interval [[Min(a,b),Max(a,b)]].
*)

Variables a b : IR.
Hypothesis Hab : a [<=] b.

Lemma compact_inc_lft : compact a b Hab a.
Proof.
 intros; split; [ apply leEq_reflexive | auto ].
Qed.

Lemma compact_inc_rht : compact a b Hab b.
Proof.
 intros; split; [ auto | apply leEq_reflexive ].
Qed.

Lemma compact_Min_lft : forall Hab', compact (Min a b) (Max a b) Hab' a.
Proof.
 split; [ apply Min_leEq_lft | apply lft_leEq_Max ].
Qed.

Lemma compact_Min_rht : forall Hab', compact (Min a b) (Max a b) Hab' b.
Proof.
 split; [ apply Min_leEq_rht | apply rht_leEq_Max ].
Qed.

(**
As we will be interested in taking functions with domain in a compact
interval, we want this predicate to be well defined.
*)

Lemma compact_wd : pred_wd IR (compact a b Hab).
Proof.
 intros; red in |- *; intros x y H H0.
 inversion_clear H; split.
  apply leEq_wdr with x; assumption.
 apply leEq_wdl with x; assumption.
Qed.

(**
Also, it will sometimes be necessary to rewrite the endpoints of an interval.
*)

Lemma compact_wd' : forall (a' b' : IR) Hab' (x : IR),
 a [=] a' -> b [=] b' -> compact a b Hab x -> compact a' b' Hab' x.
Proof.
 intros a' b' Hab' x H H0 H1.
 inversion_clear H1; split.
  apply leEq_wdl with a; auto.
 apply leEq_wdr with b; auto.
Qed.

(**
As we identify subsets with predicates, inclusion is simply implication.
*)

(**
Finally, we define a restriction operator that takes a function [F]
and a well defined predicate [P] included in the domain of [F] and
returns the restriction $F|_P$# of F to P#.
*)

Definition Frestr F P (HP : pred_wd IR P) (H : included P (Dom F)) : PartIR.
Proof.
 intros.
 apply Build_PartFunct with P (fun (x : IR) (Hx : P x) => Part F x (H x Hx)).
  assumption.
 intros. exact (pfstrx _ _ _ _ _ _ X).
Defined.

End Intervals.

Notation Compact := (compact _ _).
Arguments Frestr [F P].
Notation FRestr := (Frestr (compact_wd _ _ _)).

Section More_Intervals.

Lemma included_refl' : forall a b Hab Hab', included (compact a b Hab) (compact a b Hab').
Proof.
 intros.
 red in |- *; intros x H.
 inversion_clear H; split; auto.
Qed.

(** We prove some inclusions of compact intervals.  *)

Definition compact_map1 : forall a b Hab Hab',
 included (compact (Min a b) (Max a b) Hab') (compact a b Hab).
Proof.
 intros.
 red in |- *; intros x H.
 red in |- *; red in H.
 inversion_clear H.
 split.
  eapply leEq_wdl; [ apply H0 | apply leEq_imp_Min_is_lft; auto ].
 eapply leEq_wdr; [ apply H1 | apply leEq_imp_Max_is_rht; auto ].
Defined.

Definition compact_map2 : forall a b Hab Hab',
 included (compact a b Hab) (compact (Min a b) (Max a b) Hab').
Proof.
 intros.
 red in |- *; intros x H.
 red in |- *; red in H.
 inversion_clear H.
 split.
  eapply leEq_transitive; [ apply Min_leEq_lft | apply H0 ].
 eapply leEq_transitive; [ apply H1 | apply rht_leEq_Max ].
Defined.

Definition compact_map3 : forall a b e Hab Hab', [0] [<] e ->
 included (compact a (b[-]e) Hab') (compact a b Hab).
Proof.
 intros; red in |- *. try rename X into H.
 intros x H0. inversion_clear H0; split.
 auto.
 eapply leEq_transitive.
  apply H2.
 apply shift_minus_leEq.
 apply shift_leEq_plus'.
 astepl ZeroR; apply less_leEq; assumption.
Qed.

End More_Intervals.

#[global]
Hint Resolve included_refl' compact_map1 compact_map2 compact_map3 : included.

Section Totally_Bounded.

(**
** Totally Bounded

Totally bounded sets will play an important role in what is
to come.  The definition (equivalent to the classical one) states that
[P] is totally bounded iff
%\[\forall_{\varepsilon>0}\exists_{x_1,\ldots,x_n}\forall_{y\in P}
\exists_{1\leq i\leq n}|y-x_i|<\varepsilon\]%#&forall;e&gt;0
&exist;x<sub>1</sub>,...,x<sub>n</sub>&forall;y&isin;P&exist;
1&le;i&le;n.|y-x<sub>i</sub>|&lt;e#.

Notice the use of lists for quantification.
*)

Definition totally_bounded (P : IR -> CProp) : CProp := {x : IR | P x} and (forall e,
 [0] [<] e -> {l : list IR | forall x, member x l -> P x |
 forall x, P x -> {y : IR | member y l | AbsSmall e (x[-]y)}}).

(**
This definition is classically, but not constructively, equivalent to
the definition of compact (if completeness is assumed); the next
result, classically equivalent to the Heine-Borel theorem, justifies
that we take the definition of totally bounded to be the relevant one
and that we defined compacts as we did.
*)

Lemma compact_is_totally_bounded : forall a b Hab, totally_bounded (compact a b Hab).
Proof.
 intros. split.
  - (* compact intervals are nonempty because they include their left endpoints. *)
    exists a.
    apply compact_inc_lft.
  -  (* Show that if you have n, [a,b], and e, and (b-a)/e <= n and n - 2 <= (b-a)/e when 2 <= n...
        then we can construct our list of reals for purposes of covering the interval in balls with radius e.
        It will then be on us to prove that this fact is true. *)
     enough (forall (n : nat) (a b e : IR) (Hab : a [<=] b) (He : [0] [<] e),
     ((b[-]a)[/] e[//]pos_ap_zero IR e He) [<=] nring n ->
     (2 <= n -> nring n[-]Two [<=] ((b[-]a)[/] e[//]pos_ap_zero _ _ He)) ->
       {l : list IR | forall x : IR, member x l -> compact a b Hab x | forall x : IR,
         compact a b Hab x -> {y : IR | member y l | AbsIR (x[-]y) [<=] e}}) as H.
    + (* first we use the fact above to prove the conclusion that our compact interval is totally bounded. *)
      intros e He.
      (* Strong Archimedes implies we can find an element n such that n - 2 <= b-a / (e /2) <= n *)
      destruct (str_Archimedes ((b[-]a)[/] (e[/]TwoNZ) [//]pos_ap_zero IR (e [/]TwoNZ) (pos_div_two IR e He))) as [n Hn].
       * (* This is only going to pass muster if we can show that 0 <= (b-a) / (e / 2). *) 
         { (* we are at liberty to move (e/2) over to the LHS provided it's positive. *)
           apply shift_leEq_div.
           - (* showing that 0 < e / 2 *)
             (* 0 < e implies 0 < e / 2, but 0 < e is known. *) apply pos_div_two; assumption. 
           - (* showing that 0 * (e / 2) <= b - a *)
             (* 0 * e/2 + a <= b implies 0 * e/2 <= b - a *) apply shift_leEq_minus.
             (* 0 * e/2 + a = a on the LHS *) rstepl a.
             (* but a <= b was known already *) assumption. }
       * (* split the facts that b-a/(e/2) <= n and 2 <= n -> n - 2 <= (b-a)/(e/2) into two hypotheses. *)
         destruct Hn.
         (* Use the hypothesis for (e/2) *)
         (* the next step would nominally require we prove two other steps, that (b-a)/(e/2) <= n and that n-2 <= (b-a)/(e/2).
            but we have these from the Strong Archimedian Principle, so we immediately dispatch them with "try assumption". *)
         destruct (H n a b _ Hab (pos_div_two _ _ He)) as [l Hl' Hl]; try assumption.
         (* now we are obliged to prove that we have a list for which every member is in [a,b],  *)
         (* The claimed hypotheses are that we have our list already, that all the x in l are in our interval, and
            that for every x in [a,b], there's a y in l such that the |x-y| <= (e/2). But obviously this means it would
            work for e as well, since e/2 < e. *)
         exists l.
         (* we already had the elements guaranteed to be in the interval by assumption! *)
         assumption.
         (* Let's look at the x in our interval and show they have some y that they are within e of. *)
         intros x Hx.
         (* If we have x in Hx, we can apply it to our list we generated before to exhibit some y such that |x-y| <= e/2 *)
         destruct (Hl x Hx) as [y Hy Hy'].
         (* Let's use that y now for |x - y| < e *)
         { exists y.
           - (* Need to show y is in l but we already assumed that y was in l. *) assumption.
           - (* Basically just converting AbsSmall notation into AbsIR notation *) apply AbsIR_imp_AbsSmall.
             (* If |x - y| <= e / 2 and e / 2 <= e, then |x - y | <= e *) apply leEq_transitive with (e [/]TwoNZ).
             + (* we have | x - y | <= e/2 by assumption *) assumption.
             + (* e / 2 < e implies e / 2 <= e *) apply less_leEq.
               (* we previously proved that if 0 < e then e / 2 < e *) apply pos_div_two'; assumption. }
   + (* It is now time to induct on the size of n.
        This makes sense--we are saying that depending on how small we make our epsilon, 
        we may exploit the existence of an n such that n - 2 <= (b-a) / e <= n to construct our list.
        Probably by explicitly constructing the list of nish elements? *)
        clear Hab a b; intro n; destruct n as [| n'].
        * (* n = 0 means our interval is a point, and our list can just be {a}. *)
          intros.
          { exists (a::nil).
            - (* must show that every element of this list is in the interval! *)
              (* suppose x is in our list a::nil. *) intros x H1.
              inversion H1 as [H2 | H2].
              + (* case 1: x in nil. Dumb as hell. *) destruct H2.
              + (* because being in the interval [a,b] is well-defined, we can replace x with a. *) 
                apply compact_wd with a; algebra.
                (* it is known that the left endpoint is inside a compact interval. *) apply compact_inc_lft.
            - (* remains to show that for x in the interval, there's an element in the list within e of the element. *)
              (* let x be such an element *) intros x H1.
              (* our y can just be a. In fact this is all it can be *) exists a.
              + (* a is in our list *)
              right; algebra.
              + (* and |x - a| <= e *)
                (* we claim that x - a = 0, and prove that this implies 0 <= e *) apply leEq_wdl with ZeroR.
                * (* 0 <= e because 0 < e which is assumed. *) apply less_leEq; assumption.
                * (* 0 = |0| so we can replace it *) astepl (AbsIR [0]).
                  (* if 0 = x - a, then |0| = |x-a| *) apply AbsIR_wd.
                  { (* it'd be enough to show x - a <= 0 and 0 <= x - a *) apply leEq_imp_eq.
                    - (* a <= x implies 0 <= x - a, but this is true by the fact that x in [a,b] *)
                      apply shift_leEq_minus. astepl a. destruct H1 as [HL HU]. apply HL.
                    - (* x <= a implies x - a <= 0 *) apply shift_minus_leEq.
                      (* if x <= b and b <= a then x <= a.
                         despite the fact that b <= a looks wrong, this will work because of how small n was! *)
                      apply leEq_transitive with b.
                      + (* x <= b follows from x in [a,b] *) destruct H1 as [HL HU]. assumption.
                      + (* b <= a if b - a <= 0 *) apply shift_leEq_plus.
                        (* we can multiply by 1/e since 0 < 1/e *) apply mult_cancel_leEq with ([1][/] _[//]pos_ap_zero _ _ He).
                        * (* 0 < 1/e since 0 < e *) apply recip_resp_pos; auto.
                        * (* the RHS can be replaced with zero *) astepr ZeroR.
                          (* we can rewrite as (b-a)/e <= 0 *) rstepl (b[-]a[/] _[//]pos_ap_zero _ _ He).
                          (* but this was known by our use of the Archimedian principle and the fact that n = 0 *) assumption. } }
        * (* The case where n = S n'. We again destruct n'. *)
          { destruct n' as [| n''].
            - (* case: n = 1 *)
              intros.
              (* again, all we need is the singleton list {a} *) 
              exists (a::nil).
              + (* and again we have to prove that this list is in [a,b] *) 
                intros x H1.
                destruct H1 as [H2|].
                * destruct H2.
                * apply compact_wd with a; [ apply compact_inc_lft | algebra ].
              + (* now we prove that all points are contained in a bubble about a. *)
                 (* let x in [a,b] *)
                 intros x Hx.
                 (* then a <= x and x <= b *)
                 destruct Hx.
                 (* for our y we have only one choice: a. *)
                 exists a.
                 * (* proving a is in {a} *) simpl in |- *; right; algebra.
                 * (* proving |x - a| <= e *)
                   { (* we will replace |x - a| with x - a *)
                     apply (leEq_wdl IR (x [-] a) e (AbsIR (x [-] a))).
                     - (* to show x - a <= e, show x - a <= b - a and b - a <= e. *) 
                       apply leEq_transitive with (b[-]a).
                       + (* x <= b implies x - a <= b - a *)
                         apply minus_resp_leEq. assumption.
                       + (* showing b - a <= e *)
                         (* b - a <= e * 1 implies b - a <= e *)
                         rstepr (e[*]nring 1).
                         (* (b - a ) / e <= 1 *)
                         eapply shift_leEq_mult'.
                         * (* we need e positive. It is by assumption. *) assumption.
                         * (* (b - a) / e <= 1. this is true because of n = 1 *) apply H.
                     - (* finally showing x - a = |x - a| *)
                       (* x - a = | x - a | if 0 <= x - a *)
                       apply eq_symmetric_unfolded; apply AbsIR_eq_x.
                       (* 0 + a <= x implies 0 <= x - a *)
                       apply shift_leEq_minus.
                       (* 0 + a = 0 on LHS *)
                       astepl a.
                       (* we assumed a <= x *)
                       assumption. }
          - (* finally, real induction. *) 
            induction n'' as [| n''' Hrecn].
            + (* n = 2 *) intros.
              (* useful to have the fact that e is apart from 0 *)
              set (enz := pos_ap_zero _ _ He) in *.
              (* the midpoint of a and b is actually good enough.
                 in other words we can just use {(a+b)/2} as our list. *)
              exists (cons ((a[+]b) [/]TwoNZ) (@nil IR)).
              * (* time to prove a <= (a+b)/2 <= b *)
                intros x H1.
                (* x in (a+b)/2 :: nil means x = (a+b)/2 or x in nil *)
                { destruct H1 as [H2|].
                  - (* x in nil is absurd *) destruct H2.
                  - (* x = (a+b)/2 *)
                    (* use the fact that membership in [a,b] is well-defined to rewrite.*) 
                    apply compact_wd with ((a[+]b) [/]TwoNZ).
                    + (* prove that a <= (a+b)/2 and (a+b)/2 <= b separately. *)
                      split.
                      * (* a <= (a+b)/2 *)
                        (* rewrite as 0 <= (a+b)/2 - a *)
                        astepl (a[+][0]); apply shift_plus_leEq'.
                        (* multiply both sides by two *)
                        { apply mult_cancel_leEq with (Two:IR).
                          - (* need 0 < 2 to do this operation *) apply pos_two.
                          - (* LHS = 0 *) astepl ZeroR.
                            (* RHS = b - a *) rstepr (b[-]a).
                            (* a <= b implies 0 <= b - a *)
                            apply shift_leEq_minus; astepl a; auto. }
                      * (* (a+b)/2 <= b *)
                        (* (a+b)/2 - b <= 0 implies (a-b) / 2 <= b *)
                        astepr (b[+][0]); apply shift_leEq_plus'.
                        (* multiply by 2 on both sides *)
                        { apply mult_cancel_leEq with (Two:IR).
                          - apply pos_two.
                          - astepr ZeroR.
                            rstepl (a[-]b).
                            apply shift_minus_leEq; astepr b; auto. }
                   + algebra. }
              * (* time to prove that a ball of radius e about this point covers *)
                (* let x in [a,b] *) intros.
                (* x will be covered by the ball about the midpoint. *)
                { exists ((a[+]b) [/]TwoNZ).
                  - (* proving this midpoint is in our list *) right; algebra.
                  - (* proving x is in our ball *)
                    (* we rewrite |x - (a+b)/2| as max(x, (a+b)/2) - min(x, (a+b)/2). *)
                    eapply (leEq_wdl IR (Max x ((a [+] b) [/]TwoNZ) [-] Min x ((a [+] b) [/]TwoNZ)) e).
                    + (* rewrite as max(x, (a+b)/2) <= e + min(x, (a+b)/2) *)
                      apply shift_minus_leEq.
                      (* to prove that Max(x, (a+b)/2) is less than e + min(x, (a+b)/2),
                         it suffices to prove 
                         x <= e + min(x, (a+b)/2) and (a+b)/2 <= e + min(x, (a+b)/2). *)
                      apply Max_leEq.
                      * (* x <= e + min(x, (a+b)/2) *)
                        (* x - e <= min(x, (a+b)/2) *) apply shift_leEq_plus'.
                        { (* prove that x - e <= min(x, (a+b)/2) by cases. *)
                          apply leEq_Min.
                          - (* x - e <= x *)
                            (* x - x <= e *)
                            apply shift_minus_leEq. apply shift_leEq_plus'.
                            astepl ZeroR. apply less_leEq. assumption.
                          - (* x - e <= (a+b)/2 *)
                            (* x <= (a+b)/2 + e *)
                            apply shift_minus_leEq.
                            (* x <= b and b <= (a+b)/2 + e implies x <= (a+b)/2+e *)
                            apply leEq_transitive with b.
                            + (* x <= b, by x in [a,b] *) destruct H1; auto.
                            + (* b <= (a+b)/2 + e *)
                              (* b - (a+b)/2 <= e *)
                              apply shift_leEq_plus'.
                              (* multiply by 2 *)
                              apply mult_cancel_leEq with (Two:IR).
                              * (* need 0 < 2 *) apply pos_two.
                              * { (* divide by e *)
                                  apply shift_leEq_mult' with enz.
                                  - (* need 0 < e, known by assumption. *) assumption.
                                  - (* LHS is now (b-a)/e *) rstepl (b[-]a[/] e[//]enz).
                                    (* (b-a)/e <= n = 2 is from our case analysis on n *)
                                     assumption. } }
                      * (* (a+b)/2 <= e + min(x, (a+b)/2) *)
                        (* (a+b)/2 - e <= min(x, (a+b)/2) *) apply shift_leEq_plus'. 
                        { (* prove that (a+b)/2 - e <= min(x, (a+b)/2) by cases *) 
                          apply leEq_Min.
                          - (* (a+b)/2 - e <= x *)
                            (* (a+b)/2 - e <= a and a <= x implies (a+b)/2 <= x *)
                            apply leEq_transitive with a.
                            + (* (a+b)/2 - e <= a *) 
                              (* (a+b)/2 - a <= e *)
                              apply shift_minus_leEq; apply shift_leEq_plus'.
                              (* multiply by 2 *)
                              apply mult_cancel_leEq with (Two:IR).
                              * (* need 0 < 2 *) apply pos_two.
                              * { (* divide by e *) 
                                  apply shift_leEq_mult' with enz.
                                  - (* need 0 < e, known by assumption *) assumption.
                                  - (* (b - a) / 2 <= n = 2 from our case analysis on n *) 
                                    rstepl (b[-]a[/] e[//]enz); auto. }
                            + (* a <= x from x in [a,b] *) elim H1; auto.
                        - (* (a+b)/2 - e <= (a+b)/2 *) 
                          (* (a+b)/2 - (a+b)/2 <= e *)
                          apply shift_minus_leEq; apply shift_leEq_plus'.
                          (* 0 <= e, follows from 0 < e which is assumed. *)
                          astepl ZeroR; apply less_leEq; auto. }
                    + (* justifying the rewrite of |x-(a+b)/2| *)
                      apply eq_symmetric_unfolded; apply Abs_Max. }
            + (* n = S (S (S n''')) *) 
              (* reintroduce a,b,e, a<=b, 0 < e, 
                 (b-a)/e <= n, and 2 <= n -> n - 2 <= (b-a)/e *)
              intros.
              (* introduce b' = b-e *)
              set (b' := b[-]e) in *.
              (* we'll need a <= b', so introduce and later prove it. *)
              enough (a [<=] b') as H1.
              (* Applying the fact that if you have interval [a,b'], 0<e, (b-a)/e <= n-1, and
                 2 <= n - 1, then you can construct a cover of [a,b']. l is our list,
                 Hl' is the fact that the list is composed of elements of [a,b'], and
                 Hl is the fact that balls over the list elements cover [a,b'].
                 The fact that we've applied this with b', and not b, is essential
                 because otherwise we can't repurpose the cover (the balls will be too big!) *)
              destruct (Hrecn a b' e H1 He) as [l Hl' Hl].
              * (* to have applied our Hrecn, we actually need that
                   (b'-a)/e <= n-1. *)
                (* replace b' = b-e in our conclusion,
                   (b-e-a)/e <= n-1 *)
                unfold b' in |- *.
                (* (b-a)/e - 1 <= n - 1 *)
                rstepl ((b[-]a[/] e[//]pos_ap_zero _ _ He) [-][1]).
                (* (b-a)/e <= n - 1 + 1 *)
                apply shift_minus_leEq.
                (* simplify to (b-a)/e <= n, which is known by assumption *)
                astepr (nring (R:=IR) (S (S (S n''')))). assumption.
              * (* 2 <= n - 1 -> n - 1 - 2 <= (b'-a)/e *)
                (* move the 2 <= n - 1 into the proof environment,
                   where we won't use it. *) intro.
                (* rewrite b' = b-e in the conclusion *)
                unfold b' in |- *.
                (* n - 1 - 2 <= (b-a)/e - 1 *)
                rstepr ((b[-]a[/] e[//]pos_ap_zero _ _ He) [-][1]).
                (* n - 1 - 2 + 1 <= (b-a)/e *)
                apply shift_leEq_minus.
                (* n - 1 + 1 - 2 <= (b-a)/e *)
                rstepl (nring (R:=IR) (S (S n''')) [+][1][-]Two).
                (* simplify with arithmetic to get our given assumption about n *)
                auto with arith.
              * (* take the list that worked for [a,b'], and add b' to the list.
                   this will work for [a,b]. *)
                { exists (cons b' l).
                  - (* must prove b' :: l is composed of elements of [a,b] *)
                    (* let x be an element of b'::l *)
                    intros x H2.
                    (* rewrite b' as b - e in a<=b' (proof environment) *)
                    unfold b' in H1. Check compact_map3.
                    (* if a <= b and a <= b - e, 0 < e, then [a,b-e] is in [a,b] *)
                    apply compact_map3 with (e := e) (Hab' := H1) (b := b).
                    + (* the fact that 0 < e is known by assumption *) assumption.
                    + (* remains to show that x in [a,b-e]. *) 
                      (* either x in l or x = b' *)
                      simpl in H2. destruct H2.
                      * (* if x in l', we can use the knowledge that l' in [a,b-e] *) apply Hl'. assumption.
                      * (* if x = b', we can use the fact that membership is well-defined to substitute x for b' *)
                        apply compact_wd with b'; [ apply compact_inc_rht | algebra ]. 
                  - (* must prove that our list of balls covers [a,b] *)
                    (* let x be an element of [a,b] *) intros.
                    (* we will use the fact that either x < b' or b'-e < x *)
                    enough (x [<] b' or b'[-]e [<] x) as H3.
                    * { destruct H3.
                        - (* case x < b' *)
                          (* enough to use the fact that x in [a,b'] *)
                          enough (compact a b' H1 x) as H3.
                          + (* being in [a,b'] implies you can grab an open ball radius e from l and cover yourself *)
                            destruct (Hl x H3) as [y Hy Hy'].
                            (* but now we can use the fact that this open ball from l is in b' :: l (our new list) *)
                            exists y.
                            * (* the fact that y is in b' :: l comes from the assumption it is in l *) left; assumption.
                            * (* the fact that x is within e of y comes from the fact that we used our previous cover to get y *) assumption.
                          + (* need to show that in fact [a,b'] is in [a,b] *) 
                            (* rewrite the fact that x in [a,b] as a <= x and x <= b *)
                            destruct H2 as [Halex Hxleb].
                            (* prove x in [a,b'] by splitting into proofs that a <= x and x<=b' *)
                            split.
                            * (* we got a <= x from x in [a,b] *) assumption.
                            * (* if x < b', then x <= b' *) apply less_leEq. assumption.
                        - (* case b' - e < x *)
                          (* then x is covered by the ball around b' that we added to the original list *)
                          exists b'.
                          + (* b' in b' :: l *) right; algebra.
                          + (* |x-b'| <= e *)
                            (* rewrite |x-b'| as max(x-b', -(x-b')) *) simpl in |- *; unfold ABSIR in |- *.
                            (* if x-b' <= e, and -(x-b') <= e, then max(x-b', -(x-b')) <= e *)
                            apply Max_leEq.
                            * (* x-b' <= e *)
                              (* x <= e + b' *) apply shift_minus_leEq.
                              (* x <= e + b - e *) unfold b' in |- *.
                              (* x <= b *) rstepr b.
                              (* follows from x in [a,b] *) destruct H2 as [Halex Hxleb]. assumption.
                            * (* -(x-b') <= e *)
                              (* b'-x <= e *)
                              rstepl (b'[-]x).
                              (* b' <= e + x *) apply shift_minus_leEq.
                              (* b' - e <= x *) apply shift_leEq_plus'. 
                              (* b' - e < x implies b' - e <= x *) apply less_leEq.
                              (* but this was the assumption of the current case *) assumption. }
                    * (* proving that x<b' or b'-e < x so we can use it above *)
                      { enough (b'[-]e [<] x or x [<] b') as Hcotrans.
                        - (* b'-e < x or x < b' implies x < b' or b'-e < x is just commutativity of \/ *) tauto.
                        - (* b' - e < b' will imply b'-e < x or x < b' *) apply less_cotransitive_unfolded.
                          (* b' < b' + e *) apply shift_minus_less.
                          (* b' - b' < e *) apply shift_less_plus'.
                          (* 0 < e, which is assumed *) astepl ZeroR. assumption. } }
              * (* to have applied Hrecn, we also actually needed a <= b', which is guaranteed by the smallness of e *)
                (* b' = b - e *) unfold b' in |- *.
                (* e <= b - a *) apply shift_leEq_minus; apply shift_plus_leEq'.
                (* divide both sides by e so we can use the hypothesis about e being small *) 
                { astepl ([1][*]e); apply shift_mult_leEq with (pos_ap_zero _ _ He).
                  - (* 0 < e is assumed *) assumption.
                  - (* if 1 <= n - 2 and n-2 <= (a-b)/e, this will show 1 <= (a-b)/e *)
                    apply leEq_transitive with (nring (R:=IR) (S (S (S n'''))) [-]Two).
                    + (* 1 + 2 <= n *) apply shift_leEq_minus.
                      (* 3 <= n *) rstepl (Three:IR).
                      (* both sides are natural numbers. turn into a problem in nat *) apply nring_leEq.
                      (* n = S (S (S n''')) so this is going to be automatic *) auto with arith.
                    + (* as long as 2 <= S (S (S n''')), we will have n - 2 <= (a-b)/e *) apply H0.
                      (* but this is automatic from how S (S (S n''')) is constructed. *) auto with arith. } }
Qed.

(**
Suprema and infima will be needed throughout; we define them here both
for arbitrary subsets of [IR] and for images of functions.
*)

Definition set_glb_IR (P : IR -> CProp) a : CProp := (forall x, P x -> a [<=] x) and
 (forall e, [0] [<] e -> {x : IR | P x | x[-]a [<] e}).

Definition set_lub_IR (P : IR -> CProp) a : CProp := (forall x, P x -> x [<=] a) and
 (forall e, [0] [<] e -> {x : IR | P x | a[-]x [<] e}).

Definition fun_image F (P : IR -> CProp) x : CProp := {y : IR |
 P y and Dom F y and (forall Hy, F y Hy [=] x)}.

Definition fun_glb_IR F (P : IR -> CProp) a : CProp :=
 set_glb_IR (fun_image F P) a.

Definition fun_lub_IR F (P : IR -> CProp) a : CProp :=
 set_lub_IR (fun_image F P) a.

(* begin hide *)
Let aux_seq_lub (P : IR -> CProp) (H : totally_bounded P) :
  forall k : nat,
  Build_SubCSetoid IR
    (fun x : IR =>
     P x and (forall y : IR, P y -> y[-]x [<=] Two[*]one_div_succ k)).
Proof.
 elim H; clear H; intros non_empty H k.
 elim (H (one_div_succ k) (one_div_succ_pos IR k)).
 intros l Hl' Hl; clear H.
 cut {y : IR | member y l | maxlist l[-]one_div_succ k [<=] y}.
  intro H; inversion_clear H.
  2: apply maxlist_leEq_eps.
   2: inversion_clear non_empty.
   2: elim (Hl x).
    2: intros.
    2: exists x0.
    2: tauto.
   2: assumption.
  2: apply one_div_succ_pos.
 exists x; split.
  apply Hl'; assumption.
 intros y Hy.
 elim (Hl y Hy).
 intros z Hz Hz'.
 rstepl (y[-]z[+] (z[-]x)).
 rstepr (one_div_succ (R:=IR) k[+]one_div_succ k).
 apply plus_resp_leEq_both.
  apply leEq_transitive with (AbsIR (y[-]z)).
   apply leEq_AbsIR.
  apply AbsSmall_imp_AbsIR; assumption.
 apply shift_minus_leEq.
 apply leEq_transitive with (maxlist l).
  apply maxlist_greater; assumption.
 apply shift_leEq_plus'.
 assumption.
Qed.

Let aux_seq_lub_prop :
  forall (P : IR -> CProp) (H : totally_bounded P),
  (forall k : nat, P (scs_elem _ _ (aux_seq_lub P H k)))
  and (forall (k : nat) (y : IR),
       P y -> y[-]scs_elem _ _ (aux_seq_lub P H k) [<=] Two[*]one_div_succ k).
Proof.
 intros; cut (forall k : nat, P (scs_elem _ _ (aux_seq_lub P H k)) and (forall y : IR,
   P y -> y[-]scs_elem _ _ (aux_seq_lub P H k) [<=] Two[*]one_div_succ k)).
  intro H0.
  split; intro; elim (H0 k); intros.
   assumption.
  apply b; assumption.
 intro; apply scs_prf.
Qed.
(* end hide *)

(**
The following are probably the most important results in this section.
*)

Lemma totally_bounded_has_lub : forall P,
 totally_bounded P -> {z : IR | set_lub_IR P z}.
Proof.
 intros P tot_bnd.
 red in tot_bnd.
 elim tot_bnd; intros non_empty H.
 cut {sequence : nat -> IR | forall k : nat, P (sequence k) |
   forall (k : nat) (x : IR), P x -> x[-]sequence k [<=] Two[*]one_div_succ k}.
  intros H0.
  elim H0.
  intros seq Hseq Hseq'.
  cut (Cauchy_prop seq).
   intro H1.
   set (seq1 := Build_CauchySeq IR seq H1) in *.
   exists (Lim seq1).
   split; intros.
    apply shift_leEq_rht.
    astepl ( [--]ZeroR); rstepr ( [--] (x[-]Lim seq1)).
    apply inv_resp_leEq.
    set (seq2 := Cauchy_const x) in *.
    apply leEq_wdl with (Lim seq2[-]Lim seq1).
     2: apply cg_minus_wd; [ unfold seq2 in |- *; apply eq_symmetric_unfolded; apply Lim_const
       | algebra ].
    apply leEq_wdl with (Lim (Build_CauchySeq IR (fun n : nat => seq2 n[-]seq1 n)
      (Cauchy_minus seq2 seq1))).
     apply leEq_transitive with (Lim twice_inv_seq).
      apply Lim_leEq_Lim; intro; simpl in |- *.
      apply Hseq'; assumption.
     apply eq_imp_leEq.
     apply eq_symmetric_unfolded; apply Limits_unique.
     red in |- *; fold (SeqLimit twice_inv_seq [0]) in |- *.
     apply twice_inv_seq_Lim.
    apply Lim_minus.
   cut (Cauchy_Lim_prop2 seq (Lim seq1)).
    intro H4; red in H4. try rename X into H2.
    elim (H4 (e [/]TwoNZ) (pos_div_two _ _ H2)); clear H4.
    intros n Hn.
    exists (seq n).
     apply Hseq.
    apply leEq_less_trans with (AbsIR (Lim seq1[-]seq n)).
     apply leEq_AbsIR.
    apply leEq_less_trans with (e [/]TwoNZ).
     apply AbsSmall_imp_AbsIR.
     apply AbsSmall_minus; simpl in |- *; apply Hn.
     apply le_n.
    apply pos_div_two'; auto.
   cut (Cauchy_Lim_prop2 seq1 (Lim seq1)); intros.
    try rename X0 into H3.
    red in |- *; red in H3.
    intros eps Heps; elim (H3 eps Heps); clear H3; intros.
    exists x.
    intros m Hm; elim (p m Hm); clear p.
    intros.
    astepr (seq1 m[-]Lim seq1).
    apply AbsIR_eq_AbsSmall; assumption.
   red in |- *; fold (SeqLimit seq1 (Lim seq1)) in |- *.
   apply ax_Lim.
   apply crl_proof.
  red in |- *; intros. try rename X into H1.
  elim (Archimedes ([1][/] e[//]pos_ap_zero _ _ H1)).
  intros n Hn.
  exists (S (2 * n)); intros.
  cut ([0] [<] nring (R:=IR) n); intros.
   apply AbsIR_eq_AbsSmall. try rename X into H3.
    apply leEq_transitive with ( [--] ([1][/] nring n[//]pos_ap_zero _ _ H3)).
     apply inv_resp_leEq.
     apply shift_div_leEq.
      assumption.
     eapply shift_leEq_mult'; [ assumption | apply Hn ].
    rstepr ( [--] (seq (S (2 * n)) [-]seq m)); apply inv_resp_leEq.
    apply leEq_transitive with (Two[*]one_div_succ (R:=IR) m).
     auto.
    apply leEq_transitive with (one_div_succ (R:=IR) n).
     unfold one_div_succ in |- *.
     unfold Snring in |- *.
     rstepl ([1][/] nring (S m) [/]TwoNZ[//]
       div_resp_ap_zero_rev _ _ _ _ (nring_ap_zero IR (S m) (sym_not_eq (O_S m)))).
     apply recip_resp_leEq.
      apply pos_nring_S.
     apply shift_leEq_div.
      apply pos_two.
     simpl in |- *; fold (Two:IR) in |- *.
     rstepl (Two[*]nring (R:=IR) n[+][1][+][1]).
     apply plus_resp_leEq.
     apply leEq_wdl with (nring (R:=IR) (S (2 * n))).
      apply nring_leEq; assumption.
     Step_final (nring (R:=IR) (2 * n) [+][1]).
    unfold one_div_succ in |- *; unfold Snring in |- *; apply recip_resp_leEq.
     assumption.
    simpl in |- *; apply less_leEq; apply less_plusOne.
   apply leEq_transitive with (Two[*]one_div_succ (R:=IR) (S (2 * n))).
    auto.
   apply less_leEq. try rename X into H3.
   apply less_leEq_trans with ([1][/] nring n[//]pos_ap_zero _ _ H3).
    astepl (one_div_succ (R:=IR) (S (2 * n)) [*]Two).
    unfold one_div_succ in |- *; unfold Snring in |- *.
    apply shift_mult_less with (two_ap_zero IR).
     apply pos_two.
    rstepr ([1][/] Two[*]nring n[//] mult_resp_ap_zero _ _ _ (two_ap_zero IR) (pos_ap_zero _ _ H3)).
    apply recip_resp_less.
     astepl (ZeroR[*][0]); apply mult_resp_less_both; try apply leEq_reflexive;
       [ apply pos_two | assumption ].
    apply less_wdr with (Two[*]nring (R:=IR) n[+][1][+][1]).
     apply less_transitive_unfolded with (Two[*]nring (R:=IR) n[+][1]); apply less_plusOne.
    astepr (nring (R:=IR) (S (2 * n)) [+][1]).
    Step_final (nring (R:=IR) (2 * n) [+][1][+][1]).
   rstepr ([1][/] [1][/] e[//]pos_ap_zero _ _ H1[//] div_resp_ap_zero_rev _ _ _ _ (one_ap_zero IR)).
   apply recip_resp_leEq; [ apply recip_resp_pos; assumption | assumption ].
  eapply less_leEq_trans.
   2: apply Hn.
  apply recip_resp_pos; assumption.
 elim (aux_seq_lub_prop P tot_bnd).
 exists (fun k : nat => scs_elem _ _ (aux_seq_lub P tot_bnd k)); auto.
Qed.

(* begin hide *)
Let aux_seq_glb (P : IR -> CProp) (H : totally_bounded P) :
  forall k : nat,
  Build_SubCSetoid IR
    (fun x : IR =>
     P x and (forall y : IR, P y -> x[-]y [<=] Two[*]one_div_succ k)).
Proof.
 elim H; clear H; intros non_empty H k.
 elim (H (one_div_succ k) (one_div_succ_pos IR k)).
 intros l Hl' Hl; clear H.
 cut {y : IR | member y l | y [<=] minlist l[+]one_div_succ k}.
  intro H; inversion_clear H.
  2: apply minlist_leEq_eps.
   2: inversion_clear non_empty.
   2: elim (Hl x).
    2: intros.
    2: exists x0.
    2: tauto.
   2: assumption.
  2: apply one_div_succ_pos.
 exists x; split.
  apply Hl'; assumption.
 intros y Hy.
 elim (Hl y Hy).
 intros z Hz Hz'.
 rstepl (x[-]z[+] (z[-]y)).
 rstepr (one_div_succ (R:=IR) k[+]one_div_succ k).
 apply plus_resp_leEq_both.
  apply shift_minus_leEq.
  apply shift_leEq_plus'.
  apply leEq_transitive with (minlist l).
   apply shift_minus_leEq.
   assumption.
  apply minlist_smaller; assumption.
 apply leEq_transitive with (AbsIR (y[-]z)).
  rstepl ( [--] (y[-]z)); apply inv_leEq_AbsIR.
 apply AbsSmall_imp_AbsIR; assumption.
Qed.

Let aux_seq_glb_prop :
  forall (P : IR -> CProp) (H : totally_bounded P),
  (forall k : nat, P (scs_elem _ _ (aux_seq_glb P H k)))
  and (forall (k : nat) (y : IR),
       P y -> scs_elem _ _ (aux_seq_glb P H k) [-]y [<=] Two[*]one_div_succ k).
Proof.
 intros; cut (forall k : nat, P (scs_elem _ _ (aux_seq_glb P H k)) and (forall y : IR,
   P y -> scs_elem _ _ (aux_seq_glb P H k) [-]y [<=] Two[*]one_div_succ k)).
  intro H0.
  split; intro k; elim (H0 k); intros.
   assumption.
  apply b; assumption.
 intro; apply scs_prf.
Qed.
(* end hide *)

Lemma totally_bounded_has_glb : forall P : IR -> CProp,
 totally_bounded P -> {z : IR | set_glb_IR P z}.
Proof.
 intros P tot_bnd.
 red in tot_bnd.
 elim tot_bnd; intros non_empty H.
 cut {sequence : nat -> IR | forall k : nat, P (sequence k) |
   forall (k : nat) (x : IR), P x -> sequence k[-]x [<=] Two[*]one_div_succ k}.
  intros H0.
  elim H0.
  clear H0; intros seq H0 H1.
  cut (Cauchy_prop seq).
   intro H2.
   set (seq1 := Build_CauchySeq IR seq H2) in *.
   exists (Lim seq1).
   split; intros.
    apply shift_leEq_rht.
    astepl ( [--]ZeroR); rstepr ( [--] (Lim seq1[-]x)).
    apply inv_resp_leEq.
    set (seq2 := Cauchy_const x) in *.
    apply leEq_wdl with (Lim seq1[-]Lim seq2).
     2: apply cg_minus_wd; [ algebra
       | unfold seq2 in |- *; apply eq_symmetric_unfolded; apply Lim_const ].
    apply leEq_wdl with (Lim (Build_CauchySeq IR (fun n : nat => seq1 n[-]seq2 n)
      (Cauchy_minus seq1 seq2))).
     apply leEq_transitive with (Lim twice_inv_seq).
      apply Lim_leEq_Lim; intro.
      simpl in |- *.
      apply H1; assumption.
     apply eq_imp_leEq.
     apply eq_symmetric_unfolded; apply Limits_unique.
     red in |- *; fold (SeqLimit twice_inv_seq [0]) in |- *.
     apply twice_inv_seq_Lim.
    apply Lim_minus.
   cut (Cauchy_Lim_prop2 seq (Lim seq1)).
    intro H4; red in H4. try rename X into H3.
    elim (H4 (e [/]TwoNZ) (pos_div_two _ _ H3)); clear H4.
    intros n Hn.
    exists (seq n).
     apply H0.
    apply leEq_less_trans with (AbsIR (Lim seq1[-]seq n)).
     rstepl ( [--] (Lim seq1[-]seq n)).
     apply inv_leEq_AbsIR.
    apply leEq_less_trans with (e [/]TwoNZ).
     apply AbsSmall_imp_AbsIR.
     apply AbsSmall_minus; simpl in |- *; apply Hn.
     apply le_n.
    apply pos_div_two'; auto.
   cut (Cauchy_Lim_prop2 seq1 (Lim seq1)); intros.
    try rename X0 into H4.
    red in |- *; red in H4.
    intros eps Heps; elim (H4 eps Heps); clear H4; intros.
    exists x.
    intros m Hm; elim (p m Hm); clear p.
    intros.
    astepr (seq1 m[-]Lim seq1).
    apply AbsIR_eq_AbsSmall; assumption.
   red in |- *; fold (SeqLimit seq1 (Lim seq1)) in |- *.
   apply ax_Lim.
   apply crl_proof.
  red in |- *; intros e H2.
  elim (Archimedes ([1][/] e[//]pos_ap_zero _ _ H2)).
  intros n Hn.
  exists (S (2 * n)); intros.
  cut ([0] [<] nring (R:=IR) n); intros.
   apply AbsIR_eq_AbsSmall.
    try rename X into H4.
    apply leEq_transitive with ( [--] ([1][/] nring n[//]pos_ap_zero _ _ H4)).
     apply inv_resp_leEq.
     apply shift_div_leEq.
      assumption.
     eapply shift_leEq_mult'; [ assumption | apply Hn ].
    apply less_leEq.
    rstepr ( [--] (seq (S (2 * n)) [-]seq m)); apply inv_resp_less.
    apply leEq_less_trans with (Two[*]one_div_succ (R:=IR) (S (2 * n))).
     apply H1; apply H0.
    astepl (one_div_succ (R:=IR) (S (2 * n)) [*]Two).
    unfold one_div_succ in |- *; unfold Snring in |- *.
    apply shift_mult_less with (two_ap_zero IR).
     apply pos_two.
    rstepr ([1][/] Two[*]nring n[//] mult_resp_ap_zero _ _ _ (two_ap_zero IR) (pos_ap_zero _ _ H4)).
    apply recip_resp_less.
     astepl (ZeroR[*][0]); apply mult_resp_less_both; try apply leEq_reflexive;
       [ apply pos_two | assumption ].
    apply less_wdr with (Two[*]nring (R:=IR) n[+][1][+][1]).
     apply less_transitive_unfolded with (Two[*]nring (R:=IR) n[+][1]); apply less_plusOne.
    astepr (nring (R:=IR) (S (2 * n)) [+][1]).
    Step_final (nring (R:=IR) (2 * n) [+][1][+][1]).
   apply leEq_transitive with (Two[*]one_div_succ (R:=IR) m).
    apply H1; apply H0.
   apply leEq_transitive with (one_div_succ (R:=IR) n).
    unfold one_div_succ in |- *.
    unfold Snring in |- *.
    rstepl ([1][/] nring (R:=IR) (S m) [/]TwoNZ[//]
      div_resp_ap_zero_rev _ _ _ _ (nring_ap_zero IR (S m) (sym_not_eq (O_S m)))).
    apply recip_resp_leEq.
     apply pos_nring_S.
    apply shift_leEq_div.
     apply pos_two.
    simpl in |- *; fold (Two:IR) in |- *.
    rstepl (Two[*]nring (R:=IR) n[+][1][+][1]).
    apply plus_resp_leEq.
    apply leEq_wdl with (nring (R:=IR) (S (2 * n))).
     apply nring_leEq; assumption.
    Step_final (nring (R:=IR) (2 * n) [+][1]).
   unfold one_div_succ in |- *; unfold Snring in |- *.
   rstepr ([1][/] [1][/] e[//]pos_ap_zero _ _ H2[//] div_resp_ap_zero_rev _ _ _ _ (one_ap_zero IR)).
   apply recip_resp_leEq.
    apply recip_resp_pos; assumption.
   apply leEq_transitive with (nring (R:=IR) n);
     [ assumption | simpl in |- *; apply less_leEq; apply less_plusOne ].
  eapply less_leEq_trans.
   2: apply Hn.
  apply recip_resp_pos; assumption.
 elim (aux_seq_glb_prop P tot_bnd).
 exists (fun k : nat => scs_elem _ _ (aux_seq_glb P tot_bnd k)); auto.
Qed.

End Totally_Bounded.

Section Compact.

(**
** Compact sets

In this section we dwell a bit farther into the definition of compactness
and explore some of its properties.

The following characterization of inclusion can be very useful:
*)

Lemma included_compact : forall (a b c d : IR) Hab Hcd, compact a b Hab c ->
 compact a b Hab d -> included (compact c d Hcd) (compact a b Hab).
Proof.
 intros a b c d Hab Hcd H H0 x H1.
 inversion_clear H.
 inversion_clear H0.
 inversion_clear H1.
 split.
  apply leEq_transitive with c; auto.
 apply leEq_transitive with d; auto.
Qed.

(**
At several points in our future development of a theory we will need
to partition a compact interval in subintervals of length smaller than
some predefined value [eps]. Although this seems a
consequence of every compact interval being totally bounded, it is in
fact a stronger property.  In this section we perform that
construction (requiring the endpoints of the interval to be distinct)
and prove some of its good properties.

%\begin{convention}% Let [a,b : IR], [Hab : (a [<=] b)] and denote by [I]
the compact interval [[a,b]].  Also assume that [a [<] b], and let [e] be
a positive real number.
%\end{convention}%
*)

Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := compact a b Hab.
(* end hide *)

Hypothesis Hab' : a [<] b.

Variable e : IR.
Hypothesis He : [0] [<] e.

(**
We start by finding a natural number [n] such that [(b[-]a) [/] n [<] e].
*)

Definition compact_nat := ProjT1 (Archimedes (b[-]a[/] e[//]pos_ap_zero _ _ He)).

(** Obviously such an [n] must be greater than zero.*)

Lemma pos_compact_nat : [0] [<] nring (R:=IR) compact_nat.
Proof.
 apply less_leEq_trans with (b[-]a[/] e[//]pos_ap_zero _ _ He).
  rstepr ((b[-]a) [*] ([1][/] e[//]pos_ap_zero _ _ He)).
  apply mult_resp_pos.
   apply shift_less_minus; astepl a; assumption.
  apply recip_resp_pos; assumption.
 unfold compact_nat in |- *; apply proj2_sigT.
Qed.

(**
We now define a sequence on [n] points in [[a,b]] by
[x_i [=] Min(a,b) [+]i[*] (b[-]a) [/]n] and
prove that all of its points are really in that interval.
*)

Definition compact_part (i : nat) : i <= compact_nat -> IR.
Proof.
 intros.
 apply (a[+]nring i[*] (b[-]a[/] _[//]pos_ap_zero _ _ pos_compact_nat)).
Defined.

Lemma compact_part_hyp : forall i Hi, compact a b Hab (compact_part i Hi).
Proof.
 intros; unfold compact_part in |- *.
 split.
  astepl (a[+][0]); apply plus_resp_leEq_lft.
  astepl (ZeroR[*][0]); apply mult_resp_leEq_both; try apply leEq_reflexive.
   apply nring_nonneg.
  apply shift_leEq_div.
   apply pos_compact_nat.
  apply shift_leEq_minus; rstepl a; apply less_leEq; assumption.
 rstepr (a[+]nring compact_nat[*] (b[-]a[/] _[//]pos_ap_zero _ _ pos_compact_nat)).
 apply plus_resp_leEq_lft.
 apply mult_resp_leEq_rht; try apply nring_nonneg.
  apply nring_leEq; assumption.
 apply shift_leEq_div.
  apply pos_compact_nat.
 apply shift_leEq_minus; rstepl a; apply less_leEq; assumption.
Qed.

(**
This sequence is strictly increasing and each two consecutive points
are apart by less than [e].*)

Lemma compact_less : forall i Hi HSi, [0] [<] compact_part (S i) HSi[-]compact_part i Hi.
Proof.
 intros i H1 H2.
 apply shift_less_minus; astepl (compact_part _ H1).
 unfold compact_part in |- *.
 apply plus_resp_less_lft.
 apply mult_resp_less.
  simpl in |- *; apply less_plusOne.
 apply div_resp_pos.
  apply pos_compact_nat.
 apply shift_less_minus; astepl a; assumption.
Qed.

Lemma compact_leEq : forall i Hi HSi, compact_part (S i) HSi[-]compact_part i Hi [<=] e.
Proof.
 intros i H1 H2.
 unfold compact_part in |- *; simpl in |- *.
 rstepl (b[-]a[/] _[//]pos_ap_zero _ _ pos_compact_nat).
 apply shift_div_leEq.
  apply pos_compact_nat.
 apply shift_leEq_mult' with (pos_ap_zero _ _ He).
  assumption.
 exact (ProjT2 (Archimedes _)).
Qed.

(** When we proceed to integration, this lemma will also be useful: *)

Lemma compact_partition_lemma : forall n Hn i, i <= n ->
 Compact Hab (a[+]nring i[*] (b[-]a[/] _[//]nring_ap_zero' _ n Hn)).
Proof.
 intros n Hn i H; split.
  apply shift_leEq_plus'.
  astepl ZeroR.
  apply mult_resp_nonneg.
   apply nring_nonneg.
  apply shift_leEq_div.
   apply nring_pos; apply neq_O_lt; auto.
  apply shift_leEq_minus.
  rstepl a; assumption.
 apply shift_plus_leEq'.
 rstepr (nring n[*] (b[-]a[/] _[//]nring_ap_zero' _ _ Hn)).
 astepl ([0][+]nring i[*] (b[-]a[/] _[//]nring_ap_zero' _ _ Hn)).
 apply shift_plus_leEq.
 rstepr ((nring n[-]nring i) [*] (b[-]a[/] _[//]nring_ap_zero' _ _ Hn)).
 apply mult_resp_nonneg.
  apply shift_leEq_minus.
  astepl (nring (R:=IR) i).
  apply nring_leEq; assumption.
 apply shift_leEq_div.
  apply nring_pos; apply neq_O_lt; auto.
 apply shift_leEq_minus.
 rstepl a; assumption.
Qed.

(** The next lemma provides an upper bound for the distance between two points in an interval: *)

Lemma compact_elements : forall x y : IR,
 Compact Hab x -> Compact Hab y -> AbsIR (x[-]y) [<=] AbsIR (b[-]a).
Proof.
 clear Hab' He e.
 do 2 intro; intros Hx Hy.
 apply leEq_wdr with (b[-]a).
  2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
  2: apply shift_leEq_minus; astepl a; auto.
 eapply leEq_wdl.
  2: apply eq_symmetric_unfolded; apply Abs_Max.
 inversion_clear Hx.
 inversion_clear Hy.
 unfold cg_minus in |- *; apply plus_resp_leEq_both.
  apply Max_leEq; auto.
 apply inv_resp_leEq.
 apply leEq_Min; auto.
Qed.

Opaque Min Max.

(** The following is a variation on the previous lemma: *)

Lemma compact_elements' : forall c d Hcd x y, Compact Hab x ->
 compact c d Hcd y -> AbsIR (x[-]y) [<=] AbsIR (Max b d[-]Min a c).
Proof.
 do 5 intro; intros Hx Hy.
 eapply leEq_transitive.
  2: apply leEq_AbsIR.
 inversion_clear Hx.
 inversion_clear Hy.
 simpl in |- *; unfold ABSIR in |- *; apply Max_leEq.
  unfold cg_minus in |- *; apply plus_resp_leEq_both.
   apply leEq_transitive with b; auto; apply lft_leEq_Max.
  apply inv_resp_leEq; apply leEq_transitive with c; auto; apply Min_leEq_rht.
 rstepl (y[-]x).
 unfold cg_minus in |- *; apply plus_resp_leEq_both.
  apply leEq_transitive with d; auto; apply rht_leEq_Max.
 apply inv_resp_leEq; apply leEq_transitive with a; auto; apply Min_leEq_lft.
Qed.

(** The following lemma is a bit more specific: it shows that we can
also estimate the distance from the center of a compact interval to
any of its points. *)

Lemma compact_bnd_AbsIR : forall x y d H,
 compact (x[-]d) (x[+]d) H y -> AbsIR (x[-]y) [<=] d.
Proof.
 intros x y d H H0.
 inversion_clear H0.
 simpl in |- *; unfold ABSIR in |- *.
 apply Max_leEq.
  apply shift_minus_leEq; apply shift_leEq_plus'; auto.
 rstepl (y[-]x).
 apply shift_minus_leEq.
 astepr (x[+]d); auto.
Qed.

(** Finally, two more useful lemmas to prove inclusion of compact
intervals.  They will be necessary for the definition and proof of the
elementary properties of the integral.  *)

Lemma included2_compact : forall x y Hxy, Compact Hab x -> Compact Hab y ->
 included (compact (Min x y) (Max x y) Hxy) (Compact Hab).
Proof.
 do 3 intro. intros H H0.
 inversion_clear H.
 inversion_clear H0.
 apply included_compact; split.
    apply leEq_Min; auto.
   apply leEq_transitive with y.
    apply Min_leEq_rht.
   auto.
  apply leEq_transitive with y.
   auto.
  apply rht_leEq_Max.
 apply Max_leEq; auto.
Qed.

Lemma included3_compact : forall x y z Hxyz,
 Compact Hab x -> Compact Hab y -> Compact Hab z ->
 included (compact (Min (Min x y) z) (Max (Max x y) z) Hxyz) (Compact Hab).
Proof.
 do 4 intro. intros H H0 H1.
 inversion_clear H.
 inversion_clear H0.
 inversion_clear H1.
 apply included_compact; split.
    repeat apply leEq_Min; auto.
   apply leEq_transitive with z.
    apply Min_leEq_rht.
   auto.
  apply leEq_transitive with z.
   auto.
  apply rht_leEq_Max.
 repeat apply Max_leEq; auto.
Qed.

End Compact.

#[global]
Hint Resolve included_compact included2_compact included3_compact : included.
