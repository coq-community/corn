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
Require Export csetoid_rewrite.


Lemma abc : 
  forall A B C : Prop,
  A -> B /\ C -> A /\ B /\ C.
Proof with assumption.
intros.
split...
Show Script.
Qed.





Section test.

Variable T : CSetoid.
Variable f : (CSetoid_un_op T).
Variable g : (CSetoid_bin_op T).
Variable h : (CSetoid_part_op T).
Variable P : (CSetoid_predicate T).
Variable R : (CSetoid_relation T).
Variable Q : (CCSetoid_relation T).
Variables x y : T.
Hypothesis H : x [=] y.

Goal x [=] x.
apply eq_reflexive.
Abort.

Goal x [=] y -> y [=] x.
intro.
apply eq_symmetric.
Abort.




Goal (P y) -> (P x).
intro H0.
csetoid_rewrite_cxt_rev H H0.
info induction.
 csetoid_rewrite_cxt_rev.
csetoid_rewrite H.

my_csetoid_rewrite H in H0.

csetoid_rewrite_cxt H H0.
Abort.

Goal (P (f x)).
csetoid_rewrite H.
Abort.

Goal (P (f x)).
csetoid_rewrite H.
Abort.

Goal (P (g (f x) x)).
csetoid_rewrite H.
Abort.

Hypothesis x_ : (cspf_dom T T h x).

Goal (P (h x x_)).
csetoid_rewrite H.
Abort.

Hypothesis fx_ : (cspf_dom T T h (f x)).

Goal (P (h (f x) fx_)).
csetoid_rewrite H.
Abort.

Goal (R x (h (f x) fx_)).
csetoid_rewrite H.
Abort.

Goal (Q x (h (f x) fx_)).
csetoid_rewrite H.
Abort.

Goal (g x x)[=](f x).
csetoid_rewrite H.
Abort.

Goal (g x x)[#](f x).
csetoid_rewrite H.
Abort.

Goal (Not(P x)).
csetoid_rewrite H.
Abort.

Goal (Not(P (f x))).
csetoid_rewrite H.
Abort.

Goal (Not (P (g (f x) x))).
csetoid_rewrite H.
Abort.

Goal (Not (P (h x x_))).
csetoid_rewrite H.
Abort.

Goal (Not(P (h (f x) fx_))).
csetoid_rewrite H.
Abort.

Goal (Not(R x (h (f x) fx_))).
csetoid_rewrite H.
Abort.

Goal (Not(Q x (h (f x) fx_))).
csetoid_rewrite H.
Abort.

(* note: diff algebra CoRN: Not binds stronger than [=] and [#]. *)
 
Goal (Not((g x x)[=](f x))).
csetoid_rewrite H.
Abort.

Goal (Not((g x x)[#](f x))).
csetoid_rewrite H.
Abort.

Goal (P x)->(P x).
csetoid_rewrite H.
Abort.

Goal (R x x)/\(R x x).
csetoid_rewrite H.
Abort.

Goal (Not (R x x)/\(R x x)).
csetoid_rewrite H.
Abort.

Goal (R x x) and (R x x).
csetoid_rewrite H.
Abort.

Goal (Not (R x x) and (R x x)).
csetoid_rewrite H.
Abort.

Goal (R x x)\/False.
csetoid_rewrite H.
Show Proof.
Abort.

Goal (Not (R x x)\/(R x x)).
csetoid_rewrite H.
Abort.

Goal (P x) or (P x).
csetoid_rewrite H.
Abort.

Goal (P x) or (P x) -> (P x).
csetoid_rewrite H.
Abort.

Goal (iff (R x x) (R x x)).
csetoid_rewrite H.
Abort.

Goal (Not (iff (R x x) (R x x))).
csetoid_rewrite H.
Abort.

Goal (Iff (R x x) (R x x)).
csetoid_rewrite H.
Abort.

Goal (Not (Iff (R x x) (R x x))).
csetoid_rewrite H.
Abort.

Goal (not (R x x)).
csetoid_rewrite H.
Abort.

Goal ((P x)->(P (f x)))->(P x).
csetoid_rewrite H.
Abort.

Goal (Not (P x))->(P x).
csetoid_rewrite H.
Abort.

Goal (COr (P x)(P x)).
csetoid_rewrite H.
Abort.

Goal (CAnd (P x) (P (f x)))->CFalse.
csetoid_rewrite H.
Abort.

Goal (R x x)\/(R x (f x))->False.
csetoid_rewrite H.
Abort.

Goal (COr (P x)(P (f x)))->CFalse.
csetoid_rewrite H.
Abort.

Goal (CNot (R x x)).
csetoid_rewrite H.
Abort.

Goal (R x (f (f(f(f(f x)))))) <-> (R x x).
csetoid_rewrite H.
Abort.

Goal ((R x (f (f(f(f(f x)))))) <-> (R x x))->False.
csetoid_rewrite H.
Abort.

Goal (Iff (R x (f (f(f(f(f x)))))) (R x x)).
csetoid_rewrite H.
Abort.

Goal ( Iff (R x (f (f(f(f(f x)))))) (R x x))->False.
csetoid_rewrite H.
Abort.

End test.

Section more_tests.

Variables S T : CSetoid.
Variable f : (CSetoid_un_op T).
Variable g : (CSetoid_fun S T).
Variable h : (CSetoid_part_op T).
Variable P : (CSetoid_predicate T).
Variables x y : T.
Hypothesis x_ : (cspf_dom T T h x).
Hypothesis H : x[=]y.

Variables s1 s2 : S.
Hypothesis H0 : s1[=]s2.

Goal (P (h x x_)) -> (P (h x x_)).
fold_cspf_dom.

intro H1.
csetoid_rewrite H.
csetoid_rewrite_cxt H H1.
Abort.


Goal (P (h x x_)) -> (P (h x x_)).
intro H1.
csetoid_rewrite_cxt H H1.
Abort.

Goal (P (g s1)).
csetoid_rewrite H0.
Show Proof.

Variable j : (CSetoid_part_op S).
Variable s1_ : (cspf_dom S S j s1).

(* so, we can't handle this one, part fun and changing doms *)
Goal (P (g (j s1 s1_))).
csetoid_rewrite H0.
