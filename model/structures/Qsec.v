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

(** printing Q %\ensuremath{\mathbb{Q}}% *)
(** printing QZERO %\ensuremath{0_\mathbb{Q}}% #0<sub>Q</sub># *)
(** printing QONE %\ensuremath{1_\mathbb{Q}}% #1<sub>Q</sub># *)
(** printing QTWO %\ensuremath{2_\mathbb{Q}}% #2<sub>Q</sub># *)
(** printing QFOUR %\ensuremath{4_\mathbb{Q}}% #4<sub>Q</sub># *)

Require Export CLogic.
Require Import Arith.
Require Import Peano_dec.
Require Import Zsec.
Require Export QArith.

(**
* [Q]
** About [Q]
We define the structure of rational numbers as follows. First of all,
it consists of the set of rational numbers, defined as the set of
pairs $\langle a,n\rangle$#&lang;a,n&rang;# with [a:Z] and
[n:positive]. Intuitively, $\langle a,n\rangle$#&lang;a,n&rang;#
represents the rational number [a[/]n]. Then there is the equality on
[Q]: $\langle a,m\rangle=\langle
b,n\rangle$#&lang;a,m&rang;=&lang;b,n&rang;# iff [an [=] bm]. We
also define apartness, order, addition, multiplication, opposite,
inverse an de constants 0 and 1.  *)

Section Q.
Definition Qap (x y : Q) := ~(Qeq x y).

Definition QZERO := Qmake 0 1. 

Definition QONE := Qmake 1 1.

Definition Qinv (x : Q) (x_ : ~(Qeq x QZERO)) := Qinv x.

End Q.

Infix "/=" := Qap (no associativity, at level 70) : Q_scope.

(**
*** Constants
*)

Definition QTWO := Qmake 2%positive 1%positive.

Definition QFOUR := Qmake 4%positive 1%positive.

(**
*** Equality
Here we prove that [QONE] is #<i>#%\emph{%not equal%}%#</i># to [QZERO]: 
*)

Theorem ONEQ_neq_ZEROQ : ~ (QONE==QZERO).
Proof.
 unfold Qeq in |- *.
 simpl in |- *.
 apply Zgt_not_eq.
 exact (Zorder.Zgt_pos_0 1).
Qed.

Theorem refl_Qeq : forall x :Q, x==x.
Proof.
 intro x.
 unfold Qeq in |- *.
 apply refl_equal.
Qed.

Theorem sym_Qeq : forall x y : Q, (x==y) -> y==x. 
Proof.
 intros x y H.
 unfold Qeq in |- *.
 unfold Qeq in H.
 apply sym_equal. 
 assumption.
Qed.



Theorem trans_Qeq : forall x y z : Q, (x==y) -> (y==z) -> x==z.
Proof.
 red in |- *.
 unfold Qeq in |- *.
 intros x y z e1 e2.
 case (dec_eq (Qnum y) 0).
 intro H.
 cut (Qnum x = 0%Z).
 intro H0.
 rewrite H0.
 cut (Qnum z = 0%Z).
 intro H1.
 rewrite H1.
 simpl in |- *.
 trivial.
 rewrite H in e2.
 cut (Zpos (Qden y) <> 0%Z).
 intro H1.
 simpl in e2.
 exact (Zmult_integral_l (Qden y) (Qnum z) H1 (sym_eq e2)).
 apply Zgt_not_eq; auto with zarith. 
 rewrite H in e1.
 simpl in e1.
 cut (Zpos (Qden y) <> 0%Z).
 intro H0.
 exact (Zmult_integral_l (Qden y) (Qnum x) H0 e1).
 apply Zgt_not_eq; auto with zarith.
 intro H.
 eapply a_very_specific_lemma1; eauto.
Qed.


(**
 The equality is decidable: 
*)

Theorem dec_Qeq : forall x y : Q, {x==y} + {~ (x==y)}.
Proof.
 intros x y.
 case (Z_eq_dec (Qnum x * Qden y) (Qnum y * Qden x)).
 intro e.
 auto.
 intro n.
 right.
 intro H.
 apply n.
 assumption.
Qed.

(**
*** Apartness
*)


Lemma Q_non_zero : forall x : Q, (x/=QZERO) -> Qnum x <> 0%Z.
Proof.
intros x H.
red in H.
intro H0.
elim H.
unfold Qeq in |- *.
unfold QZERO in |- *.
unfold Qnum at 2 in |- *.
rewrite H0.
simpl in |- *.
auto.
Qed.

Lemma ap_Q_irreflexive0 : forall x : Q, Not (x/=x).
Proof. 
 intros x.
 unfold Qap in |- *.
 red in |- *.
 intro H.
 elim H.
 unfold Qeq in |- *.
 auto.
Qed.

Lemma ap_Q_symmetric0 : forall x y : Q, (x/=y) -> y/=x.
Proof.
 intros x y H.
 unfold Qap in |- *.
 red in |- *.
 intros.
 apply H.
 unfold Qeq in |- *.
 apply sym_equal.
 assumption.
Qed.


Lemma ap_Q_cotransitive0 : forall x y : Q, (x/=y) ->
 forall z : Q, (x/=z) or (z/=y).
Proof.
 intros x y X z.
 unfold Qap in |- *.
 case (dec_Qeq x z).
 intro e.
 right.
 red in |- *.
 intro H0.
 apply X.
 exact (trans_Qeq x z y e H0).
 intros n.
 left.
 intro H.
 elim n.
 auto.
Qed.

Lemma ap_Q_tight0 : forall x y : Q, Not (x/=y) <-> x==y.
Proof.
 intros x y.
 red in |- *.
 split.
 unfold Qap in |- *.
 intro.
 case (dec_Qeq x y).
 intro e.
 assumption.
 intro n.
 elim H.
 intro H0.
 elim n.
 assumption.
 intro H.
 unfold Qap in |- *.
 red in |- *.
 intro H0.
 elim H0.
 assumption.
Qed.

(**
*** Addition
*)

Theorem Qplus_simpl : forall n m p q : Q,
 (n==m) -> (p==q) -> n+p==m+q. 
Proof.
 red in |- *.
 simpl in |- *.
 unfold Qeq in |- *.
 intros n m p q. 
 intros e1 e2.
 apply a_very_specific_lemma3.
 assumption.
 assumption.
Qed.

(** 
 Addition is associative:
*)

Theorem Qplus_assoc : forall x y z : Q, x+(y+z)==(x+y)+z.
Proof.
 intros x y z.
 red in |- *.
 unfold Qplus in |- *.
 simpl in |- *.
 exact
  (a_very_specific_lemma5 (Qnum x) (Qnum y) (Qnum z) (
     Qden x) (Qden y) (Qden z)). 
Qed.

(**
 [QZERO] as the neutral element for addition:
*)


Theorem QZERO_right : forall x : Q, x+QZERO==x.
Proof.
 intro x.
 red in |- *.
 unfold Qplus in |- *.
 simpl in |- *.
 rewrite Zpos_mult_morphism in |- *.
 ring.
Qed. 

(**
 Commutativity of addition:
*)


Theorem Qplus_sym : forall x y : Q, x+y==y+x.
Proof.
 intros x y.
 red in |- *.
 unfold Qplus in |- *.
 simpl in |- *.
 rewrite Pmult_comm.
 ring.
Qed.



Lemma Qplus_strext0 : forall x1 x2 y1 y2 : Q,
 (x1+y1/=x2+y2) -> (x1/=x2) or (y1/=y2).
unfold Qap in |- *.
intros x1 x2 y1 y2 X.
case (dec_Qeq x1 x2).
intro e.
right.
red in |- *.
intro H0.
apply X.
exact (Qplus_simpl x1 x2 y1 y2 e H0).
intro n.
left.
intro H.
elim n.
auto.
Qed.

Lemma ZEROQ_as_rht_unit0 : forall x : Q, x+QZERO==x.
intro x.
red in |- *.
unfold Qplus in |- *.
simpl in |- *.
rewrite Zpos_mult_morphism in |- *.
ring.
Qed.

Lemma ZEROQ_as_lft_unit0 : forall x : Q, QZERO+x==x.
intro x.
red in |- *.
unfold Qplus in |- *.
simpl in |- *.
ring.
Qed.


Lemma Qplus_is_commut0 : forall x y : Q, x+y==y+x. 
intros x y.
unfold Qplus in |- *.
red in |- *.
simpl in |- *.
change
  (((Qnum x * Qden y + Qnum y * Qden x) * (Qden y * Qden x))%Z =
   ((Qnum y * Qden x + Qnum x * Qden y) * (Qden x * Qden y))%Z) 
 in |- *.
ring.
Qed.

(**
*** Opposite
 [-] is a well defined unary operation: 
*)

Lemma Qopp_simpl : forall x y : Q, (x==y) -> - x==- y.
Proof.
 red in |- *.
 simpl in |- *.
 unfold Qeq in |- *.
 intros x y e1.
 rewrite Zopp_mult_distr_l_reverse with (n := Qnum x) (m := Qden y).
 rewrite Zopp_mult_distr_l_reverse with (n := Qnum y) (m := Qden x).
 exact (f_equal Zopp e1).
Qed.

(**
 The group equation for [-]
*)

Theorem Qplus_inverse_r : forall q : Q, q+-q==QZERO.
Proof.
 red in |- *.
 simpl in |- *.
 intro q.
 ring.
Qed.

(**
*** Multiplication
Next we shall prove the properties of multiplication. First we prove
that [*] is well-defined
*)

Theorem Qmult_simpl : forall n m p q : Q,
 (n==m) -> (p==q) -> n*p==m*q. 
Proof.
 red in |- *.
 simpl in |- *.
 unfold Qeq in |- *.
 intros n m p q e1 e2.
 change
   ((Qnum n * Qnum p * (Qden m * Qden q))%Z =
    (Qnum m * Qnum q * (Qden n * Qden p))%Z) in |- *.
 rewrite <- Zmult_assoc.
 rewrite Zmult_permute with (m := Qden m).
 rewrite e2.
 rewrite Zmult_assoc.
 rewrite e1.
 ring.
Qed.


(**
 and it is associative:
*)

Theorem Qmult_assoc : forall n m p : Q, n*(m*p)==(n*m)*p.
Proof.
 intros n m p.
 red in |- *.
 simpl in |- *.
 rewrite Pmult_assoc.
 ring.
Qed.

(**
 [QONE] is the neutral element for multiplication:
*)

Theorem Qmult_n_1 : forall n : Q, n*QONE==n.
Proof.
 intro n.
 red in |- *.
 simpl in |- *.
 rewrite Zmult_1_r with (n := Qnum n).
 rewrite Pmult_comm.
 simpl in |- *; trivial. 
Qed.


(**
 The commutativity for [*]:
*)

Theorem Qmult_sym : forall x y : Q, x*y==y*x.
Proof.
 intros x y.
 red in |- *.
 simpl in |- *.
 rewrite Pmult_comm. 
 ring.
Qed.

Theorem Qmult_plus_distr_r : forall x y z : Q,
 x*(y+z)==x*y+x*z. 
Proof.
intros x y z.
red in |- *.
simpl in |- *.
change
  ((Qnum x * (Qnum y * Qden z + Qnum z * Qden y) *
    (Qden x * Qden y * (Qden x * Qden z)))%Z =
   ((Qnum x * Qnum y * (Qden x * Qden z) +
     Qnum x * Qnum z * (Qden x * Qden y)) *
    (Qden x * (Qden y * Qden z)))%Z) in |- *.
ring.
Qed.


(**
 And a property of multiplication which says if [x [~=] Zero] and [xy [=] Zero] then [y [=] Zero]:
*)

Theorem Qmult_eq : forall x y : Q,
 ~ (x==QZERO) -> (x*y==QZERO) -> y==QZERO.
Proof.
 intros x y.
 unfold Qeq in |- *.
 simpl in |- *.
 rewrite Zmult_1_r with (n := Qnum x).
 rewrite Zmult_1_r with (n := (Qnum x * Qnum y)%Z).
 rewrite Zmult_1_r with (n := Qnum y).
 rewrite Zmult_comm with (n := Qnum x) (m := Qnum y).
 intro H.
 cut (Qnum x <> 0%Z :>Z).
 intros H0 H1.
 apply (Zmult_integral_l (Qnum x) (Qnum y)).
 assumption.
 assumption.
 intro H0.
 apply H.
 assumption.
Qed.






Lemma Qmult_strext0 : forall x1 x2 y1 y2 : Q,
 (x1*y1/=x2*y2) -> (x1/=x2) or (y1/=y2).
unfold Qap in |- *.
intros x1 x2 y1 y2 X.
case (dec_Qeq x1 x2).
intro.
right.
red in |- *.
intro H0.
apply X.
exact (Qmult_simpl x1 x2 y1 y2 q H0).
intro n.
left.
intro H.
elim n.
assumption.
Qed.

Lemma nonZero : forall x : Q, ~(x==QZERO) ->
  ~(Qmake (Zsgn (Qnum x) * Qden x)%Z (posZ (Qnum x))==QZERO).
Proof.
intro x.
unfold Qeq in |- *.
unfold Qnum at 2 6 in |- *.
unfold QZERO in |- *.
repeat rewrite Zmult_0_l. 
unfold Qden at 1 3 in |- *.
repeat rewrite Zplus_0_l.
repeat rewrite Zmult_1_r.
simpl in |- *.
intro H.
cut (Zsgn (Qnum x) <> 0%Z).
intro H0.
cut (Zpos (Qden x) <> 0%Z).
intro H1.
intro H2.
elim H0.
exact (Zmult_integral_l (Qden x) (Zsgn (Qnum x)) H1 H2).
apply Zgt_not_eq.
auto with zarith.
apply Zsgn_3.
intro; elim H; auto.
Qed.

(**
*** Inverse
*)


Lemma Qinv_strext : forall (x y : Q) x_ y_,
 ~(Qinv x x_==Qinv y y_) -> ~(x==y).
Proof.
firstorder using Qinv_comp.
Qed.

Lemma Qinv_is_inv : forall (x : Q) (Hx : x/=QZERO),
 (x*Qinv x Hx==QONE) /\ (Qinv x Hx*x==QONE).
intros x Hx.
split.
apply (Qmult_inv_r x).
assumption.
rewrite Qmult_comm.
apply (Qmult_inv_r x).
assumption.
Qed.


(**
*** Less-than
*)

Lemma Qlt_wd_right : forall x y z : Q, (x<y) -> (y==z) -> x<z.
intros x y z X H.

red in H.

red in |- *.
apply toCProp_Zlt.
apply
 a_very_specific_lemma5'
  with
    (a := Qnum x)
    (b := Qnum y)
    (c := Qnum z)
    (m := Qden x)
    (n := Qden y)
    (p := Qden z).
generalize (CZlt_to _ _ X).
trivial.
change (y==z) in |- *.
simpl in H.
assumption.
Qed.

Lemma Qlt_wd_left : forall x y z : Q, (x<y) -> (x==z) -> z<y.
intros x y z H H0.
simpl in H0.
red in H.
red in H0.
red in |- *.
apply toCProp_Zlt.
rewrite <- Zopp_involutive with (n := (Qnum z * Qden y)%Z).
rewrite <- Zopp_involutive with (n := (Qnum y * Qden z)%Z).
apply Zgt_lt.
apply Zlt_opp.
rewrite <- Zopp_mult_distr_l_reverse with (n := Qnum y) (m := Qden z).
rewrite <- Zopp_mult_distr_l_reverse with (n := Qnum z) (m := Qden y).
apply
 a_very_specific_lemma5'
  with
    (a := (- Qnum y)%Z)
    (b := (- Qnum x)%Z)
    (c := (- Qnum z)%Z)
    (m := Qden y)
    (n := Qden x)
    (p := Qden z).
apply Zgt_lt.
rewrite Zopp_mult_distr_l_reverse.
rewrite Zopp_mult_distr_l_reverse.
apply Zlt_opp.
generalize (CZlt_to _ _ H).
trivial.
rewrite Zopp_mult_distr_l_reverse.
rewrite Zopp_mult_distr_l_reverse.
apply (f_equal Zopp (x:=(Qnum x * Qden z)%Z) (y:=(Qnum z * Qden x)%Z)).
assumption.
Qed.

Lemma Qlt_eq_gt_dec : forall q1 q2 : Q, ((q1<q2) or (q1==q2)) or (q2<q1).
intros q1 q2.
 case q1. 
 intros m1 n1.
 case q2.
 intros m2 n2.
 simpl in |- *.
 set (a := (m1 * n2)%Z) in *.
 set (b := (m2 * n1)%Z) in *.
 elim (Z_le_gt_dec a b).
 intro a0.
 elim (Z_le_lt_eq_dec a b).
 intro a1. 
 left; left.
 unfold Qlt in |- *.
 apply toCProp_Zlt; auto.

 left; right.
 unfold Qeq in |- *.
 simpl in |- *; auto.

 auto.

 intro b0.
 right.
 unfold Qlt in |- *.
 simpl in |- *.
 apply toCProp_Zlt. 
 apply Zgt_lt.
 assumption.
Qed.

Lemma Qlt_is_transitive_unfolded : forall x y z : Q, (x<y) -> (y<z) -> x<z.
intros x y z e e0.
red in |- *.
apply toCProp_Zlt.
red in e.
generalize (CZlt_to _ _ e).
intro H.
red in e0.
generalize (CZlt_to _ _ e0).
intro H0.
case (dec_eq (Qnum x) 0). 


(* x=0 *)

intro H1.
rewrite H1.
simpl in |- *.
rewrite H1 in H.
simpl in H.
rewrite <- Zmult_0_r with (n := Qden x).
rewrite Zmult_comm with (n := Qnum z).
apply Zlt_reg_mult_l.
auto with zarith.

apply Zgt_lt.
apply Zgt_mult_reg_absorb_l with (a := Qden y).

auto with zarith.

rewrite Zmult_comm.
rewrite Zmult_0_r.
apply Zgt_trans with (m := (Qnum y * Qden z)%Z).

apply Zlt_gt.
assumption.

rewrite Zmult_comm.
apply Zlt_gt.
rewrite <- Zmult_0_r with (n := Qden z).
apply Zlt_reg_mult_l.

auto with zarith.

apply Zgt_lt.
apply Zgt_mult_reg_absorb_l with (a := Qden x).

auto with zarith.

rewrite Zmult_0_r.
apply Zlt_gt.
rewrite Zmult_comm.
assumption.

intro H1.
case (not_Zeq (Qnum x) 0 H1).

(* x : 0 *)
intro H2.
case (dec_eq (Qnum z) 0).

 (* x : 0 , z = 0 *)
intro H3.
rewrite H3.
simpl in |- *.
rewrite <- Zmult_0_r with (n := Qnum x).
apply Zgt_lt.
apply Zlt_conv_mult_l.

assumption.

apply Zgt_lt.
auto with zarith.

intro H3.
case (not_Zeq (Qnum z) 0 H3).

 (* x < 0 , z < 0 *)
intro H4.
apply Zgt_mult_conv_absorb_l with (a := Qnum y). 
apply Zgt_lt.
apply Zgt_mult_reg_absorb_l with (a := Qden z).

auto with zarith.

apply Zgt_trans with (m := (Qnum z * Qden y)%Z).
rewrite Zmult_0_r.
apply Zlt_gt.
rewrite <- Zmult_0_r with (n := Qden y).
rewrite Zmult_comm.
apply Zlt_reg_mult_l.

auto with zarith.

assumption.

apply Zlt_gt.
rewrite Zmult_comm.
assumption.

apply Zgt_trans with (m := (Qnum x * Qnum z * Qden y)%Z).
rewrite Zmult_assoc.
rewrite Zmult_comm with (n := Qnum y).
rewrite <- Zmult_assoc.
rewrite <- Zmult_assoc.
apply Zlt_conv_mult_l.

assumption.

assumption.

rewrite Zmult_comm with (n := Qnum x).
rewrite Zmult_assoc.
rewrite Zmult_comm with (n := Qnum y).
rewrite <- Zmult_assoc.
rewrite <- Zmult_assoc.
apply Zlt_conv_mult_l.

assumption.

assumption.

 (* x < 0 , z > 0 *)

intro H4.
apply Zgt_lt.
apply Zgt_trans with (m := 0%Z).
apply Zlt_gt.
rewrite Zmult_comm.
rewrite <- Zmult_0_r with (n := Qden x).
apply Zlt_reg_mult_l.

auto with zarith.

assumption.

rewrite Zmult_comm.
rewrite <- Zmult_0_r with (n := Qden z).
apply Zlt_gt.
apply Zlt_reg_mult_l.

auto with zarith.
assumption.

(* x > 0 *)
intro H2.
apply Zgt_lt.
apply Zgt_mult_reg_absorb_l with (a := Qnum y).
apply Zgt_mult_reg_absorb_l with (a := Qden x).

auto with zarith.

apply Zgt_trans with (m := (Qnum x * Qden y)%Z).

rewrite Zmult_comm.
apply Zlt_gt.
assumption.

rewrite Zmult_0_r.
rewrite <- Zmult_0_r with (n := Qden y).
rewrite Zmult_comm.
apply Zlt_gt.
apply Zlt_reg_mult_l.

auto with zarith.

assumption.

apply Zgt_trans with (m := (Qnum x * Qnum z * Qden y)%Z).
rewrite Zmult_assoc.
rewrite Zmult_comm with (n := Qnum y).
rewrite Zmult_comm with (n := Qnum x).
rewrite <- Zmult_assoc.
rewrite <- Zmult_assoc.
apply Zlt_gt.
apply Zlt_reg_mult_l.

apply Zgt_mult_reg_absorb_l with (a := Qden y).

auto with zarith.

apply Zgt_trans with (m := (Qnum y * Qden z)%Z).

rewrite Zmult_comm.
apply Zlt_gt.
assumption.

rewrite Zmult_0_r.
rewrite <- Zmult_0_r with (n := Qden z).
rewrite Zmult_comm.
apply Zlt_gt.
apply Zlt_reg_mult_l.

auto with zarith.

apply Zgt_lt.
apply Zgt_mult_reg_absorb_l with (a := Qden x).

auto with zarith.

apply Zgt_trans with (m := (Qnum x * Qden y)%Z).

rewrite Zmult_comm.
apply Zlt_gt.
assumption.

rewrite Zmult_0_r.
rewrite <- Zmult_0_r with (n := Qden y).
rewrite Zmult_comm.
apply Zlt_gt.
apply Zlt_reg_mult_l.

auto with zarith.

assumption.

assumption.

rewrite Zmult_assoc.
rewrite Zmult_comm with (n := Qnum y).
rewrite <- Zmult_assoc.
rewrite <- Zmult_assoc.
apply Zlt_gt.
apply Zlt_reg_mult_l.

apply Zlt_gt.
assumption.

assumption.

Qed.

Lemma Qlt_strext_unfolded : forall x1 x2 y1 y2 : Q,
 (x1<y1) -> (x2<y2) or (x1/=x2) or (y1/=y2).
intros x1 x2 y1 y2.
intro J.
case (Qlt_eq_gt_dec x2 y2).
intro s.
case s.
intro l.
auto.
intro e.
case (dec_Qeq x1 x2).
intro e0.
right.
right.
red in |- *.
red in |- *.
intro e1.
cut (x1==y1).
intro e2.
unfold Qlt in J.
unfold Qeq in e2.
set (J0 := CZlt_to (Qnum x1 * Qden y1) (Qnum y1 * Qden x1) J) in *.
cut ((Qnum y1 * Qden x1)%Z = (Qnum x1 * Qden y1)%Z).
intro e3.
set (i := Zgt_irrefl (Qnum x1 * Qden y1)) in *.
generalize i.
unfold not in |- *.
intros i0.
elim i0.
apply Zlt_gt.
apply Zlt_le_trans with (Qnum y1 * Qden x1)%Z.
exact J0.
apply Zeq_le.
exact e3.
auto with zarith.
apply trans_Qeq with y2.
apply trans_Qeq with x2.
exact e0.
exact e.
apply sym_Qeq.
exact e1.
(*Unfold Qap.
Intro.
Unfold Qlt in J.
Generalize (CZlt_to ? ? J).
Intro J1.
Elim (Zlt_not_eq `(Qnum x1)*((Qden y1))` 
                  `(Qnum y1)*((Qden x1))` J1).
Symmetry.
Assumption.
Step_final x2.*)
intro n.
right.
left.
intro H.
elim n.
assumption.
intro l.
case (dec_Qeq x1 x2).
intro e.
right.
right.
cut (y2<y1).
intro H.
red in H.
generalize (CZlt_to _ _ H).
intro H0.
simpl in |- *.
unfold Qap in |- *.
intro H1.
elim (Zorder.Zlt_not_eq (Qnum y2 * Qden y1) (Qnum y1 * Qden y2) H0).
symmetry  in |- *.
assumption.
apply Qlt_is_transitive_unfolded with x1.
apply Qlt_wd_right with x2.
assumption.
apply sym_Qeq.
assumption.
assumption.
intro n.
right.
left.
intro H.
elim n.
assumption.
Qed.

Lemma Qlt_is_irreflexive_unfolded : forall x : Q, Not (x<x). 
intros x.
unfold Qlt in |- *.
intro X.
cut (Qnum x * Qden x > Qnum x * Qden x)%Z.
apply Zgt_irrefl with (n := (Qnum x * Qden x)%Z).
apply Zlt_gt.
apply CZlt_to.
assumption.
Qed.

Lemma Qlt_is_antisymmetric_unfolded : forall x y : Q, (x<y) -> Not (y<x).
intros x y X.
intro X0.
cut (x<x).
apply Qlt_is_irreflexive_unfolded with (x := x).
apply Qlt_is_transitive_unfolded with (x := x) (y := y) (z := x).
assumption.
assumption.
Qed.

Lemma Qplus_resp_Qlt : forall x y : Q, (x<y) -> forall z : Q, x+z<y+z.
Proof.
intros x y H z.
red in H.
simpl in |- *.
red in |- *.
unfold Qplus in |- *.
apply toCProp_Zlt.
unfold Qnum at 1 in |- *.
unfold Qden at 3 in |- *.
unfold Qnum at 3 in |- *.
unfold Qden at 7 in |- *.
change
  ((Qnum x * Qden z + Qnum z * Qden x) * (Qden y * Qden z) <
   (Qnum y * Qden z + Qnum z * Qden y) * (Qden x * Qden z))%Z 
 in |- *.
rewrite Zmult_assoc.
rewrite Zmult_assoc.
rewrite Zmult_comm with (m := Qden z).
rewrite
 Zmult_comm
            with
            (m := Qden z)
           (n := ((Qnum y * Qden z + Qnum z * Qden y) * Qden x)%Z).
apply Zlt_reg_mult_l.

auto with zarith.

rewrite Zmult_comm.
rewrite
 Zmult_comm
            with
            (m := Qden x)
           (n := (Qnum y * Qden z + Qnum z * Qden y)%Z).
rewrite Zmult_plus_distr_r with (n := Qden y).
rewrite Zmult_plus_distr_r with (n := Qden x).
rewrite Zmult_permute with (m := Qnum z).
rewrite Zmult_permute with (m := Qnum z).
rewrite Zmult_comm with (n := Qden x) (m := Qden y).
apply Zgt_lt.
rewrite Zplus_comm with (m := (Qnum z * (Qden y * Qden x))%Z).
rewrite Zplus_comm with (m := (Qnum z * (Qden y * Qden x))%Z).
apply Zplus_gt_compat_l.
rewrite Zmult_assoc.
rewrite Zmult_assoc.
rewrite Zmult_comm with (m := Qden z).
rewrite Zmult_comm with (m := Qden z).
apply Zlt_gt.
apply Zlt_reg_mult_l.

auto with zarith.

rewrite Zmult_comm.
rewrite Zmult_comm with (m := Qnum y).
apply CZlt_to.
assumption.
Qed.

Lemma Qmult_resp_pos_Qlt : forall x y : Q, (QZERO<x) -> (QZERO<y) -> QZERO<x*y.
intros x y.
intro H.
intro H0.
red in H.
unfold Qlt in |- *.
apply toCProp_Zlt.
simpl in |- *.

rewrite Zmult_1_r.
simpl in H.
rewrite Zmult_1_r in H.

unfold Qlt in H0.
unfold QZERO in H0.
unfold Qnum at 1 in H0.
unfold Qden at 2 in H0.
simpl in H0.
rewrite Zmult_1_r in H0.

rewrite <- Zmult_0_r with (n := Qnum x).
apply Zlt_reg_mult_l.
apply Zlt_gt.
apply CZlt_to.
assumption.
apply CZlt_to.
assumption.
Qed.

Lemma Qlt_gives_apartness : forall x y : Q, Iff (x/=y) ((x<y) or (y<x)).
Proof.
intros x y.
red in |- *.
split.
intro H.
unfold Qap in H.
case (Qlt_eq_gt_dec x y).
intro s.
case s.
intro l.
left.
assumption.

intro e.
elim H.
assumption.

intro l.
right.
assumption.

intros H.
case H.
intro l.

simpl in |- *.
intro H0.
cut (x<x).
intro X.
elim Qlt_is_irreflexive_unfolded with (x := x).
assumption.
cut (y==x).
intro H1.
apply Qlt_wd_right with (x := x) (y := y) (z := x).
assumption.
assumption.
apply sym_Qeq.
assumption.

intro l.
simpl in |- *.
intro H0.
cut (y==x).
intro.
elim (Qlt_is_irreflexive_unfolded x).
apply Qlt_wd_left with (x := y) (y := x) (z := x).
assumption.
assumption.
apply sym_Qeq.
assumption.
Qed.

(**
*** Miscellaneous
We consider the injection [inject_Z] from [Z] to [Q] as a coercion.
*)

Coercion inject_Z : Z >-> Q.

Lemma injz_plus : forall m n : Z,
 (inject_Z (m + n):Q)==(inject_Z m:Q)+inject_Z n.
Proof.
 intros m n.
 unfold inject_Z in |- *.
 simpl in |- *.
 unfold Qeq in |- *.
 unfold Qnum at 1 in |- *.
 unfold Qden at 2 in |- *. 
 replace ((m + n) * 1)%Z with (m + n)%Z.
 replace (Qnum (Qmake m 1+Qmake n 1)%Q * 1)%Z
  with (Qnum (Qmake m 1+Qmake n 1)).
 unfold Qplus in |- *.
 simpl in |- *.
 ring.
 ring.
 ring.
Qed.

Lemma injZ_One : (inject_Z 1:Q)==QONE.
Proof.
 unfold inject_Z in |- *.
 change ((Qmake 1%Z 1%positive:Q)==Qmake 1%Z 1%positive) in |- *.
 apply refl_Qeq.
Qed.


(** We can always find a natural Qnumber that is bigger than a given rational
Qnumber.
*)

Theorem Q_is_archemaedian0 : forall x : Q,
 {n : positive | x<Qmake n 1%positive}.
Proof.
 intro x.
 case x.
 intros p q.

 exists (P_of_succ_nat (Zabs_nat p)).
 
 red in |- *.
 unfold Qnum at 1 in |- *. 
 unfold Qden in |- *.
 apply toCProp_Zlt. 
 simpl in |- *.
 rewrite Zmult_1_r.
 apply Zlt_le_trans with (P_of_succ_nat (Zabs_nat p) * 1)%Z.
 rewrite Zmult_1_r.
 case p; simpl in |- *; auto with zarith.
 intros; rewrite P_of_succ_nat_o_nat_of_P_eq_succ; rewrite Pplus_one_succ_r.
 change (p0 < p0 + 1)%Z in |- *.
 auto with zarith.
 intros; unfold Zlt in |- *; auto.
 change
   (P_of_succ_nat (Zabs_nat p) * 1%positive <= P_of_succ_nat (Zabs_nat p) * q)%Z
  in |- *.
 apply Zmult_le_compat_l.
 change (Zsucc 0 <= q)%Z in |- *.
 apply Zgt_le_succ.
 auto with zarith.
 auto with zarith.
Qed.

Lemma Qle_is_not_lt : forall x y : Q, x <= y <-> ~ y < x.
Proof.
firstorder using Qle_not_lt Qnot_lt_le.
Qed.

Lemma Qge_is_not_gt : forall x y : Q, x >= y <-> y <= x.
Proof.
firstorder.
Qed.

Lemma Qgt_is_lt : forall x y : Q, x > y IFF  y < x.
Proof.
firstorder.
Qed.
