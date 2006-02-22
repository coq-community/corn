(* $Id: Qsec.v,v 1.10 2004/07/13 14:56:45 lcf Exp $ *)

(** printing Q %\ensuremath{\mathbb{Q}}% *)
(** printing QZERO %\ensuremath{0_\mathbb{Q}}% #0<sub>Q</sub># *)
(** printing QONE %\ensuremath{1_\mathbb{Q}}% #1<sub>Q</sub># *)
(** printing QTWO %\ensuremath{2_\mathbb{Q}}% #2<sub>Q</sub># *)
(** printing QFOUR %\ensuremath{4_\mathbb{Q}}% #4<sub>Q</sub># *)

Require Export CLogic.
Require Export Arith.
Require Export Peano_dec.
Require Export Zsec.

(** *[Q]
**About [Q]
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
Record Q : Set :=  {num : Z; den : positive}.

Definition Qeq (p q : Q) := (num p * den q)%Z = (num q * den p)%Z :>Z.

Definition Qap (x y : Q) := ~(Qeq x y).

Definition Qlt (x y : Q) := (num x * den y < num y * den x)%Z.

Definition Qplus (x y : Q) :=
  Build_Q (num x * den y + num y * den x) (den x * den y).

Definition Qmult (x y : Q) := Build_Q (num x * num y) (den x * den y).

Definition Qopp (x : Q) := Build_Q (- num x) (den x).

Definition QZERO := Build_Q 0 1. 

Definition QONE := Build_Q 1 1.

Definition Qinv (x : Q) (x_ : ~(Qeq x QZERO)) :=
  Build_Q (Zsgn (num x) * den x) (posZ (num x)).
End Q.

Infix "{=Q}" := Qeq (no associativity, at level 90).
Infix "{#Q}" := Qap (no associativity, at level 90).
Infix "{<Q}" := Qlt (no associativity, at level 90).
Infix "{+Q}" := Qplus (no associativity, at level 85).
Infix "{*Q}" := Qmult (no associativity, at level 80).
Notation "{-Q}" := Qopp (at level 1, left associativity).

(** ***Constants
*)

Definition QTWO := Build_Q 2%positive 1%positive.

Definition QFOUR := Build_Q 4%positive 1%positive.

(** ***Equality
Here we prove that [QONE] is #<i>#%\emph{%not equal%}%#</i># to [QZERO]: 
*)

Theorem ONEQ_neq_ZEROQ : ~ (QONE{=Q}QZERO).
Proof.
 unfold Qeq in |- *.
 simpl in |- *.
 apply Zgt_not_eq.
 exact (Zorder.Zgt_pos_0 1).
Qed.

Theorem refl_Qeq : forall x :Q, x{=Q}x.
Proof.
 intro x.
 unfold Qeq in |- *.
 apply refl_equal.
Qed.

Theorem sym_Qeq : forall x y : Q, (x{=Q}y) -> y{=Q}x. 
Proof.
 intros x y H.
 unfold Qeq in |- *.
 unfold Qeq in H.
 apply sym_equal. 
 assumption.
Qed.



Theorem trans_Qeq : forall x y z : Q, (x{=Q}y) -> (y{=Q}z) -> x{=Q}z.
Proof.
 red in |- *.
 unfold Qeq in |- *.
 intros x y z e1 e2.
 case (dec_eq (num y) 0).
 intro H.
 cut (num x = 0%Z).
 intro H0.
 rewrite H0.
 cut (num z = 0%Z).
 intro H1.
 rewrite H1.
 simpl in |- *.
 trivial.
 rewrite H in e2.
 cut (Zpos (den y) <> 0%Z).
 intro H1.
 simpl in e2.
 exact (Zmult_integral_l (den y) (num z) H1 (sym_eq e2)).
 apply Zgt_not_eq; auto with zarith. 
 rewrite H in e1.
 simpl in e1.
 cut (Zpos (den y) <> 0%Z).
 intro H0.
 exact (Zmult_integral_l (den y) (num x) H0 e1).
 apply Zgt_not_eq; auto with zarith.
 intro H.
 eapply a_very_specific_lemma1; eauto.
Qed.


(**
 The equality is decidable: 
*)

Theorem dec_Qeq : forall x y : Q, {x{=Q}y} + {~ (x{=Q}y)}.
Proof.
 intros x y.
 case (Z_eq_dec (num x * den y) (num y * den x)).
 intro e.
 auto.
 intro n.
 right.
 intro H.
 apply n.
 assumption.
Qed.

(** ***Apartness
*)


Lemma Q_non_zero : forall x : Q, (x{#Q}QZERO) -> num x <> 0%Z.
Proof.
intros x H.
red in H.
intro H0.
elim H.
unfold Qeq in |- *.
unfold QZERO in |- *.
unfold num at 2 in |- *.
rewrite H0.
simpl in |- *.
auto.
Qed.

Lemma ap_Q_irreflexive0 : forall x : Q, Not (x{#Q}x).
Proof. 
 intros x.
 unfold Qap in |- *.
 red in |- *.
 intro H.
 elim H.
 unfold Qeq in |- *.
 auto.
Qed.

Lemma ap_Q_symmetric0 : forall x y : Q, (x{#Q}y) -> y{#Q}x.
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


Lemma ap_Q_cotransitive0 : forall x y : Q, (x{#Q}y) ->
 forall z : Q, (x{#Q}z) or (z{#Q}y).
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

Lemma ap_Q_tight0 : forall x y : Q, Not (x{#Q}y) <-> x{=Q}y.
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

(** ***Addition
*)

Theorem Qplus_simpl : forall n m p q : Q,
 (n{=Q}m) -> (p{=Q}q) -> n{+Q}p{=Q}m{+Q}q. 
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

Theorem Qplus_assoc : forall x y z : Q, x{+Q}(y{+Q}z){=Q}(x{+Q}y){+Q}z.
Proof.
 intros x y z.
 red in |- *.
 unfold Qplus in |- *.
 simpl in |- *.
 exact
  (a_very_specific_lemma5 (num x) (num y) (num z) (
     den x) (den y) (den z)). 
Qed.

(**
 [QZERO] as the neutral element for addition:
*)


Theorem QZERO_right : forall x : Q, x{+Q}QZERO{=Q}x.
Proof.
 intro x.
 red in |- *.
 unfold Qplus in |- *.
 simpl in |- *.
 rewrite Pmult_comm. 
 ring (num x * 1)%Z. (* FIXME *) simpl in |- *.
 ring (num x + 0)%Z. (* FIXME *) simpl in |- *.
 reflexivity.
Qed. 

(**
 Commutativity of addition:
*)


Theorem Qplus_sym : forall x y : Q, x{+Q}y{=Q}y{+Q}x.
Proof.
 intros x y.
 red in |- *.
 unfold Qplus in |- *.
 simpl in |- *.
 rewrite Pmult_comm.
 ring.
Qed.



Lemma Qplus_strext0 : forall x1 x2 y1 y2 : Q,
 (x1{+Q}y1{#Q}x2{+Q}y2) -> (x1{#Q}x2) or (y1{#Q}y2).
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

Lemma ZEROQ_as_rht_unit0 : forall x : Q, x{+Q}QZERO{=Q}x.
intro x.
red in |- *.
unfold Qplus in |- *.
simpl in |- *.

ring (num x * 1)%Z. ring (num x + 0)%Z. 
rewrite Pmult_comm.
simpl in |- *.
reflexivity.
Qed.

Lemma ZEROQ_as_lft_unit0 : forall x : Q, QZERO{+Q}x{=Q}x.
intro x.
red in |- *.
unfold Qplus in |- *.
simpl in |- *.
ring.
Qed.


Lemma Qplus_is_commut0 : forall x y : Q, x{+Q}y{=Q}y{+Q}x. 
intros x y.
unfold Qplus in |- *.
red in |- *.
simpl in |- *.
change
  (((num x * den y + num y * den x) * (den y * den x))%Z =
   ((num y * den x + num x * den y) * (den x * den y))%Z) 
 in |- *.
ring.
Qed.

(** ***Opposite
 [{-Q}] is a well defined unary operation: 
*)

Lemma Qopp_simpl : forall x y : Q, (x{=Q}y) -> {-Q} x{=Q}{-Q} y.
Proof.
 red in |- *.
 simpl in |- *.
 unfold Qeq in |- *.
 intros x y e1.
 rewrite Zopp_mult_distr_l_reverse with (n := num x) (m := den y).
 rewrite Zopp_mult_distr_l_reverse with (n := num y) (m := den x).
 exact (f_equal Zopp e1).
Qed.

(**
 The group equation for [{-Q}]
*)

Theorem Qplus_inverse_r : forall q : Q, q{+Q}{-Q} q{=Q}QZERO.
Proof.
 red in |- *.
 simpl in |- *.
 intro q.
 ring.
Qed.

(** ***Multiplication
Next we shall prove the properties of multiplication. First we prove
that [{*Q}] is well-defined
*)

Theorem Qmult_simpl : forall n m p q : Q,
 (n{=Q}m) -> (p{=Q}q) -> n{*Q}p{=Q}m{*Q}q. 
Proof.
 red in |- *.
 simpl in |- *.
 unfold Qeq in |- *.
 intros n m p q e1 e2.
 change
   ((num n * num p * (den m * den q))%Z =
    (num m * num q * (den n * den p))%Z) in |- *.
 rewrite <- Zmult_assoc.
 rewrite Zmult_permute with (m := den m).
 rewrite e2.
 rewrite Zmult_assoc.
 rewrite e1.
 ring.
Qed.


(**
 and it is associative:
*)

Theorem Qmult_assoc : forall n m p : Q, n{*Q}(m{*Q}p){=Q}(n{*Q}m){*Q}p.
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

Theorem Qmult_n_1 : forall n : Q, n{*Q}QONE{=Q}n.
Proof.
 intro n.
 red in |- *.
 simpl in |- *.
 rewrite Zmult_1_r with (n := num n).
 rewrite Pmult_comm.
 simpl in |- *; trivial. 
Qed.


(**
 The commutativity for [{*Q}]:
*)

Theorem Qmult_sym : forall x y : Q, x{*Q}y{=Q}y{*Q}x.
Proof.
 intros x y.
 red in |- *.
 simpl in |- *.
 rewrite Pmult_comm. 
 ring.
Qed.

Theorem Qmult_plus_distr_r : forall x y z : Q,
 x{*Q}(y{+Q}z){=Q}x{*Q}y{+Q}x{*Q}z. 
Proof.
intros x y z.
red in |- *.
simpl in |- *.
change
  ((num x * (num y * den z + num z * den y) *
    (den x * den y * (den x * den z)))%Z =
   ((num x * num y * (den x * den z) +
     num x * num z * (den x * den y)) *
    (den x * (den y * den z)))%Z) in |- *.
ring.
Qed.


(**
 And a property of multiplication which says if [x [~=] Zero] and [xy [=] Zero] then [y [=] Zero]:
*)

Theorem Qmult_eq : forall x y : Q,
 ~ (x{=Q}QZERO) -> (x{*Q}y{=Q}QZERO) -> y{=Q}QZERO.
Proof.
 intros x y.
 unfold Qeq in |- *.
 simpl in |- *.
 rewrite Zmult_1_r with (n := num x).
 rewrite Zmult_1_r with (n := (num x * num y)%Z).
 rewrite Zmult_1_r with (n := num y).
 rewrite Zmult_comm with (n := num x) (m := num y).
 intro H.
 cut (num x <> 0%Z :>Z).
 intros H0 H1.
 apply (Zmult_integral_l (num x) (num y)).
 assumption.
 assumption.
 intro H0.
 apply H.
 assumption.
Qed.






Lemma Qmult_strext0 : forall x1 x2 y1 y2 : Q,
 (x1{*Q}y1{#Q}x2{*Q}y2) -> (x1{#Q}x2) or (y1{#Q}y2).
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

Lemma nonZero : forall x : Q, ~(x{=Q}QZERO) ->
  ~(Build_Q (Zsgn (num x) * den x)%Z (posZ (num x)){=Q}QZERO).
Proof.
intro x.
unfold Qeq in |- *.
unfold num at 2 6 in |- *.
unfold QZERO in |- *.
repeat rewrite Zmult_0_l. 
unfold den at 1 3 in |- *.
repeat rewrite Zplus_0_l.
repeat rewrite Zmult_1_r.
simpl in |- *.
intro H.
cut (Zsgn (num x) <> 0%Z).
intro H0.
cut (Zpos (den x) <> 0%Z).
intro H1.
intro H2.
elim H0.
exact (Zmult_integral_l (den x) (Zsgn (num x)) H1 H2).
apply Zgt_not_eq.
auto with zarith.
apply Zsgn_3.
intro; elim H; auto.
Qed.

(** ***Inverse
*)


Lemma Qinv_strext : forall (x y : Q) x_ y_,
 ~(Qinv x x_{=Q}Qinv y y_) -> ~(x{=Q}y).
Proof.
red in |- *.
intros x y.
case x.
intros x1 p1.
case y.
intros y1 q1.
intros x_ y_ H.
intro H0.
apply H.

unfold Qeq in H0.
unfold Qeq in |- *.
simpl in H0.
simpl in |- *.
generalize (Q_non_zero _ x_).
generalize (Q_non_zero _ y_).
simpl in |- *.
intros H1 H2.
repeat rewrite <- Zmult_assoc.
apply Zsgn_5.

apply Zgt_not_eq; auto with zarith.
apply Zgt_not_eq; auto with zarith.

rewrite Zmult_permute.
rewrite posZ_Zsgn.
rewrite Zmult_permute.
rewrite posZ_Zsgn.
rewrite Zmult_comm.
rewrite H0.
apply Zmult_comm.
assumption.
assumption.
Qed.

Lemma Qinv_is_inv : forall (x : Q) (Hx : x{#Q}QZERO),
 (x{*Q}Qinv x Hx{=Q}QONE) /\ (Qinv x Hx{*Q}x{=Q}QONE).
intro x.
case x.
intros x1 p1.
unfold Qap, Qeq in |- *.
unfold Qinv in |- *.
unfold Qmult, num, den, QONE, QZERO in |- *.
repeat rewrite Zmult_1_l.
simpl in |- *.
repeat rewrite Zmult_1_r.
intros Hx.
assert ((x1 * (Zsgn x1 * p1))%Z = (p1 * posZ x1)%positive).
rewrite Pmult_comm.
change ((x1 * (Zsgn x1 * p1))%Z = (posZ x1 * p1)%Z) in |- *.
rewrite Zmult_permute.
rewrite Zmult_assoc.
rewrite posZ_Zsgn2.
trivial.
red in |- *; intros.
elim Hx; assumption.
split; auto.
rewrite Zmult_comm.
rewrite Pmult_comm. auto.
Qed.


(** ***Less-than
*)

Lemma Qlt_wd_right : forall x y z : Q, (x{<Q}y) -> (y{=Q}z) -> x{<Q}z.
intros x y z X H.

red in H.

red in |- *.
apply toCProp_Zlt.
apply
 a_very_specific_lemma5'
  with
    (a := num x)
    (b := num y)
    (c := num z)
    (m := den x)
    (n := den y)
    (p := den z).
generalize (CZlt_to _ _ X).
trivial.
change (y{=Q}z) in |- *.
simpl in H.
assumption.
Qed.

Lemma Qlt_wd_left : forall x y z : Q, (x{<Q}y) -> (x{=Q}z) -> z{<Q}y.
intros x y z H H0.
simpl in H0.
red in H.
red in H0.
red in |- *.
apply toCProp_Zlt.
rewrite <- Zopp_involutive with (n := (num z * den y)%Z).
rewrite <- Zopp_involutive with (n := (num y * den z)%Z).
apply Zgt_lt.
apply Zlt_opp.
rewrite <- Zopp_mult_distr_l_reverse with (n := num y) (m := den z).
rewrite <- Zopp_mult_distr_l_reverse with (n := num z) (m := den y).
apply
 a_very_specific_lemma5'
  with
    (a := (- num y)%Z)
    (b := (- num x)%Z)
    (c := (- num z)%Z)
    (m := den y)
    (n := den x)
    (p := den z).
apply Zgt_lt.
rewrite Zopp_mult_distr_l_reverse.
rewrite Zopp_mult_distr_l_reverse.
apply Zlt_opp.
generalize (CZlt_to _ _ H).
trivial.
rewrite Zopp_mult_distr_l_reverse.
rewrite Zopp_mult_distr_l_reverse.
apply (f_equal Zopp (x:=(num x * den z)%Z) (y:=(num z * den x)%Z)).
assumption.
Qed.

Lemma Qlt_eq_gt_dec : forall q1 q2 : Q, ((q1{<Q}q2) or (q1{=Q}q2)) or (q2{<Q}q1).
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

Lemma Qlt_is_transitive_unfolded : forall x y z : Q, (x{<Q}y) -> (y{<Q}z) -> x{<Q}z.
intros x y z e e0.
red in |- *.
apply toCProp_Zlt.
red in e.
generalize (CZlt_to _ _ e).
intro H.
red in e0.
generalize (CZlt_to _ _ e0).
intro H0.
case (dec_eq (num x) 0). 


(* x=0 *)

intro H1.
rewrite H1.
simpl in |- *.
rewrite H1 in H.
simpl in H.
rewrite <- Zmult_0_r with (n := den x).
rewrite Zmult_comm with (n := num z).
apply Zlt_reg_mult_l.
auto with zarith.

apply Zgt_lt.
apply Zgt_mult_reg_absorb_l with (a := den y).

auto with zarith.

rewrite Zmult_comm.
rewrite Zmult_0_r.
apply Zgt_trans with (m := (num y * den z)%Z).

apply Zlt_gt.
assumption.

rewrite Zmult_comm.
apply Zlt_gt.
rewrite <- Zmult_0_r with (n := den z).
apply Zlt_reg_mult_l.

auto with zarith.

apply Zgt_lt.
apply Zgt_mult_reg_absorb_l with (a := den x).

auto with zarith.

rewrite Zmult_0_r.
apply Zlt_gt.
rewrite Zmult_comm.
assumption.

intro H1.
case (not_Zeq (num x) 0 H1).

(* x : 0 *)
intro H2.
case (dec_eq (num z) 0).

 (* x : 0 , z = 0 *)
intro H3.
rewrite H3.
simpl in |- *.
rewrite <- Zmult_0_r with (n := num x).
apply Zgt_lt.
apply Zlt_conv_mult_l.

assumption.

apply Zgt_lt.
auto with zarith.

intro H3.
case (not_Zeq (num z) 0 H3).

 (* x < 0 , z < 0 *)
intro H4.
apply Zgt_mult_conv_absorb_l with (a := num y). 
apply Zgt_lt.
apply Zgt_mult_reg_absorb_l with (a := den z).

auto with zarith.

apply Zgt_trans with (m := (num z * den y)%Z).
rewrite Zmult_0_r.
apply Zlt_gt.
rewrite <- Zmult_0_r with (n := den y).
rewrite Zmult_comm.
apply Zlt_reg_mult_l.

auto with zarith.

assumption.

apply Zlt_gt.
rewrite Zmult_comm.
assumption.

apply Zgt_trans with (m := (num x * num z * den y)%Z).
rewrite Zmult_assoc.
rewrite Zmult_comm with (n := num y).
rewrite <- Zmult_assoc.
rewrite <- Zmult_assoc.
apply Zlt_conv_mult_l.

assumption.

assumption.

rewrite Zmult_comm with (n := num x).
rewrite Zmult_assoc.
rewrite Zmult_comm with (n := num y).
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
rewrite <- Zmult_0_r with (n := den x).
apply Zlt_reg_mult_l.

auto with zarith.

assumption.

rewrite Zmult_comm.
rewrite <- Zmult_0_r with (n := den z).
apply Zlt_gt.
apply Zlt_reg_mult_l.

auto with zarith.
assumption.

(* x > 0 *)
intro H2.
apply Zgt_lt.
apply Zgt_mult_reg_absorb_l with (a := num y).
apply Zgt_mult_reg_absorb_l with (a := den x).

auto with zarith.

apply Zgt_trans with (m := (num x * den y)%Z).

rewrite Zmult_comm.
apply Zlt_gt.
assumption.

rewrite Zmult_0_r.
rewrite <- Zmult_0_r with (n := den y).
rewrite Zmult_comm.
apply Zlt_gt.
apply Zlt_reg_mult_l.

auto with zarith.

assumption.

apply Zgt_trans with (m := (num x * num z * den y)%Z).
rewrite Zmult_assoc.
rewrite Zmult_comm with (n := num y).
rewrite Zmult_comm with (n := num x).
rewrite <- Zmult_assoc.
rewrite <- Zmult_assoc.
apply Zlt_gt.
apply Zlt_reg_mult_l.

apply Zgt_mult_reg_absorb_l with (a := den y).

auto with zarith.

apply Zgt_trans with (m := (num y * den z)%Z).

rewrite Zmult_comm.
apply Zlt_gt.
assumption.

rewrite Zmult_0_r.
rewrite <- Zmult_0_r with (n := den z).
rewrite Zmult_comm.
apply Zlt_gt.
apply Zlt_reg_mult_l.

auto with zarith.

apply Zgt_lt.
apply Zgt_mult_reg_absorb_l with (a := den x).

auto with zarith.

apply Zgt_trans with (m := (num x * den y)%Z).

rewrite Zmult_comm.
apply Zlt_gt.
assumption.

rewrite Zmult_0_r.
rewrite <- Zmult_0_r with (n := den y).
rewrite Zmult_comm.
apply Zlt_gt.
apply Zlt_reg_mult_l.

auto with zarith.

assumption.

assumption.

rewrite Zmult_assoc.
rewrite Zmult_comm with (n := num y).
rewrite <- Zmult_assoc.
rewrite <- Zmult_assoc.
apply Zlt_gt.
apply Zlt_reg_mult_l.

apply Zlt_gt.
assumption.

assumption.

Qed.

Lemma Qlt_strext_unfolded : forall x1 x2 y1 y2 : Q,
 (x1{<Q}y1) -> (x2{<Q}y2) or (x1{#Q}x2) or (y1{#Q}y2).
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
cut (x1{=Q}y1).
intro e2.
unfold Qlt in J.
unfold Qeq in e2.
set (J0 := CZlt_to (num x1 * den y1) (num y1 * den x1) J) in *.
cut ((num y1 * den x1)%Z = (num x1 * den y1)%Z).
intro e3.
set (i := Zgt_irrefl (num x1 * den y1)) in *.
generalize i.
unfold not in |- *.
intros i0.
elim i0.
apply Zlt_gt.
apply Zlt_le_trans with (num y1 * den x1)%Z.
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
Elim (Zlt_not_eq `(num x1)*((den y1))` 
                  `(num y1)*((den x1))` J1).
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
cut (y2{<Q}y1).
intro H.
red in H.
generalize (CZlt_to _ _ H).
intro H0.
simpl in |- *.
unfold Qap in |- *.
intro H1.
elim (Zorder.Zlt_not_eq (num y2 * den y1) (num y1 * den y2) H0).
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

Lemma Qlt_is_irreflexive_unfolded : forall x : Q, Not (x{<Q}x). 
intros x.
unfold Qlt in |- *.
intro X.
cut (num x * den x > num x * den x)%Z.
apply Zgt_irrefl with (n := (num x * den x)%Z).
apply Zlt_gt.
apply CZlt_to.
assumption.
Qed.

Lemma Qlt_is_antisymmetric_unfolded : forall x y : Q, (x{<Q}y) -> Not (y{<Q}x).
intros x y X.
intro X0.
cut (x{<Q}x).
apply Qlt_is_irreflexive_unfolded with (x := x).
apply Qlt_is_transitive_unfolded with (x := x) (y := y) (z := x).
assumption.
assumption.
Qed.

Lemma Qplus_resp_Qlt : forall x y : Q, (x{<Q}y) -> forall z : Q, x{+Q}z{<Q}y{+Q}z.
Proof.
intros x y H z.
red in H.
simpl in |- *.
red in |- *.
unfold Qplus in |- *.
apply toCProp_Zlt.
unfold num at 1 in |- *.
unfold den at 3 in |- *.
unfold num at 3 in |- *.
unfold den at 7 in |- *.
change
  ((num x * den z + num z * den x) * (den y * den z) <
   (num y * den z + num z * den y) * (den x * den z))%Z 
 in |- *.
rewrite Zmult_assoc.
rewrite Zmult_assoc.
rewrite Zmult_comm with (m := den z).
rewrite
 Zmult_comm
            with
            (m := den z)
           (n := ((num y * den z + num z * den y) * den x)%Z).
apply Zlt_reg_mult_l.

auto with zarith.

rewrite Zmult_comm.
rewrite
 Zmult_comm
            with
            (m := den x)
           (n := (num y * den z + num z * den y)%Z).
rewrite Zmult_plus_distr_r with (n := den y).
rewrite Zmult_plus_distr_r with (n := den x).
rewrite Zmult_permute with (m := num z).
rewrite Zmult_permute with (m := num z).
rewrite Zmult_comm with (n := den x) (m := den y).
apply Zgt_lt.
rewrite Zplus_comm with (m := (num z * (den y * den x))%Z).
rewrite Zplus_comm with (m := (num z * (den y * den x))%Z).
apply Zplus_gt_compat_l.
rewrite Zmult_assoc.
rewrite Zmult_assoc.
rewrite Zmult_comm with (m := den z).
rewrite Zmult_comm with (m := den z).
apply Zlt_gt.
apply Zlt_reg_mult_l.

auto with zarith.

rewrite Zmult_comm.
rewrite Zmult_comm with (m := num y).
apply CZlt_to.
assumption.
Qed.

Lemma Qmult_resp_pos_Qlt : forall x y : Q, (QZERO{<Q}x) -> (QZERO{<Q}y) -> QZERO{<Q}x{*Q}y.
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
unfold num at 1 in H0.
unfold den at 2 in H0.
simpl in H0.
rewrite Zmult_1_r in H0.

rewrite <- Zmult_0_r with (n := num x).
apply Zlt_reg_mult_l.
apply Zlt_gt.
apply CZlt_to.
assumption.
apply CZlt_to.
assumption.
Qed.

Lemma Qlt_gives_apartness : forall x y : Q, Iff (x{#Q}y) ((x{<Q}y) or (y{<Q}x)).
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
cut (x{<Q}x).
intro X.
elim Qlt_is_irreflexive_unfolded with (x := x).
assumption.
cut (y{=Q}x).
intro H1.
apply Qlt_wd_right with (x := x) (y := y) (z := x).
assumption.
assumption.
apply sym_Qeq.
assumption.

intro l.
simpl in |- *.
intro H0.
cut (y{=Q}x).
intro.
elim (Qlt_is_irreflexive_unfolded x).
apply Qlt_wd_left with (x := y) (y := x) (z := x).
assumption.
assumption.
apply sym_Qeq.
assumption.
Qed.

(** ***Miscellaneous
We consider the injection [inject_Z] from [Z] to [Q] as a coercion.
*)

Definition inject_Z (x : Z) := Build_Q x 1%positive. 

Coercion inject_Z : Z >-> Q.

Lemma injz_plus : forall m n : Z,
 (inject_Z (m + n):Q){=Q}(inject_Z m:Q){+Q}inject_Z n.
Proof.
 intros m n.
 unfold inject_Z in |- *.
 simpl in |- *.
 unfold Qeq in |- *.
 unfold num at 1 in |- *.
 unfold den at 2 in |- *. 
 replace ((m + n) * 1)%Z with (m + n)%Z.
 replace (num (Build_Q m 1%positive{+Q}Build_Q n 1%positive) * 1)%Z
  with (num (Build_Q m 1%positive{+Q}Build_Q n 1%positive)).
 unfold Qplus in |- *.
 simpl in |- *.
 ring.
 ring.
 ring.
Qed.

Lemma injZ_One : (inject_Z 1:Q){=Q}QONE.
Proof.
 unfold inject_Z in |- *.
 change ((Build_Q 1%Z 1%positive:Q){=Q}Build_Q 1%Z 1%positive) in |- *.
 apply refl_Qeq.
Qed.


(** We can always find a natural number that is bigger than a given rational
number.
*)

Theorem Q_is_archemaedian0 : forall x : Q,
 {n : positive | x{<Q}Build_Q n 1%positive}.
Proof.
 intro x.
 case x.
 intros p q.

 exists (P_of_succ_nat (Zabs_nat p)).
 
 red in |- *.
 unfold num at 1 in |- *. 
 unfold den in |- *.
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
