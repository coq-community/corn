(* $Id$ *)


Require Import CLogic.

Require Export Arith.
Require Export Peano_dec.
Require Export Zsec.

(** printing Q %\ensuremath{\mathbb{Q}}% *)

(** *About Q
*)

(** **Q
*)

(** We define the module of the structure of rational numbers as follows. First of all, it consists of the set of rational numbers, defined as the set of pairs [<a,n>] with [a:Z] and [n:positive]. Intuitively, [<a,n>] represents the rational number a/n. Then there is the equality on Q: [<a,m>=<b,n>] iff [an=bm]. We also define appartness, order, addition, multiplication, opposite, inverse an de constants 0 and 1.
*)

Module Q.
Record Q : Set :=  {num : Z; den : positive}.
Definition eq (p q : Q) := (num p * den q)%Z = (num q * den p)%Z :>Z.
Definition ap (x y : Q) := CNot (eq x y).
Definition lt (x y : Q) := Zlts (num x * den y) (num y * den x).
Definition plus (x y : Q) :=
  Build_Q (num x * den y + num y * den x) (den x * den y).
Definition mult (x y : Q) := Build_Q (num x * num y) (den x * den y).
Definition opp (x : Q) := Build_Q (- num x) (den x).
Definition ZERO := Build_Q 0 1. 
Definition ONE := Build_Q 1 1.
Definition inv (x : Q) (x_ : CNot (eq x ZERO)) :=
  Build_Q (Zsgn (num x) * den x) (Zsec.Zpos (num x)).
End Q.

Infix "{=Q}" := Q.eq (no associativity, at level 90).
Infix "{#Q}" := Q.ap (no associativity, at level 90).
Infix "{<Q}" := Q.lt (no associativity, at level 90).
Infix "{+Q}" := Q.plus (no associativity, at level 85).
Infix "{*Q}" := Q.mult (no associativity, at level 80).
Notation "{-Q}" := Q.opp (at level 1, left associativity).



(** **Constants
*)

Definition QTWO := Q.Build_Q 2%positive 1%positive.

Definition QFOUR := Q.Build_Q 4%positive 1%positive.

(** **Equality
*)

(**
 Here we prove that [Q.ONE] is #<i>#%\emph{%not equal%}%#</i># to [Q.ZERO]: 
*)

Theorem ONEQ_neq_ZEROQ : ~ (Q.ONE{=Q}Q.ZERO).
Proof.
 unfold Q.eq in |- *.
 simpl in |- *.
 apply Zgt_not_eq.
 exact (Zorder.Zgt_pos_0 1).
Qed.

Theorem refl_Qeq : forall x : Q.Q, x{=Q}x.
Proof.
 intro x.
 unfold Q.eq in |- *.
 apply refl_equal.
Qed.

Theorem sym_Qeq : forall x y : Q.Q, (x{=Q}y) -> y{=Q}x. 
Proof.
 intros x y H.
 unfold Q.eq in |- *.
 unfold Q.eq in H.
 apply sym_equal. 
 assumption.
Qed.



Theorem trans_Qeq : forall x y z : Q.Q, (x{=Q}y) -> (y{=Q}z) -> x{=Q}z.
Proof.
 red in |- *.
 unfold Q.eq in |- *.
 intros x y z e1 e2.
 case (dec_eq (Q.num y) 0).
 intro H.
 cut (Q.num x = 0%Z).
 intro H0.
 rewrite H0.
 cut (Q.num z = 0%Z).
 intro H1.
 rewrite H1.
 simpl in |- *.
 trivial.
 rewrite H in e2.
 cut (BinInt.Zpos (Q.den y) <> 0%Z).
 intro H1.
 simpl in e2.
 exact (Zmult_integral_l (Q.den y) (Q.num z) H1 (sym_eq e2)).
 apply Zgt_not_eq; auto with zarith. 
 rewrite H in e1.
 simpl in e1.
 cut (BinInt.Zpos (Q.den y) <> 0%Z).
 intro H0.
 exact (Zmult_integral_l (Q.den y) (Q.num x) H0 e1).
 apply Zgt_not_eq; auto with zarith.
 intro H.
 eapply a_very_specific_lemma1; eauto.
Qed.


(**
 The equality is decidable: 
*)

Theorem dec_Qeq : forall x y : Q.Q, {x{=Q}y} + {~ (x{=Q}y)}.
Proof.
 intros x y.
 case (Z_eq_dec (Q.num x * Q.den y) (Q.num y * Q.den x)).
 intro e.
 auto.
 intro n.
 right.
 intro H.
 apply n.
 assumption.
Qed.

(** **Apartness
*)


Lemma Q_non_zero : forall x : Q.Q, (x{#Q}Q.ZERO) -> Q.num x <> 0%Z.
Proof.
intros x H.
red in H.
intro H0.
elim H.
unfold Q.eq in |- *.
unfold Q.ZERO in |- *.
unfold Q.num at 2 in |- *.
rewrite H0.
simpl in |- *.
auto.
Qed.

Lemma ap_Q_irreflexive0 : forall x : Q.Q, Not (x{#Q}x).
Proof. 
 intros x.
 unfold Q.ap in |- *.
 red in |- *.
 intro H.
 elim H.
 unfold Q.eq in |- *.
 auto.
Qed.

Lemma ap_Q_symmetric0 : forall x y : Q.Q, (x{#Q}y) -> y{#Q}x.
Proof.
 intros x y H.
 unfold Q.ap in |- *.
 red in |- *.
 intros.
 apply H.
 unfold Q.eq in |- *.
 apply sym_equal.
 assumption.
Qed.


Lemma ap_Q_cotransitive0 :
 forall x y : Q.Q, (x{#Q}y) -> forall z : Q.Q, (x{#Q}z) or (z{#Q}y).
Proof.
 intros x y X z.
 unfold Q.ap in |- *.
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

Lemma ap_Q_tight0 : forall x y : Q.Q, Not (x{#Q}y) <-> x{=Q}y.
Proof.
 intros x y.
 red in |- *.
 split.
 unfold Q.ap in |- *.
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
 unfold Q.ap in |- *.
 red in |- *.
 intro H0.
 elim H0.
 assumption.
Qed.

(** **Addition
*)

Theorem Qplus_simpl :
 forall n m p q : Q.Q, (n{=Q}m) -> (p{=Q}q) -> n{+Q}p{=Q}m{+Q}q. 
Proof.
 red in |- *.
 simpl in |- *.
 unfold Q.eq in |- *.
 intros n m p q. 
 intros e1 e2.
 apply a_very_specific_lemma3.
 assumption.
 assumption.
Qed.

(** 
 Addition is associative:
*)

Theorem Qplus_assoc : forall x y z : Q.Q, x{+Q}(y{+Q}z){=Q}(x{+Q}y){+Q}z.
Proof.
 intros x y z.
 red in |- *.
 unfold Q.plus in |- *.
 simpl in |- *.
 exact
  (a_very_specific_lemma5 (Q.num x) (Q.num y) (Q.num z) (
     Q.den x) (Q.den y) (Q.den z)). 
Qed.

(**
 [Q.ZERO] as the neutral element for addition:
*)


Theorem QZERO_right : forall x : Q.Q, x{+Q}Q.ZERO{=Q}x.
Proof.
 intro x.
 red in |- *.
 unfold Q.plus in |- *.
 simpl in |- *.
 rewrite Pmult_comm. 
 ring (Q.num x * 1)%Z. (* FIXME *) simpl in |- *.
 ring (Q.num x + 0)%Z. (* FIXME *) simpl in |- *.
 reflexivity.
Qed. 

(**
 Commutativity of addition:
*)


Theorem Qplus_sym : forall x y : Q.Q, x{+Q}y{=Q}y{+Q}x.
Proof.
 intros x y.
 red in |- *.
 unfold Q.plus in |- *.
 simpl in |- *.
 rewrite Pmult_comm.
 ring.
Qed.



Lemma Qplus_is_extensional0 :
 forall x1 x2 y1 y2 : Q.Q, (x1{+Q}y1{#Q}x2{+Q}y2) -> (x1{#Q}x2) or (y1{#Q}y2).
unfold Q.ap in |- *.
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

Lemma ZEROQ_as_rht_unit0 : forall x : Q.Q, x{+Q}Q.ZERO{=Q}x.
intro x.
red in |- *.
unfold Q.plus in |- *.
simpl in |- *.

ring (Q.num x * 1)%Z. ring (Q.num x + 0)%Z. 
rewrite Pmult_comm.
simpl in |- *.
reflexivity.
Qed.

Lemma ZEROQ_as_lft_unit0 : forall x : Q.Q, Q.ZERO{+Q}x{=Q}x.
intro x.
red in |- *.
unfold Q.plus in |- *.
simpl in |- *.
ring.
Qed.


Lemma Qplus_is_commut0 : forall x y : Q.Q, x{+Q}y{=Q}y{+Q}x. 
intros x y.
unfold Q.plus in |- *.
red in |- *.
simpl in |- *.
change
  (((Q.num x * Q.den y + Q.num y * Q.den x) * (Q.den y * Q.den x))%Z =
   ((Q.num y * Q.den x + Q.num x * Q.den y) * (Q.den x * Q.den y))%Z) 
 in |- *.
ring.
Qed.

(** **Opposite
*)

(**
 [Q.opp] is a well defined unary operation: 
*)

Lemma Qopp_simpl : forall x y : Q.Q, (x{=Q}y) -> {-Q} x{=Q}{-Q} y.
Proof.
 red in |- *.
 simpl in |- *.
 unfold Q.eq in |- *.
 intros x y e1.
 rewrite Zopp_mult_distr_l_reverse with (n := Q.num x) (m := Q.den y).
 rewrite Zopp_mult_distr_l_reverse with (n := Q.num y) (m := Q.den x).
 exact (f_equal Zopp e1).
Qed.

(**
 The group equation for [Qopp]
*)

Theorem Qplus_inverse_r : forall q : Q.Q, q{+Q}{-Q} q{=Q}Q.ZERO.
Proof.
 red in |- *.
 simpl in |- *.
 intro q.
 ring.
Qed.

(** **Multiplication
*)

(**  Next we shall prove the properties of multiplication. First we prove that [Q.mult] is well-defined
*)

Theorem Qmult_simpl :
 forall n m p q : Q.Q, (n{=Q}m) -> (p{=Q}q) -> n{*Q}p{=Q}m{*Q}q. 
Proof.
 red in |- *.
 simpl in |- *.
 unfold Q.eq in |- *.
 intros n m p q e1 e2.
 change
   ((Q.num n * Q.num p * (Q.den m * Q.den q))%Z =
    (Q.num m * Q.num q * (Q.den n * Q.den p))%Z) in |- *.
 rewrite <- Zmult_assoc.
 rewrite Zmult_permute with (m := Q.den m).
 rewrite e2.
 rewrite Zmult_assoc.
 rewrite e1.
 ring.
Qed.


(**
 and it is associative:
*)

Theorem Qmult_assoc : forall n m p : Q.Q, n{*Q}(m{*Q}p){=Q}(n{*Q}m){*Q}p.
Proof.
 intros n m p.
 red in |- *.
 simpl in |- *.
 rewrite Pmult_assoc.
 ring.
Qed.

(**
 [Q.ONE] is the neutral element for multiplication:
*)

Theorem Qmult_n_1 : forall n : Q.Q, n{*Q}Q.ONE{=Q}n.
Proof.
 intro n.
 red in |- *.
 simpl in |- *.
 rewrite Zmult_1_r with (n := Q.num n).
 rewrite Pmult_comm.
 simpl in |- *; trivial. 
Qed.


(**
 The commutativity for [Q.mult]:
*)

Theorem Qmult_sym : forall x y : Q.Q, x{*Q}y{=Q}y{*Q}x.
Proof.
 intros x y.
 red in |- *.
 simpl in |- *.
 rewrite Pmult_comm. 
 ring.
Qed.

Theorem Qmult_plus_distr_r :
 forall x y z : Q.Q, x{*Q}(y{+Q}z){=Q}x{*Q}y{+Q}x{*Q}z. 
Proof.
intros x y z.
red in |- *.
simpl in |- *.
change
  ((Q.num x * (Q.num y * Q.den z + Q.num z * Q.den y) *
    (Q.den x * Q.den y * (Q.den x * Q.den z)))%Z =
   ((Q.num x * Q.num y * (Q.den x * Q.den z) +
     Q.num x * Q.num z * (Q.den x * Q.den y)) *
    (Q.den x * (Q.den y * Q.den z)))%Z) in |- *.
ring.
Qed.


(**
 And a property of multiplication which says if $x\neq 0$ #x &ne; 0# and [xy=0] then [y=0]:
*)

Theorem Qmult_eq :
 forall x y : Q.Q, ~ (x{=Q}Q.ZERO) -> (x{*Q}y{=Q}Q.ZERO) -> y{=Q}Q.ZERO.
Proof.
 intros x y.
 unfold Q.eq in |- *.
 simpl in |- *.
 rewrite Zmult_1_r with (n := Q.num x).
 rewrite Zmult_1_r with (n := (Q.num x * Q.num y)%Z).
 rewrite Zmult_1_r with (n := Q.num y).
 rewrite Zmult_comm with (n := Q.num x) (m := Q.num y).
 intro H.
 cut (Q.num x <> 0%Z :>Z).
 intros H0 H1.
 apply (Zmult_integral_l (Q.num x) (Q.num y)).
 assumption.
 assumption.
 intro H0.
 apply H.
 assumption.
Qed.






Lemma Qmult_is_extensional0 :
 forall x1 x2 y1 y2 : Q.Q, (x1{*Q}y1{#Q}x2{*Q}y2) -> (x1{#Q}x2) or (y1{#Q}y2).
unfold Q.ap in |- *.
intros x1 x2 y1 y2 X.
case (dec_Qeq x1 x2).
intro.
right.
red in |- *.
intro H0.
apply X.
exact (Qmult_simpl x1 x2 y1 y2 e H0).
intro n.
left.
intro H.
elim n.
assumption.
Qed.

Lemma nonZero :
 forall x : Q.Q,
 CNot (x{=Q}Q.ZERO) ->
 CNot
   (Q.Build_Q (Zsgn (Q.num x) * Q.den x)%Z (Zsec.Zpos (Q.num x)){=Q}Q.ZERO).
Proof.
intro x.
unfold Q.eq in |- *.
unfold Q.num at 2 6 in |- *.
unfold Q.ZERO in |- *.
repeat rewrite Zmult_0_l. 
unfold Q.den at 1 3 in |- *.
repeat rewrite Zplus_0_l.
repeat rewrite Zmult_1_r.
simpl in |- *.
intro H.
cut (Zsgn (Q.num x) <> 0%Z).
intro H0.
cut (BinInt.Zpos (Q.den x) <> 0%Z).
intro H1.
intro H2.
elim H0.
exact (Zmult_integral_l (Q.den x) (Zsgn (Q.num x)) H1 H2).
apply Zgt_not_eq.
auto with zarith.
apply Zsgn_3.
intro; elim H; auto.
Qed.

(** **Inverse
*)


Lemma Qinv_is_extensional :
 forall (x y : Q.Q) x_ y_, CNot (Q.inv x x_{=Q}Q.inv y y_) -> CNot (x{=Q}y).
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

unfold Q.eq in H0.
unfold Q.eq in |- *.
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
rewrite Zpos_Zsgn.
rewrite Zmult_permute.
rewrite Zpos_Zsgn.
rewrite Zmult_comm.
rewrite H0.
apply Zmult_comm.
assumption.
assumption.
Qed.

Lemma Qinv_is_inv :
 forall (x : Q.Q) (Hx : x{#Q}Q.ZERO),
 (x{*Q}Q.inv x Hx{=Q}Q.ONE) /\ (Q.inv x Hx{*Q}x{=Q}Q.ONE).
intro x.
case x.
intros x1 p1.
unfold Q.ap, Q.eq in |- *.
unfold Q.inv in |- *.
unfold Q.mult, Q.num, Q.den, Q.ONE, Q.ZERO in |- *.
repeat rewrite Zmult_1_l.
simpl in |- *.
repeat rewrite Zmult_1_r.
intros Hx.
assert ((x1 * (Zsgn x1 * p1))%Z = (p1 * Zsec.Zpos x1)%positive).
rewrite Pmult_comm.
change ((x1 * (Zsgn x1 * p1))%Z = (Zsec.Zpos x1 * p1)%Z) in |- *.
rewrite Zmult_permute.
rewrite Zmult_assoc.
rewrite Zpos_Zsgn2.
trivial.
red in |- *; intros.
elim Hx; assumption.
split; auto.
rewrite Zmult_comm.
rewrite Pmult_comm. auto.
Qed.


(** **Less-than
*)

Lemma Qlt_is_well_defined_right :
 forall x y z : Q.Q, (x{<Q}y) -> (y{=Q}z) -> x{<Q}z.
intros x y z X H.

red in H.

red in |- *.
apply toCProp_Zlt.
apply
 a_very_specific_lemma5'
  with
    (a := Q.num x)
    (b := Q.num y)
    (c := Q.num z)
    (m := Q.den x)
    (n := Q.den y)
    (p := Q.den z).
generalize (CZlt_to _ _ X).
trivial.
change (y{=Q}z) in |- *.
simpl in H.
assumption.
Qed.

Lemma Qlt_is_well_defined_left :
 forall x y z : Q.Q, (x{<Q}y) -> (x{=Q}z) -> z{<Q}y.
intros x y z H H0.
simpl in H0.
red in H.
red in H0.
red in |- *.
apply toCProp_Zlt.
rewrite <- Zopp_involutive with (n := (Q.num z * Q.den y)%Z).
rewrite <- Zopp_involutive with (n := (Q.num y * Q.den z)%Z).
apply Zgt_lt.
apply Zlt_opp.
rewrite <- Zopp_mult_distr_l_reverse with (n := Q.num y) (m := Q.den z).
rewrite <- Zopp_mult_distr_l_reverse with (n := Q.num z) (m := Q.den y).
apply
 a_very_specific_lemma5'
  with
    (a := (- Q.num y)%Z)
    (b := (- Q.num x)%Z)
    (c := (- Q.num z)%Z)
    (m := Q.den y)
    (n := Q.den x)
    (p := Q.den z).
apply Zgt_lt.
rewrite Zopp_mult_distr_l_reverse.
rewrite Zopp_mult_distr_l_reverse.
apply Zlt_opp.
generalize (CZlt_to _ _ H).
trivial.
rewrite Zopp_mult_distr_l_reverse.
rewrite Zopp_mult_distr_l_reverse.
apply (f_equal Zopp (x:=(Q.num x * Q.den z)%Z) (y:=(Q.num z * Q.den x)%Z)).
assumption.
Qed.

Lemma Qlt_eq_gt_dec :
 forall q1 q2 : Q.Q, ((q1{<Q}q2) or (q1{=Q}q2)) or (q2{<Q}q1).
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
 unfold Q.lt in |- *.
 apply toCProp_Zlt; auto.

 left; right.
 unfold Q.eq in |- *.
 simpl in |- *; auto.

 auto.

 intro b0.
 right.
 unfold Q.lt in |- *.
 simpl in |- *.
 apply toCProp_Zlt. 
 apply Zgt_lt.
 assumption.
Qed.

Lemma Qlt_is_transitive_unfolded :
 forall x y z : Q.Q, (x{<Q}y) -> (y{<Q}z) -> x{<Q}z.
intros x y z e e0.
red in |- *.
apply toCProp_Zlt.
red in e.
generalize (CZlt_to _ _ e).
intro H.
red in e0.
generalize (CZlt_to _ _ e0).
intro H0.
case (dec_eq (Q.num x) 0). 


(* x=0 *)

intro H1.
rewrite H1.
simpl in |- *.
rewrite H1 in H.
simpl in H.
rewrite <- Zmult_0_r with (n := Q.den x).
rewrite Zmult_comm with (n := Q.num z).
apply Zlt_reg_mult_l.
auto with zarith.

apply Zgt_lt.
apply Zgt_mult_reg_absorb_l with (a := Q.den y).

auto with zarith.

rewrite Zmult_comm.
rewrite Zmult_0_r.
apply Zgt_trans with (m := (Q.num y * Q.den z)%Z).

apply Zlt_gt.
assumption.

rewrite Zmult_comm.
apply Zlt_gt.
rewrite <- Zmult_0_r with (n := Q.den z).
apply Zlt_reg_mult_l.

auto with zarith.

apply Zgt_lt.
apply Zgt_mult_reg_absorb_l with (a := Q.den x).

auto with zarith.

rewrite Zmult_0_r.
apply Zlt_gt.
rewrite Zmult_comm.
assumption.

intro H1.
case (not_Zeq (Q.num x) 0 H1).

(* x : 0 *)
intro H2.
case (dec_eq (Q.num z) 0).

 (* x : 0 , z = 0 *)
intro H3.
rewrite H3.
simpl in |- *.
rewrite <- Zmult_0_r with (n := Q.num x).
apply Zgt_lt.
apply Zlt_conv_mult_l.

assumption.

apply Zgt_lt.
auto with zarith.

intro H3.
case (not_Zeq (Q.num z) 0 H3).

 (* x < 0 , z < 0 *)
intro H4.
apply Zgt_mult_conv_absorb_l with (a := Q.num y). 
apply Zgt_lt.
apply Zgt_mult_reg_absorb_l with (a := Q.den z).

auto with zarith.

apply Zgt_trans with (m := (Q.num z * Q.den y)%Z).
rewrite Zmult_0_r.
apply Zlt_gt.
rewrite <- Zmult_0_r with (n := Q.den y).
rewrite Zmult_comm.
apply Zlt_reg_mult_l.

auto with zarith.

assumption.

apply Zlt_gt.
rewrite Zmult_comm.
assumption.

apply Zgt_trans with (m := (Q.num x * Q.num z * Q.den y)%Z).
rewrite Zmult_assoc.
rewrite Zmult_comm with (n := Q.num y).
rewrite <- Zmult_assoc.
rewrite <- Zmult_assoc.
apply Zlt_conv_mult_l.

assumption.

assumption.

rewrite Zmult_comm with (n := Q.num x).
rewrite Zmult_assoc.
rewrite Zmult_comm with (n := Q.num y).
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
rewrite <- Zmult_0_r with (n := Q.den x).
apply Zlt_reg_mult_l.

auto with zarith.

assumption.

rewrite Zmult_comm.
rewrite <- Zmult_0_r with (n := Q.den z).
apply Zlt_gt.
apply Zlt_reg_mult_l.

auto with zarith.
assumption.

(* x > 0 *)
intro H2.
apply Zgt_lt.
apply Zgt_mult_reg_absorb_l with (a := Q.num y).
apply Zgt_mult_reg_absorb_l with (a := Q.den x).

auto with zarith.

apply Zgt_trans with (m := (Q.num x * Q.den y)%Z).

rewrite Zmult_comm.
apply Zlt_gt.
assumption.

rewrite Zmult_0_r.
rewrite <- Zmult_0_r with (n := Q.den y).
rewrite Zmult_comm.
apply Zlt_gt.
apply Zlt_reg_mult_l.

auto with zarith.

assumption.

apply Zgt_trans with (m := (Q.num x * Q.num z * Q.den y)%Z).
rewrite Zmult_assoc.
rewrite Zmult_comm with (n := Q.num y).
rewrite Zmult_comm with (n := Q.num x).
rewrite <- Zmult_assoc.
rewrite <- Zmult_assoc.
apply Zlt_gt.
apply Zlt_reg_mult_l.

apply Zgt_mult_reg_absorb_l with (a := Q.den y).

auto with zarith.

apply Zgt_trans with (m := (Q.num y * Q.den z)%Z).

rewrite Zmult_comm.
apply Zlt_gt.
assumption.

rewrite Zmult_0_r.
rewrite <- Zmult_0_r with (n := Q.den z).
rewrite Zmult_comm.
apply Zlt_gt.
apply Zlt_reg_mult_l.

auto with zarith.

apply Zgt_lt.
apply Zgt_mult_reg_absorb_l with (a := Q.den x).

auto with zarith.

apply Zgt_trans with (m := (Q.num x * Q.den y)%Z).

rewrite Zmult_comm.
apply Zlt_gt.
assumption.

rewrite Zmult_0_r.
rewrite <- Zmult_0_r with (n := Q.den y).
rewrite Zmult_comm.
apply Zlt_gt.
apply Zlt_reg_mult_l.

auto with zarith.

assumption.

assumption.

rewrite Zmult_assoc.
rewrite Zmult_comm with (n := Q.num y).
rewrite <- Zmult_assoc.
rewrite <- Zmult_assoc.
apply Zlt_gt.
apply Zlt_reg_mult_l.

apply Zlt_gt.
assumption.

assumption.

Qed.

Lemma Qlt_is_extensional_unfolded :
 forall x1 x2 y1 y2 : Q.Q,
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
unfold Q.lt in J.
unfold Q.eq in e2.
set (J0 := CZlt_to (Q.num x1 * Q.den y1) (Q.num y1 * Q.den x1) J) in *.
cut ((Q.num y1 * Q.den x1)%Z = (Q.num x1 * Q.den y1)%Z).
intro e3.
set (i := Zgt_irrefl (Q.num x1 * Q.den y1)) in *.
generalize i.
unfold not in |- *.
intros i0.
elim i0.
apply Zlt_gt.
apply Zlt_le_trans with (Q.num y1 * Q.den x1)%Z.
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
(*Unfold Q.ap.
Intro.
Unfold Q.lt in J.
Generalize (CZlt_to ? ? J).
Intro J1.
Elim (Zlt_not_eq `(Q.num x1)*((Q.den y1))` 
                  `(Q.num y1)*((Q.den x1))` J1).
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
unfold Q.ap in |- *.
intro H1.
elim (Zorder.Zlt_not_eq (Q.num y2 * Q.den y1) (Q.num y1 * Q.den y2) H0).
symmetry  in |- *.
assumption.
apply Qlt_is_transitive_unfolded with x1.
apply Qlt_is_well_defined_right with x2.
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

Lemma Qlt_is_irreflexive_unfolded : forall x : Q.Q, Not (x{<Q}x). 
intros x.
unfold Q.lt in |- *.
intro X.
cut (Q.num x * Q.den x > Q.num x * Q.den x)%Z.
apply Zgt_irrefl with (n := (Q.num x * Q.den x)%Z).
apply Zlt_gt.
apply CZlt_to.
assumption.
Qed.

Lemma Qlt_is_antisymmetric_unfolded :
 forall x y : Q.Q, (x{<Q}y) -> Not (y{<Q}x).
intros x y X.
intro X0.
cut (x{<Q}x).
apply Qlt_is_irreflexive_unfolded with (x := x).
apply Qlt_is_transitive_unfolded with (x := x) (y := y) (z := x).
assumption.
assumption.
Qed.

Lemma Qplus_resp_Qlt :
 forall x y : Q.Q, (x{<Q}y) -> forall z : Q.Q, x{+Q}z{<Q}y{+Q}z.
Proof.
intros x y H z.
red in H.
simpl in |- *.
red in |- *.
unfold Q.plus in |- *.
apply toCProp_Zlt.
unfold Q.num at 1 in |- *.
unfold Q.den at 3 in |- *.
unfold Q.num at 3 in |- *.
unfold Q.den at 7 in |- *.
change
  ((Q.num x * Q.den z + Q.num z * Q.den x) * (Q.den y * Q.den z) <
   (Q.num y * Q.den z + Q.num z * Q.den y) * (Q.den x * Q.den z))%Z 
 in |- *.
rewrite Zmult_assoc.
rewrite Zmult_assoc.
rewrite Zmult_comm with (m := Q.den z).
rewrite
 Zmult_comm
            with
            (m := Q.den z)
           (n := ((Q.num y * Q.den z + Q.num z * Q.den y) * Q.den x)%Z).
apply Zlt_reg_mult_l.

auto with zarith.

rewrite Zmult_comm.
rewrite
 Zmult_comm
            with
            (m := Q.den x)
           (n := (Q.num y * Q.den z + Q.num z * Q.den y)%Z).
rewrite Zmult_plus_distr_r with (n := Q.den y).
rewrite Zmult_plus_distr_r with (n := Q.den x).
rewrite Zmult_permute with (m := Q.num z).
rewrite Zmult_permute with (m := Q.num z).
rewrite Zmult_comm with (n := Q.den x) (m := Q.den y).
apply Zgt_lt.
rewrite Zplus_comm with (m := (Q.num z * (Q.den y * Q.den x))%Z).
rewrite Zplus_comm with (m := (Q.num z * (Q.den y * Q.den x))%Z).
apply Zplus_gt_compat_l.
rewrite Zmult_assoc.
rewrite Zmult_assoc.
rewrite Zmult_comm with (m := Q.den z).
rewrite Zmult_comm with (m := Q.den z).
apply Zlt_gt.
apply Zlt_reg_mult_l.

auto with zarith.

rewrite Zmult_comm.
rewrite Zmult_comm with (m := Q.num y).
apply CZlt_to.
assumption.
Qed.

Lemma Qmult_resp_pos_Qlt :
 forall x y : Q.Q, (Q.ZERO{<Q}x) -> (Q.ZERO{<Q}y) -> Q.ZERO{<Q}x{*Q}y.
intros x y.
intro H.
intro H0.
red in H.
unfold Q.lt in |- *.
apply toCProp_Zlt.
simpl in |- *.

rewrite Zmult_1_r.
simpl in H.
rewrite Zmult_1_r in H.

unfold Q.lt in H0.
unfold Q.ZERO in H0.
unfold Q.num at 1 in H0.
unfold Q.den at 2 in H0.
simpl in H0.
rewrite Zmult_1_r in H0.

rewrite <- Zmult_0_r with (n := Q.num x).
apply Zlt_reg_mult_l.
apply Zlt_gt.
apply CZlt_to.
assumption.
apply CZlt_to.
assumption.
Qed.

Lemma Qlt_gives_apartness :
 forall x y : Q.Q, Iff (x{#Q}y) ((x{<Q}y) or (y{<Q}x)).
Proof.
intros x y.
red in |- *.
split.
intro H.
unfold Q.ap in H.
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
apply Qlt_is_well_defined_right with (x := x) (y := y) (z := x).
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
apply Qlt_is_well_defined_left with (x := y) (y := x) (z := x).
assumption.
assumption.
apply sym_Qeq.
assumption.
Qed.

(** **Miscellaneous
*)

(**
We consider the injection [inject_Z] from [Z] to [QQ] as a
coercion.
*)

Definition inject_Z (x : Z) := Q.Build_Q x 1%positive. 

Coercion inject_Z : Z >-> Q.Q.


Lemma injz_plus :
 forall m n : Z, (inject_Z (m + n):Q.Q){=Q}(inject_Z m:Q.Q){+Q}inject_Z n.
Proof.
 intros m n.
 unfold inject_Z in |- *.
 simpl in |- *.
 unfold Q.eq in |- *.
 unfold Q.num at 1 in |- *.
 unfold Q.den at 2 in |- *. 
 replace ((m + n) * 1)%Z with (m + n)%Z.
 replace (Q.num (Q.Build_Q m 1%positive{+Q}Q.Build_Q n 1%positive) * 1)%Z
  with (Q.num (Q.Build_Q m 1%positive{+Q}Q.Build_Q n 1%positive)).
 unfold Q.plus in |- *.
 simpl in |- *.
 ring.
 ring.
 ring.
Qed.

Lemma injZ_One : (inject_Z 1:Q.Q){=Q}Q.ONE.
Proof.
 unfold inject_Z in |- *.
 change ((Q.Build_Q 1%Z 1%positive:Q.Q){=Q}Q.Build_Q 1%Z 1%positive) in |- *.
 apply refl_Qeq.
Qed.


(** We can always find a natural number that is bigger than a given rational
number.
*)

Theorem Q_is_archemaedian0 :
 forall x : Q.Q, {n : positive | x{<Q}Q.Build_Q n 1%positive}.
Proof.
 intro x.
 case x.
 intros p q.

 exists (P_of_succ_nat (Zabs_nat p)).
 
 red in |- *.
 unfold Q.num at 1 in |- *. 
 unfold Q.den in |- *.
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






