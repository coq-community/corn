(* $Id$ *)


Require Export Peano_dec.
Require Export Relations.
Require Import CLogic.

(** *About N
*)

Infix "{+N}" := plus (no associativity, at level 85).
Infix "{*N}" := mult (no associativity, at level 80).

(** printing {+N} $+_{\mathbb{N}}$ #+<SUB>N<\SUB># *)
(** printing {*N} $*_{\mathbb{N}}$ #*<SUB>N<\SUB># *)


(** We prove some basic lemmas of the natural numbers.
*)

(** A variant of [0_S] from the standard library
*)

Lemma S_O : forall n : nat, S n <> 0.
intro n.
red in |- *.
intro H.
generalize O_S.
intro H0.
red in H0.
apply H0 with n.
apply sym_eq.
exact H.
Qed.

(** **Apartness
*)

Definition ap_nat (x y : nat) := CNot (x = y :>nat).

Infix "{#N}" := ap_nat (no associativity, at level 90).

(** printing {#N} $\#_{\mathbb{N}}$ *)

Lemma ap_nat_irreflexive0 : forall x : nat, Not (x{#N}x).
red in |- *.
unfold ap_nat in |- *.
intros x X.
cut (x = x).
intro.
elim X.
assumption.
constructor 1.
Qed.

Lemma ap_nat_symmetric0 : forall x y : nat, (x{#N}y) -> y{#N}x.
 intros x y.
 unfold ap_nat in |- *.
 intros X.
 red in |- *.
 intro Y.
 apply X.
 auto.
Qed.

Lemma ap_nat_cotransitive0 :
 forall x y : nat, (x{#N}y) -> forall z : nat, (x{#N}z) or (z{#N}y).
 intros x y X z. 
 unfold ap_nat in |- *.
 case (eq_nat_dec x z).
 intro e.
 right.
 rewrite <- e.
 assumption.
 intro.
 left.
 intro.
 elim n.
 assumption.
Qed.

Lemma ap_nat_tight0 : forall x y : nat, Not (x{#N}y) <-> x = y.
intros x y.
 red in |- *.
 split.
 unfold ap_nat in |- *.
 intro H.
 case (eq_nat_dec x y).
 intro e.
 assumption.
 intro n.  
 elim H.
 intro H0.
 elim n.
 assumption.
 intro H.
 unfold ap_nat in |- *.
 intro H0.
 elim H0.
 assumption.
Qed.

(** **Addition
*)

Lemma plus_is_extensional0 :
 forall x1 x2 y1 y2 : nat, (x1{+N}y1{#N}x2{+N}y2) -> (x1{#N}x2) or (y1{#N}y2).
intros x1 x2 y1 y2 H.
unfold ap_nat in |- *.
unfold ap_nat in H.
case (eq_nat_dec x1 x2).
intro e.
right.
red in |- *.
intro H0.
apply H.
auto.
intro n.
left.
intro H0.
elim n.
assumption.
Qed.

(** There is no inverse for addition, because every candidate will fail for 2
*)

Lemma no_inverse0 :
 forall f : nat -> nat, ~ ((2{+N}f 2) = 0 /\ (f 2{+N}2) = 0).
intro f.
simpl in |- *.
red in |- *.
intro H.
elim H.
intros H1 H2.
set (H3 := O_S (S (f 2))) in *.
generalize H3.
unfold not in |- *.
intro H4.
apply H4.
omega.
Qed.



(** **Multiplication
*)

Lemma mult_is_extensional0 :
 forall x1 x2 y1 y2 : nat, (x1{*N}y1{#N}x2{*N}y2) -> (x1{#N}x2) or (y1{#N}y2).
unfold ap_nat in |- *.
intros x1 x2 y1 y2 H.
cut ({x1 = x2} + {x1 <> x2}).
intro H1.
elim H1.
intro e.
right.
red in |- *.
intro H0.
apply H.
exact (f_equal2 mult e H0).
intro X.
left.
apply Ccontrapos' with (x1 = x2).
auto.
exact X.
apply eq_nat_dec.
Qed.
