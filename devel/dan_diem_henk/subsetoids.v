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
Require Export CLogic.

Section subsetoids.

Record subset (ss_crr : Type) (P:ss_crr -> CProp) : Type :=
 {elt :    ss_crr;
  elt_in : P elt}.

Record subsetoid (ss_crr : Type): Type :=
 {ss_dom :  ss_crr -> CProp;
  ss_rel :  Crelation ss_crr;
  ss_eqv :  Cequivalence ss_crr ss_rel
 }.

Implicit Arguments Build_subsetoid [ss_crr].

(* 
  we can't put a coercion from the sigma type [subset ss_crr]
  to the parameter [ss_crr] it depends on, like this:
  [[  elt :>    ss_crr
  ]].
  (for the syntax definition of [=] we work around this 
   by using left projections, as follows below.)
*)

Definition inclusion (ss_crr : Type)(s1 s2 : subsetoid ss_crr) :=
   forall c : ss_crr, ss_dom ss_crr s1 c -> ss_dom ss_crr s2 c.

Lemma inclusion_refl : forall T A, inclusion T A A.
Proof.
intros T A t H.
exact H.
Qed.

End subsetoids.

(* note: both implicit arg and notations as well as coercions (?) 
don't survive sections *)

Definition subsetCoercion (crr:Type)(s:subsetoid crr) : Type := subset crr (ss_dom crr s).

Coercion subsetCoercion : subsetoid >-> Sortclass.

Implicit Arguments ss_dom [ss_crr].
Implicit Arguments ss_rel [ss_crr].
Implicit Arguments ss_eqv  [ss_crr].
Implicit Arguments subset [ss_crr].
Implicit Arguments elt [ss_crr P].
Implicit Arguments elt_in [ss_crr P].

Definition equal (crr:Type)(s:subsetoid crr)(a1 a2: s ):= ss_rel s (elt a1) (elt a2).

Notation "x '[=]' y" := (equal _ _ x y) (at level 70, no associativity).

Section Stuff.

Variable T1 T2:Type.

Definition type2subsetoid : subsetoid T1.
apply (Build_subsetoid T1 (fun _ => True) (eq (A:=T1))).
split; red.
reflexivity.
intros x y H1; symmetry; assumption.
intros x y z H1 H2; transitivity y; assumption.
Defined.

Definition fun_wd (A : subsetoid T1)(B : subsetoid T2)(f : A -> B) := 
  forall x y : A, x[=]y -> (f x)[=](f y).

Record ss_function 
                   (A : subsetoid T1) 
                   (B : subsetoid T2) : Type :=
  {ss_fun :> A -> B;
   ss_wd  :  fun_wd A B ss_fun
  }.

Definition algo_part (A : subsetoid T1) (B: subsetoid T2) (f:ss_function A B) : 
   (A -> T2 ) := fun a => elt (f a).

(* include is just an example of a set operation defined on subsetoids *)


Definition is_in (A B : subsetoid T1) :=  fun a:A => ss_dom B (elt a).


(*Definition proof_part(A B : subsetoid) (f:ss_function A B) : 
   (A -> B) := fun a => elem_in (f a).
*)

(*Definition simpl_ss_function (A B:subsetoid) (f:ss_crr A -> ss_crr (*B) (is_nice:forall a:A, ss_dom B (f a)) (wd:forall (a1 a2 : A), a1 [=] a2 -> f (elem a1) [=] f (elem a2)): ss_function A B := 
     (Build_ss_function A B (fun x => Build_subset B (f (elem x)) (is_nice x))
                            (fun a1 a2 a1eqa2 => wd a1 a2 a1eqa2)).
*)
Ltac ex_falso :=
  match goal with
  H : False |- _ => destruct H
  end.

End Stuff.

Implicit Arguments ss_function [T1 T2].

Definition compose_ss_function 
  (T1 T2 T3 : Type) (A : subsetoid T1) (B : subsetoid T2) (C : subsetoid T3)
  (f : ss_function A B) (g : ss_function B C) : ss_function A C.
intros T1 T2 T3 A B C f g.
set (_h := fun a : A => g (f (a))).
assert (h_wd : fun_wd T1 T3 A C _h).
intros a1 a2 H.
unfold _h.
apply ss_wd.
apply ss_wd.
exact H.
set (h := Build_ss_function T1 T3 A C _h h_wd).
exact h.
Defined.

Implicit Arguments compose_ss_function [T1 T2 T3 A B C].

Notation "g '[o]' f" := (compose_ss_function f g) (at level 75, right associativity).

Section eq_equivalence.

Variable T: Type.
Variable A:subsetoid T.
Variable a1 a2 a3:A.

Lemma eq_reflexive: a1 [=] a1.
exact (Cequiv_refl _ _  (ss_eqv A) (elt a1)).
Qed.

Lemma eq_symmetric: a1 [=]a2 -> a2 [=] a1.
exact (Cequiv_symm  _ _  (ss_eqv A) (elt a1) (elt a2)).
Qed.

Lemma eq_transitive: a1 [=] a2 -> a2 [=] a3 -> a1 [=] a3.
exact (Cequiv_trans  _ _  (ss_eqv A) (elt a1) (elt a2) (elt a3)).
Qed.

End eq_equivalence.

Section isomorphisms.

Variables T1 T2 : Type.
Variable A : subsetoid T1.
Variable B : subsetoid T2.

Definition left_inverse (f : ss_function A B) (g : ss_function B A) :=
  forall x : A, g (f x) [=] x.

Definition right_inverse  (f: ss_function A B) (g: ss_function B A) :=
  forall y : B, f (g y) [=] y.

Definition inverse (f: ss_function A B) (g: ss_function B A) :=
  (left_inverse f g) and (right_inverse f g).

Definition isomorphic :=
  {f : ss_function A B | {g : ss_function B A | inverse f g}}.

End isomorphisms.

Implicit Arguments left_inverse [T1 T2 A B].
Implicit Arguments right_inverse [T1 T2 A B].
Implicit Arguments inverse [T1 T2 A B].
Implicit Arguments isomorphic [T1 T2].

Infix "[~]" := isomorphic (at level 70).

Section isomorphism_properties.

Variable T1 T2 T3: Type.
Variable A:subsetoid T1.
Variable B:subsetoid T2.
Variable C:subsetoid T3.

Lemma isomorphic_reflexive :
  A[~]A.
Proof.
Admitted.
(*intro A.
exists (id A); exists (id A).
split; intro x; refl.
Qed.
*)
Lemma isomorphic_symmetric :
A[~]B -> B[~]A.
Proof.
Admitted.
(*intros A B [ f [ f' H ] ].
exists f'; exists f.
apply inverse_symmetric with (1:=H).
Qed.
*)

Lemma isomorphic_transitive :
A[~]B -> B[~]C -> A[~]C.
Proof.
Admitted.
(*intros A B C [ f [ f' H1 ] ] [ g [ g' H2 ]].
exists (f[o]g).
exists (g'[o]f').
apply composition_preserves_inverse with (1:=H1) (2:=H2).
Qed.
*)

End isomorphism_properties.

Definition Nat : subsetoid nat := 
  type2subsetoid nat.

Definition restrict (T:Type)(A:subsetoid T)(P:T -> CProp) : subsetoid T:=
   Build_subsetoid T (fun x: T => ss_dom A x and P x) (ss_rel A) (ss_eqv A).


Definition restrict2 (T:Type)(A:subsetoid T)(P:A -> CProp) : subsetoid T:=
   Build_subsetoid T (fun x: A => ss_dom A x and P x) (ss_rel A) (ss_eqv A).


Implicit Arguments restrict [T].

Notation "A [|] P " := 
  (restrict A P) (at level 60, left associativity).

(*Definition subsetoidPredicate (s:subsetoid):= ss_crr s ->  CProp.

Definition test1 (s:subsetoid)(P1 P2: subsetoidPredicate s) : ss_function (s [|] P1 [|] P2) (s [|] P2 [|] P1).
intros.
apply (simpl_ss_function (s [|] P1 [|] P2) (s [|] P2 [|] P1)  (fun x => x)).
intros.

simpl.
destruct a.
destruct elem_in0.
destruct s0.
simpl.
repeat split; assumption.
intros.
assumption.
Qed.
*)

Lemma nat_eq_dec : 
  forall n m : nat, Cdecidable (n = m).
Proof.
induction n.
simple destruct m.
left; reflexivity.
right; red in |- *; intro h; discriminate h.
simple destruct m.
right; red in |- *; intro h; discriminate h.
intro m'.
elim (IHn m'); intro h.
left; rewrite h; reflexivity.
right; red in |- *; intro h0; injection h0; intro h1; exact (h h1).
Qed.

Definition N_ k : nat -> CProp :=
  fun n => n < k.

Definition NS_ k (*nat -> subsetoid*) := Nat[|](N_ k).


Definition Finite (T:Type) (A:subsetoid T) : CProp :=
  {k : nat | A[~](NS_ k)}.

Implicit Arguments Finite [T].

Definition pred_ext_eq (T:Type)(A:subsetoid T) (P Q : A -> CProp) :=
  forall x : A, P x ->  Q x and Q x -> P x.

Implicit Arguments pred_ext_eq [T].

Notation "P '=e' Q" := (pred_ext_eq _ P Q) (at level 80).

Definition empty (T:Type)(A:subsetoid T) :  A ->  CProp :=
  fun a => False.

Implicit Arguments empty [T].

Definition decidable p := p  or Not p.

Definition decidable_pred A (P : A -> CProp) := 
  forall x, decidable (P x).

Implicit Arguments decidable_pred [A].

Definition add (T:Type)(A:subsetoid T) (P : A -> CProp) (a : A) : A -> CProp:=
  fun x => P x or (x [=] a).

Implicit Arguments add [T].

Let unequal_to (T:Type) (A: subsetoid T) (a : A) :=
  fun x => Not (x [=] a).

Implicit Arguments unequal_to [T A].

Definition coarser (T : Type) (R1 R2 : Crelation T) :=
  forall x y, R1 x y -> R2 x y.

Lemma coarser_refl : forall T R, coarser T R R.
Proof.
intros T R x y H.
exact H.
Qed.

Definition coarser_subsetoid 
  (T : Type) (A B : subsetoid T) :=
  coarser T (ss_rel A) (ss_rel B).

Lemma coarser_subsetoid_refl :
  forall T A,
  coarser_subsetoid T A A.
Proof.
intros T A.
red.
apply coarser_refl.
Qed.

Definition restrict_function (* rename *)
  (T1 T2 : Type) (A B : subsetoid T1) (C D : subsetoid T2)(f : ss_function A C)
  :
  coarser_subsetoid T1 B A ->
  inclusion T1 B A ->
  coarser_subsetoid T2 C D ->
  inclusion T2 C D ->
  ss_function B D.
intros T1 T2 A B C D f H H0 H1 H2.
set 
  (_g1 :=
    fun b : B (* subset (ss_dom B)*) =>
    let (t1,p) := b in
    f (Build_subset T1 (ss_dom A) t1 (H0 t1 p))
  ).
assert (g1_wd : forall b1 b2 : B, b1[=]b2 -> (_g1 b1)[=](_g1 b2)).
intros [b1 p1] [b2 p2] H3.
simpl.
apply ss_wd.
red; simpl.
red in H3; simpl in H3.
apply H with (1:=H3).
set (g1 := Build_ss_function T1 T2 B C _g1 g1_wd).
set 
  (_g2 :=
    fun c : C (* subset (ss_dom C) *) =>
    let (t2,q) := c in
    (Build_subset T2 (ss_dom D) t2 (H2 t2 q))
  ).
assert (g2_wd : forall c1 c2 : C, c1[=]c2 -> (_g2 c1)[=](_g2 c2)).
intros [c1 p1] [c2 p2] H4.
simpl.
red; simpl.
red in H4; simpl in H4.
apply H1 with (1:=H4).
set (g2 := Build_ss_function T2 T2 C D _g2 g2_wd).
exact (g2[o]g1).
Defined.

Implicit Arguments restrict_function [T1 T2 A C].

(*Definition add (T:Type)(A:subsetoid T)(P: T -> CProp) (a:T) := (* rename *)
  fun x => P x or (ss_rel A a  x).*)

Lemma add_preserves_finiteness :
  forall (T:Type) (A:subsetoid T)(P : A -> CProp), 
  decidable_pred P ->
  Finite (A[|]P) -> 
  forall a : A, 
  Finite (A[|](add A P a)).
Proof.






Lemma Finite_ind :
  forall T:Type,
  forall A : subsetoid T,
  Finite A ->
  forall M : (A -> CProp) -> CProp, 
  (forall P Q, M P -> P =e Q -> M Q) ->
  M (empty A) ->
  ( forall (P : A -> CProp), 
    decidable_pred P -> 
    M P -> forall a, M (add A P a)
  ) ->
  forall P : A -> CProp, 
  decidable_pred P ->
  M P.
Proof.
intros T A [ k H ].
generalize A H; clear H A.
induction k as [ | k IH ]; intros A H M Mext Mbase Mstep P Pdec.
(* 0 *)
destruct H as [ f _ ].
assert (H : (empty A) =e P).
red.
intuition.
eapply Mext.
apply Mbase.
exact H. 
(* S case *)
destruct H as [ f [ g H ] ].
assert (H0 : ss_dom (NS_ (S k)) k).
simpl.
split; auto.
apply (lt_n_Sn k).
set (k' := Build_subset _ _ k H0).
assert (H1 : coarser_subsetoid nat (NS_ k) (NS_ (S k))).
intros m1 m2 H1.
simpl in H1 |- * .
exact H1.
assert (H2 : inclusion nat (NS_ k) (NS_ (S k))).
red.
intros c H2.
simpl in H2 |- * .
destruct H2 as [_ H2].
split.
auto.
red.
red in H2.
auto with arith.
set (g' := restrict_function (NS_ k) A g H1 H2 (coarser_subsetoid_refl T A) (inclusion_refl T A)).
set (a := g k').
set (A' := A[|](unequal_to a)).
assert (A' [~]NS_ k).

assert (f_algo := algo_part _ _ f).
destruct f as [f_fun f_wd].
assert (f_ok' : forall a : A', ss_dom (NS_  k) (f_algo a)).
intro a'.
destruct (nat_eq_dec k (f_fun a')).
assert (a [=]a').
assert (g k [=] g (f_fun a')).
apply ss_wd.
exact e.
assert (ss_fun (NS_ (S k)) A g (f_fun a') [=] a').
destruct H.
apply l.
eapply (eq_transitive _ _ _ _ X X0).












exact X.


destruct a_eqap.
assert (nx := ss_dom A' a').
apply A'.
exists (Build_ssfunction f_fun 
assert (ss_function A' (NS_ k).

set (U := map_pred _ _ f Uk').
assert (H0 : IN_ (S k)[|]Uk' [~] IN_ k).
unfold Uk'.
unfold IN_.
apply isomorphic_transitive with (Nat[|](N_ (S k)[/\]Uk)).
apply nn.





.
