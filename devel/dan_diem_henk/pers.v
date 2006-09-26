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
(* tbd :
- wishlist
- more appropriate names for lemmas and defs
- precedence levels 
- use CLogic.v
*)

Require Export CLogic.
Require Export tactics.

Definition predicate (A : Type) :=
  A -> Prop.

Definition relation (A : Type) := 
  A -> A -> Prop (*CProp?*).

Definition transitive (A : Type) (R : relation A) :=
  forall a b c, R a b -> R b c -> R a c.

Definition symmetric (A : Type) (R : relation A) := 
  forall a b, R a b -> R b a.

Definition reflexive (A : Type) (R : relation A) :=
  forall a, R a a.

Implicit Arguments transitive [A].
Implicit Arguments symmetric [A].
Implicit Arguments reflexive [A].

Record equivalence (A : Type) : Type :=
  { eqv_rel : relation A;
    eqv_refl : reflexive eqv_rel;
    eqv_sym : symmetric eqv_rel;
    eqv_trans : transitive eqv_rel
  }.

Record per : Type :=
  { car : Type;
    rel : relation car;
    tra : transitive rel;
    sym : symmetric rel
  }.

Definition mk_per A := Build_per A.

Implicit Arguments mk_per [A].

Notation "x [=] y" := 
  (rel _ x y) (at level 70, no associativity).

Ltac trans y :=
  match goal with 
  |- ?x [=] ?z => apply (tra _ x y z)
  end.

Ltac symm :=
  match goal with 
  |- ?x [=] ?y => apply (sym _ y x)
  end.

Implicit Types A B C : per.

Definition isin A (a : car A) := a [=] a.

Notation "a 'in' A" := (isin A a) (at level 90).

Record bar A : Type :=
  { elt :> car A;
    elt_in : elt [=] elt
  }.

Definition mk_bar := Build_bar.

Implicit Arguments elt [A].
Implicit Arguments elt_in [A].

Coercion bar : per >-> Sortclass.

Ltac refl :=
  match goal with 
  |- (rel ?A (elt ?x) (elt ?x)) => apply (elt_in x)
  end.

Definition type2per (A : Type) :=
  mk_per (eq (A:=A)) (trans_equal (A:=A)) (sym_eq (A:=A)).

(* think of [(Bar A)] as the quotient (car A)/(rel A) *)

Definition Bar A : per :=
  mk_per (fun a a' => elt a [=] elt a')
  (fun a b c => tra A (elt a) (elt b) (elt c))
  (fun a b => sym A (elt a) (elt b)).

(** [A[->]B], the function space [A->B] as a PER *)

Definition fun_wd A B (f : A -> B) :=
  forall a a' : A, a[=]a' -> f a [=] f a'.

Implicit Arguments fun_wd [A B].

Record per_fun A B : Type :=
  { pf_fun :> A -> B;
    pf_wd : fun_wd pf_fun
  }.

Definition mk_per_fun A B := Build_per_fun A B.

Implicit Arguments mk_per_fun [A B].

Definition pf_eq A B :=
  fun f g : per_fun A B => 
  forall a, f a [=] g a.

Lemma pf_eq_trans : 
  forall A B, transitive (pf_eq A B).
Proof.
intros A B f g h Hfg Hgh a.
trans (g a).
apply Hfg.
apply Hgh.
Qed.

Lemma pf_eq_symm : 
  forall A B, symmetric (pf_eq A B).
Proof.
intros A B f g Hfg a. 
symm.
apply Hfg.
Qed.

Definition perFS A B :=
  mk_per (pf_eq A B) (pf_eq_trans A B) (pf_eq_symm A B).

Infix "[->]" := perFS (at level 85).

Definition fap A B (f : A [->] B) (a : A) :=
  pf_fun A B (elt f) a.

Implicit Arguments fap [A B].

Lemma fap_wd : 
  forall A B (f : A[->]B) (x y : A),
  x[=]y -> fap f x [=] fap f y.
Proof.
intros A B f x y H.
unfold fap.
apply pf_wd with (1:=H).
Qed.

Definition per_fun_to_elt_of_FS A B (f : per_fun A B) : A [->] B.
intros.
apply (mk_bar (A[->]B) f).
intros [a ap].
apply pf_wd.
simpl.
exact ap.
Defined.

Notation "! f" := (per_fun_to_elt_of_FS _ _ f) (at level 80).

Coercion per_fun_to_elt_of_FS : per_fun >-> bar.

Definition id A : A [->] A :=
  mk_per_fun (fun a => a) (fun a a' H => H).

Definition empty_rel (A : Type) : relation A := 
  fun _ _ => False.

Definition empty_per A : per.
intro A.
apply (mk_per (empty_rel A)); red; trivial.
Defined.

Definition empty_fun A B : empty_per A [->] B :=
  mk_per_fun 
    (fun a : empty_per A => (False_rect B (elt_in a)))
    (fun a _ _ => (False_rect _ (elt_in a))).

Definition compose A B C (f : A[->]B) (g : B[->]C) : A[->]C.
intros A B C.
intros [f f_p] [g g_p].
simpl in f,g.
assert (H : fun_wd (fun a : A => g (f a))).
intros a1 a2 H.
apply pf_wd.
apply pf_wd.
exact H.
exact (mk_per_fun _ H).
Defined.

Notation "g '[o]' f" := (compose _ _ _ f g) (at level 69).

Definition injective A B (f : A[->]B) :=
  forall x1 x2 : A, fap f x1 [=] fap f x2 -> x1 [=] x2.

Definition surjective A B (f : A[->]B) := 
  forall y : B, {x : A | fap f x [=] y}.

Implicit Arguments injective [A B].
Implicit Arguments surjective [A B].

Definition bijective A B (f : A[->]B) := 
  injective f and surjective f.

Implicit Arguments bijective [A B].

Definition left_inverse A B (f : A[->]B) (g : B[->]A) :=
  forall x : A, fap g (fap f x) [=] x.

Definition right_inverse A B (f : A[->]B) (g : B[->]A) :=
  forall y : B, fap f (fap g y) [=] y.

Implicit Arguments left_inverse [A B].
Implicit Arguments right_inverse [A B].

Definition inverse A B (f : A[->]B) (g : B[->]A) :=
  left_inverse f g and right_inverse f g.

Implicit Arguments inverse [A B].

Lemma left_inverse_injective :
  forall A B (f : A[->]B) (g : B[->]A), 
  left_inverse f g ->
  injective f.
Proof.
intros A B f g H x1 x2 H0.
trans (fap g (fap f x1)).
symm.
apply H.
trans (fap g (fap f x2)).
apply fap_wd.
exact H0.
apply H.
Qed.

Lemma right_inverse_surjective :
  forall A B (f : A[->]B) (g : B[->]A),
  right_inverse f g ->
  surjective f.
Proof.
intros A B f g H y.
exists (fap g y).
exact (H y).
Qed.

Lemma inverse_bijective :
  forall A B (f : A[->]B) (g : B[->]A),
  inverse f g ->
  bijective f.
Proof.
intros A B f g [ Hl Hr ].
split.
apply left_inverse_injective with (1:=Hl).
apply right_inverse_surjective with (1:=Hr).
Qed.

(* not so nice ... *)
Lemma composition_preserves_inverse :
  forall A B C (f : A[->]B)(f' : B[->]A)(g : B[->]C)(g' : C[->]B),
  inverse f f' ->
  inverse g g' ->
  inverse (g[o]f) (f'[o]g').
Proof.
intros A B C [f fp] [f' f'p] [g gp] [g' g'p] [ lif rif ] [ lig rig ].
red in lif, rif, lig, rig.
unfold fap in lif, rif, lig, rig.
simpl_all.
split; red; intro x; unfold fap; simpl.
trans (f' (f x)).
apply pf_wd.
apply lig.
apply lif.
trans (g (g' x)).
apply pf_wd.
apply rif.
apply rig.
Qed.

Lemma inverse_symmetric :
  forall A B (f : A[->]B) (g : B[->]A),
  inverse f g -> 
  inverse g f.
Proof.
intros A B f g [ Hl Hr ].
split; [ exact Hr | exact Hl ].
Qed.

Definition isomorphic A B :=
  {f : A[->]B | {g : B[->]A | inverse f g}}.

Infix "[~]" := isomorphic (at level 70).

Lemma isomorphic_reflexive :
  forall A, A[~]A.
Proof.
intro A.
exists (id A); exists (id A).
split; intro x; unfold fap; simpl; refl.
Qed.

Lemma isomorphic_symmetric :
  forall A B, A[~]B -> B[~]A.
Proof.
intros A B [ f [ g H ] ].
exists g; exists f.
apply inverse_symmetric with (1:=H).
Qed.

Lemma isomorphic_transitive :
  forall A B C, A[~]B -> B[~]C -> A[~]C.
Proof.
intros A B C [ f [ f' H1 ] ] [ g [ g' H2 ]].
exists (g[o]f).
exists (f'[o]g').
apply composition_preserves_inverse with (1:=H1) (2:=H2).
Qed.

(** Quotients [A[/]R] *)

Definition pred_wd A (P: predicate A) :=
  forall a a' : A, a[=]a' -> P a -> P a'.

Definition rel_wdl A B (R: relation A) :=
  forall a a' b : A, a[=]a' -> R a b -> R a' b.

Definition rel_wdr A B (R: relation A) :=
  forall a a' b : A, a[=]a' -> R b a -> R b a'.

Record per_rel A : Type :=
  { pr_rel :> A -> A -> Prop;
    pr_tra : transitive pr_rel;
    pr_sym : symmetric pr_rel;
    pr_inc : forall a b : A, a[=]b -> pr_rel a b
  }.

Definition mk_per_rel := Build_per_rel.

Implicit Arguments mk_per_rel [A].

Definition quotient A (R : per_rel A) : per :=
  mk_per R (pr_tra A R) (pr_sym A R).

Infix "[/]" := quotient (at level 80).

Definition class A (R: per_rel A) : A [->] A[/]R.
intros A R.
set (_f := fun a : A => mk_bar (A[/]R) a (pr_inc A R a a (elt_in a))).
assert (f_wd : fun_wd _f).
intros a a' H.
simpl.
apply pr_inc with (1:=H).
exact (mk_per_fun _f f_wd).
Defined.

Notation "'[' a ']_' R" := 
  (fap (class _ R) a) (at level 69, format "'[' [ a ]_ R ']'").

Lemma class_surj :
  forall A (R : per_rel A),
  surjective (class A R).
Proof.
intros A R [y y_p].
exists y.
simpl.
exact y_p.
Qed.

Lemma main (* rename *): 
  forall A (R : per_rel A),
  class A R in A [->] A[/]R.
Proof.
intros A R.
exact (elt_in (class A R)).
Qed.

Lemma main2 (* rename *) : 
  forall A (R : per_rel A) (a a' : A),
  R a a' <-> [a]_R [=] [a']_R.
Proof.
auto.
Qed.

Definition rel_to_per_rel A : per_rel A.
intro A.
apply (Build_per_rel A (rel A)).
intros a b c.
exact (tra A a b c).
intros a b.
exact (sym A a b).
trivial.
Defined.

Lemma Bar_quot :
  forall A (a : A), 
  a in Bar A 
  <-> 
  a in (A[/](rel_to_per_rel A)).
Proof.
auto.
Qed.

(** Products A[*]B *)

Definition prodp_car A B := 
  prodT (car A) (car B).

Definition prodp_rel A B : relation (prodp_car A B).
intros A B [a b] [a' b'].
exact (rel A a a' /\ rel B b b').
Defined.

Lemma prodp_rel_trans : 
  forall A B, transitive (prodp_rel A B).
Proof.
intros A B [a1 b1] [a2 b2] [a3 b3] [Ha12 Hb12] [Ha23 Hb23].
split.
apply tra with (1:=Ha12) (2:=Ha23).
apply tra with (1:=Hb12) (2:=Hb23).
Qed.

Lemma prodp_rel_symm : 
  forall A B, symmetric (prodp_rel A B).
Proof.
intros A B [a1 b1][a2 b2] [Ha Hb].
split.
apply sym with (1:=Ha).
apply sym with (1:=Hb).
Qed.

Definition prodp A B :=
  mk_per (prodp_rel A B) (prodp_rel_trans A B) (prodp_rel_symm A B).

Infix "[*]" := prodp (at level 80).

Definition pairp A B : A -> B -> A [*] B.
intros A B [a a_] [b b_].
apply (mk_bar (A [*] B) (pairT a b)).
simpl.
split; aa.
Defined.

Implicit Arguments pairp [A B].

Lemma L6 (* rename *): 
  forall A B (c : A[*]B),
  exists a : A, exists b : B, 
  c = pairp a b.
Proof.
intros A B [[a b] [a_ b_]].
exists (mk_bar A a a_).
exists (mk_bar B b b_).
simpl.
reflexivity.
Qed.

Lemma L7 (* rename *) :
  forall A B (a1 a2 : A) (b1 b2 : B),
  pairp a1 b1 [=] pairp a2 b2 <->
  a1 [=] a2 /\ b1 [=] b2.
Proof.
intros A B [a1 a1_] [a2 a2_] [b1 b1_] [b2 b2_].
simpl.
split; trivial.
Qed.

(** Subsets [A[|]P] (or: [{x : A | P x}]) *)

Definition Restr A (P : A -> Prop) :=
  fun a b : A => a [=] b /\ P a /\ P b.

Lemma Restr_trans : 
  forall A (P : A -> Prop),
  transitive (Restr A P).
Proof.
intros A P.
intros a b c [Hab [p _]] [Hbc [_ q]].
split.
apply tra with (1:=Hab) (2:=Hbc).
spl.
Defined.

Lemma Restr_symm : 
  forall A (P : A -> Prop),
  symmetric (Restr A P).
Proof.
intros A P a b [Hab [p q]].
split.
apply sym with (1:=Hab).
spl.
Qed.

Definition restr A (P : A -> Prop) :=
  mk_per (Restr A P) (Restr_trans A P) (Restr_symm A P).

Infix "[|]" := restr (at level 69).

Notation "{ x : A | P }" := 
  (restr A (fun x => P)) (at level 0, x at level 99) : type_scope.

Lemma L30 (* rename *) : 
  forall A (a : A) (P : A -> Prop), 
  a in { x : A | P x } 
  <->
  (a in A) /\ P a.
Proof.
intros A a P.
split; intro H; destruct H as [H H0].
exact (conj H (proj1 H0)).
exact (conj H (conj H0 H0)).
Qed.

(** A sub B *)

Definition inj1 :
  forall A (P : A -> Prop),
  { x : A | P x } -> A.
intros A P [[a p] _].
exact (mk_bar A a p).
Defined.

Lemma inj1_wd : 
  forall A (P : A -> Prop), 
  fun_wd (inj1 A P).
Proof.
intros A P [[a ap1] ap2] [[a' a'p1] a'p2] [H [H0 H1]].
simpl_all.
exact H.
Qed.

Definition inj A (P : A -> Prop) :=
  mk_per_fun (inj1 A P) (inj1_wd A P).

Definition restr_f1 A B (P : A -> Prop) (f : A [->] B) :=
  f [o] inj A P.

Definition restr_f2 A B (Q : B -> Prop) (f : A [->] {b : B | Q b}) :=
  inj B Q [o] f.

Definition restr_f
  A B (P : A -> Prop) (Q : B -> Prop) (f : A [->] {y : B | Q y}) :=
  (restr_f2 A B Q f) [o] inj A P.

Implicit Arguments restr_f1 [A B].
Implicit Arguments restr_f2 [A B].
Implicit Arguments restr_f [A B].

(** [Pred A], the PER of predicates over [A] *)

Definition pred_eq A (P Q : predicate A) :=
  forall a : A, P a <-> Q a.

Lemma pred_eq_trans : forall A, transitive (pred_eq A).
Proof.
intros A P1 P2 P3 H12 H23 a.
split; intro H.
exact (proj1 (H23 a) (proj1 (H12 a) H)).
exact (proj2 (H12 a) (proj2 (H23 a) H)).
Qed.

Lemma pred_eq_symm : forall A, symmetric (pred_eq A).
Proof.
intros A P1 P2 H12 a.
split; intro H.
exact (proj2 (H12 a) H).
exact (proj1 (H12 a) H).
Qed.

Definition Pred A :=
  mk_per (pred_eq A) (pred_eq_trans A) (pred_eq_symm A).

(* let's do it *)

Lemma le_lt_or_eq_dec : 
  forall n m : nat, n <= m -> {n < m} + {n = m}.
Proof.
induction n; destruct m; intro H.
right; reflexivity.
left.
auto with arith.
assert False. (* *)
inversion H.
elim H0.
assert (n <= m).
auto with arith.
elim (IHn m H0); auto with arith.
Qed.

Definition IN := 
  type2per nat.

Definition N_ (k : nat) :=
  fun i : IN => (elt i) < k.

Definition IN_ k :=
  IN[|](N_ k).

Lemma IN_S_dec (* rename *) : 
  forall k (m : (IN_ (S k))),
  {(elt (elt m)) < k} + {(elt (elt m)) = k}.
Proof.
intros k m.
destruct (elt_in m) as [ _ [H _]].
assert (H0 := le_S_n _ _ H).
exact (le_lt_or_eq_dec _ _ H0).
Qed.

(*
sigT syntax is overridden by syntax for restr;
using || in restr doesn't work .

Definition finite A :=
  {k : nat | A [~] (IN_ k)}.
*)

Definition finite A :=
  (sigT (fun k => A [~] (IN_ k))).

Lemma empty_per_finite : 
  forall A, finite (empty_per A).
intro A.
exists 0.
set (f := fun a : (empty_per A) => False_rect (IN_ 0)(elt_in a)).
assert (f_wd : fun_wd f).
intros a a' H.
unfold f.
ex_falso.
(* :( *)
set (g := fun m : (IN_ 0) => 
  False_rect (empty_per A)(lt_n_O _ (proj1 (proj2 (elt_in m))))).
assert (g_wd : fun_wd g).
intros a a' H.
unfold g.
ex_falso.
exists (! (mk_per_fun f f_wd)).
exists (! (mk_per_fun g g_wd)).
split; intro a; unfold fap; simpl.
red.
exact (elt_in a).
red.
destruct (lt_n_O _ (proj1 (proj2 (elt_in a)))).
Qed.

