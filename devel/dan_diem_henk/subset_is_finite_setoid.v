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
Require Export Arith.
Require Export SetoidFun.

Definition nat_eq_dec : forall n m : nat, {n = m} + {n <> m}.
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
Defined.

Implicit Types A B : Setoid.

(* text *)

Definition le_lt_or_eq_dec : 
  forall n m : nat, n <= m -> {n < m} + {n = m}.
Proof.
induction n; destruct m; intro H.
right; reflexivity.
left.
auto with arith.
assert False. (* ??? *)
inversion H.
elim H0.
assert (n <= m).
auto with arith.
elim (IHn m H0); auto with arith.
Defined.

Definition decidable p := {p} + {~p}.

Definition decidable_pred (A : Type) (P : A -> Prop) := 
  forall x, (decidable (P x)).

Definition Nat : Setoid := Type2Setoid nat.

Definition N_ n := 
  fun i => i < n.

Definition IN_ n : Setoid :=
  Build_SubSetoid Nat (N_ n).

Definition Finite A : CProp :=
  {n : nat | {f : Setoid_fun A (IN_ n) |  bijective f}}.

Definition Emptyset : Setoid := 
  Type2Setoid False.

Definition Singleton A (a:A) :=
  Build_SubSetoid A (fun a' => a' = a).

Implicit Arguments Singleton [A].

Infix "[U]" := UnionSetoid (at level 40, left associativity).

Definition Eqset A B :=
  {f : Setoid_fun A B | bijective f}.

Infix "=s" := Eqset (at level 70).

Lemma empty_finite : forall A, Finite Emptyset.
Proof.
exists O.
set (f :=  fun s :  Emptyset => (False_rect (IN_ 0) s)).
assert (f_wd : fun_wd f).
intro x1; elim x1.
exists (Build_Setoid_fun _ _ f f_wd).
split.
intro x1; elim x1.
intro y.
assert (H := (ss_prf y)).
elim (lt_n_O (ss_elt y) H).
Qed.

Lemma eqset_finite :
  forall A B, A =s B -> Finite A -> Finite B.
Proof.
intros A B [ f Bijf ] [ n [ g Bijg ] ].
exists n.
exists ((Inv Bijf)[o]g).
apply composition_respects_bijection.
apply Inv_bijective.
exact Bijg.
Qed.

(*
extremely bad
*)

Definition _lift_N_ n : (IN_ n) -> (IN_ (S n)).
intros n H.
apply (Build_subsetoid_crr Nat (N_ (S n)) (ss_elt H)).
apply le_S with (1:=(ss_prf H)).
Defined.

Lemma _lift_N__wd : forall n : nat, fun_wd (_lift_N_ n).
Proof.
intros n x1 x2 H.
destruct x1.
destruct x2.
exact H. (* This is sooooooo ugly *)
Qed.

Definition lift_N_ n :=
  Build_Setoid_fun (IN_ n) (IN_ (S n)) (_lift_N_ n) (_lift_N__wd n).


Definition n_in_N_Sn n :=
  Build_subsetoid_crr Nat (N_ (S n)) n (lt_n_Sn n).

(*
Lemma lift_N_diff_n :
  forall (n : nat) (m : (IN_ n)),
  (lift_N_ n m) <> (n_in_N_Sn n).
Proof.
intros n m.
destruct m as [ m_e m_p ].
simpl.
unfold _lift_N_.
unfold n_in_N_Sn.
red.
simpl.
intro H.
unfold N_ in m_p.
elim (lt_irrefl n).
injection H.
intro H0.
clear H.
rewrite H0 in m_p.
exact m_p.
Qed.
*)

Lemma lift_N_diff_n :
  forall (n : nat) (m : (IN_ n)),
  (lift_N_ n m) [~=] (n_in_N_Sn n).
Proof.
intros n m.
destruct m as [ m_e m_p ].
simpl.
unfold _lift_N_.
unfold n_in_N_Sn.
red.
simpl.
intro H.
unfold N_ in m_p.
elim (lt_irrefl n).
rewrite H in m_p.
exact m_p.
Qed.

Definition proj_N_' :
  forall (n : nat) (m : (IN_ (S n))),
  (ss_elt m) <> n ->
  (IN_ n).
intros n m H.
elim (le_lt_or_eq_dec (ss_elt m) n (le_S_n _ _ (ss_prf m))); intro H0.
exact (Build_subsetoid_crr Nat (N_ n) (ss_elt m) H0).
elim (H H0).
Defined.

Definition proj_N_ :
  forall (n : nat) (m : (IN_ (S n))),
  (ss_elt m) [~=] n ->
  (IN_ n) :=
fun n m H =>
  match (le_lt_or_eq_dec (ss_elt m) n (le_S_n _ _ (ss_prf m))) 
  with
  |(left p)  => (Build_subsetoid_crr Nat (N_ n) (ss_elt m) p)
  |(right p) => (False_rect (IN_ n) (H p))
  end.

Lemma swap_proj_lift :
  forall (n : nat) (m : IN_ n) (m' : IN_ (S n)) (H : ss_elt m' [~=] n),
  m' [=] lift_N_ n m ->
  proj_N_ n m' H [=] m.
Proof.
intros n m m' H H0.
unfold proj_N_.
case (le_lt_or_eq_dec (ss_elt m') n (le_S_n (ss_elt m') n (ss_prf m'))); intro H1.
destruct m as [ m_e m_p ].
destruct m' as [ m'_e m'_p ].
simpl in  *|-* .
exact H0.
elim H.
rewrite H1.
apply eq_reflexive.
Qed.


Lemma swap_lift_proj :
  forall (n : nat) (m : IN_ n) (m' : IN_ (S n)) (H : ss_elt m' [~=] n),
  m [=] proj_N_ n m' H ->
  lift_N_ n m [=] m'.
Proof.
intros n m m' H H0.
unfold proj_N_ in H0.
destruct (le_lt_or_eq_dec (ss_elt m') n (le_S_n (ss_elt m') n (ss_prf m')))
  as [ H1 | H1 ].
destruct m as [ m_e m_p ].
destruct m' as [ m'_e m'_p ].
simpl in  *|-* .
exact H0.
elim H.
rewrite H1.
apply eq_reflexive.
Qed.

Lemma we_should_have_this:
   forall S:Setoid, forall P: S -> Prop, forall x: Build_SubSetoid S P, forall s:S, forall p:P s,
       x[=] Build_subsetoid_crr S P s p -> ss_elt x [=] s.
intros S P x s p.
destruct x as [x_e x_prf].
simpl.
intro H; exact H.
Qed.

Lemma add_one_preserves_finiteness :
   forall A D,
   Finite D ->
   forall a : A, Finite (D [U] (Singleton a)).
Proof.
intros A D [ n [ f [ Injf Surjf ] ] ] a.
exists (S n).
(* naming conventions svp *)
set 
  (_f' := 
    fun u : D[U](Singleton a) => 
      match u with 
      | Tinleft d   => (lift_N_ n (f d))
      | Tinright a' => 
          (Build_subsetoid_crr Nat (N_ (S n)) n (lt_n_Sn n))
      end
  ).
(* we have to explicitly give the setoid args of fun_wd;
if we don't, S2 is set to Nat instead of (IN_ (S n)).
!!!
make setoid args implicit in fun_wd asks too much of the 
type inference system, not always can it infer S from (s_crr S)
!!!
*)
(* wrong! silly thing
assert (_f'_wd : fun_wd f').
*)
assert (_f'_wd : fun_wd (S2:=(IN_ (S n))) _f').
intros x1 x2.
destruct x1; destruct x2; (* paper and pen !!! *)
  simpl; intro H.
generalize (sf_wd _ _ f s s0 H).
destruct (f s).
destruct (f s0).
simpl.
trivial.
elim H.
elim H.
reflexivity.
set (f' := (Build_Setoid_fun (D[U]Singleton a) (IN_ (S n)) _f' _f'_wd)).
exists f'.
(* prove that f' is bijective *)
split.
intros x1 x2; destruct x1; destruct x2; (* paper and pen again! *)
  simpl; intro H.
apply (Injf s s0).
destruct (f s); destruct (f s0); simpl in * |- *.
exact H.
assert (H0 := (ss_prf (f s))).
rewrite H in H0.
elim lt_irrefl with (1:=H0).
assert (H0 := (ss_prf (f s0))).
rewrite <- H in H0.
elim lt_irrefl with (1:=H0).
destruct s; destruct s0.
simpl.
rewrite ss_prf; rewrite ss_prf0; apply eq_reflexive.
intro y.
assert (H := (ss_prf y)).
unfold N_ in H.
(* we have to use a decidable version of le_lt_or_eq *)
elim le_lt_or_eq_dec with (1:=H); intro H0.
assert ((ss_elt y) < n).
auto with arith.
set (y' := (Build_subsetoid_crr Nat (N_ n) _ H1)).
elim (Surjf y'); intros x H2.
exists (Tinleft D (Singleton a) x).
assert (y [=] (lift_N_ n y')).
simpl.
unfold _lift_N_.
simpl.
destruct y.
simpl.
reflexivity.
apply eq_transitive with (lift_N_ n y').
(* simpl simplifies too much! *)
change ((_lift_N_ n (f x))[=](_lift_N_ n y')).
apply (_lift_N__wd n).
exact H2.
apply eq_symmetric.
exact H3.
injection H0; clear H0; intro H0.
exists 
  (Tinright D (Singleton a) 
    (Build_subsetoid_crr A (fun a' => a' = a) a (refl_equal a))).
(* not nice : *)
destruct y; simpl in *|-*.
symmetry.
exact H0.
Qed.


(*
Lemma Build_subsetoid_crr_wd : 
  forall (A : Setoid) (P : A -> Prop) (a : A) (p : P a),
  fun_wd (Build_subsetoid_crr A P a p).

*)


(* tbd : 
- prove that finite sets are decidable
- improve definitions like le_lt_or_eq_dec, nat_eq_dec ...
  make them fully transparent?
- clean up lift, proj stuff
- turn proj_N_ into a setoid function ?, 
*)

Theorem subset_is_finite :
  forall (A : Setoid) (P : Setoid_predicate A),
  decidable_pred A P ->
  Finite A -> 
  Finite (Build_SubSetoid A P).
Proof.
intros A P decP [ n [ f Bijf ] ].
generalize A P decP f Bijf; clear Bijf f decP P A.
induction n; intros A P decP f Bijf.
(* 0 *)
set (B := (Build_SubSetoid A P)).
exists O.
set (_g := fun b : B => (ss_elt b)).
assert (_g_wd : (fun_wd _g)).
intros x1 x2 H.
(* omg, exact H doesn't work, try "Set Printing Coercions." *)
destruct x1; destruct x2; exact H.
set (g := (Build_Setoid_fun _ _ _g _g_wd)).
assert (Bijg : bijective g).
split.
intros x1 x2.
destruct x1; destruct x2; trivial.
intro y.
assert (H := ss_prf (f y)).
unfold N_ in H.
elim lt_n_O with (1:=H).
exists (g[o]f).
apply composition_respects_bijection with (1:=Bijg) (2:=Bijf).
(* S n *)
set (B := (Build_SubSetoid A P)).
elim Bijf; intros Injf Surjf.
(* first we construct a bijection g in (A - {x}) -> (IN_ n),
  where x is the element corresponding to n *)
(* n' is just n, but in the subsetoid (IN_ (S n)) *)
set (n' := (n_in_N_Sn n)).
elim (Surjf n'); intros x H.
set (unequal_to_x := fun a : A => (ss_elt (f a)) <> n).
(* A' := A - {x} *)
set (A' := Build_SubSetoid A unequal_to_x).
set (_P' := fun a' : A' => (P (ss_elt a'))).
assert (P'wd : pred_wd A' _P').
intros a1' a2'.
destruct a1'. destruct a2'. 
unfold _P'.
simpl.
intros H1 H2.
apply (sp_wd A P _ _ H1 H2).
set (P' := Build_Setoid_predicate _ _P' P'wd).
assert (decP' : (decidable_pred A' P')).
exact (fun a' : A' => (decP (ss_elt a'))).
set (_g := fun a' : A' => (proj_N_ n (f (ss_elt a')) (ss_prf a'))).
assert (_g_wd : fun_wd _g).
intros x1 x2 H0.
destruct x1 as [ x1_e x1_p ]; destruct x2 as [ x2_e x2_p ].
simpl in H0.
change ((proj_N_ n (f x1_e) x1_p) [=] (proj_N_ n (f x2_e) x2_p)).
unfold proj_N_.
case (le_lt_or_eq_dec (ss_elt (sf_fun A (IN_ (S n)) f x1_e)) n
        (le_S_n (ss_elt (sf_fun A (IN_ (S n)) f x1_e)) n
           (ss_prf (sf_fun A (IN_ (S n)) f x1_e)))); intro H1.
case (le_lt_or_eq_dec (ss_elt (sf_fun A (IN_ (S n)) f x2_e)) n
        (le_S_n (ss_elt (sf_fun A (IN_ (S n)) f x2_e)) n
           (ss_prf (sf_fun A (IN_ (S n)) f x2_e)))); intro H2.
(* here we worked hard to see that this goal is *not* convertible with
(f x1_e) [=] (f x2_e)
*)
(*
Set Printing Coercions.
*)
(* 
do 5 red.
*)
change ((ss_elt (f x1_e))[=](ss_elt (f x2_e))).
apply ss_elt_wd.
apply sf_wd with (1:=H0).
elim (x2_p H2).
elim (x1_p H1).
set (g := Build_Setoid_fun A' (IN_ n) _g _g_wd).
assert (Bijg : bijective g).
split.
(* injectivity of g *)
intros x1 x2 H0.
destruct x1 as [ x1_e x1_p].
destruct x2 as [ x2_e x2_p].
simpl.
change ((proj_N_ n (f x1_e) x1_p) [=] (proj_N_ n (f x2_e) x2_p)) in H0.
unfold proj_N_ in H0.
destruct (le_lt_or_eq_dec (ss_elt (sf_fun A (IN_ (S n)) f x1_e)) n
          (le_S_n (ss_elt (sf_fun A (IN_ (S n)) f x1_e)) n
           (ss_prf (sf_fun A (IN_ (S n)) f x1_e)))) as [ H1 | H1 ].
destruct (le_lt_or_eq_dec (ss_elt (sf_fun A (IN_ (S n)) f x2_e)) n
          (le_S_n (ss_elt (sf_fun A (IN_ (S n)) f x2_e)) n
           (ss_prf (sf_fun A (IN_ (S n)) f x2_e)))) as [ H2 | H2 ].
change ((ss_elt (f x1_e))[=](ss_elt (f x2_e))) in H0.
apply Injf.
(* [apply ss_elt_inj.] doesn't work *)
apply (ss_elt_inj Nat (N_ (S n))).
exact H0.
elim (x2_p H2).
elim (x1_p H1).
(* surjectivity of g *)
intro y.
elim (Surjf (lift_N_ n y)); intros a H0.
assert (H1 := lift_N_diff_n n y).
fold n' in H1.
assert (H2 : (f a) [~=] n').
intro H2.
apply H1.
apply eq_transitive with (f a).
apply eq_symmetric.
exact H0.
exact H2.
assert (H3: (ss_elt (f a)) <> n).
intro H3.
apply H2.
(* proving setoid equality fomr equality should be easy, right? *)
destruct (f a); simpl in *|-* .
exact H3.
set (a' := (Build_subsetoid_crr A unequal_to_x a H3)).
exists a'.
unfold g, _g.
simpl.
exact (swap_proj_lift n y (f a) H3 H0).
assert (H0 := (IHn A' P' decP' g Bijg)).
unfold B.
set (B' := (Build_SubSetoid A' P')).
fold B' in H0.
elim H0; intros m H1; elim H1; clear H1; intros h Bijh.
elim Bijh; intros Injh Surjh.
elim (decP x); intro H2.
exists (S m).
set 
  (_i := 
    fun b : B =>
    match (nat_eq_dec (ss_elt (f (ss_elt b))) n) with
    |(left _)  => (n_in_N_Sn m)
    |(right p) => 
      (lift_N_ m (h (Build_subsetoid_crr A' P'
       (Build_subsetoid_crr A unequal_to_x (ss_elt b) p) (ss_prf b))))
    end
  ).
assert (_i_wd : (fun_wd _i)).
intros b1 b2 H3.
unfold _i.
destruct b1 as [ b1_e b1_p ].
destruct b2 as [ b2_e b2_p ].
simpl in H3.
case 
  (nat_eq_dec
   (ss_elt (f (ss_elt (Build_subsetoid_crr A P b1_e b1_p)))) n); 
  intro H4;
  case 
    (nat_eq_dec
     (ss_elt (f (ss_elt (Build_subsetoid_crr A P b2_e b2_p)))) n); 
    intro H5;
  simpl in H4, H5.
apply eq_reflexive.
elim H5.
rewrite <- H4.
apply (ss_elt_wd Nat (N_ (S n))).
apply sf_wd.
apply eq_symmetric with (1:=H3).
elim H4.
rewrite <- H5.
apply (ss_elt_wd Nat (N_ (S n))).
apply sf_wd with (1:=H3).
(* simpl simplifies the [=] into = as well; we don't want that *)
change 
  (
  ss_elt (h (Build_subsetoid_crr A' P'
      (Build_subsetoid_crr A unequal_to_x b1_e H4) b1_p))
  [=]
  ss_elt (h (Build_subsetoid_crr A' P'
      (Build_subsetoid_crr A unequal_to_x b2_e H5) b2_p))
  ).
apply ss_elt_wd. (* this time it works *)
(* this is so unreadable! why do the coercions fail to do their job *)
apply sf_wd.
simpl.
exact H3.
set (i := Build_Setoid_fun B (IN_ (S m)) _i _i_wd).
exists i.
split.
(* injectivity of i *)
intros b1 b2 H3.
unfold i, _i in H3.
destruct b1 as [ b1_e b1_p ].
destruct b2 as [ b2_e b2_p ].
simpl.
simpl in H3.
destruct (nat_eq_dec (ss_elt (sf_fun A (IN_ (S n)) f b1_e)) n) 
  as [ H4 | H4 ];
  destruct (nat_eq_dec (ss_elt (sf_fun A (IN_ (S n)) f b2_e)) n) 
    as [ H5 | H5 ]; 
  simpl in H3.
apply Injf.
apply (ss_elt_inj Nat (N_ (S n))). (* apply identity !?*)
simpl in H4, H5.
rewrite H4; rewrite H5.
apply eq_reflexive.
assert (H6 :=
  (ss_prf (h (Build_subsetoid_crr A' P'
              (Build_subsetoid_crr A unequal_to_x b2_e H5) b2_p)))).
unfold N_ in H6.
rewrite H3 in H6. (* but not rewrite <- H3 in H6 , WHY NOT?? *)
elim lt_irrefl with (1:=H6).
assert (H6 :=
  (ss_prf (h (Build_subsetoid_crr A' P'
              (Build_subsetoid_crr A unequal_to_x b1_e H4) b1_p)))).
unfold N_ in H6.
rewrite <- H3 in H6. (* but not rewrite H3 in H6 , WHY NOT?? *)
elim lt_irrefl with (1:=H6).
set 
  (b1' := 
    (Build_subsetoid_crr A' _P' 
     (Build_subsetoid_crr A unequal_to_x b1_e H4) b1_p)).
set 
  (b2' := 
    (Build_subsetoid_crr A' _P' 
     (Build_subsetoid_crr A unequal_to_x b2_e H5) b2_p)).
fold b1' in H3.
fold b2' in H3.
assert (H6 := Injh b1' b2').
apply H6.
Set Printing Coercions.
apply (ss_elt_inj Nat (N_ m)).
rewrite H3.
apply eq_reflexive.
(* surjectivity of i *)
intro y.
destruct y as [ y_e y_p ].
elim (nat_eq_dec y_e m); intro H3.
exists (Build_subsetoid_crr A P x H2).
unfold i, _i.
simpl.
case (nat_eq_dec (ss_elt (sf_fun A (IN_ (S n)) f x)) n); intro H4.
simpl.
symmetry.
exact H3.
elim H4.
assert (H99 := H).
destruct (f x); simpl in H99 |- *.
exact H99.
assert (H4 : y_e [~=] m).
intro H4.
elim H3.
exact H4.
(* silly, reconstruct y *)
set (y := (Build_subsetoid_crr Nat (N_ (S m)) y_e y_p)).
set (y' := (proj_N_ m y H4)).
elim (Surjh y'); intros b' H5.
destruct b' as [ b'_e b'_p ].
destruct b'_e as [b'_e_e b'_e_p ].
set (b := (Build_subsetoid_crr A P b'_e_e b'_p)).
exists b.
unfold i, _i.
(* we don't [=] to be simplified ( as simpl does) *)
simpl.
(* we also now that we're in the second case (right), 
because we have b'_e_p; can we do a rewrite instead? *) 
case (nat_eq_dec (ss_elt (sf_fun A (IN_ (S n)) f b'_e_e)) n); intro H6.
simpl.
unfold unequal_to_x in b'_e_p.
elim (b'_e_p H6).
(* don't simpl here (you'd lose [=]) *)
change 
(
 (_lift_N_ m
        (sf_fun B' (IN_ m) h
           (Build_subsetoid_crr A' P'
              (Build_subsetoid_crr A unequal_to_x b'_e_e H6) b'_p)))
[=] y
).
apply (swap_lift_proj m  (sf_fun B' (IN_ m) h
        (Build_subsetoid_crr A' P'
           (Build_subsetoid_crr A unequal_to_x b'_e_e H6) b'_p)) y H4).
(* ! *)
assert (wow : 
(Build_subsetoid_crr A' P'
            (Build_subsetoid_crr A unequal_to_x b'_e_e b'_e_p) b'_p)
[=]
(Build_subsetoid_crr A' P'
            (Build_subsetoid_crr A unequal_to_x b'_e_e H6) b'_p)).
simpl.
apply eq_reflexive.
assert (H7 :
 ss_elt
     (sf_fun B' (IN_ m) h
        (Build_subsetoid_crr A' P'
           (Build_subsetoid_crr A unequal_to_x b'_e_e H6) b'_p))
[=]
ss_elt
(sf_fun B' (IN_ m) h
         (Build_subsetoid_crr A' P'
            (Build_subsetoid_crr A unequal_to_x b'_e_e b'_e_p) b'_p))
).
apply ss_elt_wd.
apply sf_wd.
exact wow.
clear wow.
apply (ss_elt_inj Nat (N_ m)).
apply 
(eq_transitive Nat
 (ss_elt
         (sf_fun B' (IN_ m) h
            (Build_subsetoid_crr A' P'
               (Build_subsetoid_crr A unequal_to_x b'_e_e H6) b'_p)))



 (ss_elt
         (sf_fun B' (IN_ m) h
            (Build_subsetoid_crr A' P'
               (Build_subsetoid_crr A unequal_to_x b'_e_e b'_e_p) b'_p))) 

(ss_elt (proj_N_ m y H4))
H7).
apply ss_elt_wd.
exact H5.
(* The ~P x case *)
exists m.
assert (H' :ss_elt (f x) [=] n).
apply (we_should_have_this _ _ _ _ _ H).
set (_i :=
 fun b : B =>
  match (nat_eq_dec (ss_elt (f  (ss_elt b))) n) with
  |(left p) => (False_rect (IN_ m) (H2 (sp_wd _ P _ _ (ss_prf b) (Injf (ss_elt b) x (ss_elt_inj _ _ _ _ (eq_transitive _ _ _ _ (lift_eq Nat (ss_elt (f  (ss_elt b))) n  p) (eq_symmetric _ _ _ H')))))))
  | (right p) => h (Build_subsetoid_crr A' P' (Build_subsetoid_crr A unequal_to_x (ss_elt b) p) (ss_prf b))
  end).
assert (i_wd : (fun_wd _i)).
intros b1 b2 H3.
unfold _i.
destruct ( nat_eq_dec (ss_elt (sf_fun A (IN_ (S n)) f (ss_elt b1))) n) as [p1 | p1].
(* Dimitri thinks he can do this better *)
elim (     (H2
        (sp_wd A P (ss_elt b1) x (ss_prf b1)
           (Injf (ss_elt b1) x
              (ss_elt_inj Nat (N_ (S n))
                 (sf_fun A (IN_ (S n)) f (ss_elt b1))
                 (sf_fun A (IN_ (S n)) f x)
                 (eq_transitive Nat
                    (ss_elt (sf_fun A (IN_ (S n)) f (ss_elt b1))) n
                    (ss_elt (sf_fun A (IN_ (S n)) f x))
                    (lift_eq Nat
                       (ss_elt (sf_fun A (IN_ (S n)) f (ss_elt b1))) n p1)
                    (eq_symmetric Nat (ss_elt (sf_fun A (IN_ (S n)) f x)) n
                       H'))))))).
destruct (nat_eq_dec (ss_elt (sf_fun A (IN_ (S n)) f (ss_elt b2))) n) as [p2 | p2].
elim  (H2
        (sp_wd A P (ss_elt b2) x (ss_prf b2)
           (Injf (ss_elt b2) x
              (ss_elt_inj Nat (N_ (S n))
                 (sf_fun A (IN_ (S n)) f (ss_elt b2))
                 (sf_fun A (IN_ (S n)) f x)
                 (eq_transitive Nat
                    (ss_elt (sf_fun A (IN_ (S n)) f (ss_elt b2))) n
                    (ss_elt (sf_fun A (IN_ (S n)) f x))
                    (lift_eq Nat
                       (ss_elt (sf_fun A (IN_ (S n)) f (ss_elt b2))) n p2)
                    (eq_symmetric Nat (ss_elt (sf_fun A (IN_ (S n)) f x)) n
                       H')))))).
destruct b1 as [b1_e b1_p].
destruct b2 as [b2_e b2_p].
simpl in p1, p2.
simpl.
change 
 ((sf_fun B' (IN_ m) h
   (Build_subsetoid_crr A' _P'
    (Build_subsetoid_crr A unequal_to_x b1_e p1) b1_p)) 
  [=]
  (sf_fun B' (IN_ m) h
   (Build_subsetoid_crr A' _P'
    (Build_subsetoid_crr A unequal_to_x b2_e p2) b2_p))).
apply sf_wd.
simpl.
simpl in H3.
exact H3.
set (i := Build_Setoid_fun _ _ _i i_wd).
exists i.
split.
(* Injectivity of i *)
intros b1 b2 H3.
unfold i, _i in H3.
simpl in H3.
destruct ( nat_eq_dec (ss_elt (sf_fun A (IN_ (S n)) f (ss_elt b1))) n) as [p1 | p1].
elim (     (H2
        (sp_wd A P (ss_elt b1) x (ss_prf b1)
           (Injf (ss_elt b1) x
              (ss_elt_inj Nat (N_ (S n))
                 (sf_fun A (IN_ (S n)) f (ss_elt b1))
                 (sf_fun A (IN_ (S n)) f x)
                 (eq_transitive Nat
                    (ss_elt (sf_fun A (IN_ (S n)) f (ss_elt b1))) n
                    (ss_elt (sf_fun A (IN_ (S n)) f x))
                    (lift_eq Nat
                       (ss_elt (sf_fun A (IN_ (S n)) f (ss_elt b1))) n p1)
                    (eq_symmetric Nat (ss_elt (sf_fun A (IN_ (S n)) f x)) n
                       H'))))))).
destruct (nat_eq_dec (ss_elt (sf_fun A (IN_ (S n)) f (ss_elt b2))) n) as [p2 | p2].
elim  (H2
        (sp_wd A P (ss_elt b2) x (ss_prf b2)
           (Injf (ss_elt b2) x
              (ss_elt_inj Nat (N_ (S n))
                 (sf_fun A (IN_ (S n)) f (ss_elt b2))
                 (sf_fun A (IN_ (S n)) f x)
                 (eq_transitive Nat
                    (ss_elt (sf_fun A (IN_ (S n)) f (ss_elt b2))) n
                    (ss_elt (sf_fun A (IN_ (S n)) f x))
                    (lift_eq Nat
                       (ss_elt (sf_fun A (IN_ (S n)) f (ss_elt b2))) n p2)
                    (eq_symmetric Nat (ss_elt (sf_fun A (IN_ (S n)) f x)) n
                       H')))))).
destruct b1 as [b1_e b1_p].
destruct b2 as [b2_e b2_p].
simpl in p1, p2 |- * .
change 
 ((sf_fun B' (IN_ m) h
   (Build_subsetoid_crr A' _P'
    (Build_subsetoid_crr A unequal_to_x b1_e p1) b1_p)) 
  [=]
  (sf_fun B' (IN_ m) h
   (Build_subsetoid_crr A' _P'
    (Build_subsetoid_crr A unequal_to_x b2_e p2) b2_p))) in H3.
apply (Injh _ _ H3).
(* surjectivity *)
intro y.
destruct (Surjh y) as [b' H3].
destruct b' as [b'_e b'_p].
destruct b'_e as [b'_e_e b'_e_p].
set (b := Build_subsetoid_crr A P b'_e_e b'_p).
exists b.
unfold i, _i.
simpl.
destruct (nat_eq_dec (ss_elt (sf_fun A (IN_ (S n)) f b'_e_e)) n) as [p | p].
elim 
        (H2
           (sp_wd A P b'_e_e x b'_p
              (Injf b'_e_e x
                 (ss_elt_inj Nat (N_ (S n)) (sf_fun A (IN_ (S n)) f b'_e_e)
                    (sf_fun A (IN_ (S n)) f x)
                    (eq_transitive Nat
                       (ss_elt (sf_fun A (IN_ (S n)) f b'_e_e)) n
                       (ss_elt (sf_fun A (IN_ (S n)) f x))
                       (lift_eq Nat (ss_elt (sf_fun A (IN_ (S n)) f b'_e_e))
                          n p)
                       (eq_symmetric Nat (ss_elt (sf_fun A (IN_ (S n)) f x))
                          n H')))))).
change ((sf_fun B' (IN_ m) h
        (Build_subsetoid_crr A' _P'
           (Build_subsetoid_crr A unequal_to_x b'_e_e p) b'_p)) [=] y).
unfold P' in H3.
(* the goal is just H3, but there is a different proof object (b'_e_p vs. p);
however the setoid equality makes those proofs irrlevant. why does coq not see it? *)
(* we had this before*)
set (b1 := 
     (Build_subsetoid_crr A'
            (sp_pred A' (Build_Setoid_predicate A' _P' P'wd))
            (Build_subsetoid_crr A unequal_to_x b'_e_e b'_e_p) b'_p)).
fold b1 in H3.
set (b2 :=
     (Build_subsetoid_crr A' _P'
        (Build_subsetoid_crr A unequal_to_x b'_e_e p) b'_p)).
assert (wow : b1 [=] b2).
simpl.
apply eq_reflexive.
assert (H7 : (ss_elt (h b1)) [=] (ss_elt (h b2))).
apply ss_elt_wd.
apply sf_wd.
exact wow.
apply (ss_elt_inj Nat (N_ m)).
(* are we detouring here? *)
Set Printing Coercions.
assert (H3' : (ss_elt (sf_fun B' (IN_ m) h b1))[=](ss_elt y)).
apply ss_elt_wd with (1:=H3).
exact (* ha! *)
(eq_transitive Nat
 (ss_elt (h b2))
 (ss_elt (h b1))
 (ss_elt y)
 (eq_symmetric _ _ _ H7)
 H3'
).
Qed.
