Require Export CLogic.

Section subsetoids.

Set Implicit Arguments.

Record subsetoid : Type :=
 {ss_crr : Type; 
  ss_dom :  ss_crr -> CProp;
  ss_rel :  Crelation ss_crr;
  ss_eqv :  Cequivalence ss_crr ss_rel
 }.

Record subset (A:subsetoid) : Type :=
 {elt :>    ss_crr A;
  elt_in : ss_dom A elt}.


Definition subsetCoercion (A:subsetoid): Type := 
   subset A.

Coercion subsetCoercion : subsetoid >-> Sortclass.


(*Definition inclusion (s1 s2 : subsetoid) :=
  forall c : ss_crr, ss_dom ss_crr s1 c -> ss_dom ss_crr s2 c.

Lemma inclusion_refl : forall T A, inclusion T A A.
Proof.
intros T A t H.
exact H.
Qed.

*) End subsetoids.


(* So we need a pair, but only compare the second element *)

Definition equal (s:subsetoid)(a1 a2: ss_crr s ):= ss_rel s a1 a2.

Notation "x '[=]' y" := (equal _ x y) (at level 70, no associativity).

Section Stuff.

Definition type2subsetoid (T:Type): subsetoid.
intro T.
apply (Build_subsetoid (fun _ => True) (ss_rel :=(eq (A:=T)))).
split; red.
reflexivity.
intros x y H1; symmetry; assumption.
intros x y z H1 H2; transitivity y; assumption.
Defined.

Definition fun_wd (A B: subsetoid)(f : A -> B) := 
  forall x y : A, x[=]y -> (f x)[=](f y).

Record ss_function (A B: subsetoid) : Type :=
  {ss_fun :> A -> B;
   ss_wd  :  fun_wd ss_fun
  }.
(*
Definition algo_part (A : subsetoid T1) (B: subsetoid T2) (f:ss_function A B) : 
   (A -> T2 ) := fun a => elt (f a).
*)
(* include is just an example of a set operation defined on subsetoids *)


(*Definition is_in (A B : subsetoid T1) :=  fun a:A => ss_dom B (elt a).*)


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

Definition compose_ss_function 
  (A B C: subsetoid)
  (f : ss_function A B) (g : ss_function B C) : ss_function A C.
intros A B C f g.
set (_h := fun a : A => g (f (a))).
assert (h_wd : fun_wd _h).
intros a1 a2 H.
unfold _h.
apply ss_wd.
apply ss_wd.
exact H.
set (h := Build_ss_function h_wd).
exact h.
Defined.

Notation "g '[o]' f" := (compose_ss_function f g) (at level 75, right associativity).

Section eq_equivalence.

Variable A:subsetoid.
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

Variable A B : subsetoid.

Definition left_inverse (f : ss_function A B) (g : ss_function B A) :=
  forall x : A, g (f x) [=] x.

Definition right_inverse  (f: ss_function A B) (g: ss_function B A) :=
  forall y : B, f (g y) [=] y.

Definition inverse (f: ss_function A B) (g: ss_function B A) :=
  (left_inverse f g) and (right_inverse f g).

Definition isomorphic :=
  {f : ss_function A B | {g : ss_function B A | inverse f g}}.

End isomorphisms.

Infix "[~]" := isomorphic (at level 70).

Section isomorphism_properties.

Variable A B C:subsetoid.

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

Definition Nat : subsetoid := 
  type2subsetoid nat.

Definition subsetoid_pred (A:subsetoid) := ss_crr A -> CProp.

Definition restrict (A:subsetoid)(P:subsetoid_pred A) : subsetoid :=
   Build_subsetoid (fun x: ss_crr A => ss_dom A x and P x) (ss_eqv A).

Coercion restrict: subsetoid_pred >-> subsetoid.


Notation "A [|] P " := 
  (restrict (A:=A) P) (at level 60, left associativity).

Lemma curry_restrict:
   forall (A:subsetoid) (P1 P2: subsetoid_pred A),
   (P1 [|] P2) [~] ((fun x => (P1 x and P2 x)):subsetoid_pred A). 
(* This is a bit funny *)
Admitted.


Definition dep_restrict (A:subsetoid)(P:A -> CProp) : subsetoid :=
   Build_subsetoid (fun x: ss_crr A => {p:ss_dom A x | P (Build_subset A x p)}) (ss_eqv A).


Notation "A [||] P " := 
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


Definition Finite (A:subsetoid) : CProp :=
  {k : nat | A[~](NS_ k)}.

Definition pred_ext_eq (A:subsetoid) (P Q : subsetoid_pred A) :=
  forall x : A, (P x ->  Q x) and (Q x -> P x).

Notation "P '=e' Q" := (pred_ext_eq P Q) (at level 80).

Definition empty (A:subsetoid) :  subsetoid_pred A:=
  fun a => False.

Definition decidable p := p  or Not p.

Definition decidable_pred A (P : subsetoid_pred A ) := 
  forall x, decidable (P x).

Implicit Arguments decidable_pred [A].

Definition add (A:subsetoid ) (P : subsetoid_pred A) (a : ss_crr A) : subsetoid_pred A:=
  fun x => P x or (x [=] a).


Let unequal_to (A: subsetoid) (a : ss_crr A) :=
  fun x => Not (x [=] a).


Definition coarser (T : Type) (R1 R2 : Crelation T) :=
  forall x y, R1 x y -> R2 x y.

Lemma coarser_refl : forall T (R:Crelation T), coarser R R.
Proof.
intros T R x y H.
exact H.
Qed.

(*Definition coarser_subsetoid 
  (A B : subsetoid) :=
  coarser (ss_rel A) (ss_rel B).

Lemma coarser_subsetoid_refl :
  forall T A,
  coarser_subsetoid T A A.
Proof.
intros T A.
red.
apply coarser_refl.
Qed.
*)

Lemma Finite_ind :
  forall A : subsetoid,
  Finite A ->
  forall M : subsetoid_pred A -> CProp, 
  (forall P Q, M P -> P =e Q -> M Q) ->
  M (empty A) ->
  ( forall (P : subsetoid_pred A), 
    decidable_pred P -> 
    M P -> forall a, M (add P a)
  ) ->
  forall P : subsetoid_pred A, 
  decidable_pred P ->
  M P.
Proof.
intros A [ k H ].
generalize A H; clear H A.
induction k as [ | k IH ]; intros A H M Mext Mbase Mstep P Pdec.
(* 0 *)
destruct H as [ f _ ].
assert (H : (empty A) =e P).
red.
intro x; split; intro H.
destruct H.
destruct (lt_n_O (elt (f x)) (CAnd_proj2 _ _ (elt_in (f x)))).
exact (Mext (empty A) P Mbase H).
(* S k *)
(* here dimitri proves that equality on A is decidable.
first prove that equality on (NS_ (S k)) is decidable...
(
the new approach should make this easier, 
since the equality is on the carrier by definition
)
and then use the lemma that isomorphisms preseve decidability
*)
(*
assert 
  (N_Sn_eq_dec := 
    subsetoid_preserves_decidable_eq IN (fun n m => sumbool2or _ _ (nat_eq_dec n m)) (N_ (S k))).
set (H' := isomorphic_symmetric _ _ H).
assert 
  (A_eq_dec := 
    isomorphic_preserves_decidable_eq  _ _ H' N_Sn_eq_dec).
clear H'.
*)
destruct H as [ f [ f' H ] ].
(*
assert (H' := inverse_symmetric H).
set (k' := k_in_IN_Sk k).
*)
(* dimitri did:
set (Uk := unequal_to Nat k). 
set (Uk' := Uk[||]N_ (S k)).
*)
(* now we can do better and use k directly *)
set (Uk' := unequal_to (NS_ (S k)) k).

(*
set (U := map_pred _ _ f Uk').
*)

set (U

assert (H0 : IN_ (S k)[|]Uk' [~] IN_ k).
unfold Uk'.
unfold IN_.
apply isomorphic_transitive with (IN[|](N_ (S k)[/\]Uk)).
apply nn.
apply pred_ext_eq_implies_isomorphic_subsetoids.
intro n.
unfold N_; simpl.
split.
intros [ H0 H1 ].
assert (H2 : n <= k).
auto with arith.
destruct (le_lt_or_eq n k H2) as [ H3 | H3 ].
exact H3.
elim (H1 H3).
intro H0.
split.
apply lt_S with (1:=H0).
intro H1.
apply (lt_irrefl k).
rewrite H1 in H0.
exact H0.
assert (H1 :  A[|]U [~] IN_ k).
apply isomorphic_transitive with (2:=H0).
apply isomorphic_symmetric.
exact (subsetoid_preserves_isomorphic _ _ _ _ H' Uk').
clear H0; rename H1 into H0.
assert (Udec : decidable_pred U).
unfold U.
apply map_pred_preserves_decidability.
unfold Uk'.
unfold IN_.
apply restrict_predicate_preserves_decidability.
unfold Uk, unequal_to.
apply complement_preserves_decidability.
intro n.
exact (sumbool2or _ _ (nat_eq_dec n k)).
set (F := fun Q => (my_if A U Udec Q)).
set (M' := fun Q => M (F Q)).
assert (M'ext : forall P Q, M' P -> P =e Q -> M' Q).
intros P1 P2 H1 H2.
unfold M' in H1 |- * .
apply Mext with (1:=H1).
intro a.
unfold M'.
simpl.
destruct (Udec a) as [ p | p ].
apply H2.
split; id.
assert (M'base : M' (empty (A[|]U))).
unfold M'.
simpl.
apply Mext with (1:=Mbase).
intro a.
simpl.
destruct (Udec a); split; id.
assert 
  (M'step : 
    forall P : Setoid_predicate (A[|]U),
    decidable_pred P ->
    M' P -> 
    forall a : (A[|]U), M' (add (A[|]U) P a)
  ).
intros Q decQ H1 x.
change (M (my_if A U Udec (add (A[|]U) Q x))).
assert 
  (H2 :
    (add A (my_if A U Udec Q) (ss_elt x))
    =e (my_if A U Udec (add (A[|]U) Q x))
  ).
intro a.
simpl.
destruct (Udec a) as [ p | p ].
set (a_p := mk_ss_elt U a p).
change 
  (((Q a_p) or a [=] (ss_elt x))
  IFF
  ((Q a_p) or a_p [=] x)).
destruct x as [ x_e x_p ]; simpl; split; id.
split; intro H2.
destruct H2 as [ H2 | H2 ].
destruct H2.
apply p.
intro q.
destruct x as [ x_e x_p ].
simpl in H2.
apply x_p.
simpl.
transitivity (ss_elt (f a)).
apply (ss_elt_wd _ _ (f x_e) (f a)).
apply sf_wd.
symm.
exact q.
left.
exact H2.
apply Mext with (2:=H2).
apply Mstep with (2:=H1).
intro a.
simpl.
destruct (Udec a) as [ p | p ].
set (a_p := mk_ss_elt U a p).
change (Cdecidable (Q a_p)).
exact (decQ a_p).
right; id.
set (P' := P[||]U).
assert (P'dec : decidable_pred P').
unfold P'.
apply restrict_predicate_preserves_decidability with (1:=Pdec).
assert (Fdec := my_if_dec A U Udec P' P'dec).
rename H0 into H1.
assert (H0 := IH (A[|]U) H1 M' M'ext M'base M'step P' P'dec).
unfold M' in H0.
clear IH N_Sn_eq_dec H' H1 M' M'ext M'base M'step.
destruct (Pdec (f' k')) as [ H1 | H1 ].
(* P (f' k') *)
assert (H2 := Mstep (F P') Fdec H0 (f' k')).
unfold add in H2.
apply Mext with (1:=H2).
intro a.
simpl.
destruct (Udec a) as [ H3 | H3 ]; split; intro H4.
destruct H4 as [ H4 | H4 ].
exact H4.
destruct H3.
simpl.
assert (H5 := (CAnd_proj2 _ _ (inv_swap_eq _ _ f f' H a k') H4)).
destruct (f a); exact H5.
left; exact H4.
destruct H4 as [ H4 | H4 ].
destruct H4.
apply sp_wd with (1:=H1).
symm.
right.
apply dec_raa.
apply A_eq_dec.
intro H5.
apply H3.
intro H6.
apply H5.
simpl_all.
apply (CAnd_proj1 _ _ (inv_swap_eq _ _ f f' H a k')).
destruct (f a); exact H6.
(* ~ P (f' k') *)
apply Mext with (1:=H0).
intro a.
simpl.
destruct (Udec a) as [ H2 | H2 ]; split.
id.
id.
destruct 1.
intro H3.
apply H2.
intro H4.
apply H1.
apply sp_wd with (1:=H3).
apply (CAnd_proj1 _ _ (inv_swap_eq _ _ f f' H a k')).
destruct (f a); exact H4.
Qed.
