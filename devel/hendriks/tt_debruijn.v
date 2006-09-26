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
fRequire Export Bool.
Require Export ListType.

Infix "::" := cons (at level 60, right associativity) : type_scope.

Implicit Types i j n m : nat.

Fixpoint nat_eqb n m {struct n} : bool :=
  match n, m with
  | O  , O   => true
  | S n, S m => nat_eqb n m
  | _  , _   => false
  end.
  
Inductive type : Type :=
  type_atm : type
| type_arr : type -> type -> type.

Implicit Types A B C : type.

Fixpoint type_eqb A B {struct A} : bool :=
  match A, B with
    type_atm, type_atm => true
  | type_arr A1 A2, type_arr B1 B2 => 
    andb (type_eqb A1 B1) (type_eqb A2 B2)
  | _, _ => false
  end.

Lemma andb_elim :
  forall b1 b2 : bool,
  andb b1 b2 = true ->
  b1 = true /\ b2 = true.
Proof.
destruct b1; [ destruct b2; [ split; reflexivity | discriminate 1 ]
 | discriminate 1 ].
Qed.

Lemma type_eqb_refl :
  forall A,
  type_eqb A A = true.
Proof.
induction A as [ | A1 IH1 A2 IH2 ]; simpl.
reflexivity.
rewrite IH1; rewrite IH2; reflexivity.
Qed.

Lemma type_eqb_to_eq :
  forall A B,
  type_eqb A B = true ->
  A = B.
induction A as [ | A1 IH1 A2 IH2 ]; destruct B as [ | B1 B2 ]; simpl.
reflexivity.
discriminate 1.
discriminate 1.
intro H.
elim (andb_elim _ _ H); intros H1 H2.
rewrite IH1 with (1:=H1).
rewrite IH2 with (1:=H2).
reflexivity.
Qed.

Inductive term : Type :=
  term_var : nat -> term
| term_lam : type -> term -> term
| term_app : term -> term -> term.

Implicit Types s t u : term.

Fixpoint term_eqb t u {struct t} : bool :=
  match t, u with
  | term_var i, term_var j => nat_eqb i j
  | term_lam A t, term_lam B u => andb (type_eqb A B) (term_eqb t u)
  | term_app t1 t2, term_app u1 u2 => 
      andb (term_eqb t1 u1) (term_eqb t2 u2)
  | _, _ => false
  end.

Definition cxt := (list type).

Implicit Types G : cxt.

Inductive der : cxt -> term -> type -> Type :=
  der_hyp_O : 
    forall A G, 
    der (A :: G) (term_var 0) A
| der_hyp_S : 
    forall A B G i, 
    der G (term_var i) A ->
    der (B :: G) (term_var (S i)) A
| der_lam :
    forall A B t G,
    der (A :: G) t B ->
    der G (term_lam A t) (type_arr A B)
| der_app :
    forall G t u A B,
    der G t (type_arr A B) ->
    der G u A ->
    der G (term_app t u) B.

Inductive option (A : Type) : Type :=
  some : A -> option A
| none : option A.

Implicit Arguments none [A].
Implicit Arguments some [A].

Fixpoint opt_nth (A : Type) n (l : list A) {struct n} : option A :=
  match l with 
    nil     => none
  | a :: l' => 
    match n with
      O    => some a
    | S n' => opt_nth A n' l'
    end
  end.

Lemma der_hyp_nth :
  forall i G A,
  opt_nth type i G = some A
  -> der G (term_var i) A.
Proof.
induction i as [ | i IHi ]; intros G A;
  (destruct G; simpl; intro H; [ discriminate H | idtac ] ).
injection H; intro H0; rewrite H0.
clear t H0 H.
apply der_hyp_O.
apply der_hyp_S.
apply IHi with (1:=H).
Qed.

Fixpoint check G t {struct t} : option type :=
  match t with
    term_var i => opt_nth type i G
  | term_lam A t => 
    match check (A :: G) t with
      none   => none
    | some B => some (type_arr A B)
    end
  | term_app t u =>
    match check G t, check G u with
    | some (type_arr A B), some A' =>
      if   type_eqb A A'
      then some B
      else none
    | _, _ => none
    end
  end.

Ltac expl_case t :=
  cut (t = t); 
  [ pattern t at -1; case t; intros until 1 
  | reflexivity ].

Ltac split_check G t :=
  let A := fresh "A" in
  let H := fresh "H" in
  let o := constr:(check G t) in
  ( cut (o = o); 
    [ pattern o at -1; case o; [ intros A H | intro H ] 
      | reflexivity ] ).

Ltac load x := generalize x; clear x.

Ltac some_some :=
  let H := fresh in
  ( intro H; injection H; clear H; intro H; 
    ( rewrite -> H || rewrite <- H ); clear H ).

Lemma check2der :
  forall G t C,
  check G t = some C ->
  der G t C.
Proof.
intros G t.
load G.
induction t as [ i | B t IHt | t IHt u IHu ] ; simpl; intros G C.
intro H.
apply der_hyp_nth with (1:=H).
split_check (B :: G) t; [ idtac | discriminate 1 ].
some_some.
apply der_lam.
apply IHt with (1:=H).
split_check G t; [ idtac | discriminate 1 ].
destruct A.
discriminate 1.
split_check G u; [ idtac | discriminate 1 ].
expl_case (type_eqb A1 A); [ idtac | discriminate 1 ].
rewrite (type_eqb_to_eq _ _ H1) in H.
some_some.
apply der_app with (A:=A).
apply IHt with (1:=H).
apply IHu with (1:=H0).
Qed.

Lemma der2check :
  forall G t A,
  der G t A ->
  check G t = some A.
Proof.
induction 1 as 
  [ A G | A B G i d IH | A B t G d IH 
    | G t u A B d1 IH1 d2 IH2 ]; simpl.
reflexivity.
exact IH.
load IH.
split_check (A :: G) t; [ some_some | discriminate 1 ].
reflexivity.
load IH1.
split_check G t; [ some_some | discriminate 1 ].
load IH2.
split_check G u; [ some_some | discriminate 1 ].
rewrite type_eqb_refl.
reflexivity.
Qed.

Require Export CSetoidFun.

Infix "[*]"  := ProdCSetoid (at level 80, right associativity).
Infix "[->]" := FS_as_CSetoid (at level 75, right associativity).

Inductive unitT : Type :=
  ttT : unitT.

Definition unitT_eq : (Relation unitT) := fun _ _ => True.
Definition unitT_ap : (Crelation unitT) := fun _ _ => False.

Lemma unitT_ap_irrefl :
  irreflexive unitT_ap.
intros x H; exact H.
Qed.

Lemma unitT_ap_symm :
  Csymmetric unitT_ap.
intros x y H.
exact H.
Qed.

Lemma unitT_ap_cotrans :
  cotransitive unitT_ap.
intros x y H z.
left; exact H.
Qed.

Lemma unitT_ap_tight :
  tight_apart unitT_eq unitT_ap.
intros x y.
split; intro H0.
constructor.
intro H1.
exact H1.
Qed.

Definition unitT_is_CSetoid :=
  Build_is_CSetoid unitT unitT_eq unitT_ap unitT_ap_irrefl unitT_ap_symm unitT_ap_cotrans unitT_ap_tight.

Definition unitT_CSetoid :=
  Build_CSetoid unitT unitT_eq unitT_ap unitT_is_CSetoid.

Notation "[1]" := unitT_CSetoid.

Section interpretation.

Variable S : CSetoid.

Fixpoint interp_type A : CSetoid :=
  match A with
    type_atm => S
  | type_arr A1 A2 => (interp_type A1) [->] (interp_type A2)
  end.

(*
Fixpoint interp_cxt G : Type :=
  match G with
    nil    => unitT
  | A :: G => prodT (interp_type A) (interp_cxt G)
  end.

*)


(*
Definition assignment :=
  (forall n, interp_type (opt_nth n G)).
*)

(*
Definition interp_term :
  forall G t A,
  der G t A ->
  interp_cxt G ->
  interp_type A.
induction 1 as [ A G | A B G i d IH | A B t G d IH  | ].
intros [ a g ]; exact a.
intros [ b g ]; exact (IH g).
intro g.
simpl.
pose (f := (fun a : (interp_type A) => (IH (pairT a g)))).
apply Build_CSetoid_fun with f.
unfold fun_strext.
intros x y H.
unfold f in H.
simpl in H.

*)


Fixpoint interp_cxt G : CSetoid :=
  match G with
    nil    => [1]
  | A :: G => (interp_type A) [*] (interp_cxt G)
  end.

Definition interp_term :
  forall G t A,
  der G t A ->
  interp_cxt G [->]
  interp_type A.

induction 1 as [ A G | A B G i d IH | A B t G d IH  | ].
(* der_hyp_O *)
intros [ a g ]; exact a.
(* der_hyp_S *)
intros [ b g ]; exact (IH g).
(* der_lam *)
intro g.
simpl.
pose (f := (fun a : (interp_type A) => (IH (pairT a g)))).
apply Build_CSetoid_fun with f.
unfold fun_strext.
intros x y H.
unfold f in H.
simpl in H.

Section aa.

Print Coercions.


Set Printing Coercions.

(*
Coercion FS_as_CSetoid 
*)

Definition id : FS_as_CSetoid S S :=
  Build_CSetoid_fun S S (fun x => x) (fun x y H => H).

Print id.


Variable s : S.

Eval compute in (cs_crr (FS_as_CSetoid S S)).


Definition ids := ((id : (CSetoid_fun S S)) s).

Print ids.


