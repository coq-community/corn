(*
Copyright © 2009 Valentin Blot

Permission is hereby granted, free of charge, to any person obtaining a copy of
this proof and associated documentation files (the "Proof"), to deal in
the Proof without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Proof, and to permit persons to whom the Proof is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Proof.

THE PROOF IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE PROOF OR THE USE OR OTHER DEALINGS IN THE PROOF.
*)

Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
Require Import finfun paths perm.

Require Import CPoly_Degree Setoid Morphisms Ring CRingClass CPoly_Euclid.
Require Import bigopsClass matrixClass.

Set Implicit Arguments.
Unset Strict Implicit.

Opaque csg_op.
Opaque cm_unit.
Opaque cr_mult.
Opaque _C_.
Opaque cr_one.
Opaque cpoly_apply_fun.
Opaque cg_inv.

Section Cayley_Hamilton.

Variable CR : CRing.
Add Ring cr_r : (RingClass.r_rt (Ring:=CRing_is_Ring CR)).
Add Ring cpoly_r : (RingClass.r_rt (Ring:=CRing_is_Ring (cpoly_cring CR))).

Section degree_le.

Global Instance degree_le_morph : Morphism (Equivalence.equiv==>Equivalence.equiv==>Equivalence.equiv) (@degree_le CR).
Proof. by move=> p q -> x y eqxy; split;[|symmetry in eqxy]; apply degree_le_wd. Qed.

Lemma bigsum_degree_le : forall n (I : finType) (F : I -> cpoly_cring CR),
  (forall i : I, degree_le n (F i)) -> degree_le n (\big[csg_op/Zero]_i (F i)).
Proof.
move=> n I F H.
have Hz : degree_le n (Zero : cpoly_cring CR) by move=> m Hlt; reflexivity.
have Hplus : forall p q : cpoly_cring CR, degree_le n p -> degree_le n q -> degree_le n (p[+]q).
  by move=> p q; apply degree_le_plus.
by apply (big_prop Hz Hplus _ (P:=predT)).
Qed.

Lemma bigprod_degree_le : forall (I : finType) (P : pred I) (F : I -> cpoly_cring CR) (deg : I -> nat),
  (forall i : I, P i -> degree_le (deg i) (F i)) -> degree_le (\big[addn/0]_(i|P i) (deg i)) (\big[cr_mult/One]_(i|P i) (F i)).
Proof.
move=> I P F deg Hdeg.
generalize (index_enum I).
elim=>[|i r Hrec].
  case; [case/lt_irrefl|reflexivity].
simpl; have{Hdeg}:=Hdeg i.
case: (P i)=> Hi; last by apply Hrec.
by apply degree_le_mult; [apply Hi|apply Hrec].
Qed.

Global Instance nth_coeff_morph : Morphism (Equivalence.equiv==>Equivalence.equiv==>Equivalence.equiv) (@nth_coeff CR).
Proof. by move=> p q -> x y eqxy; apply nth_coeff_wd. Qed.

Lemma nth_coeff_bigsum : forall n (I : finType) (F : I -> cpoly_cring CR),
  nth_coeff n (\big[csg_op/Zero]_i (F i)) [=] \big[csg_op/Zero]_i (nth_coeff n (F i)).
Proof.
move=> n I F.
have Hz : nth_coeff n Zero [=] (Zero : CR) by reflexivity.
have Hplus : forall p q : cpoly_cring CR, nth_coeff n (p[+]q) [=] nth_coeff n p [+] nth_coeff n q.
  by move=> p q; apply nth_coeff_plus.
by apply (big_morph Hplus Hz _ predT).
Qed.

Global Instance monic_morphism : Morphism (Equivalence.equiv==>Equivalence.equiv==>Equivalence.equiv) (@monic CR).
Proof. by move=> p q -> x y eqxy; split; [|symmetry in eqxy]; apply monic_wd. Qed.

Lemma monic_bigsum : forall n (I : finType) (F : I -> cpoly_cring CR) (i : I),
  monic n.+1 (F i) -> (forall j : I, j != i -> degree_le n (F j)) ->
    monic n.+1 (\big[csg_op/Zero]_i F i).
Proof.
move=> n I F i Hmon Hdeg.
split; last first.
  apply bigsum_degree_le=> j.
  case_eq (i==j).
    by move/eqP=> <-; apply Hmon.
  rewrite eq_sym.
  move/negbT=> Heq.
  apply (degree_le_mon _ _ n); first by apply le_S; apply le_n.
  by apply (Hdeg j).
rewrite nth_coeff_bigsum.
setoid_rewrite (bigD1 (P:=predT) (j:=i) (fun i0 => nth_coeff n.+1 (F i0))); last by done.
transitivity ((One : CR)[+]Zero); last by ring.
apply csbf_wd; first by apply Hmon.
apply big1=> j'.
case/andP=> Pj' neqj'.
by apply Hdeg.
Qed.

Lemma monic_bigprod : forall (I : finType) (F : I -> cpoly_cring CR) (deg : I -> nat),
  (forall i : I, monic (deg i) (F i)) -> monic (\big[addn/0]_i deg i) (\big[cr_mult/One]_i F i).
Proof.
move=> I F deg Hdeg.
elim:(index_enum I)=>[|i r Hrec].
  by apply monic_c_one.
simpl.
by apply monic_mult.
Qed.

Global Instance cpoly_apply_morph : Morphism (Equivalence.equiv==>Equivalence.equiv==>Equivalence.equiv) (cpoly_apply CR).
Proof. by move=> a b eqab x y eqxy; apply cpoly_apply_wd. Qed.

Lemma apply_bigsum : forall (I : finType) (F : I -> cpoly_cring CR) (x : CR),
    (\big[csg_op/Zero]_i F i) ! x [=] \big[csg_op/Zero]_i (F i) ! x.
Proof.
move=> I F x.
elim:(index_enum I)=>[|j r Hrec] /=.
  by apply poly_eq_zero; reflexivity.
rewrite (plus_apply _ (F j)).
by rewrite Hrec; reflexivity.
Qed.

Lemma apply_big_prod : forall (I : finType) (F : I -> cpoly_cring CR) (x : CR),
    (\big[cr_mult/One]_i F i) ! x [=] \big[cr_mult/One]_i (F i) ! x.
Proof.
move=> I F x.
elim:(index_enum I)=>[|j r Hrec] /=.
  by apply one_apply.
rewrite (mult_apply _ (F j)).
by rewrite Hrec; reflexivity.
Qed.

End degree_le.

Open Scope matrix_scope.

Section char_poly.

Variable n : nat.
Notation Local "R [ 'X' ]" := (cpoly_cring R)
  (at level 0, format "R [ 'X' ]").
Notation Local "'M' ( R )" := (matrix R n n)
  (at level 0, format "'M' ( R )").

Variable A : M(CR).
Definition matrixC : M(CR[X]) := \matrix_(i,j < n) _C_ (A i j).
Definition char_poly : CR[X] := \det (_X_%:M -m matrixC).

Lemma char_poly_monic : monic n char_poly.
Proof.
rewrite /char_poly /determinant /matrixC.
move: n A.
clear n A.
case=>[|n]=>A.
  have -> : index_enum (perm_for_finType (ordinal_finType 0)) = [::perm_one (ordinal_finType 0)]; last first.
    rewrite /= odd_perm1 /=.
    apply (monic_wd _ One); last by apply monic_c_one.
    rewrite /index_enum -enumT.
    have <- : [::] = enum (ordinal_finType 0); last first.
      by change ((One : CR[X])[=]One[*]One[+]Zero); ring.
    rewrite <- enum0.
    by apply eq_enum; case.
  rewrite /index_enum -enumT.
  have := (enum1 (perm_one (ordinal_finType 0)))=> /= <-.
  apply (@eq_enum _ 'S_0)=> s /=.
  symmetry.
  apply/eqP.
  apply/permP=> x.
  by case:x.
apply (monic_bigsum (i:=perm_one (ordinal_finType n.+1)) (F:=fun s => _)).
  rewrite odd_perm1 /=.
  change (n.+1) with (0 + n.+1).
  apply monic_mult; first by apply monic_c_one.
  have : n.+1 = \big[addn/0]_(i<n.+1) 1.
    symmetry.
    setoid_rewrite big_const_ord.
    clear A; revert n.
    elim; first by done.
    by move=> n /= ->.
  move => Heq.
  rewrite -> Heq at 1.
  apply monic_bigprod=> i.
  rewrite /scalar_mx /addmx /oppmx perm1 eq_refl.
  split; first by rewrite -> nth_coeff_plus; reflexivity.
  apply degree_le_plus; first by apply degree_le_x_.
  change (degree_le 1 [--](_C_(A i i))).
  apply degree_le_inv.
  apply (degree_le_mon _ _ 0); first by apply le_S; apply le_n.
  by apply degree_le_c_.
move=> s neq.
change n with (0 + n).
apply degree_le_mult.
  change (One : CR[X]) with (_C_ (One : CR)).
  case: (odd_perm s)=> /=; last by apply degree_le_c_.
    change (degree_le 0 ([--](_C_ One)[*](_C_ (One : CR)))).
    change 0 with (0 + 0).
    by apply degree_le_mult; [apply degree_le_inv|]; apply degree_le_c_.
have: existsb i : ordinal_finType n.+1, s i != i.
  apply/forallP=> Heq.
  case: (negP neq)=> {neq}.
  apply/eqP.
  apply/permP=> x.
  rewrite perm1.
  apply/eqP.
  by apply Heq.
case/existsP=> j Hj.
setoid_rewrite (bigD1 (j:=j)); last by done.
change n with (0 + n).
apply degree_le_mult=> [|/=].
  rewrite /scalar_mx /addmx /oppmx eq_sym (negbTE Hj).
  setoid_rewrite cm_lft_unit.
  apply degree_le_inv.
  by apply degree_le_c_.
change (0 + n) with n.
have Heq : n = \big[addn/0]_(i|i!=j) 1.
  setoid_rewrite big_const_seq; clear.
  have -> : count (predC (pred1 j)) (index_enum (ordinal_finType n.+1)) = n; last first.
    move=> {j}; revert n.
    by elim; [|move=> n /= <-].
  have := (count_predC (pred1 j) (index_enum (ordinal_finType n.+1))).
  rewrite enumP /index_enum -enumT size_enum_ord /= add1n.
  by move/eqP; rewrite eqSS; move/eqP.
rewrite {1}Heq=> {Heq}.
apply bigprod_degree_le=> i Hneq.
rewrite /scalar_mx /addmx /oppmx.
apply degree_le_plus.
  case: (i == s i); first by apply degree_le_x_.
  apply (degree_le_mon _ _ 0); first by apply le_S; apply le_n.
  by move=> n' _; apply nth_coeff_zero.
change (degree_le 1 ([--](_C_(A i (s i))))).
apply degree_le_inv.
apply (degree_le_mon _ _ 0); first by apply le_S; apply le_n.
by apply degree_le_c_.
Qed.

Lemma char_poly_apply : forall a : CR, char_poly ! a === \det (a%:M -m A).
Proof.
rewrite /char_poly /determinant=> a.
rewrite apply_bigsum.
apply eq_bigr=> s _.
rewrite -> mult_apply.
apply csbf_wd.
  case: (odd_perm s)=> /=; last by apply one_apply.
  rewrite /Equivalence.equiv.
  rewrite (mult_apply CR).
  apply csbf_wd; last by apply one_apply.
  rewrite -> inv_apply.
  rewrite -> one_apply.
  by reflexivity.
rewrite apply_big_prod.
apply eq_bigr=> i _.
rewrite /scalar_mx /addmx /oppmx /matrixC.
rewrite -> plus_apply.
rewrite -> inv_apply.
rewrite ->  _c_apply.
apply csbf_wd; last by reflexivity.
case: (i == s i); first by apply _x_apply.
by apply poly_eq_zero; reflexivity.
Qed.

Lemma Cayley_Hamilton : forall (a : CR) (X : matrix CR n 1),
  A *m X === a%:M *m X -> (char_poly ! a)%:M *m X === '0m.
Proof.
move=> a X Heq.
rewrite char_poly_apply.
rewrite <- mulmx_adjl.
rewrite <- (mulmx0 (\adj (a%:M -m A))).
rewrite <- mulmxA.
apply mulmx_morph; first by reflexivity.
rewrite -> mulmx_addl.
Existing Instance addmx_morph.
rewrite <- Heq=> i j {Heq}.
rewrite /addmx /oppmx /mulmx /null_mx.
have Heq : forall k, xpredT k -> [--](A i k)[*]X k j [=] [--](A i k[*]X k j) by move=> k _; ring.
setoid_rewrite (eq_bigr _ Heq)=> {Heq}.
setoid_rewrite <- (big_morph (op1:=csg_op) (idx1:=Zero) (phi:=fun x => [--]x))=> /=[|x y| |]; [by ring|by ring|by ring|].
move=> x x' eqx y y' eqy.
by rewrite eqx eqy; reflexivity.
Qed.

End char_poly.

End Cayley_Hamilton.
