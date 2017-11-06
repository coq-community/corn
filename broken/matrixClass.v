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
Require Import finfun bigops ssralg groups perm zmodp morphisms.

Require Import Ring RingClass.
Require Import bigopsClass.

Require Import Setoid Morphisms.
Notation " x === y " := (Equivalence.equiv x y) (at level 70, no associativity).

Open Scope signature_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Reserved Notation "''M_' n"       (at level 8, n at level 2, format "''M_' n").
Reserved Notation "''M_' ( n )"   (at level 8, only parsing).
Reserved Notation "''M_' ( m , n )" (at level 8, format "''M_' ( m ,  n )").

Reserved Notation "\matrix_ ( i , j ) E"
  (at level 36, E at level 36, i, j at level 50,
   format "\matrix_ ( i ,  j )  E").
Reserved Notation "\matrix_ ( i < m , j < n ) E"
  (at level 36, E at level 36, i, m, j, n at level 50,
   format "\matrix_ ( i  <  m ,  j  <  n )  E").
Reserved Notation "\matrix_ ( i , j < n ) E"
  (at level 36, E at level 36, i, j, n at level 50,
   format "\matrix_ ( i ,  j  <  n )  E").

Reserved Notation "x %:M"   (at level 8, format "x %:M").
Reserved Notation "-m A"    (at level 35, right associativity).
Reserved Notation "A +m B"  (at level 50, left associativity).
Reserved Notation "A -m B"  (at level 50, left associativity).
Reserved Notation "x *m: A" (at level 40, left associativity).
Reserved Notation "A *m B"  (at level 40, left associativity).
Reserved Notation "A ^T"    (at level 8).
Reserved Notation "\tr A"   (at level 10, A at level 8, format "\tr  A").
Reserved Notation "\det A"  (at level 10, A at level 8, format "\det  A").
Reserved Notation "\adj A"  (at level 10, A at level 8, format "\adj  A").

Delimit Scope matrix_scope with M.

Local Open Scope matrix_scope.

Definition setoid_cancel {A : Type} {B : Type} `{Equivalence A aeq} (f : A -> B) g :=
    forall x, g (f x) === x.

Section MatrixDef.

Variable R : Type.
Variables m n : nat.

Definition matrix : Type :=  'I_m -> 'I_n -> R.

End MatrixDef.

Notation "''M_' n"  := (matrix _ n n) : type_scope.
Notation "''M_' ( n )" := 'M_n (only parsing) : type_scope.
Notation "''M_' ( m , n )" := (matrix _ m n) : type_scope.

Notation "\matrix_ ( i < m , j < n ) E" :=
  (fun (i : 'I_m) (j : 'I_n) => E) (only parsing).

Notation "\matrix_ ( i , j < n ) E" :=
  (\matrix_(i < n, j < n) E) (only parsing).

Notation "\matrix_ ( i , j ) E" := (\matrix_(i < _, j < _) E).

Section Slicing.

Context `{r_st : Equivalence R req}.

Definition mx_row m n i0 (A : 'M_(m, n)) :=
  \matrix_(i < 1, j < n) (A i0 j : R).
Global Instance mx_row_morph m n i0 : Proper (Equivalence.equiv==>Equivalence.equiv) (@mx_row m n i0).
Proof. by move=> m n i0 A B eqAB i; apply eqAB. Qed.
Definition mx_col m n j0 (A : 'M_(m, n)) :=
  \matrix_(i < m, j < 1) (A i j0 : R).
Global Instance mx_col_morph m n i0 : Proper (Equivalence.equiv==>Equivalence.equiv) (@mx_col m n i0).
Proof. by move=> m n i0 A B eqAB i j; apply eqAB. Qed.
Definition mx_row' m n i0 (A : 'M_(m, n)) :=
  \matrix_(i, j) (A (lift i0 i) j : R).
Global Instance mx_row'_morph m n i0 : Proper (Equivalence.equiv==>Equivalence.equiv) (@mx_row' m n i0).
Proof. by move=> m n i0 A B eqAB i; apply eqAB. Qed.
Definition mx_col' m n j0 (A : 'M_(m, n)) :=
  \matrix_(i, j) (A i (lift j0 j) : R).
Global Instance mx_col'_morph m n i0 : Proper (Equivalence.equiv==>Equivalence.equiv) (@mx_col' m n i0).
Proof. by move=> m n i0 A B eqAB i j; apply eqAB. Qed.

Definition rswap m n i1 i2 (A : 'M_(m, n)) :=
  \matrix_(i, j) (A (tperm i1 i2 i) j : R).
Global Instance rswap_morph m n i1 i2 : Proper (Equivalence.equiv==>Equivalence.equiv) (@rswap m n i1 i2).
Proof. by move=> m n i1 i2 A B eqAB i; apply eqAB. Qed.

Definition cswap m n i1 i2 (A : 'M_(m, n)) :=
  \matrix_(i, j) (A i (tperm i1 i2 j) : R).
Global Instance cswap_morph m n i1 i2 : Proper (Equivalence.equiv==>Equivalence.equiv) (@cswap m n i1 i2).
Proof. by move=> m n i1 i2 A B eqAB i j; apply eqAB. Qed.
    
Definition trmx m n (A : 'M_(m, n)) := \matrix_(i, j) (A j i : R).
Global Instance trmx_morph m n : Proper (Equivalence.equiv==>Equivalence.equiv) (@trmx m n).
Proof. by move=> m n A B eqAB i j; apply eqAB. Qed.

Lemma trmxK : forall m n, setoid_cancel (@trmx m n) (@trmx n m).
Proof. by move=> m n A i j; rewrite/trmx; reflexivity. Qed.

Lemma trmx_inj : forall m n (A B : 'M_(m, n)), trmx A === trmx B -> A === B.
Proof. by rewrite/trmx=> m n A B eqtr i j; apply eqtr. Qed.

Notation "A ^T" := (trmx A).

Lemma trmx_row : forall m n i0 (A : 'M_(m, n)),
  (mx_row i0 A)^T === mx_col i0 A^T.
Proof. by rewrite/trmx/mx_row/mx_col=> m n i0 A i j; reflexivity. Qed.

Lemma trmx_row' : forall m n i0 (A : 'M_(m, n)),
  (mx_row' i0 A)^T === mx_col' i0 A^T.
Proof. by rewrite/trmx/mx_row/mx_col=> m n i0 A i j; reflexivity. Qed.

Lemma trmx_col : forall m n j0 (A : 'M_(m, n)),
  (mx_col j0 A)^T === mx_row j0 A^T.
Proof. by rewrite/trmx/mx_row/mx_col=> m n i0 A i j; reflexivity. Qed.

Lemma trmx_col' : forall m n j0 (A : 'M_(m, n)),
  (mx_col' j0 A)^T === mx_row' j0 A^T.
Proof. by rewrite/trmx/mx_row/mx_col=> m n i0 A i j; reflexivity. Qed.

Lemma trmx_cswap : forall m n (A : 'M_(m, n)) i1 i2, 
  (cswap i1 i2 A)^T === rswap i1 i2 A^T.
Proof. by rewrite/trmx/rswap/cswap=> m n A i1 i2 i j; case tpermP; reflexivity. Qed.

Lemma trmx_rswap : forall m n (A : 'M_(m, n)) i1 i2, 
  (rswap i1 i2 A)^T === cswap i1 i2 A^T. 
Proof. by rewrite/trmx/rswap/cswap=> m n A i1 i2 i j; case tpermP; reflexivity. Qed.

Lemma mx_row_id : forall n (A : 'M_(1, n)), mx_row ord0 A === A.
Proof. by move=> n A i j; (have -> : ord0 = i by rewrite (ord1 i); apply ord_inj => //); reflexivity. Qed.

Lemma mx_row_eq : forall m1 m2 n i1 i2 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)),
  mx_row i1 A1 === mx_row i2 A2 -> A1 i1 === A2 i2.
Proof.
rewrite/mx_row => m1 m2 n i1 i2 A1 A2 eqA1A2 j.
by apply eqA1A2; apply (@Ordinal 1 0).
Qed.

Lemma mx_row'_eq : forall m n i0 (A B : 'M_(m, n)),
  mx_row' i0 A === mx_row' i0 B -> {in predC1 i0, forall i, A i === B i}.
Proof.
move=> m n i0 A B eqAB i; rewrite /mx_row' inE /= eq_sym.
by case/unlift_some=> i' -> _; apply: eqAB.
Qed.

Section CutPaste.

Variables m n1 n2 : nat.

(* The shape of the (dependent) width parameter of the type of A *)
(* determines where the cut is made! *)

Definition lcutmx (A : 'M_(m, n1 + n2)):=
  \matrix_(i < m, j < n1) (A i (lshift n2 j) : R).
Global Instance lcutmx_morph : Proper (Equivalence.equiv==>Equivalence.equiv) lcutmx.
Proof. by move=> A B eqAB i j; apply eqAB. Qed.

Definition rcutmx (A : 'M_(m, n1 + n2)) :=
  \matrix_(i < m, j < n2) (A i (rshift n1 j) : R).
Global Instance rcutmx_morph : Proper (Equivalence.equiv==>Equivalence.equiv) rcutmx.
Proof. by move=> A B eqAB i j; apply eqAB. Qed.

Definition pastemx (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :=
   \matrix_(i < m, j < n1 + n2)
      (match split j with inl j1 => A1 i j1 | inr j2 => A2 i j2 end : R).
Global Instance pastemx_morph : Proper (Equivalence.equiv==>Equivalence.equiv==>Equivalence.equiv) pastemx.
Proof.
rewrite/pastemx=> A1 B1 eqAB1 A2 B2 eqAB2 i j; case: (splitP j)=> j' _; first by apply eqAB1.
by apply eqAB2.
Qed.

Lemma pastemxEl : forall A1 A2 i j, pastemx A1 A2 i (lshift n2 j) === A1 i j.
Proof. by rewrite/pastemx=> A1 A2 i j; rewrite (unsplitK (inl _ _)); reflexivity. Qed.

Lemma pastemxEr : forall A1 A2 i j, pastemx A1 A2 i (rshift n1 j) === A2 i j.
Proof. by rewrite/pastemx=> A1 A2 i j; rewrite (unsplitK (inr _ _)); reflexivity. Qed.

Lemma pastemxKl : forall A1 A2, lcutmx (pastemx A1 A2) === A1.
Proof. by move=> A1 A2 i j; rewrite /lcutmx; rewrite -> pastemxEl; reflexivity. Qed.

Lemma pastemxKr : forall A1 A2, rcutmx (pastemx A1 A2) === A2.
Proof. by move=> A1 A2 i j; rewrite /rcutmx; rewrite -> pastemxEr; reflexivity. Qed.

Lemma cutmxK : forall A, pastemx (lcutmx A) (rcutmx A) === A.
Proof.
move=> A i j.
rewrite/pastemx/lcutmx/rcutmx.
case: splitP; case=> /= k kprf eqk.
  by have <- : j = lshift n2 (Ordinal kprf); [apply ord_inj; apply eqk | reflexivity].
by have <- : j = rshift n1 (Ordinal kprf); [apply ord_inj; apply eqk | reflexivity].
Qed.

End CutPaste.

Lemma mx_row_paste : forall m n1 n2 i0 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)),
  mx_row i0 (pastemx A1 A2) === pastemx (mx_row i0 A1) (mx_row i0 A2).
Proof. by reflexivity. Qed.

Lemma mx_row'_paste : forall m n1 n2 i0 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)),
  mx_row' i0 (pastemx A1 A2) === pastemx (mx_row' i0 A1) (mx_row' i0 A2).
Proof. by reflexivity. Qed.

Lemma mx_col_lshift : forall m n1 n2 j1 (A1 : 'M_(m, n1)) A2,
  mx_col (lshift n2 j1) (pastemx A1 A2) === mx_col j1 A1.
Proof. by rewrite/mx_col=> m n1 n2 j1 A1 A2 i j; rewrite -> pastemxEl; reflexivity. Qed.

Lemma mx_col_rshift : forall m n1 n2 j2 A1 (A2 : 'M_(m, n2)),
  mx_col (rshift n1 j2) (pastemx A1 A2) === mx_col j2 A2.
Proof. by rewrite/mx_col=> m n1 n2 j1 A1 A2 i j; rewrite -> pastemxEr; reflexivity. Qed.

Lemma mx_col'_lshift : forall m n1 n2 j1 (A1 : 'M_(m, n1.+1)) A2,
  mx_col' (lshift n2 j1) (pastemx A1 A2) === pastemx (mx_col' j1 A1) A2.
Proof.
move=> m n1 n2 j1 A1 A2 i /= j.
case: (splitP j) => j' def_j'.
  have -> : j = lshift n2 j' by apply ord_inj; apply def_j'.
  rewrite -> pastemxEl; rewrite /mx_col'.
  have -> : lift (lshift n2 j1) (lshift n2 j') = lshift n2 (lift j1 j'); last by rewrite -> pastemxEl; reflexivity.
  by apply ord_inj.
have -> : j = rshift n1 j' by apply ord_inj; apply def_j'.
rewrite -> pastemxEr; rewrite /mx_col'.
have -> : lift (lshift n2 j1) (rshift n1 j') = (rshift n1.+1 j'); last by rewrite -> pastemxEr; reflexivity.
apply ord_inj => /=.
rewrite/bump //= addSnnS addnS -def_j' -(addn1 j) addnC.
have -> : j1 <= j=>//.
rewrite def_j' {def_j'}.
by apply leq_trans with n1; [apply j1 | apply leq_addr].
Qed.

Lemma mx_col'_rcast : forall n1 n2, 'I_n2 -> (n1 + n2.-1)%N === (n1 + n2).-1.
Proof. by move=> n1 n2 [j]; move/ltn_predK <-; rewrite addnS. Qed.

(*Lemma paste_mx_col' : forall m n1 n2 j2 A1 (A2 : 'M_(m, n2)),
  pastemx A1 (mx_col' j2 A2) 
    === eq_rect _ (matrix R m) (mx_col' (rshift n1 j2) (pastemx A1 A2))
              _ (esym (mx_col'_rcast n1 j2)).
Proof.
move=> m n1 n2 j2 A1 A2; apply/matrixP=> i /= j; rewrite mxE.
case: splitP => j' def_j'; case: (n1 + n2.-1)%N / (esym _) => /= in j def_j' *.
  rewrite mxE -(pastemxEl _ A2); congr (pastemx _ _ _); apply: ord_inj.
  by rewrite /= def_j' /bump leqNgt ltn_addr.
rewrite 2!mxE -(pastemxEr A1); congr (pastemx _ _ _ _); apply: ord_inj => /=.
by rewrite def_j' /bump leq_add2l addnCA.
Qed.

Lemma mx_col'_rshift : forall m n1 n2 j2 A1 (A2 : 'M_(m, n2)),
  mx_col' (rshift n1 j2) (pastemx A1 A2) 
    = eq_rect _ (matrix R m) (pastemx A1 (mx_col' j2 A2))
              _ (mx_col'_rcast n1 j2).
Proof.
move=> m n1 n2 j2 A1 A2; rewrite paste_mx_col'.
by case: _.-1 / (mx_col'_rcast n1 j2) {A1 A2}(mx_col' _ _).
Qed.*)

Section Block.

Variables m1 m2 n1 n2 : nat.

Definition block_mx Aul Aur All Alr : 'M_(m1 + m2, n1 + n2) :=
  (pastemx (pastemx Aul Aur)^T (pastemx All Alr)^T)^T.
Global Instance block_mx_morph : Proper (Equivalence.equiv==>Equivalence.equiv==>Equivalence.equiv==>Equivalence.equiv==>Equivalence.equiv) block_mx.
Proof.
rewrite/block_mx=> Aul1 Aul2 eqAul Aur1 Aur2 eqAur All1 All2 eqAll Alr1 Alr2 eqAlr i j.
by apply pastemx_morph; apply trmx_morph; apply pastemx_morph.
Qed.

Section CutBlock.

Variable A : matrix R (m1 + m2) (n1 + n2).

Definition ulsubmx := lcutmx (lcutmx A^T)^T.
Definition ursubmx := rcutmx (lcutmx A^T)^T.
Definition llsubmx := lcutmx (rcutmx A^T)^T.
Definition lrsubmx := rcutmx (rcutmx A^T)^T.

Lemma submxK : block_mx ulsubmx ursubmx llsubmx lrsubmx === A.
Proof.
rewrite/block_mx/ulsubmx/ursubmx/llsubmx/lrsubmx.
rewrite -> !cutmxK => i j.
rewrite/rcutmx/lcutmx/pastemx/trmx.
case: splitP => i' eqii'.
by have -> : lshift m2 i' = i; [apply ord_inj|reflexivity].
by have -> : rshift m1 i' = i; [apply ord_inj|reflexivity].
Qed.

End CutBlock.

Section PasteBlock.

Variables (Aul : matrix R m1 n1) (Aur : matrix R m1 n2).
Variables (All : matrix R m2 n1) (Alr : matrix R m2 n2).

Let A := block_mx Aul Aur All Alr.

Lemma block_mxEul : forall i j, A (lshift m2 i) (lshift n2 j) === Aul i j.
Proof. by move=> i j; rewrite /A /block_mx /trmx; rewrite -> !pastemxEl; reflexivity. Qed.

Lemma block_mxKul : ulsubmx A === Aul.
Proof. by move=> i j; rewrite /A /block_mx /ulsubmx /lcutmx /trmx; rewrite -> !pastemxEl; reflexivity. Qed.

Lemma block_mxEur : forall i j, A (lshift m2 i) (rshift n1 j) === Aur i j.
Proof. by move=> i j; rewrite /A /block_mx /trmx; rewrite -> pastemxEl, pastemxEr; reflexivity. Qed.

Lemma block_mxKur : ursubmx A === Aur.
Proof. by move=> i j; rewrite /A /block_mx /ursubmx /lcutmx /rcutmx /trmx; rewrite -> pastemxEl, pastemxEr; reflexivity. Qed.

Lemma block_mxEll : forall i j, A (rshift m1 i) (lshift n2 j) === All i j.
Proof. by move=> i j; rewrite /A /block_mx /trmx; rewrite -> pastemxEr, pastemxEl; reflexivity. Qed.

Lemma block_mxKll : llsubmx A === All.
Proof. by move=> i j; rewrite /A /block_mx /llsubmx /lcutmx /rcutmx /trmx; rewrite -> pastemxEr, pastemxEl; reflexivity. Qed.

Lemma block_mxElr : forall i j, A (rshift m1 i) (rshift n1 j) === Alr i j.
Proof. by move=> i j; rewrite /A /block_mx /trmx; rewrite -> !pastemxEr; reflexivity. Qed.

Lemma block_mxKlr : lrsubmx A === Alr.
Proof. by move=> i j; rewrite /A /block_mx /lrsubmx /lcutmx /rcutmx /trmx; rewrite -> !pastemxEr; reflexivity. Qed.

End PasteBlock.

End Block.

Section TrBlock.

Variables m1 m2 n1 n2 : nat.

Section TrCut.

Variable A : matrix R (m1 + m2) (n1 + n2).

Lemma trmx_ulsub : (ulsubmx A)^T === ulsubmx A^T.
Proof. by move => i j /=; reflexivity. Qed.

Lemma trmx_ursub : (ursubmx A)^T === llsubmx A^T.
Proof. by move => i j /=; reflexivity. Qed.

Lemma trmx_llsub : (llsubmx A)^T === ursubmx A^T.
Proof. by move => i j /=; reflexivity. Qed.

Lemma trmx_lrsub : (lrsubmx A)^T === lrsubmx A^T.
Proof. by move => i j /=; reflexivity. Qed.

End TrCut.

Lemma trmx_block : forall (Aul : 'M_(m1, n1)) Aur All (Alr : 'M_(m2, n2)),
 (block_mx Aul Aur All Alr)^T ===
    block_mx Aul^T All^T Aur^T Alr^T.
Proof.
move=> Aul Aur All Alr.
pose (block_mx Aul Aur All Alr).
rewrite -/m.
rewrite <- (block_mxKul Aul Aur All Alr).
rewrite <- (block_mxKll Aul Aur All Alr) at 2.
rewrite <- (block_mxKur Aul Aur All Alr) at 3.
rewrite <- (block_mxKlr Aul Aur All Alr) at 4.
by rewrite -> trmx_ulsub, trmx_llsub, trmx_ursub, trmx_lrsub, submxK; reflexivity.
Qed.

End TrBlock.

End Slicing.

Notation "A ^T" := (trmx A).
Prenex Implicits lcutmx rcutmx ulsubmx ursubmx llsubmx lrsubmx.

(* Definition of operations for matrices over a ring *)
Section MatrixOpsDef.


Context `{r_ring : Ring}.

Add Ring r_r : r_rt (setoid r_st r_ree, preprocess [unfold Equivalence.equiv]).

Notation "0" := rO.
Notation "1" := rI.
Notation "x + y" := (radd x y).
Notation "x * y " := (rmul x y).
Notation "x - y " := (rsub x y).
Notation "- x" := (ropp x).

Notation "\sum_ ( <- r | P ) F" := (\big[radd/0]_(<- r | P) F).
Notation "\sum_ ( i <- r | P ) F" := (\big[radd/0]_(i <- r | P) F).
Notation "\sum_ ( i <- r ) F" := (\big[radd/0]_(i <- r) F).
Notation "\sum_ ( m <= i < n | P ) F" := (\big[radd/0]_(m <= i < n | P) F).
Notation "\sum_ ( m <= i < n ) F" := (\big[radd/0]_(m <= i < n) F).
Notation "\sum_ ( i | P ) F" := (\big[radd/0]_(i | P) F).
Notation "\sum_ i F" := (\big[radd/0]_i F).
Notation "\sum_ ( i : t | P ) F" := (\big[radd/0]_(i : t | P) F) (only parsing).
Notation "\sum_ ( i : t ) F" := (\big[radd/0]_(i : t) F) (only parsing).
Notation "\sum_ ( i < n | P ) F" := (\big[radd/0]_(i < n | P) F).
Notation "\sum_ ( i < n ) F" := (\big[radd/0]_(i < n) F).
Notation "\sum_ ( i \in A | P ) F" := (\big[radd/0]_(i \in A | P) F).
Notation "\sum_ ( i \in A ) F" := (\big[radd/0]_(i \in A) F).

Notation "\prod_ ( <- r | P ) F" := (\big[rmul/1]_(<- r | P) F).
Notation "\prod_ ( i <- r | P ) F" := (\big[rmul/1]_(i <- r | P) F).
Notation "\prod_ ( i <- r ) F" := (\big[rmul/1]_(i <- r) F).
Notation "\prod_ ( m <= i < n | P ) F" := (\big[rmul/1]_(m <= i < n | P) F).
Notation "\prod_ ( m <= i < n ) F" := (\big[rmul/1]_(m <= i < n) F).
Notation "\prod_ ( i | P ) F" := (\big[rmul/1]_(i | P) F).
Notation "\prod_ i F" := (\big[rmul/1]_i F).
Notation "\prod_ ( i : t | P ) F" := (\big[rmul/1]_(i : t | P) F) (only parsing).
Notation "\prod_ ( i : t ) F" := (\big[rmul/1]_(i : t) F) (only parsing).
Notation "\prod_ ( i < n | P ) F" := (\big[rmul/1]_(i < n | P) F).
Notation "\prod_ ( i < n ) F" := (\big[rmul/1]_(i < n) F).
Notation "\prod_ ( i \in A | P ) F" := (\big[rmul/1]_(i \in A | P) F).
Notation "\prod_ ( i \in A ) F" := (\big[rmul/1]_(i \in A) F).

Existing Instance radd_morph.
Existing Instance rmul_morph.
Existing Instance rsub_morph.
Existing Instance ropp_morph.

Existing Instance radd_assoc.
Existing Instance radd_comm.
Existing Instance radd_left_unit.
Existing Instance rmul_assoc.
Existing Instance rmul_comm.
Existing Instance rmul_left_unit.
Existing Instance rmul_left_zero.
Existing Instance radd_rmul_left_distr.

Section ZmodOps.
(* The Zmodule structure *)

Variables m n : nat.
Implicit Types A B C : matrix R m n.

Definition null_mx := \matrix_(i < m, j < n) (0 : R).
Definition oppmx A := \matrix_(i < m, j < n) (- A i j).
Definition addmx A B := \matrix_(i < m, j < n) (A i j + B i j).
Definition scalemx x A := \matrix_(i < m, j < n) (x * A i j).

Global Instance addmx_morph : Proper (Equivalence.equiv==>Equivalence.equiv==>Equivalence.equiv) addmx.
Proof. by move=> A A' eqAA' B B' eqBB' i j; rewrite/addmx; setoid_rewrite eqAA'; setoid_rewrite eqBB'; reflexivity. Qed.

Global Instance oppmx_morph : Proper (Equivalence.equiv==>Equivalence.equiv) oppmx.
Proof. by move=> A A' eqAA' i j ; rewrite/oppmx; setoid_rewrite eqAA'; reflexivity. Qed.

Global Instance scalemx_morph : Proper (Equivalence.equiv==>Equivalence.equiv==>Equivalence.equiv) scalemx.
Proof. by move=> A A' eqAA' B B' eqBB' i j ; rewrite/scalemx; setoid_rewrite eqAA'; setoid_rewrite eqBB'; reflexivity. Qed.

Lemma summxE : forall I r (P : pred I) (E : I -> 'M_(m, n)) i j,
  (\big[addmx/null_mx]_(k <- r | P k) E k) i j === \sum_(k <- r | P k) E k i j.
Proof.
move=> I r P E i j.
apply: (big_morph (phi:=fun A => A i j)) => [A B||].
  by rewrite/addmx; ring.
by rewrite/null_mx; ring.
apply radd_morph.
Qed.

(* Vector space structure... pending the definition *)

Notation "'0m" := null_mx.
Notation "-m A" := (oppmx A).
Notation "A +m B" := (addmx A B).
Notation "A -m B" := (addmx A (oppmx B)).
Notation "x *m: A" := (scalemx x A).

Lemma scale0mx : forall A, 0 *m: A === '0m.
Proof. by rewrite/null_mx/addmx/oppmx/scalemx=> A i j; ring. Qed.

Lemma scalemx0 : forall x, x *m: '0m === '0m.
Proof. by rewrite/null_mx/addmx/oppmx/scalemx=> x i j; ring. Qed.

Lemma scale1mx : forall A, 1 *m: A === A.
Proof. by rewrite/null_mx/addmx/oppmx/scalemx=> A i j; ring. Qed.

Lemma scaleNmx : forall x A, (- x) *m: A === -m (x *m: A).
Proof. by rewrite/null_mx/addmx/oppmx/scalemx=> x A i j; ring. Qed.

Lemma scalemxN : forall x A, x *m: (-m A) === -m (x *m: A).
Proof. by rewrite/null_mx/addmx/oppmx/scalemx=> x A i j; ring. Qed.

Lemma scalemx_addl : forall x y A, (x + y) *m: A === (x *m: A) +m (y *m: A).
Proof. by rewrite/null_mx/addmx/oppmx/scalemx=> x y A i j; ring. Qed.

Lemma scalemx_addr : forall x A B, x *m: (A +m B) === (x *m: A) +m (x *m: B).
Proof. by rewrite/null_mx/addmx/oppmx/scalemx=> x A B i j; ring. Qed.

Lemma scalemx_subl : forall x y A, (x - y) *m: A ===  (x *m: A) -m (y *m: A).
Proof. by rewrite/null_mx/addmx/oppmx/scalemx=> x y A i j; ring. Qed.

Lemma scalemx_subr : forall x A B, x *m: (A -m B) === (x *m: A) -m (x *m: B).
Proof. by rewrite/null_mx/addmx/oppmx/scalemx=> x A B i j; ring. Qed.

Lemma scalemxA : forall x y A, x *m: (y *m: A) === (x * y) *m: A.
Proof. by rewrite/null_mx/addmx/oppmx/scalemx=> x y A i j; ring. Qed.

(* Basis... *)

Definition delta_mx i0 j0 :=
  \matrix_(i < m, j < n) (if ((i == i0) && (j == j0)) then 1 else 0).

Lemma matrix_sum_delta : forall A,
  A === \big[addmx/null_mx]_(i < m) \big[addmx/null_mx]_(j < n) (A i j *m: delta_mx i j).
Proof.
move=> A i j.
setoid_rewrite summxE.
setoid_rewrite summxE.
setoid_rewrite (bigD1 (j:=i))=>//=.
setoid_rewrite (big1 (P:=fun i0 => i0 != i))=>[|i0 Hi0].
  setoid_rewrite (bigD1 (j:=j))=>//=.
  setoid_rewrite (big1 (P:=fun i0 => i0 != j))=>[|i0 Hi0].
    by rewrite/delta_mx/scalemx !eq_refl/=; ring.
  rewrite/delta_mx/scalemx !eq_refl/= eq_sym; move:Hi0.
  by case/negbRL=>->/=; ring.
apply (big1 (P:=fun _ => true) (F:=fun k => (A i0 k *m: delta_mx i0 k) i j))=>i1 _.
rewrite/delta_mx/scalemx eq_sym/=; move:Hi0.
by case/negbRL=>->/=; ring.
Qed.

End ZmodOps.

Notation "'0m" := (@null_mx _ _).
Notation "-m A" := (oppmx A).
Notation "A +m B" := (addmx A B).
Notation "A -m B" := (addmx A (oppmx B)).
Notation "x *m: A" := (scalemx x A).

Lemma trmx0 : forall (m n : nat), (@null_mx m n)^T === @null_mx n m.
Proof. by move=> m n; rewrite/trmx/null_mx/addmx/oppmx/scalemx; reflexivity. Qed.

Lemma trmx_add : forall m n (A B : 'M_(m, n)), (A +m B)^T === A^T +m B^T.
Proof. by move=> m n; rewrite/trmx/null_mx/addmx/oppmx/scalemx; reflexivity. Qed.

Lemma trmx_scale : forall m n a (A : 'M_(m, n)), (a *m: A)^T === a *m: A^T.
Proof. by move=> m n; rewrite/trmx/null_mx/addmx/oppmx/scalemx; reflexivity. Qed.

Lemma mx_row0 : forall m n i0, mx_row i0 (@null_mx m n) === (@null_mx 1 n).
Proof. by move=> m n; rewrite/trmx/null_mx/addmx/oppmx/scalemx; reflexivity. Qed.

Lemma mx_col0 : forall m n j0, mx_col j0 (@null_mx m n) === (@null_mx m 1).
Proof. by move=> m n; rewrite/trmx/null_mx/addmx/oppmx/scalemx; reflexivity. Qed.

Lemma mx_row'0 : forall m n i0, mx_row' i0 (@null_mx m n) === (@null_mx m.-1 n).
Proof. by move=> m n; rewrite/trmx/null_mx/addmx/oppmx/scalemx; reflexivity. Qed.

Lemma mx_col'0 : forall m n i0, mx_col' i0 (@null_mx m n) === (@null_mx m n.-1).
Proof. by move=> m n; rewrite/trmx/null_mx/addmx/oppmx/scalemx; reflexivity. Qed.

Lemma pastemx0 : forall m n1 n2,
  pastemx (@null_mx m n1) (@null_mx m n2) === (@null_mx m (n1 + n2)).
Proof. by move=> m n1 n2 i j; rewrite/pastemx/trmx/null_mx/addmx/oppmx/scalemx; case: split; reflexivity. Qed.

Lemma addmx_paste : forall m n1 n2 (A1 B1 : 'M_(m, n1)) (A2 B2 : 'M_(m, n2)),
  pastemx A1 A2 +m pastemx B1 B2 === pastemx (A1 +m B1) (A2 +m B2).
Proof. by move=> m n1 n2 iA1 B1 A2 B2 i j; rewrite/pastemx/trmx/null_mx/addmx/oppmx/scalemx; case: split; reflexivity. Qed.

Lemma scalemx_paste : forall m n1 n2 a (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)),
  a *m: pastemx A1 A2 === pastemx (a *m: A1) (a *m: A2).
Proof. by move=> m n1 n2 a A1 A2 i j; rewrite/pastemx/trmx/null_mx/addmx/oppmx/scalemx; case: split; reflexivity. Qed.

Lemma block_mx0 : forall m1 m2 n1 n2,
  block_mx (@null_mx m1 n1) (@null_mx m1 n2) (@null_mx m2 n1) (@null_mx m2 n2) === @null_mx (m1 + m2) (n1 + n2).
Proof. by move=> m1 m2 n1 n2 i j; rewrite/block_mx/pastemx/trmx/null_mx/addmx/oppmx/scalemx; case: split; case: split; reflexivity. Qed.

Lemma addmx_block : forall m1 m2 n1 n2 (Aul Bul : 'M_(m1, n1)) (Aur Bur : 'M_(m1, n2)) (All Bll : 'M_(m2, n1)) (Alr Blr : 'M_(m2, n2)),
  block_mx Aul Aur All Alr +m block_mx Bul Bur Bll Blr
    === block_mx (Aul +m Bul) (Aur +m Bur) (All +m Bll) (Alr +m Blr).
Proof. by move=> m1 m2 n1 n2 Aul Bul Aur Bur All Bll Alr Blr i j; rewrite/block_mx/pastemx/trmx/null_mx/addmx/oppmx/scalemx; case: split; case: split; reflexivity. Qed.

Lemma scalemx_block : forall m1 m2 n1 n2 a  (Aul : 'M_(m1, n1)) (Aur : 'M_(m1, n2)) (All : 'M_(m2, n1)) (Alr : 'M_(m2, n2)),
  a *m: block_mx Aul Aur All Alr
     === block_mx (a *m: Aul) (a *m: Aur) (a *m: All) (a *m: Alr).
Proof. by move=> m1 m2 n1 n2 a Aul Aur All Alr i j; rewrite/block_mx/pastemx/trmx/null_mx/addmx/oppmx/scalemx; case: split; case: split; reflexivity. Qed.

(* The graded ring structure *)

Definition scalar_mx n x := \matrix_(i , j < n) (if i == j then x else 0).
Global Instance scalar_mx_morph n : Morphism (Equivalence.equiv==>Equivalence.equiv) (@scalar_mx n).
Proof. by rewrite/scalar_mx=>n x y eqxy i j; case:(i==j); [apply eqxy | reflexivity]. Qed.

Definition mulmx m n p (A : 'M_(m, n)) (B : 'M_(n, p)) :=
  \matrix_(i < m, k < p) \big [radd/0]_(j < n) (A i j * B j k).
Global Instance mulmx_morph m n p : Morphism (Equivalence.equiv==>Equivalence.equiv==>Equivalence.equiv) (@mulmx m n p).
Proof.
move=> m n p A A' eqAA' B B' eqBB' i k.
rewrite/mulmx; apply eq_bigr=> j _.
by setoid_rewrite eqAA'; setoid_rewrite eqBB'; reflexivity.
Qed.

Notation "x %:M" := (@scalar_mx _ x).
Notation "A *m B" := (mulmx A B).

Lemma scalar_mx0 : forall n, 0 %:M === @null_mx n n.
Proof. by move=> n i j; rewrite/block_mx/pastemx/trmx/null_mx/addmx/oppmx/scalemx/scalar_mx/mulmx; case: eqP=> _; ring. Qed.

Lemma scalar_mx_opp : forall (n : nat) a, (- a)%:M === -m (@scalar_mx n a).
Proof. by move=> n a i j; rewrite/block_mx/pastemx/trmx/null_mx/addmx/oppmx/scalemx/scalar_mx/mulmx; case: eqP=> _; ring. Qed.

Lemma scalar_mx_add : forall n a b, @scalar_mx n (a + b) === a%:M +m b%:M.
Proof. by move=> n a b i j; rewrite/block_mx/pastemx/trmx/null_mx/addmx/oppmx/scalemx/scalar_mx/mulmx; case: eqP=> _; ring. Qed.

Lemma mulmx_scalar : forall m n a (A : 'M_(m, n)), (a%:M) *m A === a *m: A.
Proof.
move=> m n a A i j; rewrite/block_mx/pastemx/trmx/null_mx/addmx/oppmx/scalemx/scalar_mx/mulmx.
setoid_rewrite (bigD1 (j:=i))=>//.
setoid_rewrite big1=>[|i'/=]; first by case: eqP=>ii'//; ring.
by rewrite/is_true eq_sym; move/negbRL=>->/=; ring.
Qed.

Lemma scalar_mx_mul : forall n a b, @scalar_mx n (a * b) === a%:M *m b%:M.
Proof. by move=> n a b; rewrite -> mulmx_scalar; rewrite /scalar_mx /scalemx=> i j; by case (i==j); ring. Qed.

Lemma trmx_scalar : forall n a, (a%:M)^T === @scalar_mx n a.
Proof. by move=> n a i j; rewrite/trmx/null_mx/addmx/oppmx/scalemx/scalar_mx/mulmx eq_sym; reflexivity. Qed.

Lemma mul1mx : forall m n (A : 'M_(m, n)), 1%:M *m A === A.
Proof. by move=> m n A; rewrite -> mulmx_scalar, scale1mx; reflexivity. Qed.

Lemma mulmx_addl : forall m n p (A1 A2 : 'M_(m, n)) (B : 'M_(n, p)),
  (A1 +m A2) *m B === A1 *m B +m A2 *m B.
Proof.
move=> m n p A1 A2 B i k; rewrite /addmx /mulmx.
setoid_rewrite <- big_split.
by apply eq_bigr=> j _; ring.
Qed.

Lemma scalemx_add : forall n a1 a2, @scalar_mx n (a1 + a2) === a1%:M +m a2%:M.
Proof. by move=> n a1 a2 i j; rewrite/scalar_mx/addmx; case: (i==j); ring. Qed.

Lemma scalemxAl : forall m n p a (A : 'M_(m, n)) (B : 'M_(n, p)),
  a *m: (A *m B) === (a *m: A) *m B.
Proof.
move=> m n p a A B i k.
rewrite/scalemx/mulmx.
setoid_rewrite (big_distrr).
apply eq_bigr => j _; ring.
Qed.

Lemma mul0mx : forall m n p (A : 'M_(n, p)), '0m *m A === @null_mx m p.
Proof. by move=> m n p A i k; rewrite/mulmx/null_mx; apply (big1 (P:=fun _ => true) (F:=fun j => 0 * A j k))=> j _; ring. Qed.

Lemma mulmx0 : forall m n p (A : 'M_(m, n)), A *m '0m === @null_mx m p.
Proof. by move=> m n p A i k; rewrite/mulmx/null_mx; apply (big1 (P:=fun _ => true) (F:=fun j => A i j * 0))=> j _; ring. Qed.

Lemma mulmx1 : forall m n (A : 'M_(m, n)), A *m 1%:M === A.
Proof.
move=> m n A i k; rewrite/mulmx/scalar_mx.
setoid_rewrite (bigD1 (j:=k))=>//.
setoid_rewrite big1=> [| j/=]; first by rewrite eq_refl; ring.
by rewrite/is_true; move/negbRL=>->/=; ring.
Qed.

Lemma mulmx_addr : forall m n p (A : 'M_(m, n)) (B1 B2 : 'M_(n, p)),
  A *m (B1 +m B2) === A *m B1 +m A *m B2.
Proof. by move=> m n p A B1 B2 i k; rewrite/mulmx/addmx; setoid_rewrite <- big_split; apply eq_bigr=> j _; ring. Qed.

Lemma mulmxA : forall m n p q (A : 'M_(m, n)) (B : 'M_(n, p)) (C : 'M_(p, q)),
  A *m (B *m C) === A *m B *m C.
Proof.
move=> m n p q A B C i l; rewrite/mulmx.
setoid_rewrite big_distrr; setoid_rewrite big_distrl.
setoid_rewrite (exchange_big predT predT (fun j k => A i j * (B j k * C k l))).
by apply eq_bigr=> j _; apply eq_bigr=> k _; ring.
Qed.

Definition perm_mx n (s : 'S_n) :=
  \matrix_(i, j) (if s i == j then 1 else 0).

Definition tperm_mx n i1 i2 := @perm_mx n (tperm i1 i2).

Lemma trmx_perm : forall n (s : 'S_n), (perm_mx s)^T === perm_mx s^-1.
Proof. by move=> n s i j; rewrite /trmx /perm_mx (canF_eq (permK _)) eq_sym; reflexivity. Qed.

Lemma trmx_tperm : forall n i1 i2, (@tperm_mx n i1 i2)^T === tperm_mx i1 i2.
Proof. by move=> n i1 i2; rewrite /tperm_mx; rewrite -> trmx_perm, tpermV; reflexivity. Qed.

Lemma mulmx_perm : forall n (s t : 'S_n),
  perm_mx s *m perm_mx t === perm_mx (s * t).
Proof.
move=> n s t i j; rewrite/mulmx/perm_mx.
setoid_rewrite (bigD1 (j:=s i))=>//=.
setoid_rewrite (big1 (P:=fun k => k != s i))=>[|k]; first by rewrite eq_refl permM; ring.
by rewrite eq_sym; move/negbTE => ->; ring.
Qed.

Lemma mul_tperm_mx : forall m n (A : 'M_(m, n)) i1 i2, 
  (tperm_mx i1 i2) *m A === rswap i1 i2 A.
Proof.
move=> m n' A i1 i2 i j.
rewrite /mulmx /tperm_mx /perm_mx /rswap.
setoid_rewrite (bigD1 (j:=tperm i1 i2 i))=>//=.
setoid_rewrite (big1 (P:=fun k => k != tperm i1 i2 i))=>[|k]; first by rewrite eq_refl; ring.
by rewrite eq_sym; move/negbTE => ->; ring.
Qed. 

Lemma perm_mx1 : forall n, perm_mx 1 === @scalar_mx n 1.
Proof. by move=> n i j; rewrite /perm_mx /scalar_mx perm1; reflexivity. Qed.

(* The trace, in 1/4 line. *)
Definition mx_trace n (A : 'M_n) := \sum_(i < n) A i i.
Notation "'\tr' A" := (mx_trace A).

Lemma mx_trace0 : forall n, \tr ('0m : 'M_n) === 0.
Proof. by move=> n; apply (big1 (I:=ordinal_finType n))=> i _; reflexivity. Qed.

Lemma mx_trace_scale : forall n a (A : 'M_n), \tr (a *m: A) === a * \tr A.
Proof. by move=> n a A; rewrite/mx_trace; setoid_rewrite (big_distrr (I:=ordinal_finType n)); apply eq_bigr => i _; reflexivity. Qed.

Notation "a *+ n" := (iter n (radd a) rO).

Lemma mx_trace_scalar : forall n a, \tr (a%:M : 'M_n) === a *+ n.
Proof. by move=> n a; rewrite <- big_const_ord; apply eq_bigr=> i _; rewrite/scalar_mx eq_refl; reflexivity. Qed.

Lemma mx_trace_add : forall n A B, \tr (A +m B : 'M_n) === \tr A + \tr B.
Proof. by move=> n A B; rewrite/mx_trace/addmx; apply big_split. Qed.

Lemma mx_trace_tr : forall n (A : 'M_n), \tr A^T === \tr A.
Proof. by move=> n A; apply eq_bigr=> i _; reflexivity. Qed.

Lemma mx_trace_block : forall n1 n2 Aul Aur All Alr,
  \tr (block_mx Aul Aur All Alr : 'M_(n1 + n2)) === \tr Aul + \tr Alr.
Proof.
move=> n1 n2 Aul Aur All Alr; rewrite /mx_trace; setoid_rewrite big_split_ord => /=.
apply radd_morph; apply eq_bigr=> i _; [rewrite -> block_mxEul | rewrite -> block_mxElr]; reflexivity.
Qed.

Lemma mulmx_paste : forall m n p1 p2 (A : 'M_(m, n)) (B1 : 'M_(n, p1)) (B2 : 'M_(n, p2)),
  A *m (pastemx B1 B2) === pastemx (A *m B1) (A *m B2).
Proof. by move=> m n p1 p2 A B1 B2 i k; rewrite/pastemx/mulmx; case defk: (split k) => [k1 | k2]; apply eq_bigr=> j _; reflexivity. Qed.

Lemma dotmx_paste : forall m n1 n2 p A1 A2 B1 B2,
  (pastemx A1 A2 : 'M_(m, n1 + n2)) *m (pastemx B1 B2 : 'M_(p, n1 + n2))^T
    === A1 *m B1^T +m A2 *m B2^T.
Proof.
move=> m n1 n2 p A1 A2 B1 B2 i k; rewrite/mulmx/addmx/trmx; setoid_rewrite big_split_ord.
by apply radd_morph; apply eq_bigr=> j _; [rewrite -> pastemxEl, pastemxEl | rewrite -> pastemxEr, pastemxEr]; reflexivity.
Qed.

End MatrixOpsDef.

Notation "'0m" := (@null_mx _ _ _ _ _ _ _ _ _ _ _ _).
Notation "-m A" := (oppmx A).
Notation "A +m B" := (addmx A B).
Notation "A -m B" := (addmx A (oppmx B)).
Notation "x *m: A" := (scalemx x A).
Notation "x %:M" := (scalar_mx x).
Notation "A *m B" := (mulmx A B).
Notation "'\tr' A" := (mx_trace A).

Section TrMul.

Context `{r_ring : Ring}.

Notation "0" := rO.
Notation "1" := rI.
Notation "x + y" := (radd x y).
Notation "x * y " := (rmul x y).
Notation "x - y " := (rsub x y).
Notation "- x" := (ropp x).

Notation "\sum_ ( <- r | P ) F" := (\big[radd/0]_(<- r | P) F).
Notation "\sum_ ( i <- r | P ) F" := (\big[radd/0]_(i <- r | P) F).
Notation "\sum_ ( i <- r ) F" := (\big[radd/0]_(i <- r) F).
Notation "\sum_ ( m <= i < n | P ) F" := (\big[radd/0]_(m <= i < n | P) F).
Notation "\sum_ ( m <= i < n ) F" := (\big[radd/0]_(m <= i < n) F).
Notation "\sum_ ( i | P ) F" := (\big[radd/0]_(i | P) F).
Notation "\sum_ i F" := (\big[radd/0]_i F).
Notation "\sum_ ( i : t | P ) F" := (\big[radd/0]_(i : t | P) F) (only parsing).
Notation "\sum_ ( i : t ) F" := (\big[radd/0]_(i : t) F) (only parsing).
Notation "\sum_ ( i < n | P ) F" := (\big[radd/0]_(i < n | P) F).
Notation "\sum_ ( i < n ) F" := (\big[radd/0]_(i < n) F).
Notation "\sum_ ( i \in A | P ) F" := (\big[radd/0]_(i \in A | P) F).
Notation "\sum_ ( i \in A ) F" := (\big[radd/0]_(i \in A) F).

Notation "\prod_ ( <- r | P ) F" := (\big[rmul/1]_(<- r | P) F).
Notation "\prod_ ( i <- r | P ) F" := (\big[rmul/1]_(i <- r | P) F).
Notation "\prod_ ( i <- r ) F" := (\big[rmul/1]_(i <- r) F).
Notation "\prod_ ( m <= i < n | P ) F" := (\big[rmul/1]_(m <= i < n | P) F).
Notation "\prod_ ( m <= i < n ) F" := (\big[rmul/1]_(m <= i < n) F).
Notation "\prod_ ( i | P ) F" := (\big[rmul/1]_(i | P) F).
Notation "\prod_ i F" := (\big[rmul/1]_i F).
Notation "\prod_ ( i : t | P ) F" := (\big[rmul/1]_(i : t | P) F) (only parsing).
Notation "\prod_ ( i : t ) F" := (\big[rmul/1]_(i : t) F) (only parsing).
Notation "\prod_ ( i < n | P ) F" := (\big[rmul/1]_(i < n | P) F).
Notation "\prod_ ( i < n ) F" := (\big[rmul/1]_(i < n) F).
Notation "\prod_ ( i \in A | P ) F" := (\big[rmul/1]_(i \in A | P) F).
Notation "\prod_ ( i \in A ) F" := (\big[rmul/1]_(i \in A) F).

Existing Instance radd_morph.
Existing Instance rmul_morph.
Existing Instance rsub_morph.
Existing Instance ropp_morph.

Existing Instance radd_assoc.
Existing Instance radd_comm.
Existing Instance radd_left_unit.
Existing Instance rmul_assoc.
Existing Instance rmul_comm.
Existing Instance rmul_left_unit.
Existing Instance rmul_left_zero.
Existing Instance radd_rmul_left_distr.

Add Ring r_r2 : r_rt (setoid r_st r_ree, preprocess [unfold Equivalence.equiv]).

Existing Instance addmx_morph.
Existing Instance oppmx_morph.
Existing Instance mulmx_morph.

Existing Instance trmx_morph.
Existing Instance pastemx_morph.
Existing Instance block_mx_morph.

Lemma trmx_mul_rev : forall m n p (A : matrix R m n) (B : matrix R n p),
  (A *m B)^T === B^T *m A^T.
Proof. by move=> m n p A B k i; rewrite/trmx; apply eq_bigr=> j _; ring. Qed.

Lemma mulmx_block : forall m1 m2 n1 n2 p1 p2 (Aul : matrix R m1 n1) Aur All Alr Bul Bur Bll Blr,
  (block_mx Aul Aur All Alr : 'M_(m1 + m2, n1 + n2))
   *m (block_mx Bul Bur Bll Blr : 'M_(n1 + n2, p1 + p2))
    === block_mx (Aul *m Bul +m Aur *m Bll) (Aul *m Bur +m Aur *m Blr)
               (All *m Bul +m Alr *m Bll) (All *m Bur +m Alr *m Blr).
Proof.
move=> m1 m2 n1 n2 p1 p2 Aul Aur All Alr Bul Bur Bll Blr/=; rewrite <- (trmxK (_ *m _)).
rewrite -> trmx_mul_rev, (trmx_block Aul); rewrite /block_mx; rewrite -> (trmxK (pastemx _ _)), dotmx_paste, <- !addmx_paste.
by rewrite -> !trmx_add, (trmxK _), (trmxK _), <- addmx_paste, !mulmx_paste, <- !trmx_mul_rev, !mulmx_paste; reflexivity.
Qed.

Lemma mul_mx_tperm : forall m n (A : matrix R m n) i1 i2, 
  A *m (tperm_mx i1 i2) === cswap i1 i2 A.
Proof.
move=> m n A i1 i2; apply: trmx_inj.
by rewrite -> trmx_mul_rev, trmx_tperm, mul_tperm_mx, trmx_cswap; reflexivity.
Qed.

End TrMul.

Section ComMatrix.

Context `{r_ring : Ring}.

Notation "0" := rO.
Notation "1" := rI.
Notation "x + y" := (radd x y).
Notation "x * y " := (rmul x y).
Notation "x - y " := (rsub x y).
Notation "- x" := (ropp x).

Notation "\sum_ ( <- r | P ) F" := (\big[radd/0]_(<- r | P) F).
Notation "\sum_ ( i <- r | P ) F" := (\big[radd/0]_(i <- r | P) F).
Notation "\sum_ ( i <- r ) F" := (\big[radd/0]_(i <- r) F).
Notation "\sum_ ( m <= i < n | P ) F" := (\big[radd/0]_(m <= i < n | P) F).
Notation "\sum_ ( m <= i < n ) F" := (\big[radd/0]_(m <= i < n) F).
Notation "\sum_ ( i | P ) F" := (\big[radd/0]_(i | P) F).
Notation "\sum_ i F" := (\big[radd/0]_i F).
Notation "\sum_ ( i : t | P ) F" := (\big[radd/0]_(i : t | P) F) (only parsing).
Notation "\sum_ ( i : t ) F" := (\big[radd/0]_(i : t) F) (only parsing).
Notation "\sum_ ( i < n | P ) F" := (\big[radd/0]_(i < n | P) F).
Notation "\sum_ ( i < n ) F" := (\big[radd/0]_(i < n) F).
Notation "\sum_ ( i \in A | P ) F" := (\big[radd/0]_(i \in A | P) F).
Notation "\sum_ ( i \in A ) F" := (\big[radd/0]_(i \in A) F).

Notation "\prod_ ( <- r | P ) F" := (\big[rmul/1]_(<- r | P) F).
Notation "\prod_ ( i <- r | P ) F" := (\big[rmul/1]_(i <- r | P) F).
Notation "\prod_ ( i <- r ) F" := (\big[rmul/1]_(i <- r) F).
Notation "\prod_ ( m <= i < n | P ) F" := (\big[rmul/1]_(m <= i < n | P) F).
Notation "\prod_ ( m <= i < n ) F" := (\big[rmul/1]_(m <= i < n) F).
Notation "\prod_ ( i | P ) F" := (\big[rmul/1]_(i | P) F).
Notation "\prod_ i F" := (\big[rmul/1]_i F).
Notation "\prod_ ( i : t | P ) F" := (\big[rmul/1]_(i : t | P) F) (only parsing).
Notation "\prod_ ( i : t ) F" := (\big[rmul/1]_(i : t) F) (only parsing).
Notation "\prod_ ( i < n | P ) F" := (\big[rmul/1]_(i < n | P) F).
Notation "\prod_ ( i < n ) F" := (\big[rmul/1]_(i < n) F).
Notation "\prod_ ( i \in A | P ) F" := (\big[rmul/1]_(i \in A | P) F).
Notation "\prod_ ( i \in A ) F" := (\big[rmul/1]_(i \in A) F).

Existing Instance radd_morph.
Existing Instance rmul_morph.
Existing Instance rsub_morph.
Existing Instance ropp_morph.

Existing Instance radd_assoc.
Existing Instance radd_comm.
Existing Instance radd_left_unit.
Existing Instance rmul_assoc.
Existing Instance rmul_comm.
Existing Instance rmul_left_unit.
Existing Instance rmul_left_zero.
Existing Instance radd_rmul_left_distr.

Add Ring r_r3 : r_rt (setoid r_st r_ree, preprocess [unfold Equivalence.equiv]).

Existing Instance addmx_morph.
Existing Instance oppmx_morph.
Existing Instance mulmx_morph.

Existing Instance trmx_morph.
Existing Instance pastemx_morph.
Existing Instance block_mx_morph.

Lemma trmx_mul : forall m n p (A : matrix R m n) (B : 'M_(n, p)),
  (A *m B)^T === B^T *m A^T.
Proof.
move=> m n p A B; rewrite -> trmx_mul_rev; rewrite /mulmx=> k i.
by apply (eq_bigr (I:=ordinal_finType n)) => j _; reflexivity.
Qed.

Lemma scalemxAr : forall m n p a (A : matrix R m n) (B : 'M_(n, p)),
  a *m: (A *m B) === A *m (a *m: B).
Proof.
move=> m n p a A B; apply trmx_inj.
by rewrite -> trmx_scale, !trmx_mul, trmx_scale, scalemxAl; reflexivity.
Qed.

Lemma scalar_mx_comm : forall (n : pos_nat) a (A : matrix R n n),
  A *m (a%:M) === (a%:M) *m A.
Proof.
move=> n a A; apply: trmx_inj; rewrite -> trmx_mul, trmx_scalar.
by rewrite -> !mulmx_scalar, trmx_scale; reflexivity.
Qed.

Lemma mx_trace_mulC : forall m n (A : matrix R m n) B,
  \tr (A *m B) === \tr (B *m A).
Proof.
move=> m n A B; transitivity (\sum_(i < m) \sum_(j < n) A i j * B j i).
  by apply eq_bigr; reflexivity.
setoid_rewrite (exchange_big (I:=ordinal_finType m)); apply eq_bigr => i _.
by apply eq_bigr => j _; ring.
Qed.

Local Notation "x ^+ n" := (iter n (rmul x) 1).

(* The determinant, in one line. *)
Definition determinant n (A : matrix R n n) :=
  \big[radd/0]_(s : 'S_n) ((-(1:R)) ^+ s * \prod_(i < n) A i (s i)).
Global Instance determinant_morph n : Morphism (Equivalence.equiv==>Equivalence.equiv) (@determinant n).
Proof.
move=> n A B eqAB; rewrite /determinant; apply eq_bigr => s _.
apply rmul_morph; first by reflexivity.
by apply eq_bigr => i _; apply eqAB.
Qed.

Notation "'\det' A" := (determinant A).

Definition cofactor n A (i j : 'I_n) : R :=
  (-(1:R)) ^+ (i + j) * \det (mx_row' i (mx_col' j A)).

Definition adjugate n A := \matrix_(i, j < n) (cofactor A j i : R).

Lemma determinant_multilinear : forall n (A B C : 'M_n) i0 b c,
    mx_row i0 A === b *m: mx_row i0 B +m c *m: mx_row i0 C ->
    mx_row' i0 B === mx_row' i0 A ->
    mx_row' i0 C === mx_row' i0 A ->
  \det A === b * \det B + c * \det C.
Proof.
move=> n A B C i0 b c; rewrite <- (mx_row_id (_ +m _)); move/mx_row_eq=> ABC.
move/mx_row'_eq=> BA; move/mx_row'_eq=> CA; rewrite/determinant.
setoid_rewrite (big_distrr _ b); setoid_rewrite (big_distrr _ c).
rewrite <- big_split; apply eq_bigr => s _ /=.
have Heq : forall x y z, req (b * (z * x) + c * (z * y)) (z * (b * x + c * y)) by move=> x y z; ring.
rewrite -> Heq.
apply rmul_morph; first by reflexivity.
setoid_rewrite (bigD1 (j:=i0))=>//=.
rewrite -> (ABC _).
rewrite/mx_row/addmx/scalemx.
transitivity ((b * B i0 (s i0)) * \prod_(i < n | i != i0) A i (s i)
                   + c * (C i0 (s i0) * \prod_(i < n | i != i0) A i (s i))).
  set tmp := reducebig _ _ _ _ _; ring.
apply radd_morph.
  ring_simplify; apply rmul_morph; first by reflexivity.
  by apply eq_bigr => i neq; symmetry; apply BA.
ring_simplify; apply rmul_morph; first by reflexivity.
by apply eq_bigr => i neq; symmetry; apply CA.
Qed.

Lemma alternate_determinant : forall n (A : 'M_n) i1 i2,
  i1 != i2 -> A i1 === A i2 -> \det A === 0.
Proof.
move=> n A i1 i2 Di12 A12; pose r := 'I_n.
pose t := tperm i1 i2; pose tr s := (t * s)%g.
have trK : involutive tr by move=> s; rewrite /tr mulgA tperm2 mul1g.
rewrite /(\det _).
setoid_rewrite (bigID (index_enum (perm_for_finType (ordinal_finType n))) (fun s => (s : bool))) => /=.
set S1 := reducebig _ _ _ _ _; set T := S1 + _.
have: req (S1 + (- S1)) 0 by ring.
move => eq; rewrite <- eq; clear eq.
apply radd_morph; first by reflexivity.
rewrite {T}/S1.
setoid_rewrite (big_morph (op2:=radd) (idx2:=0) (phi:=ropp)); [|by move=> x y; ring|by ring|by apply radd_morph].
setoid_rewrite (reindex (h:=tr)) at 1 => /=; last by exists tr => ? _.
symmetry; apply eq_big => [s | s seven].
  by rewrite /tr odd_permM odd_tperm Di12 negbK.
rewrite odd_permM odd_tperm Di12 seven=> /=; ring_simplify.
setoid_rewrite (reindex (h:=t)) at 1=>/=; last by exists (t : _ -> _) => i _; exact: tpermK.
apply eq_bigr => i _;  rewrite permM /t.
by case: tpermP=> [H|H|H1 H2]; [rewrite -> H, (A12 _)|rewrite -> H, (A12 _)|]; reflexivity.
Qed.

Lemma det_trmx : forall n (A : 'M_n), \det A^T === \det A.
Proof.
move=> n A; pose r := 'I_n; pose ip p : 'S_n := p^-1%g.
rewrite /(\det _).
setoid_rewrite (reindex (h:=ip)) at 1 => /=; last first.
  by exists ip => s _; rewrite /ip invgK.
apply eq_bigr => s _; rewrite !odd_permV /=.
apply rmul_morph; first by reflexivity.
setoid_rewrite (reindex (h:=s)) at 1.
apply eq_bigr => i _; rewrite permK /trmx; reflexivity.
by exists (s^-1%g : _ -> _) => i _; rewrite ?permK ?permKV.
Qed.

Lemma det_perm_mx : forall n (s : 'S_n), \det (perm_mx s) === (-(1:R)) ^+s.
Proof.
move=> n s; rewrite /(\det _); setoid_rewrite (bigD1 (j:=s))=>//=.
setoid_rewrite (big1 (I:=perm_for_finType (ordinal_finType n))).
  rewrite/perm_mx; setoid_rewrite (big1 (I:=ordinal_finType n)); first by ring.
  by move=> i _; rewrite eq_refl; reflexivity.
move=> t neq; rewrite/perm_mx.
have Heq : req (\prod_(i < n) (if s i == t i then 1 else 0)) 0; last by rewrite -> Heq; ring.
case: (pickP (fun i => s i != t i)) => [i ist | Est].
  by setoid_rewrite (bigD1 (j:=i))=>//; rewrite (negbTE ist); ring.
by case/eqP:neq; apply/permP=>i; apply/eqP; move:(Est i); rewrite eq_sym; apply negbFE.
Qed.

Lemma det1 : forall n, \det (1%:M : matrix R n n) === 1.
Proof.
move=> n; rewrite <- perm_mx1, det_perm_mx, odd_perm1.
by rewrite/iter/=; reflexivity.
Qed.

Lemma det_scalemx : forall n x (A : 'M_n),
  \det (x *m: A) === x ^+ n * \det A.
Proof.
move=> n x A; rewrite/determinant.
setoid_rewrite (big_distrr (I:=perm_for_finType (ordinal_finType n)))=>/=.
apply eq_bigr => s _; ring_simplify.
setoid_rewrite <- rmul_assoc; apply rmul_morph; first by reflexivity.
rewrite/scalemx; setoid_rewrite <- (card_ord n) at 4.
setoid_rewrite big_split; apply rmul_morph; last by reflexivity.
by rewrite <- big_const; apply eq_bigr; reflexivity.
Qed.

Lemma det_mulmx : forall n (A B : 'M_n), \det (A *m B) === \det A * \det B.
Proof.
move=> n A B.
pose AB (f : {ffun _}) := \matrix_(i, j) (A i (f i) * B (f i) j).
transitivity (\sum_f \det (AB f)).
  rewrite{2}/determinant.
  setoid_rewrite (exchange_big (I:=finfun_of_finType (ordinal_finType n) (ordinal_finType n))).
  apply eq_bigr => /= s _.
  rewrite <- big_distrr => /=; apply rmul_morph; first by reflexivity.
  rewrite/mulmx.
  setoid_rewrite (bigA_distr_bigA (I:=ordinal_finType n)).
  by apply eq_bigr=>s' _; reflexivity.
pose P_inj := fun f : {ffun 'I_n -> 'I_n} => injectiveb f.
setoid_rewrite (bigID _ P_inj xpredT (fun f => \det (AB f)))=> /=.
setoid_rewrite (big1 (I:=finfun_of_finType (ordinal_finType n) (ordinal_finType n))) at 2=>[|f]; last first.
  rewrite{}/P_inj; case/injectivePn=>i0;case=>j0 neq eq; rewrite{}/AB /determinant.
  setoid_rewrite big_split; setoid_rewrite rmul_comm at 2; setoid_rewrite rmul_assoc.
  rewrite <- big_distrl; rewrite -/(\det \matrix_(i,j) B (f i) j).
  by rewrite -> (alternate_determinant neq)=>[|i]; [ring|rewrite eq; reflexivity].
setoid_rewrite (reindex (J:=perm_for_finType (ordinal_finType n)) (h:=fun s => pval s)); last first.
  have s0 : 'S_n := 1%g; pose uf (f : {ffun 'I_n -> 'I_n}) := uniq (val f).
  exists (insubd s0) => /= f Uf; first apply: val_inj; exact: insubdK.
setoid_rewrite (eq_bigl (I:=perm_for_finType (ordinal_finType n)) (P1:=fun j => P_inj (pval j)) (P2:=predT) _ (fun j => \det (AB (pval j)))); last by case.
rewrite{2}/determinant=>{P_inj}; setoid_rewrite (big_distrl _ (\det _)).
ring_simplify; apply eq_bigr=>s _; rewrite{}/AB (pvalE s) {2}/determinant.
setoid_rewrite big_distrr.
transitivity (\sum_(s' : 'S_n) (- (1)) ^+ s * (- rI) ^+ s' * (\prod_(i < n) A i (s i) *
  \prod_(i < n) B i (s' i))); last by apply eq_bigr=> j _; ring.
have : forall s' : 'S_n, req ((- rI) ^+ s * (- rI) ^+ s') ((-rI) ^+ (s * s')%g).
  by move=>s'; rewrite odd_permM; case: (odd_perm s); case: (odd_perm s')=>/=; ring.
move=>eq_puiss; setoid_rewrite eq_puiss; clear eq_puiss.
setoid_rewrite (reindex (h:=fun t => (s^-1%g * t)%g)); last first.
  by exists [eta mulg s]=>s' _ /=; [apply (mulKVg s s') | apply (mulKg s s')].
apply eq_bigr=> s' _; rewrite (mulKVg s s'); apply rmul_morph; first by reflexivity.
setoid_rewrite (reindex (h:=s)) at 3; last by exists (s^-1)%g=>i _; [rewrite permK|rewrite permKV].
setoid_rewrite big_split; apply rmul_morph; first by reflexivity.
by apply eq_bigr=>i _; rewrite -permM (mulKVg s s'); reflexivity.
Qed.

Definition lift_perm_fun n i j (s : 'S_n) k :=
  if @unlift n.+1 i k is Some k' then @lift n.+1 j (s k') else j.

Lemma lift_permK : forall n i j s,
  cancel (@lift_perm_fun n i j s) (lift_perm_fun j i s^-1%g).
Proof.
move=> n i j s k; rewrite /lift_perm_fun.
by case: (unliftP i k) => [j'|] ->; rewrite (liftK, unlift_none) ?permK.
Qed.

Definition lift_perm n i j s := perm (can_inj (@lift_permK n i j s)).

Lemma lift_perm_id : forall n i j s, lift_perm i j s i = j :> 'I_n.+1.
Proof. by move=> n i j s; rewrite permE /lift_perm_fun unlift_none. Qed.

Lemma lift_perm_lift : forall n i j s k,
  lift_perm i j s (lift i k) = lift j (s k) :> 'I_n.+1.
Proof. by move=> n i j s k; rewrite permE /lift_perm_fun liftK. Qed.

Lemma lift_permM : forall n i j k s t,
  (@lift_perm n i j s * lift_perm j k t)%g = lift_perm i k (s * t)%g.
Proof.
move=> n i j k s t; apply/permP=> i1; case: (unliftP i i1) => [i2|] ->{i1}.
  by rewrite !(permM, lift_perm_lift).
by rewrite permM !lift_perm_id.
Qed.

Lemma lift_perm1 : forall n i, @lift_perm n i i 1 = 1%g.
Proof.
by move=> n i; apply: (mulgI (lift_perm i i 1)); rewrite lift_permM !mulg1.
Qed.

Lemma lift_permV : forall n i j s,
  (@lift_perm n i j s)^-1%g = lift_perm j i s^-1.
Proof.
by move=> n i j s; apply/eqP; rewrite eq_invg_mul lift_permM mulgV lift_perm1.
Qed.

Lemma odd_lift_perm : forall n i j s,
  @lift_perm n i j s = odd i (+) odd j (+) s :> bool.
Proof.
move=> n i j s; rewrite -{1}(mul1g s) -(lift_permM _ j) odd_permM.
congr (_ (+) _); last first.
  case: (prod_tpermP s) => ts ->{s} _.
  elim: ts => [|t ts IHts] /=; first by rewrite bigops.big_nil lift_perm1 !odd_perm1.
  rewrite bigops.big_cons odd_mul_tperm -(lift_permM _ j) odd_permM {}IHts //.
  congr (_ (+) _); rewrite (_ : _ j _ = tperm (lift j t.1) (lift j t.2)).
    by rewrite odd_tperm (inj_eq (@lift_inj _ _)).
  apply/permP=> k; case: (unliftP j k) => [k'|] ->.
    rewrite lift_perm_lift inj_tperm //; exact: lift_inj.
  by rewrite lift_perm_id tpermD // eq_sym neq_lift.
suff{i j s} odd_lift0: forall k : 'I_n.+1, lift_perm ord0 k 1 = odd k :> bool.
  rewrite -!odd_lift0 -{2}invg1 -lift_permV odd_permV -odd_permM.
  by rewrite lift_permM mulg1.
move=> k; elim: {k}(k : nat) {1 3}k (erefl (k : nat)) => [|m IHm] k def_k.
  rewrite (_ : k = ord0) ?lift_perm1 ?odd_perm1 //; exact: val_inj.
have le_mn: m < n.+1 by [rewrite -def_k ltnW]; pose j := Ordinal le_mn.
rewrite -(mulg1 1)%g -(lift_permM _ j) odd_permM {}IHm // addbC.
rewrite (_ : _ k _ = tperm j k).
  by rewrite odd_tperm neq_ltn def_k leqnn.
apply/permP=> i; case: (unliftP j i) => [i'|] ->; last first.
  by rewrite lift_perm_id tpermL.
apply: ord_inj; rewrite lift_perm_lift !permE /= eq_sym -if_neg neq_lift.
rewrite fun_if -val_eqE /= def_k /bump ltn_neqAle andbC.
case: leqP => [_ | lt_i'm] /=; last by rewrite -if_neg neq_ltn leqW.
by rewrite add1n eqSS eq_sym; case: eqP.
Qed.

Lemma expand_cofactor : forall n (A : 'M_n) i j,
  cofactor A i j ===
    \sum_(s : 'S_n | s i == j) (-(1:R)) ^+ s * \prod_(k | i != k) A k (s k).
Proof.
move=> [_ [] //|n] A i0 j0; setoid_rewrite (reindex (h:=lift_perm i0 j0)); last first.
  pose ulsf i (s : 'S_n.+1) k := odflt k (unlift (s i) (s (lift i k))).
  have ulsfK: forall i (s : 'S__) k, lift (s i) (ulsf i s k) = s (lift i k).
    rewrite /ulsf => i s k; have:= neq_lift i k.
    by rewrite -(inj_eq (@perm_inj _ s)); case/unlift_some=> ? ? ->.
  have inj_ulsf: injective (ulsf i0 _).
    move=> s; apply: can_inj (ulsf (s i0) s^-1%g) _ => k'.
    by rewrite {1}/ulsf ulsfK !permK liftK.
  exists (fun s => perm (inj_ulsf s)) => [s _ | s].
    by apply/permP=> k'; rewrite permE /ulsf lift_perm_lift lift_perm_id liftK.
  move/(s _ =P _) => si0; apply/permP=> k.
  case: (unliftP i0 k) => [k'|] ->; rewrite ?lift_perm_id //.
  by rewrite lift_perm_lift -si0 permE ulsfK.
rewrite /cofactor /determinant.
setoid_rewrite (big_distrr (I:=perm_for_finType (ordinal_finType (predn (S n)))))=> /=.
apply eq_big => [s | s _]; first by rewrite lift_perm_id eqxx.
have Heq : forall i, req ((-rI) ^+ i) ((-rI) ^+ (odd i)).
  elim=>[|i]//=; first by reflexivity.
  by case: (odd i)=>/= H; simpl; ring_simplify; rewrite -> H; ring.
rewrite -> Heq, odd_lift_perm, <- odd_add, (Rmul_assoc r_rt).
apply rmul_morph; first by case: (odd (i0 + j0)); case (odd_perm s)=>//=; ring.
case: (pickP 'I_n) => [k0 _ | n0]; last first.
  setoid_rewrite (big1 (I:=ordinal_finType n))=>[|i _]; last by have:= n0 i.
  setoid_rewrite (big1 (I:=ordinal_finType (S n)))=>[|j]; first by reflexivity.
  by case/unlift_some=> i; have:= n0 i.
setoid_rewrite (reindex (h:=lift i0)).
  apply eq_big => [k | k _] /=; first by rewrite neq_lift //.
  by rewrite lift_perm_lift; reflexivity.
exists (fun k => odflt k0 (unlift i0 k)) => k; first by rewrite liftK.
by case/unlift_some=> k' -> ->.
Qed.

Lemma expand_det_row : forall n (A : 'M_n) i0,
  \det A === \sum_j A i0 j * cofactor A i0 j.
Proof.
move=> n A i0; rewrite /(\det A).
setoid_rewrite (partition_big (P:=predT) (p:=fun s : 'S_n => s i0) (Q:=predT))=>//.
apply eq_bigr => j0 _; rewrite -> expand_cofactor.
setoid_rewrite (big_distrr _ (A i0 j0)).
apply eq_bigr => s; move/eqP=> Dsi0.
setoid_rewrite (bigID _ (pred1 i0)) at 1=>/=.
setoid_rewrite (big_pred1_eq (I:=ordinal_finType n)).
rewrite Dsi0; ring_simplify.
apply rmul_morph; first by reflexivity.
by apply eq_bigl=>i; rewrite eq_sym.
Qed.

Lemma cofactor_tr : forall n (A : 'M_n) i j,
  cofactor A^T i j === cofactor A j i.
Proof.
move=> n A i j; rewrite /cofactor addnC.
apply rmul_morph; first by reflexivity.
rewrite <- det_trmx; apply determinant_morph.
by apply trmx_inj=>i' j'; apply trmxK.
Qed.

Lemma expand_det_col : forall n (A : 'M_n) j0,
  \det A === \sum_i (A i j0 * cofactor A i j0).
Proof.
move=> n A j0; rewrite <- det_trmx, (expand_det_row _ j0).
by apply eq_bigr => i _; rewrite -> cofactor_tr; reflexivity.
Qed.

Lemma mulmx_adjr : forall n (A : 'M_n), A *m adjugate A === (\det A)%:M.
Proof.
rewrite/scalar_mx=> n A i1 i2; case Di: (i1 == i2).
  rewrite -> (eqP Di), (expand_det_row _ i2)=> //=.
  by apply eq_bigr => j _; apply rmul_morph; reflexivity.
pose B := \matrix_(i, j) (if i == i2 then A i1 j else A i j).
have EBi12: pointwise_relation 'I_n req (B i1) (B i2).
  by rewrite /B Di eq_refl=>j; reflexivity.
rewrite <- (alternate_determinant (negbT Di) EBi12) at 2.
rewrite -> (expand_det_row _ i2); apply eq_bigr => j _.
rewrite /B eq_refl; apply rmul_morph; first by reflexivity.
rewrite/adjugate/cofactor; apply rmul_morph; first by reflexivity.
apply eq_bigr => s _; apply rmul_morph; first by reflexivity.
apply eq_bigr => i _; rewrite /mx_row' /mx_col'.
by rewrite eq_sym -if_neg neq_lift; reflexivity.
Qed.

Lemma trmx_adj : forall n (A : 'M_n), (adjugate A)^T === adjugate A^T.
Proof. by move=> n A i j; rewrite /adjugate; rewrite -> cofactor_tr; rewrite /trmx; reflexivity. Qed.

Lemma mulmx_adjl : forall n (A : 'M_n), adjugate A *m A === (\det A)%:M.
Proof.
move=> n A; apply trmx_inj; rewrite -> trmx_mul, trmx_adj, mulmx_adjr.
by rewrite -> det_trmx, trmx_scalar; reflexivity.
Qed.

Lemma detM : forall (n : pos_nat) (A B : 'M_n), \det (A *m B) === \det A * \det B.
Proof. move=> n; exact: det_mulmx. Qed.

Lemma det_scalar : forall n a, \det (a%:M : 'M_n) === a ^+ n.
Proof.
move=> n a.
transitivity ((a ^+ n) * rI); last by ring.
setoid_rewrite <- (det1 n) at 3; setoid_rewrite <- det_scalemx.
apply determinant_morph; rewrite <- mulmx_scalar; rewrite <- scalar_mx_mul.
by apply scalar_mx_morph; ring.
Qed.

Lemma det_scalar1 : forall a, \det (a%:M : 'M_1) === a.
Proof. by move=>a; rewrite -> (det_scalar 1 a)=> /=; ring. Qed.

Lemma det_ublock : forall n1 n2 (Aul : 'M_(n1, n1)) (Aur : 'M_(n1, n2)) (Alr : 'M_(n2, n2)),
  \det (block_mx Aul Aur (@null_mx _ _ _ _ _ _ _ _ _ _ _ _) Alr : 'M_(n1 + n2)) === \det Aul * \det Alr.
Proof.
move=> n1 n2 Aul Aur Alr; elim: n1 => [|n1 IHn1] in Aul Aur *.
  have Heq : req (\det Aul) 1.
    by rewrite <- det1; apply determinant_morph; case.
  rewrite -> Heq; ring_simplify; apply determinant_morph=> i j; rewrite/block_mx/pastemx/trmx.
  case:splitP; [ by case | move=>i'; move/val_inj ->].
  by case:splitP; [ case | move=> j'; move/val_inj ->; reflexivity].
rewrite -> (expand_det_col (block_mx Aul _ _ _) (lshift n2 ord0)).
setoid_rewrite big_split_ord=>/=.
setoid_rewrite (Radd_comm (r_rt (Ring:=r_ring))).
setoid_rewrite (big1 (I:= ordinal_finType n2))=>[|i _]; last first.
  by rewrite -> block_mxEll; rewrite /null_mx; ring.
setoid_rewrite (Radd_0_l (r_rt (Ring:=r_ring))).
setoid_rewrite (expand_det_col Aul ord0).
setoid_rewrite big_distrl.
apply eq_bigr=>i _; rewrite -> block_mxEul.
setoid_rewrite <- Rmul_assoc; last by apply r_ring.
apply rmul_morph; first by reflexivity.
rewrite/cofactor; rewrite <- (Rmul_assoc r_rt).
rewrite <- (IHn1 (mx_row' i (mx_col' ord0 Aul)) (mx_row' i Aur)).
have -> : (addn (nat_of_ord i) (@nat_of_ord (S n1) ord0) = nat_of_ord i) by done.
apply rmul_morph; first by reflexivity.
apply determinant_morph; rewrite {2}/block_mx; rewrite <- (mx_row'_paste i), (trmx_row' i).
rewrite <- (mx_col'_lshift i), (trmx_col' (lshift n2 i)); apply (mx_row'_morph (lshift n2 i)).
rewrite <- (mx_col'_lshift ord0 Aul), (trmx_col' (lshift n2 ord0) (pastemx Aul Aur)).
rewrite /block_mx; rewrite <- trmx_row', mx_row'_paste; apply trmx_morph.
apply pastemx_morph; first by reflexivity.
rewrite <- trmx_col'; apply trmx_morph; rewrite -> mx_col'_lshift.
apply pastemx_morph; last by reflexivity.
by move=> i' j'; rewrite/mx_col'/lift/null_mx; reflexivity.
Qed.

Lemma det_lblock :  forall n1 n2 Aul All Alr,
  \det (block_mx Aul '0m All Alr : 'M_(n1 + n2)) === \det Aul * \det Alr.
Proof.
move=> n1 n2 Aul All Alr.
by rewrite <- det_trmx, trmx_block, trmx0, det_ublock, !det_trmx; reflexivity.
Qed.

End ComMatrix.

Notation "\det A" := (determinant A).
Notation "\adj A" := (adjugate A).
