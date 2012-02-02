(*
Copyright © 2006-2008 Russell O’Connor

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

Require Export CPolynomials.
Require Import CSums.
Require Import Rational.
Require Import Qordfield.
Require Import COrdFields2.
Require Import CRing_Homomorphisms.
Require Vector.
Export Vector.VectorNotations.

Set Implicit Arguments.

(**
** Bernstein Polynomials
*)

Section Bernstein.
Opaque cpoly_cring.

Variable R : CRing.
Add Ring R : (CRing_Ring R) (preprocess [unfold cg_minus;simpl]).
Add Ring cpolycring_th : (CRing_Ring (cpoly_cring R))  (preprocess [unfold cg_minus;simpl]).
(** [Bernstein n i] is the ith element of the n dimensional Bernstein basis *)

Fixpoint Bernstein (n i:nat) {struct n}: (i <= n) -> cpoly_cring R :=
match n return (i <= n) -> cpoly_cring R  with
 O => fun _ => [1]
|S n' =>
  match i return (i <= S n') -> cpoly_cring R  with
   O => fun _ => ([1][-]_X_)[*](Bernstein (le_O_n n'))
  |S i' => fun p =>
    match (le_lt_eq_dec _ _ p) with
     | left p' => ([1][-]_X_)[*](Bernstein (lt_n_Sm_le _ _ p'))[+]_X_[*](Bernstein (le_S_n _ _ p))
     | right _ => _X_[*](Bernstein (lt_n_Sm_le _ _ p))
    end
  end
end.

(** These lemmas provide an induction principle for polynomials using the Bernstien basis *)
Lemma Bernstein_inv1 : forall n i (H:i < n) (H0:S i <= S n),
 Bernstein H0[=]([1][-]_X_)[*](Bernstein (lt_n_Sm_le _ _ (lt_n_S _ _ H)))[+]_X_[*](Bernstein (le_S_n _ _ H0)).
Proof.
 intros n i H H0.
 simpl (Bernstein H0).
 destruct (le_lt_eq_dec _ _ H0).
  replace (lt_n_Sm_le (S i) n l) with (lt_n_Sm_le _ _ (lt_n_S _ _ H)) by apply le_irrelevent.
  reflexivity.
 elimtype False; omega.
Qed.

Lemma Bernstein_inv2 : forall n (H:S n <= S n),
 Bernstein H[=]_X_[*](Bernstein (le_S_n _ _ H)).
Proof.
 intros n H.
 simpl (Bernstein H).
 destruct (le_lt_eq_dec _ _ H).
  elimtype False; omega.
 replace (lt_n_Sm_le n n H) with (le_S_n n n H) by apply le_irrelevent.
 reflexivity.
Qed.

Lemma Bernstein_ind : forall n i (H:i<=n) (P : nat -> nat -> cpoly_cring R -> Prop),
P 0 0 [1] ->
(forall n p, P n 0 p -> P (S n) 0 (([1][-]_X_)[*]p)) ->
(forall n p, P n n p -> P (S n) (S n) (_X_[*]p)) ->
(forall i n p q, (i < n) -> P n i p -> P n (S i) q -> P (S n) (S i) (([1][-]_X_)[*]q[+]_X_[*]p)) ->
P n i (Bernstein H).
Proof.
 intros n i H P H0 H1 H2 H3.
 revert n i H.
 induction n; intros [|i] H.
    apply H0.
   elimtype False; auto with *.
  apply H1.
  apply IHn.
 simpl.
 destruct (le_lt_eq_dec (S i) (S n)).
  apply H3; auto with *.
 inversion e.
 revert H.
 rewrite H5.
 intros H.
 apply H2.
 auto with *.
Qed.

(** [1] important property of the Bernstein basis is that its elements form a partition of unity *)

Lemma partitionOfUnity : forall n, @Sumx (cpoly_cring R) _ (fun i H => Bernstein (lt_n_Sm_le i n H)) [=][1].
Proof.
 induction n.
  reflexivity.
 set (A:=(fun (i : nat) (H : i < S n) => Bernstein (lt_n_Sm_le i n H))) in *.
 set (B:=(fun i => ([1][-]_X_)[*](part_tot_nat_fun (cpoly_cring R) _ A i)[+]_X_[*]match i with O => [0] | S i' => (part_tot_nat_fun _ _ A i') end)).
 rewrite -> (fun a b => Sumx_Sum0 _ a b B).
  unfold B.
  rewrite -> Sum0_plus_Sum0.
  do 2 rewrite -> mult_distr_sum0_lft.
  rewrite -> Sumx_to_Sum in IHn; auto with *.
   setoid_replace (Sum0 (S (S n)) (part_tot_nat_fun (cpoly_cring R) (S n) A))
     with (Sum0 (S (S n)) (part_tot_nat_fun (cpoly_cring R) (S n) A)[-][0]) using relation (@st_eq (cpoly_cring R)) by ring.
   change (Sum0 (S (S n)) (part_tot_nat_fun (cpoly_cring R) (S n) A)[-][0])
     with (Sum 0 (S n) (part_tot_nat_fun (cpoly_cring R) (S n) A)).
   set (C:=(fun i : nat => match i with | 0 => ([0] : cpoly_cring R)
     | S i' => part_tot_nat_fun (cpoly_cring R) (S n) A i' end)).
   setoid_replace (Sum0 (S (S n)) C) with (Sum0 (S (S n)) C[-][0]) using relation (@st_eq (cpoly_cring R)) by ring.
   change (Sum0 (S (S n)) C[-][0]) with (Sum 0 (S n) C).
   rewrite -> Sum_last.
   rewrite -> IHn.
   replace (part_tot_nat_fun (cpoly_cring R) (S n) A (S n)) with ([0]:cpoly_cring R).
    rewrite -> Sum_first.
    change (C 0) with ([0]:cpoly_cring R).
    rewrite <- (Sum_shift _ (part_tot_nat_fun (cpoly_cring R) (S n) A)) by reflexivity.
     rewrite -> IHn by ring.
    ring.
   unfold part_tot_nat_fun.
   destruct (le_lt_dec (S n) (S n)).
    reflexivity.
   elimtype False; omega.
  intros i j Hij. subst.
  intros Hi Hj.
  unfold A.
  replace (lt_n_Sm_le j n Hi) with (lt_n_Sm_le j n Hj) by apply le_irrelevent.
  apply eq_reflexive.
 destruct i; intros Hi; unfold B, A, part_tot_nat_fun.
  simpl. symmetry.
  rewrite <- (le_irrelevent _ _ (le_0_n _) _).
  ring.
 destruct (le_lt_dec (S n) i).
  elimtype False; omega.
 destruct (le_lt_dec (S n) (S i)); simpl (Bernstein (lt_n_Sm_le (S i) (S n) Hi));
   destruct (le_lt_eq_dec (S i) (S n) (lt_n_Sm_le (S i) (S n) Hi)).
    elimtype False; omega.
   replace  (lt_n_Sm_le i n (lt_n_Sm_le (S i) (S n) Hi)) with (lt_n_Sm_le i n l) by apply le_irrelevent.
  ring.
  replace (le_S_n i n (lt_n_Sm_le (S i) (S n) Hi)) with (lt_n_Sm_le i n l) by apply le_irrelevent.
  replace l1 with l0 by apply le_irrelevent.
  reflexivity.
 elimtype False; omega.
Qed.

Lemma RaiseDegreeA : forall n i (H:i<=n), (nring (S n))[*]_X_[*]Bernstein H[=](nring (S i))[*]Bernstein (le_n_S _ _ H).
Proof.
 induction n.
  intros [|i] H; [|elimtype False; omega].
  repeat split; ring.
 intros i H.
 change (nring (S (S n)):cpoly_cring R) with (nring (S n)[+][1]:cpoly_cring R).
 rstepl (nring (S n)[*]_X_[*]Bernstein H[+]_X_[*]Bernstein H).
 destruct i as [|i].
  simpl (Bernstein H) at 1.
  rstepl (([1][-]_X_)[*](nring (S n)[*]_X_[*]Bernstein (le_O_n n))[+] _X_[*]Bernstein H).
  rewrite -> IHn.
  rstepl ((([1][-]_X_)[*]Bernstein (le_n_S _ _ (le_O_n n))[+]_X_[*]Bernstein H)).
  rstepr (Bernstein (le_n_S 0 (S n) H)).
  set (le_n_S 0 n (le_0_n n)).
  rewrite (Bernstein_inv1 l).
  rewrite (le_irrelevent _ _ (lt_n_Sm_le 1 (S n) (lt_n_S 0 (S n) l)) l).
  rewrite (le_irrelevent _ _ H (le_S_n 0 (S n) (le_n_S 0 (S n) H))).
  reflexivity.
 simpl (Bernstein H) at 1.
 destruct (le_lt_eq_dec _ _ H).
  rstepl (([1][-]_X_)[*](nring (S n)[*]_X_[*]Bernstein (lt_n_Sm_le (S i) n l))[+]
    _X_[*](nring (S n)[*]_X_[*]Bernstein (le_S_n i n H))[+] _X_[*]Bernstein H).
  do 2 rewrite -> IHn.
  change (nring (S (S i)):cpoly_cring R) with (nring (S i)[+][1]:cpoly_cring R).
  set (l0:= (le_n_S (S i) n (lt_n_Sm_le (S i) n l))).
  replace (le_n_S i n (le_S_n i n H)) with H by apply le_irrelevent.
  rstepl ((nring (S i)[+][1])[*](([1][-]_X_)[*]Bernstein l0[+]_X_[*]Bernstein H)).
  rewrite (Bernstein_inv1 l).
  replace (lt_n_Sm_le (S (S i)) (S n) (lt_n_S (S i) (S n) l)) with l0 by apply le_irrelevent.
  replace (le_S_n (S i) (S n) (le_n_S (S i) (S n) H)) with H by apply le_irrelevent.
  reflexivity.
 rstepl (_X_[*](nring (S n)[*]_X_[*]Bernstein (lt_n_Sm_le _ _ H))[+] _X_[*]Bernstein H).
 rewrite IHn.
 replace (le_n_S i n (lt_n_Sm_le i n H)) with H by apply le_irrelevent.
 revert H.
 inversion_clear e.
 intros H.
 rewrite -> (Bernstein_inv2 (le_n_S _ _ H)).
 replace (le_S_n (S n) (S n) (le_n_S (S n) (S n) H)) with H by apply le_irrelevent.
 change (nring (S (S n)):cpoly_cring R) with (nring (S n)[+][1]:cpoly_cring R).
 ring.
Qed.

Lemma RaiseDegreeB : forall n i (H:i<=n), (nring (S n))[*]([1][-]_X_)[*]Bernstein H[=](nring (S n - i))[*]Bernstein (le_S _ _ H).
Proof.
 induction n.
  intros [|i] H; [|elimtype False; omega].
  repeat split; ring.
 intros i H.
 change (nring (S (S n)):cpoly_cring R) with (nring (S n)[+][1]:cpoly_cring R).
 set (X0:=([1][-](@cpoly_var R))) in *.
 rstepl (nring (S n)[*]X0[*]Bernstein H[+]X0[*]Bernstein H).
 destruct i as [|i].
  simpl (Bernstein H) at 1.
  fold X0.
  rstepl (X0[*](nring (S n)[*]X0[*]Bernstein (le_O_n n))[+] X0[*]Bernstein H).
  rewrite -> IHn.
  replace (le_S 0 n (le_O_n n)) with H by apply le_irrelevent.
  simpl (S n - 0).
  change (nring (S (S n) - 0):cpoly_cring R) with (nring (S n)[+][1]:cpoly_cring R).
  rstepl ((nring (S n))[*](X0[*]Bernstein H)[+]X0[*]Bernstein H).
  change (Bernstein (le_S _ _ H)) with (X0[*]Bernstein (le_O_n (S n))).
  replace (le_O_n (S n)) with H by apply le_irrelevent.
  ring.
 simpl (Bernstein H) at 1.
 destruct (le_lt_eq_dec _ _ H).
  fold X0.
  rstepl (X0[*](nring (S n)[*]X0[*]Bernstein (lt_n_Sm_le (S i) n l))[+]
    _X_[*](nring (S n)[*]X0[*]Bernstein (le_S_n i n H))[+] X0[*]Bernstein H).
  do 2 rewrite -> IHn.
  rewrite <- (minus_Sn_m n i) by auto with *.
  rewrite <-(minus_Sn_m (S n) (S i)) by auto with *.
  replace (S n - S i) with (n - i) by auto with *.
  change (nring (S (n - i)):cpoly_cring R) with (nring (n - i)[+][1]:cpoly_cring R).
  replace (le_S (S i) n (lt_n_Sm_le (S i) n l)) with H by apply le_irrelevent.
  set (l0:= (le_S i n (le_S_n i n H))).
  rstepl ((nring (n - i)[+][1])[*](X0[*]Bernstein H[+]_X_[*]Bernstein l0)).
  rewrite -> (Bernstein_inv1 H).
  fold X0.
  replace (lt_n_Sm_le _ _ (lt_n_S _ _ H)) with H by apply le_irrelevent.
  replace (le_S_n _ _ (le_S (S i) (S n) H)) with l0 by apply le_irrelevent.
  reflexivity.
 revert H.
 inversion e.
 clear - IHn.
 intros H.
 assert (l:(n < (S n))) by auto.
 rewrite -> (Bernstein_inv1 l).
 fold X0.
 rstepl (_X_[*](nring (S n)[*]X0[*]Bernstein (lt_n_Sm_le _ _ H))[+] X0[*]Bernstein H).
 rewrite -> IHn.
 replace (S n - n) with 1 by auto with *.
 replace (S (S n) - S n) with 1 by auto with *.
 replace (le_S_n n (S n) (le_S (S n) (S n) H))
   with (le_S n n (lt_n_Sm_le n n H)) by apply le_irrelevent.
 replace (lt_n_Sm_le (S n) (S n) (lt_n_S n (S n) l)) with H by apply le_irrelevent.
 ring.
Qed.

Lemma RaiseDegree : forall n i (H: i<=n),
 (nring (S n))[*]Bernstein H[=](nring (S n - i))[*]Bernstein (le_S _ _ H)[+](nring (S i))[*]Bernstein (le_n_S _ _ H).
Proof.
 intros n i H.
 rstepl ((nring (S n))[*]([1][-]_X_)[*]Bernstein H[+](nring (S n))[*]_X_[*]Bernstein H).
 rewrite RaiseDegreeA, RaiseDegreeB. reflexivity.
Qed.

Opaque Bernstein.

(** Given a vector of coefficents for a polynomial in the Bernstein basis, return the polynomial *)

Fixpoint evalBernsteinBasisH (n i:nat) (v:Vector.t R i) : i <= n -> cpoly_cring R :=
match v in Vector.t _ i return i <= n -> cpoly_cring R with
|Vector.nil => fun _ => [0]
|Vector.cons a i' v' =>
  match n as n return (S i' <= n) -> cpoly_cring R with
  | O => fun p => False_rect _ (le_Sn_O _ p)
  | S n' => fun p => _C_ a[*]Bernstein (le_S_n _ _ p)[+]evalBernsteinBasisH v' (le_Sn_le _ _ p)
  end
end.

Definition evalBernsteinBasis (n:nat) (v:Vector.t R n) : cpoly_cring R :=
evalBernsteinBasisH v (le_refl n).

(** The coefficents are linear *)
Opaque polyconst.

Section obsolute_stuff_from_Bvector.
Variable A : Type.
Variable (g : A -> A -> A).
Lemma Vbinary : forall (n : nat), Vector.t A n -> Vector.t A n -> Vector.t A n.
Proof.
  induction n as [| n h]; intros v v0.
  apply Vector.nil.

  inversion v as [| a n0 H0 H1]; inversion v0 as [| a0 n1 H2 H3].
  exact (Vector.cons A (g a a0) n (h H0 H2)).
Defined.

Definition Vid n : Vector.t A n -> Vector.t A n :=
  match n with
  | O => fun _ => Vector.nil A
  | S n' => fun v : Vector.t A (S n') => Vector.cons A (Vector.hd v) _ (Vector.tl v)
  end.

Lemma Vid_eq : forall (n:nat) (v:Vector.t A n), v = Vid v.
Proof.
  destruct v; auto.
Qed.

Lemma VSn_eq :
  forall (n : nat) (v : Vector.t A (S n)), v = Vector.cons A (Vector.hd v) _ (Vector.tl v).
Proof.
  intros.
  exact (Vid_eq v).
Qed.

Lemma V0_eq : forall (v : Vector.t A 0), v = Vector.nil A.
Proof.
  intros.
  exact (Vid_eq v).
Qed.
End obsolute_stuff_from_Bvector.

Lemma evalBernsteinBasisPlus : forall n (v1 v2: Vector.t R n),
evalBernsteinBasis (Vbinary (fun (x y:R)=>x[+]y) v1 v2)[=]evalBernsteinBasis v1[+]evalBernsteinBasis v2.
Proof.
 unfold evalBernsteinBasis.
 intros n.
 generalize (le_refl n).
 generalize n at 1 3 4  6 7  9 11.
 intros i.
 induction i.
  intros l v1 v2.
  rewrite (V0_eq v1), (V0_eq v2). ring.
 intros l v1 v2.
 destruct n as [|n].
  elimtype False; auto with *.
 rewrite (VSn_eq v1), (VSn_eq v2).
 simpl.
 rewrite IHi.
 rewrite -> c_plus. ring.
Qed.

Lemma evalBernsteinBasisConst : forall n c,
evalBernsteinBasis (Vector.const c (S n))[=]_C_ c.
Proof.
 intros n c.
 stepr (evalBernsteinBasis (Vector.const c (S n))[+]_C_ c[*]Sum (S n) n (part_tot_nat_fun _ _ (fun (i : nat) (H : i < S n) => Bernstein (lt_n_Sm_le i n H)))).
  rewrite -> Sum_empty by auto with *.
  ring.
 unfold evalBernsteinBasis.
 generalize (le_refl (S n)).
 generalize (S n) at 1 4 5 6.
 intros i l.
 induction i.
  rstepr (_C_ c[*][1]).
  rewrite <- (partitionOfUnity n).
  rewrite -> Sumx_to_Sum; auto with *.
  intros i j Hij.
  rewrite Hij.
  intros H H'.
  replace (lt_n_Sm_le j n H) with (lt_n_Sm_le j n H') by apply le_irrelevent.
  reflexivity.
 rstepl (evalBernsteinBasisH (Vector.const c i) (le_Sn_le i (S n) l)[+]
   _C_ c[*](Bernstein (le_S_n i n l)[+] Sum (S i) n (part_tot_nat_fun (cpoly_cring R) (S n)
     (fun (i0 : nat) (H : i0 < S n) => Bernstein (lt_n_Sm_le i0 n H))))).
 replace (Bernstein (le_S_n _ _ l)) with (part_tot_nat_fun (cpoly_cring R) (S n)
   (fun (i0 : nat) (H : i0 < S n) => Bernstein (lt_n_Sm_le i0 n H)) i).
  rewrite <- Sum_first.
  apply IHi.
 clear - i.
 unfold part_tot_nat_fun.
 destruct (le_lt_dec (S n) i).
  elimtype False; auto with *.
 simpl.
 replace (lt_n_Sm_le _ _ l0) with (le_S_n _ _ l) by apply le_irrelevent.
 reflexivity.
Qed.

Variable eta : RingHom Q_as_CRing R.

Opaque Qred.
Opaque Q_as_CRing.
Opaque Vbinary.
Opaque Vector.const.

(** To convert a polynomial to the Bernstein basis, we need to know how to
multiply a bernstein basis element by [_X_] can convert it to the Bernstein basis.
At this point we must work with rational coeffients.  So we assume there is a
ring homomorphism from [Q] to R *)

Fixpoint BernsteinBasisTimesXH (n i:nat) (v:Vector.t R i) : i <= n -> Vector.t R (S i) :=
match v in Vector.t _ i return i <= n -> Vector.t R (S i) with
| Vector.nil => fun _ => Vector.cons _ [0] _ (Vector.nil _)
| Vector.cons a i' v' => match n as n return S i' <= n -> Vector.t R (S (S i')) with
  | O => fun p => False_rect _ (le_Sn_O _ p)
  | S n' => fun p => Vector.cons _ (eta(Qred (i#P_of_succ_nat n'))[*]a) _ (BernsteinBasisTimesXH v' (le_Sn_le _ _ p))
  end
end.

Definition BernsteinBasisTimesX (n:nat) (v:Vector.t R n) : Vector.t R (S n) :=
BernsteinBasisTimesXH v (le_refl n).

Lemma evalBernsteinBasisTimesX : forall n (v:Vector.t R n),
 evalBernsteinBasis (BernsteinBasisTimesX v)[=]_X_[*]evalBernsteinBasis v.
Proof.
 intros n.
 unfold evalBernsteinBasis, BernsteinBasisTimesX.
 generalize (le_refl (S n)) (le_refl n).
 generalize n at 1 3 5 7 9 11.
 intros i.
 induction i.
  intros l l0 v.
  rewrite (V0_eq v).
  simpl.
  rewrite <- c_zero. ring.
 intros l l0 v.
 destruct n as [|n].
  elimtype False; auto with *.
 rewrite (VSn_eq v).
 simpl.
 rewrite -> IHi.
 rewrite -> c_mult.
 rewrite -> ring_dist_unfolded.
 apply csbf_wd; try reflexivity.
 set (A:= (_C_ (eta (Qred (Qmake (Zpos (P_of_succ_nat i)) (P_of_succ_nat n)))))).
 rstepl (_C_ (Vector.hd v)[*](A[*]Bernstein (le_S_n (S i) (S n) l))).
 rstepr (_C_ (Vector.hd v)[*](_X_[*]Bernstein (le_S_n i n l0))).
 apply mult_wdr.
 unfold A; clear A.
 assert (Hn : (nring (S n):Q)[#][0]).
  stepl (S n:Q).
   simpl.
   unfold Qap, Qeq.
   auto with *.
  symmetry; apply nring_Q.
 setoid_replace (Qred (P_of_succ_nat i # P_of_succ_nat n))
   with (([1][/](nring (S n))[//]Hn)[*](nring (S i))).
  set (eta':=RHcompose _ _ _ _C_ eta).
  change (_C_ (eta (([1][/]nring (S n)[//]Hn)[*]nring (S i))))
    with ((eta' (([1][/]nring (S n)[//]Hn)[*]nring (S i))):cpoly_cring R).
  rewrite -> rh_pres_mult.
  rewrite -> rh_pres_nring.
  rewrite <- mult_assoc_unfolded.
  replace (le_S_n (S i) (S n) l) with (le_n_S _ _ (le_S_n i n l0)) by apply le_irrelevent.
  rewrite <- RaiseDegreeA.
  rewrite <- (@rh_pres_nring _ _ eta').
  rewrite <- mult_assoc_unfolded.
  rewrite -> mult_assoc_unfolded.
  rewrite <- rh_pres_mult.
  setoid_replace (eta' (([1][/]nring (S n)[//]Hn)[*]nring (S n))) with ([1]:cpoly_cring R).
   ring.
  rewrite <- (@rh_pres_unit _ _ eta').
  apply csf_wd.
  apply (@div_1 Q_as_CField).
 rewrite -> Qred_correct.
 rewrite -> Qmake_Qdiv.
 change (Zpos (P_of_succ_nat n)) with ((S n):Z).
 rewrite <- (nring_Q (S n)).
 change (Zpos (P_of_succ_nat i)) with ((S i):Z).
 rewrite <- (nring_Q (S i)).
 change (nring (S i)/nring (S n) == (1/(nring (S n)))*nring (S i))%Q.
 field.
 apply Hn.
Qed.

(** Convert a polynomial to the Bernstein basis *)
Fixpoint BernsteinCoefficents (p:cpoly_cring R) : sigT (Vector.t R) :=
match p with
| cpoly_zero => existT _ _ (Vector.nil R)
| cpoly_linear c p' =>
  let (n', b') := (BernsteinCoefficents p') in
  existT _ _  (Vbinary (fun (x y:R)=>x[+]y) (Vector.const c _) (BernsteinBasisTimesX b'))
end.

Lemma evalBernsteinCoefficents : forall p, (let (n,b) := BernsteinCoefficents p in evalBernsteinBasis b)[=]p.
Proof.
 induction p.
  reflexivity.
 simpl.
 destruct (BernsteinCoefficents p).
 rewrite -> evalBernsteinBasisPlus.
 rewrite -> evalBernsteinBasisConst.
 rewrite -> evalBernsteinBasisTimesX.
 rewrite -> IHp.
 rewrite -> poly_linear.
 ring.
Qed.

End Bernstein.

Section BernsteinOrdField.

Variable F : COrdField.

Opaque cpoly_cring.

(** A second important property of the Bernstein polynomials is that they
are all non-negative on the unit interval. *)

Lemma BernsteinNonNeg : forall x:F, [0] [<=] x -> x [<=] [1] ->
forall n i (p:le i n), [0][<=](Bernstein F p)!x.
Proof.
 intros x Hx0 Hx1.
 induction n.
  intros i p.
  simpl (Bernstein F p).
  autorewrite with apply.
  auto with *.
 intros [|i] p; simpl (Bernstein F p).
  autorewrite with apply.
  auto with *.
 destruct (le_lt_eq_dec (S i) (S n) p); autorewrite with apply; auto with *.
Qed.

End BernsteinOrdField.
