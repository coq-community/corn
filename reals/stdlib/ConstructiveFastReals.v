(*
Copyright © 2020 Vincent Semeria

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*)


(** Proof that CoRN's fast reals implement the standard library's
    interface ConstructiveReals. *)

Require Import Coq.Reals.Abstract.ConstructiveReals.
Require Import CoRN.model.metric2.Qmetric.
Require Import CoRN.model.metric2.CRmetric.
Require Import CoRN.reals.fast.CRFieldOps.
Require Import CoRN.reals.fast.CRArith.
Require Import CoRN.reals.fast.CRabs.
Require Import CoRN.model.totalorder.QposMinMax.
Require Import Coq.Logic.ConstructiveEpsilon.

Lemma CRltT_linear : @isLinearOrder (RegularFunction Qball) CRltT.
Proof.
  split. split.
  - intros. apply (CRlt_trans _ _ _ H) in H0.
    apply (CRlt_irrefl x H0).
  - intros. exact (CRlt_trans _ _ _ H H0).
  - apply CRlt_linear.
Qed.

Lemma CRlt_equiv : forall x y : CR,
    CRlt x y
    <-> exists n:nat, approximate x (Qpos2QposInf (1#Pos.of_nat n)) + (2#Pos.of_nat n)
             < approximate y (Qpos2QposInf (1#Pos.of_nat n)).
Proof.
  split.
  - intros H. apply CR_lt_ltT in H. destruct H as [q H].
    destruct q as [q qpos]; unfold proj1_sig in H.
    destruct q as [a b]. destruct a as [|a|a].
    exfalso; inversion qpos.
    2: exfalso; inversion qpos. clear qpos.
    assert (translate (1#b) x <= y)%CR.
    { rewrite (CRplus_le_r _ _ x) in H.
      ring_simplify in H. 
      rewrite <- CRplus_translate.
      apply (@CRle_trans _ (' (Z.pos a # b) + x)%CR).
      2: exact H.
      apply CRplus_le_r, CRle_Qle. 
      change (b <= a*b)%positive.
      apply (Pos.le_trans _ (1*b)).
      apply Pos.le_refl.
      apply Pos.mul_le_mono_r. apply Pos.le_1_l. }
    clear H a.
    exists (Pos.to_nat (5*b)).
    rewrite Pos2Nat.id.
    apply (CRle_trans (lower_CRapproximation (translate (1#b) x) (1#5*b)%Qpos))
      in H0.
    pose proof (upper_CRapproximation y (1#5*b)%Qpos) as H.
    apply (CRle_trans H0) in H. clear H0.
    apply CRle_Qle in H. simpl in H.
    rewrite Qplus_comm in H.
    unfold Qminus in H. rewrite <- Qplus_assoc in H.
    setoid_replace ((1 # b) + - (1 # b + b~0~0))
      with ((3#5*b) + (1#5*b)) in H.
    rewrite Qplus_assoc in H. apply Qplus_le_l in H.
    refine (Qlt_le_trans _ _ _ _ H).
    apply Qplus_lt_r. 
    apply Pos.mul_lt_mono_r. reflexivity.
    unfold canonical_names.equiv, stdlib_rationals.Q_eq.
    rewrite Qinv_plus_distr.
    setoid_replace (1#b) with (5#5*b) by reflexivity.
    rewrite Qinv_minus_distr. reflexivity.
  - intros [n H].
    apply CR_lt_ltT.
    apply (@CRle_lt_trans _ _ _ (upper_CRapproximation x (1#Pos.of_nat n)%Qpos)).
    refine (CRlt_le_trans _ _ _ _ (lower_CRapproximation y (1#Pos.of_nat n)%Qpos)).
    apply CRlt_Qlt. simpl.
    apply (Qplus_lt_l _ _ (1# Pos.of_nat n)).
    ring_simplify.
    refine (Qle_lt_trans _ _ _ _ H).
    apply Qplus_le_r. apply Qle_refl.
Qed.

Lemma CRlt_or_epsilon : (forall a b c d : CR,
       CRlt a b \/ CRlt c d -> (a < b)%CR + (c < d)%CR).
Proof.
  intros. 
  assert (exists n:nat,
             approximate a (Qpos2QposInf (1#Pos.of_nat n)) + (2#Pos.of_nat n)
             < approximate b (Qpos2QposInf (1#Pos.of_nat n))
             \/ approximate c (Qpos2QposInf (1#Pos.of_nat n)) + (2#Pos.of_nat n)
               < approximate d (Qpos2QposInf (1#Pos.of_nat n))).
  { destruct H.
    - apply CRlt_equiv in H. destruct H as [n H].
      exists n. left. exact H.
    - apply CRlt_equiv in H. destruct H as [n H].
      exists n. right. exact H. }
  apply constructive_indefinite_ground_description_nat in H0.
  - destruct H0 as [n H0].
    destruct (Qlt_le_dec (approximate a (Qpos2QposInf (1 # Pos.of_nat n)) + (2 # Pos.of_nat n))
                         (approximate b (Qpos2QposInf (1 # Pos.of_nat n)))).
    + left. apply CR_lt_ltT, CRlt_equiv.
      exists n. exact q.
    + right. apply CR_lt_ltT, CRlt_equiv.
      exists n. destruct H0. 2: exact H0. exfalso.
      exact (Qlt_not_le _ _ H0 q).
  - intro n. clear H0 H.
    destruct (Qlt_le_dec (approximate a (Qpos2QposInf (1 # Pos.of_nat n)) + (2 # Pos.of_nat n))
                         (approximate b (Qpos2QposInf (1 # Pos.of_nat n)))).
    left. left. exact q.
    destruct (Qlt_le_dec (approximate c (Qpos2QposInf (1 # Pos.of_nat n)) + (2 # Pos.of_nat n))
                         (approximate d (Qpos2QposInf (1 # Pos.of_nat n)))).
    left. right. exact q0.
    right. intros [H|H].
    exact (Qlt_not_le _ _ H q).
    exact (Qlt_not_le _ _ H q0). 
Qed.

Lemma CReq_nlt : forall a b : CR,
    st_eq a b
    <-> (fun x y : CR =>
         (fun x0 y0 : CR => (y0 < x0)%CR -> False) y x /\
         (fun x0 y0 : CR => (y0 < x0)%CR -> False) x y) a b.
Proof.
  split.
  - split. intro abs.
    exact (CRlt_irrefl _ (@CRltT_wd _ _ H b _ (reflexivity _) abs)).
    intro abs.
    exact (CRlt_irrefl _ (@CRltT_wd b _ (reflexivity _) _ _ H abs)).
  - intros [H H0]. apply CRle_antisym. split.
    apply CRle_not_lt in H0. exact H0.
    apply CRle_not_lt in H. exact H.
Qed.

Lemma inject_Q_CR_plus : forall q r : Q,
       (fun x y : CR =>
        (fun x0 y0 : CR => (y0 < x0)%CR -> False) y x /\
        (fun x0 y0 : CR => (y0 < x0)%CR -> False) x y)
         (' (q + r)%Q)%CR (CRplus (' q)%CR (' r)%CR).
Proof.
  intros q r. apply CReq_nlt, (CRplus_Qplus q r).
Qed.

Lemma inject_Q_CR_mult : forall q r : Q,
       (fun x y : CR =>
        (fun x0 y0 : CR => (y0 < x0)%CR -> False) y x /\
        (fun x0 y0 : CR => (y0 < x0)%CR -> False) x y)
         (' (q * r)%Q)%CR (CRmult (' q)%CR (' r)%CR).
Proof.
  intros q r. 
  apply CReq_nlt. symmetry. apply (CRmult_Qmult q r).
Qed.

Lemma CR_ring_nlt : ring_theory 0%CR 1%CR CRplus CRmult
        (fun x y : CR => CRplus x (- y)%CR) CRopp
        (fun x y : CR =>
         (fun x0 y0 : CR => (y0 < x0)%CR -> False) y x /\
         (fun x0 y0 : CR => (y0 < x0)%CR -> False) x y).
Proof.
  destruct CR_ring_theory. split.
  - intro x. apply CReq_nlt, Radd_0_l.
  - intros x y. apply CReq_nlt, Radd_comm.
  - intros x y z. apply CReq_nlt, Radd_assoc.
  - intro x. apply CReq_nlt, Rmul_1_l.
  - intros x y. apply CReq_nlt, Rmul_comm.
  - intros x y z. apply CReq_nlt, Rmul_assoc.
  - intros x y z. apply CReq_nlt, Rdistr_l.
  - intros x y. apply CReq_nlt, Rsub_def.
  - intro x. apply CReq_nlt, Ropp_def.
Qed.

Lemma CR_ring_ext_nlt : ring_eq_ext CRplus CRmult CRopp
        (fun x y : CR =>
         (fun x0 y0 : CR => (y0 < x0)%CR -> False) y x /\
         (fun x0 y0 : CR => (y0 < x0)%CR -> False) x y).
Proof.
  split.
  - intros x y H z t H0.
    apply CReq_nlt.
    apply CReq_nlt in H.
    apply CReq_nlt in H0.
    rewrite H, H0. reflexivity.
  - intros x y H z t H0.
    apply CReq_nlt.
    apply CReq_nlt in H.
    apply CReq_nlt in H0.
    rewrite H, H0. reflexivity.
  - intros x y H.
    apply CReq_nlt.
    apply CReq_nlt in H.
    rewrite H. reflexivity.
Qed.

Lemma CRmult_inv_r_nlt : (forall (r : CR)
         (rnz : (fun x y : CR => ((x < y)%CR + (y < x)%CR)%type) r 0%CR),
       (fun x y : CR =>
        (fun x0 y0 : CR => (y0 < x0)%CR -> False) y x /\
        (fun x0 y0 : CR => (y0 < x0)%CR -> False) x y)
         (CRinvT r rnz * r)%CR 1%CR).
Proof.
  intros. apply CReq_nlt.
  rewrite CRmult_comm. apply CRmult_inv_r.
Qed.

Definition CRup (x : CR)
  : {n : positive & (x < ' (Z.pos n # 1))%CR}.
Proof.
  exists (match Qnum (proj1_sig (CR_b (1#1)%Qpos x)) with
     | Z0 => 1%positive
     | Zpos p => Pos.succ p
     | Zneg p => 1%positive end).
  apply (CRle_lt_trans _ _ _ (CR_b_upperBound (1#1)%Qpos x)).
  apply CRlt_Qlt.
  destruct (CR_b (1 # 1) x), x0. simpl.
  destruct Qnum.
  - reflexivity.
  - change (p*1 < Pos.succ p * Qden)%positive.
    apply (Pos.le_lt_trans _ (p * Qden)).
    apply Pos.mul_le_mono_l. apply Pos.le_1_l.
    apply Pos.mul_lt_mono_r.
    apply Pos.lt_succ_diag_r.
  - reflexivity.
Qed.

Lemma CRabs_nlt : forall x y : CR,
    (((y < x)%CR -> False) /\ ((y < -x)%CR -> False))
    <-> ((y < CRabs x)%CR -> False).
Proof.
  split.
  - intros [H H0] H1. 
    apply CRle_not_lt in H1. contradiction. clear H2 H1.
    pose proof (CRdistance_CRle y x 0%CR) as [H2 _].
    unfold CRdistance in H2. rewrite CRopp_0, CRplus_0_r in H2.
    apply H2. clear H2. split.
    apply (CRplus_le_r _ _ y).
    apply CRle_not_lt in H.
    ring_simplify. exact H.
    apply CRle_not_lt in H0.
    rewrite (CRplus_le_r _ _ x) in H0.
    ring_simplify in H0. exact H0.
  - split.
    apply CRle_not_lt in H.
    apply CRle_not_lt.
    apply (@CRle_trans _ (CRabs x)). 2: exact H.
    apply CRle_abs.
    apply CRle_not_lt in H.
    apply CRle_not_lt.
    apply (@CRle_trans _ (CRabs x)). 2: exact H.
    rewrite <- CRabs_opp.
    apply CRle_abs. 
Qed.

Definition CRcauchy_sequence (xn : nat -> CR) : Set
  := forall p : positive,
   {n : nat
   | forall i j : nat,
     (n <= i)%nat ->
     (n <= j)%nat -> (' (1 # p) < CRabs (xn i - xn j))%CR -> False}.

Lemma Qarchimedean_le : forall q : Q, { p : positive | q <= Z.pos p # 1 }.
Proof.
  intros. destruct q as [a b]. destruct a.
  - exists xH. discriminate.
  - exists p. unfold Qle; simpl.
    apply Pos.mul_le_mono_l, Pos.le_1_l.
  - exists xH. discriminate.
Defined.

Definition CRstandard_modulus (xn : nat -> CR)
           (xncau : CRcauchy_sequence xn)
           (e : QposInf) : CR
  := match e with
     | Qpos2QposInf q
       => xn (proj1_sig (xncau (proj1_sig (Qarchimedean_le (/ proj1_sig q)))))
     | QposInfinity => 0%CR
     end.

Lemma CRstandard_regular : forall (xn : nat -> CR)
                             (xncau : CRcauchy_sequence xn),
    is_RegularFunction (@ball CR) (CRstandard_modulus xn xncau).
Proof.
  intros xn xncau e1 e2.
  apply CRabs_ball. unfold CRstandard_modulus.
  destruct (le_ge_dec
             (proj1_sig (xncau (proj1_sig (Qarchimedean_le (/ proj1_sig e1))))) 
             (proj1_sig (xncau (proj1_sig (Qarchimedean_le (/ proj1_sig e2)))))).
  - destruct (xncau (proj1_sig (Qarchimedean_le (/ proj1_sig e1)))) as [n H].
    simpl in l.
    destruct e1 as [e1 e1pos].
    destruct e2 as [e2 e2pos].
    unfold proj1_sig. specialize (H n _ (Nat.le_refl _) l).
    apply CRle_not_lt in H.
    apply (CRle_trans H). clear H. 
    apply CRle_Qle. unfold proj1_sig.
    destruct (Qarchimedean_le (/ e1)) as [p H].
    apply (Qle_trans _ (e1+0)).
    2: apply Qplus_le_r, Qlt_le_weak, e2pos.
    rewrite Qplus_0_r.
    apply (Qmult_le_l _ _ e1) in H. 2: exact e1pos.
    rewrite Qmult_inv_r in H.
    change (1#p) with (/(Z.pos p#1)).
    apply Qle_shift_inv_r. reflexivity.
    apply H.
    apply (Qpos_nonzero (exist _ e1 e1pos)).
  - destruct (xncau (proj1_sig (Qarchimedean_le (/ proj1_sig e2)))) as [n H].
    simpl in g.
    destruct e1 as [e1 e1pos].
    destruct e2 as [e2 e2pos].
    unfold proj1_sig. specialize (H _ n g (Nat.le_refl _)).
    apply CRle_not_lt in H.
    apply (CRle_trans H). clear H. 
    apply CRle_Qle. unfold proj1_sig.
    destruct (Qarchimedean_le (/ e2)) as [p H].
    apply (Qle_trans _ (0+e2)).
    2: apply Qplus_le_l, Qlt_le_weak, e1pos.
    rewrite Qplus_0_l.
    apply (Qmult_le_l _ _ e2) in H. 2: exact e2pos.
    rewrite Qmult_inv_r in H. 
    change (1#p) with (/(Z.pos p#1)).
    apply Qle_shift_inv_r. reflexivity.
    apply H.
    apply (Qpos_nonzero (exist _ e2 e2pos)).
Qed.

Lemma CRcauchy_complete : forall xn : nat -> CR,
  CRcauchy_sequence xn ->
  {l : CR &
  forall p : positive,
  {n : nat
  | forall i : nat,
    (n <= i)%nat -> (' (1 # p) < CRabs (xn i - l))%CR -> False}}.
Proof.
  intros xn xncau.
  exists (Cjoin_fun (Build_RegularFunction (CRstandard_regular xn xncau))).
  intro p.
  exists (proj1_sig (xncau (2*p)%positive)).
  intros i H. apply CRle_not_lt.
  apply (CRle_trans (CRdistance_triangle _ (CRstandard_modulus xn xncau (Qpos2QposInf (1#2*p))) _)).
  apply (@CRle_trans _ ('(1#2*p) + '(1#2*p))%CR).
  apply CRplus_le_compat.
  - simpl.
    destruct (xncau (2*p)%positive) as [n H0] eqn:des.
    apply CRle_not_lt. apply H0.
    exact H. clear H i.
    simpl in des. rewrite des. apply Nat.le_refl.
  - apply CRabs_ball, ball_sym.
    apply (Cjoin_ball (Build_RegularFunction (CRstandard_regular xn xncau))
                      (1#2*p)).
  - rewrite CRplus_Qplus.
    apply CRle_Qle.
    rewrite Qinv_plus_distr.
    apply Z.le_refl.
Qed. 

Definition FastRealsConstructive : ConstructiveReals
  := Build_ConstructiveReals
       (RegularFunction Qball)
       CRltT CRltT_linear CRlt
       (fun x y => fst (CR_lt_ltT x y))
       (fun x y => snd (CR_lt_ltT x y))
       CRlt_or_epsilon
       inject_Q_CR CRlt_Qlt Qlt_from_CRlt
       CRplus CRopp CRmult
       inject_Q_CR_plus inject_Q_CR_mult
       CR_ring_nlt CR_ring_ext_nlt
       (CRlt_Qlt 0 1 eq_refl)
       (fun r r1 r2 => fst (CRplus_lt_l r1 r2 r))
       (fun r r1 r2 => snd (CRplus_lt_l r1 r2 r))
       CRmult_lt_0_compat CRinvT
       CRmult_inv_r_nlt CRinv_0_lt_compat
       CRlt_Qmid CRup CRabs CRabs_nlt
       CRcauchy_complete.

