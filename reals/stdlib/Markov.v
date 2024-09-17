(*
Copyright © 2020 Vincent Semeria

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*)

(** Consequence of the Markov principle on constructive reals. *)

From Coq Require Import QArith_base.
From Coq Require Import ConstructiveReals.
From Coq Require Import ConstructiveAbs.

Local Open Scope ConstructiveReals.

(* This axiom has computational content :
   run the unbounded search Pdec 0, Pdec 1, ...
   and the last hypothesis is a proof of termination. *)
Definition Markov : Prop
  := forall (P : nat -> Prop),
    (forall n:nat, {P n} + {~P n})
    -> (~~exists n:nat, P n)
    -> exists n:nat, P n.

Lemma Markov_notnot_lt_0 : forall {R : ConstructiveReals} (x : CRcarrier R),
    Markov -> (~~CRltProp R 0 x) -> CRltProp R 0 x.
Proof.
  intro R.
  assert (forall (x : CRcarrier R) (n:nat),
             x - CR_of_Q R (1#Pos.of_nat n) < x) as bumpDown.
  { intros x n.
    apply (CRlt_le_trans _ (x-0)).
    apply CRplus_lt_compat_l.
    apply CRopp_gt_lt_contravar, CR_of_Q_lt.
    reflexivity.
    unfold CRminus. rewrite CRopp_0, CRplus_0_r.
    apply CRle_refl. }
  intros x markov xpos. 
  assert (exists n:nat, Qlt 0 (let (q,_) := CR_Q_dense R _ _ (bumpDown x n) in q)).
  { apply markov.
    - intro n.
      destruct (CR_Q_dense R _ _ (bumpDown x n)) as [q H].
      destruct (Qlt_le_dec 0 q).
      left. exact q0. right. apply (Qle_not_lt _ _ q0).
    - intro abs. contradict xpos; intro xpos.
      apply CRltEpsilon in xpos.
      contradict abs.
      destruct (CR_archimedean R (CRinv R x (inr xpos))) as [n H].
      exists (Pos.to_nat n).
      destruct ( CR_Q_dense R (x - CR_of_Q R (1 # Pos.of_nat (Pos.to_nat n)))%ConstructiveReals
        x (bumpDown x (Pos.to_nat n))) as [q H0].
      apply (lt_CR_of_Q R).
      refine (CRle_lt_trans _ _ _ _ (fst H0)).
      clear H0 q.
      rewrite Pos2Nat.id.
      apply (CRplus_le_reg_r (CR_of_Q R (1#n))).
      unfold CRminus.
      rewrite CRplus_0_l.
      rewrite CRplus_assoc.
      rewrite CRplus_opp_l, CRplus_0_r.
      apply CRlt_asym in H.
      apply (CRmult_le_compat_l x) in H.
      rewrite CRinv_r in H.
      apply (CRmult_le_compat_r (CR_of_Q R (1#n))) in H.
      rewrite CRmult_1_l, CRmult_assoc, <- CR_of_Q_mult in H.
      setoid_replace ((Z.pos n # 1) * (1 # n))%Q with 1%Q in H.
      rewrite CRmult_1_r in H. exact H.
      unfold Qeq; simpl.
      rewrite Pos.mul_1_r, Pos.mul_1_r. reflexivity.
      apply CR_of_Q_le; discriminate.
      apply CRlt_asym, xpos. }
  clear xpos.
  destruct H as [n H].
  destruct (CR_Q_dense R _ _ (bumpDown x n)) as [q H0].
  apply CRltForget.
  apply (CRlt_trans _ (CR_of_Q R q)).
  apply CR_of_Q_lt, H. 
  apply H0.
Qed.

Lemma Markov_notnot_lt : forall {R : ConstructiveReals} (x y : CRcarrier R),
    Markov -> (~~CRltProp R x y) -> CRltProp R x y.
Proof.
  intros. apply CRltForget.
  apply (CRplus_lt_reg_r (-x)).
  apply (CRle_lt_trans _ 0).
  rewrite CRplus_opp_r. apply CRle_refl.
  apply CRltEpsilon.
  apply (Markov_notnot_lt_0 (y-x) H).
  intro abs. contradict H0; intro H0.
  contradict abs.
  apply CRltForget.
  apply (CRplus_lt_reg_r x).
  apply (CRle_lt_trans _ x).
  rewrite CRplus_0_l. apply CRle_refl.
  apply (CRlt_le_trans _ y).
  apply CRltEpsilon, H0.
  unfold CRminus.
  rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
  apply CRle_refl.
Qed.

Lemma Markov_notnot_apart_0 : forall {R : ConstructiveReals} (x : CRcarrier R),
    Markov -> (~(x == 0)) -> (x ≶ 0).
Proof.
  intros.
  apply CRabs_appart_0.
  apply CRltEpsilon, (Markov_notnot_lt_0 _ H).
  intro abs. contradict H0.
  assert (CRabs R x <= 0) as H0.
  { intro H0. contradict abs.
    apply CRltForget, H0. }
  pose proof (CRabs_def2 x 0 H0) as [H1 H2].
  rewrite CRopp_0 in H2.
  split; assumption.
Qed.

Lemma Markov_notnot_apart : forall {R : ConstructiveReals} (x y : CRcarrier R),
    Markov -> (~(x == y)) -> (x ≶ y).
Proof.
  intros. 
  apply (CRplus_appart_reg_r (-y)). 
  rewrite CRplus_opp_r.
  apply (Markov_notnot_apart_0 _ H).
  intro abs. contradict H0.
  apply (CRplus_eq_reg_r (-y)).
  rewrite CRplus_opp_r. exact abs.
Qed.
