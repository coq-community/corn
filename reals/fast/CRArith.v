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

Require Import Ring_theory.
Require Import Setoid.
Require Import QArith.
Require Export CRreal.
Require Import Complete.
Require Export CRFieldOps.
Require Import Qmetric.
Require Import CornTac.

Open Local Scope CR_scope.

(** Operations on rational numbers over CR are the same as the operations
on rational numbers. *)
Lemma CReq_Qeq : forall (x y:Q), inject_Q x == inject_Q y <-> (x == y)%Q.
Proof.
unfold CR, inject_Q.
rapply Cunit_eq.
Qed.

Lemma CRle_Qle : forall (x y:Q), inject_Q x <= inject_Q y <-> (x <= y)%Q.
Proof.
split.
intros H.
destruct (Qlt_le_dec y x) as [X|X];[|assumption].
destruct (Qpos_lt_plus X) as [c Hc].
assert (Y:=(H ((1#2)*c)%Qpos)).
simpl in Y.
unfold Cap_raw in Y; simpl in Y.
rewrite Qle_minus_iff in Y.
rewrite Hc in Y.
autorewrite with QposElim in Y.
ring_simplify in Y.
elim (Qle_not_lt _ _ Y).
rewrite Qlt_minus_iff.
ring_simplify.
rapply Qpos_prf.

intros H e.
simpl.
unfold Cap_raw; simpl.
rewrite Qle_minus_iff in H.
apply Qle_trans with (0%Q);[|assumption].
rewrite Qle_minus_iff; ring_simplify.
apply Qpos_nonneg.
Qed.

Lemma CRplus_Qplus : forall (x y:Q), inject_Q x + inject_Q y == inject_Q (x + y)%Q.
Proof.
intros x y e1 e2; rapply ball_refl.
Qed.

Hint Rewrite <- CRplus_Qplus : toCRring.

Lemma CRopp_Qopp : forall (x:Q), - inject_Q x == inject_Q (- x)%Q.
Proof.
intros x e1 e2; rapply ball_refl.
Qed.
(* begin hide *)
Hint Rewrite CRopp_Qopp : CRfast_compute.
Hint Rewrite <- CRopp_Qopp : toCRring.
(* end hide *)
Lemma CRminus_Qminus : forall (x y:Q), inject_Q x - inject_Q y == inject_Q (x - y)%Q.
Proof.
intros x y e1 e2; rapply ball_refl.
Qed.
(* begin hide *)
Hint Rewrite <- CRminus_Qminus : toCRring.
(* end hide *)
Lemma CRmult_Qmult : forall (x y:Q), inject_Q x * inject_Q y == inject_Q (x * y)%Q.
Proof.
intros x y.
rewrite CRmult_scale.
intros e1 e2; rapply ball_refl.
Qed.
(* begin hide *)
Hint Rewrite <- CRmult_Qmult : toCRring.
(* end hide *)
Lemma Qap_CRap : forall (x y:Q), (~(x==y))%Q -> (' x)><(' y).
Proof.
intros x y Hxy.
destruct (Q_dec x y) as [[H|H]|H]; try contradiction;
destruct (Qpos_lt_plus H) as [c Hc];[left|right]; exists c;
abstract (rewrite CRminus_Qminus;
rewrite CRle_Qle;
rewrite Hc;
ring_simplify;
apply Qle_refl).
Defined.

Lemma CRinv_Qinv : forall (x:Q) x_, CRinv (inject_Q x) x_ == inject_Q (/x).
Proof.
intros x [[c x_]|[c x_]];
[change (' c <= ' 0%Q + - ' x)%CR in x_|change (' c <= ' x + - ' 0%Q)%CR in x_];
unfold CRinv;
rewrite CRopp_Qopp, CRplus_Qplus, CRle_Qle in x_;
try rewrite CRopp_Qopp;
rewrite (@CRinv_pos_Qinv c).
   rewrite CRopp_Qopp.
   rewrite CReq_Qeq.
   assert (~x==0)%Q.
    intros H.
    rewrite H in x_.
    apply (Qle_not_lt _ _ x_).
    rapply Qpos_prf.
   field.
   intros X; apply H.
   replace LHS with (- - x)%Q by ring.
   rewrite X.
   reflexivity.
  replace RHS with (0 + - x)%Q by ring.
  assumption.
 reflexivity.
replace RHS with (x + - 0)%Q by ring.
assumption.
Qed.
(* begin hide *)
Hint Rewrite <- CRinv_Qinv : toCRring.
(* end hide *)
(**
** Ring
CR forms a ring for the ring tactic.
*)
Lemma CR_ring_theory : 
 @ring_theory CR (' 0%Q) (' 1%Q) (ucFun2 CRplus) CRmult
 (fun (x y:CR) => (x + - y)) CRopp (@st_eq CR).
Proof.
split.
rapply cm_lft_unit_unfolded.
rapply cag_commutes_unfolded.
rapply plus_assoc_unfolded.
rapply one_mult.
rapply mult_commut_unfolded.
rapply mult_assoc_unfolded.
intros x y z;generalize z x y;rapply ring_distl_unfolded.
reflexivity.
rapply cg_minus_correct.
Qed.

Lemma CR_Q_ring_morphism : 
 ring_morph (inject_Q 0%Q) (inject_Q 1%Q) (ucFun2 CRplus) CRmult
 (fun x y => (x + - y)) CRopp (@st_eq CR)
  (0%Q) (1%Q) Qplus Qmult Qminus Qopp Qeq_bool (inject_Q).
Proof.
split; try reflexivity.
apply CRplus_Qplus.
apply CRminus_Qminus.
intros x y; rewrite CRmult_Qmult; reflexivity.
apply CRopp_Qopp.
intros x y H.
rewrite CReq_Qeq.
apply Qeq_bool_eq.
assumption.
Qed.

Ltac CRcst t :=
  match t with
  | (inject_Q ?z) => Qcst z
  | _ => NotConstant
  end.

Ltac CRring_pre := autorewrite with toCRring.

Lemma CR_ring_eq_ext : ring_eq_ext (ucFun2 CRplus) CRmult CRopp (@st_eq CR).
Proof.
split.
rapply ucFun2_wd.
rapply CRmult_wd.
rapply uc_wd.
Qed.

Add Ring CR_ring : CR_ring_theory (morphism CR_Q_ring_morphism, setoid (@st_isSetoid (@msp_is_setoid CR)) CR_ring_eq_ext, constants [CRcst], preprocess [CRring_pre]).

(** Relationship between strict and nonstrict positivity *)
Lemma CRpos_nonNeg : forall x, CRpos x -> CRnonNeg x.
intros x [c Hx].
cut ('0 <= x)%CR.
 unfold CRle.
 intros H.
 setoid_replace (x - '0)%CR with x in H by ring.
 assumption.
apply CRle_trans with (' c)%CR; auto with *.
rewrite CRle_Qle; auto with *.
Qed.

Lemma CRneg_nonPos : forall x, CRneg x -> CRnonPos x.
intros x [c Hx].
cut (x <= '0)%CR.
 unfold CRle.
 intros H.
 setoid_replace ('0 - x)%CR with (-x)%CR in H by ring.
 intros e.
 rewrite <- (Qopp_involutive e).
 rewrite <- (Qopp_involutive (approximate x e)).
 apply Qopp_le_compat.
 rapply H.
apply CRle_trans with (' - c)%CR; auto with *.
rewrite CRle_Qle; auto with *.
Qed.