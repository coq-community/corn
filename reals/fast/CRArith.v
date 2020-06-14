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

Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import CoRN.model.totalorder.QMinMax.
Require Import CoRN.model.totalorder.QposMinMax.
Require Import Coq.setoid_ring.Ring_theory.
Require Import Coq.Setoids.Setoid.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qround.
Require Export CoRN.model.reals.CRreal.
Require Import CoRN.metric2.Complete.
Require Export CoRN.reals.fast.CRFieldOps.
Require Import CoRN.model.rings.Qring.
Require Import CoRN.model.metric2.Qmetric.
Require Import CoRN.tactics.CornTac.
Require Import CoRN.logic.Stability.
Require Import Coq.Logic.ConstructiveEpsilon.
Require Import CoRN.util.Qdlog.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.

Local Open Scope CR_scope.

(** Operations on rational numbers over CR are the same as the operations
on rational numbers. *)
Lemma CReq_Qeq : forall (x y:Q), inject_Q_CR x == inject_Q_CR y <-> (x == y)%Q.
Proof.
 intros x y.
 apply Cunit_eq.
Qed.

Lemma CRle_Qle : forall (x y:Q), inject_Q_CR x <= inject_Q_CR y <-> (x <= y)%Q.
Proof.
 split.
  intros H.
  destruct (Qlt_le_dec y x) as [X|X];[|assumption].
  destruct (Qpos_sub _ _ X) as [c Hc].
  assert (Y:=(H ((1#2)*c)%Qpos)).
  simpl in Y.
  unfold Cap_raw in Y; simpl in Y.
  rewrite -> Qle_minus_iff in Y.
  rewrite -> Hc in Y.
  autorewrite with QposElim in Y.
  ring_simplify in Y.
  elim (Qle_not_lt _ _ Y).
  rewrite -> Qlt_minus_iff.
  ring_simplify.
  apply Q.Qmult_lt_0_compat; auto with *.
 intros H e.
 simpl.
 unfold Cap_raw; simpl.
 rewrite -> Qle_minus_iff in H.
 apply Qle_trans with (0%Q);[|assumption].
 rewrite -> Qle_minus_iff; ring_simplify.
 apply Qpos_nonneg.
Qed.

Lemma CRplus_Qplus : forall (x y:Q), inject_Q_CR x + inject_Q_CR y == inject_Q_CR (x + y)%Q.
Proof.
 intros x y e1 e2; apply ball_refl.
 apply (Qpos_nonneg (e1+e2)).
Qed.

Hint Rewrite <- CRplus_Qplus : toCRring.

Lemma CRopp_Qopp : forall (x:Q), - inject_Q_CR x == inject_Q_CR (- x)%Q.
Proof.
 intros x e1 e2; apply ball_refl.
 apply (Qpos_nonneg (e1+e2)). 
Qed.
(* begin hide *)
Hint Rewrite CRopp_Qopp : CRfast_compute.
Hint Rewrite <- CRopp_Qopp : toCRring.
(* end hide *)
Lemma CRminus_Qminus : forall (x y:Q), inject_Q_CR x - inject_Q_CR y == inject_Q_CR (x - y)%Q.
Proof.
 intros x y e1 e2; apply ball_refl.
 apply (Qpos_nonneg (e1+e2)). 
Qed.
(* begin hide *)
Hint Rewrite <- CRminus_Qminus : toCRring.
(* end hide *)
Lemma CRmult_Qmult : forall (x y:Q), inject_Q_CR x * inject_Q_CR y == inject_Q_CR (x * y)%Q.
Proof.
 intros x y.
 rewrite -> CRmult_scale.
 intros e1 e2; apply ball_refl.
 apply (Qpos_nonneg (e1+e2)). 
Qed.
(* begin hide *)
Hint Rewrite <- CRmult_Qmult : toCRring.
(* end hide *)
Lemma Qap_CRap : forall (x y:Q), (~(x==y))%Q -> (' x)><(' y).
Proof.
 intros x y Hxy.
 destruct (Q_dec x y) as [[H|H]|H]; try contradiction;
   destruct (Qpos_sub _ _ H) as [c Hc];[left|right]; exists c; abstract (rewrite -> CRminus_Qminus;
     rewrite -> CRle_Qle; rewrite -> Hc; ring_simplify; apply Qle_refl).
Defined.

Lemma CRinv_Qinv : forall (x:Q) x_, CRinvT (inject_Q_CR x) x_ == inject_Q_CR (/x)%Q.
Proof.
 intros x [[c x_]|[c x_]];
   [change (' proj1_sig c <= 0 + - 'x)%CR in x_|change (' proj1_sig c <= ' x + - 0)%CR in x_]; unfold CRinvT;
     rewrite -> CRopp_Qopp, CRplus_Qplus, CRle_Qle in x_; try rewrite -> CRopp_Qopp;
       rewrite -> (@CRinv_pos_Qinv c).
    rewrite -> CRopp_Qopp.
    rewrite -> CReq_Qeq.
    assert (~x==0)%Q.
     intros H.
     rewrite -> H in x_.
     apply (Qle_not_lt _ _ x_).
     apply Qpos_ispos.
    field.
    intros X; apply H.
    assumption.
   rewrite -> Qplus_0_l in x_.
   assumption.
  reflexivity.
 rewrite -> Qplus_0_r in x_.
 assumption.
Qed.

(* begin hide *)
Hint Rewrite <- CRinv_Qinv : toCRring.
(* end hide *)
(**
** Ring
CR forms a ring for the ring tactic.
*)

Lemma CRplus_0_l (x: CR): (0 + x == x)%CR.
Proof.
  intros e1 e2. destruct x; simpl. 
  unfold Cap_raw; simpl.
  rewrite Qplus_0_l.
  assert ((1#2)*`e1 + `e2 <= `e1 + `e2)%Q.
  { apply Qplus_le_l. rewrite <- (Qmult_1_l (`e1)) at 2.
    apply Qmult_le_r. apply Qpos_ispos. discriminate. }
  apply (ball_weak_le Q_as_MetricSpace _ _ H),
  (regFun_prf ((1#2)*e1)%Qpos e2).
Qed. 

Lemma CRplus_comm (x y: CR): x + y == y + x.
Proof.
  intros e1 e2. destruct x,y; simpl; unfold Cap_raw; simpl.
  apply AbsSmall_Qabs. 
  setoid_replace (approximate ((1 # 2)%Q ↾ eq_refl * e1)%Qpos +
      approximate0 ((1 # 2) * e1)%Qpos -
      (approximate0 ((1 # 2) * e2)%Qpos +
       approximate ((1 # 2) * e2)%Qpos))%Q
    with (approximate ((1 # 2) * e1)%Qpos -
      approximate ((1 # 2) * e2)%Qpos +
      (approximate0 ((1 # 2) * e1)%Qpos -
       approximate0 ((1 # 2) * e2)%Qpos))%Q
    by ring.
  apply (Qle_trans _ _ _ (Qabs_triangle _ _)).
  setoid_replace (` e1 + ` e2)%Q
    with ((1#2)* ` e1 + (1#2)* `e2 + ((1#2)*`e1 + (1#2)* ` e2))%Q by ring.
  apply Qplus_le_compat.
  specialize (regFun_prf ((1#2)*e1)%Qpos ((1#2)*e2)%Qpos).
  apply AbsSmall_Qabs in regFun_prf. exact regFun_prf.
  specialize (regFun_prf0 ((1#2)*e1)%Qpos ((1#2)*e2)%Qpos).
  apply AbsSmall_Qabs in regFun_prf0. exact regFun_prf0.
Qed.

Lemma CRplus_assoc (x y z: CR): x + (y + z) == (x + y) + z.
Proof.
  intros. 
  intros e1 e2. destruct x,y,z; simpl; unfold Cap_raw; simpl.
  unfold Cap_raw; simpl.
  apply AbsSmall_Qabs. 
  setoid_replace (approximate ((1 # 2) * e1)%Qpos +
      (approximate0 ((1 # 2) * ((1 # 2) * e1))%Qpos +
       approximate1 ((1 # 2) * ((1 # 2) * e1))%Qpos) -
      (approximate ((1 # 2) * ((1 # 2) * e2))%Qpos +
       approximate0 ((1 # 2) * ((1 # 2) * e2))%Qpos +
       approximate1 ((1 # 2) * e2)%Qpos))%Q
    with ((approximate ((1 # 2) * e1)%Qpos
           - approximate ((1 # 2) * ((1 # 2) * e2))%Qpos)
          + (approximate0 ((1 # 2) * ((1 # 2) * e1))%Qpos
             - approximate0 ((1 # 2) * ((1 # 2) * e2))%Qpos)
          + (approximate1 ((1 # 2) * ((1 # 2) * e1))%Qpos
             - approximate1 ((1 # 2) * e2)%Qpos))%Q
    by ring.
  setoid_replace (` e1 + ` e2)%Q
    with (((1#2)* ` e1 + (1#2)*((1#2) * `e2))
          + ((1#2)*((1#2)* `e1) + (1#2)*((1#2)*`e2))
          + ((1#2)*((1#2)* `e1) + (1#2)* ` e2))%Q by ring.
  apply (Qle_trans _ _ _ (Qabs_triangle _ _)).
  apply Qplus_le_compat.
  apply (Qle_trans _ _ _ (Qabs_triangle _ _)).
  apply Qplus_le_compat.
  - apply AbsSmall_Qabs.
    apply (regFun_prf ((1#2)*e1)%Qpos ((1#2)*((1#2)*e2))%Qpos).
  - apply AbsSmall_Qabs.
    apply (regFun_prf0 ((1#2)*((1#2)*e1))%Qpos ((1#2)*((1#2)*e2))%Qpos).
  - apply AbsSmall_Qabs.
    apply (regFun_prf1 ((1#2)*((1#2)*e1))%Qpos ((1#2)*e2)%Qpos). 
Qed. 

Lemma CRmult_1_l : forall (x: CR), 1 * x == x.
Proof.
  intro x. rewrite CRmult_scale. 
  intros e1 e2. destruct x; simpl.
  rewrite Qmult_1_l.
  rewrite <- (Qmult_1_l (`e1)).
  apply (regFun_prf ((1#1)*e1)%Qpos e2).
Qed.

Lemma CR_ring_theory :
 @ring_theory CR 0 1 (ucFun2 CRplus_uc) CRmult
 (fun (x y:CR) => (x + - y)) CRopp (@st_eq CR).
Proof.
 split.
 - exact CRplus_0_l.
 - exact CRplus_comm.
 - exact CRplus_assoc.
 - exact CRmult_1_l.
 - apply: mult_commut_unfolded.
 - apply: mult_assoc_unfolded.
 - intros x y z;generalize z x y;apply: ring_distl_unfolded.
 - reflexivity.
 - apply: cg_minus_correct.
Qed.

Lemma CR_Q_ring_morphism :
 ring_morph 0%CR 1%CR (ucFun2 CRplus_uc) CRmult
 (fun x y => (x + - y)) CRopp (@st_eq CR)
  (0%Q) (1%Q) Qplus Qmult Qminus Qopp Qeq_bool (inject_Q_CR).
Proof.
 split; try reflexivity.
     apply CRplus_Qplus.
    apply CRminus_Qminus.
   intros x y; rewrite -> CRmult_Qmult; reflexivity.
  apply CRopp_Qopp.
 intros x y H.
 rewrite -> CReq_Qeq.
 apply Qeq_bool_eq.
 assumption.
Qed.

Ltac CRcst t :=
  match t with
  | (inject_Q_CR ?z) => Qcst z
  | _ => NotConstant
  end.

Ltac CRring_pre := autorewrite with toCRring.

Lemma CR_ring_eq_ext : ring_eq_ext (ucFun2 CRplus_uc) CRmult CRopp (@st_eq CR).
Proof.
 split.
   rapply ucFun2_wd.
  rapply CRmult_wd.
 rapply uc_wd.
Qed.

Add Ring CR_ring : CR_ring_theory (morphism CR_Q_ring_morphism, setoid (@st_isSetoid (@msp_is_setoid CR)) CR_ring_eq_ext, constants [CRcst], preprocess [CRring_pre]).

(** Relationship between strict and nonstrict positivity *)
Lemma CRpos_nonNeg : forall x, CRpos x -> CRnonNeg x.
Proof.
 intros x [c Hx].
 cut (0 <= x)%CR.
  unfold CRle.
  intros H.
  assert (x == x - 0)%CR. ring. rewrite -> H0.
  assumption.
 apply CRle_trans with (' proj1_sig c)%CR; auto with *.
 rewrite -> CRle_Qle; auto with *.
Qed.

Lemma CRneg_nonPos : forall x, CRneg x -> CRnonPos x.
Proof.
 intros x [c Hx].
 cut (x <= 0)%CR.
  unfold CRle.
  intros H.
  assert (0 - x == -x)%CR. ring. rewrite -> H0 in H.
  intros e.
  rewrite <- (Qopp_involutive (proj1_sig e)).
  rewrite <- (Qopp_involutive (approximate x e)).
  apply Qopp_le_compat.
  apply H.
 apply CRle_trans with ('(-proj1_sig c)%Q)%CR; auto with *.
 rewrite -> CRle_Qle. 
 apply (Qopp_le_compat 0). apply Qpos_nonneg.
Qed.

(** Now that we have ring-ness, we can easily prove some auxiliary utility lemmas about operations on CR. *)

Ltac CRring_replace x y :=
  assert (x == y) as CRring_replace_temp by ring;
  rewrite CRring_replace_temp;
  clear CRring_replace_temp.
  (* setoid_replace picks the st_eq equality which ring doesn't work for... *)

Lemma CRle_opp (x y: CR): x <= y <-> - y <= - x.
Proof.
 unfold CRle. intros.
 assert (- x - - y == y - x)%CR as E by ring.
 rewrite E.
 intuition.
Qed.

Lemma CRopp_opp (x: CR): (--x == x)%CR.
Proof. intros. ring. Qed.

Lemma CRplus_opp (x: CR): (x  + - x == 0)%CR.
Proof. intros. ring. Qed.

Lemma CRopp_0: (-0 == 0)%CR.
Proof. intros. ring. Qed.

Lemma CRplus_0_r (x: CR): (x + 0 == x)%CR.
Proof. intros. ring. Qed.

Lemma approximate_CRplus (x y: CR) (e: Qpos):
 approximate (x + y)%CR e = (approximate x ((1#2) * e)%Qpos + approximate y ((1#2) * e)%Qpos)%Q.
Proof. reflexivity. Qed.

Lemma CRnonNeg_CRplus (x y: CR): CRnonNeg x -> CRnonNeg y -> CRnonNeg (x + y)%CR.
Proof.
 unfold CRnonNeg. intros. rewrite approximate_CRplus.
 setoid_replace (- proj1_sig e)%Q
   with (- proj1_sig ((1#2)*e)%Qpos + - proj1_sig ((1#2)*e)%Qpos)%Q by (simpl; ring).
 apply Qplus_le_compat; auto.
Qed.

Lemma CRplus_eq_l (z x y: CR): x == y <-> x + z == y + z.
Proof with ring.
 split; intro E. rewrite E...
 rewrite <- (CRplus_0_r x), <- (CRplus_opp z), CRplus_assoc, E...
Qed.

Lemma CRplus_eq_r (z x y: CR): x == y <-> z + x == z + y.
Proof. intros. do 2 rewrite (CRplus_comm z). apply CRplus_eq_l. Qed.

Lemma CRplus_le_r (x y z: CR): x <= y <-> x+z <= y+z.
Proof.
 unfold CRle. intros.
 assert (y + z - (x + z) == y - x)%CR as E by ring. rewrite E.
 intuition.
Qed.

Lemma CRplus_le_l x: forall y z : CR, x <= y <-> z + x <= z + y.
Proof.
 intros. rewrite (CRplus_le_r x y z), (CRplus_comm x), (CRplus_comm y). reflexivity.
Qed.

Lemma CRplus_le_compat (x x' y y': CR): x <= x' -> y <= y' -> x+y <= x'+y'.
Proof.
 unfold CRle. intros.
 assert (x' + y' - (x + y) == (x' - x) + (y' - y)) as E by ring. rewrite E.
 apply CRnonNeg_CRplus; assumption.
Qed.

Lemma CRlt_irrefl (x: CR): x < x -> False.
Proof with auto.
 unfold CRltT.
 intro.
 assert (x - x == 0)%CR by ring.
 intros.
 generalize (CRpos_wd H0 H).
 unfold CRpos.
 intros.
 destruct H1.
 destruct x0.
 simpl in c.
 assert (x0 <= 0)%Q.
  rewrite <- CRle_Qle...
 apply Qlt_irrefl with 0%Q.
 apply Qlt_le_trans with x0...
Qed.

Lemma in_CRball (r: Q) (x y : CR)
  : x - ' r <= y /\ y <= x + ' r <-> ball r x y.
  (* A characterization of ball in terms of <=, similar to CRAbsSmall. *)
Proof with intuition.
 intros.
 cut (AbsSmall (' r) (x - y) <-> (x - ' r <= y /\ y <= x + ' r)).
 - pose proof (CRAbsSmall_ball x y r)...
 - unfold AbsSmall.
 simpl.
 setoid_replace (x - y <= ' r) with (x - ' r <= y).
  setoid_replace (- ' r <= x - y) with (y <= x + ' r).
   intuition.
  rewrite (CRplus_le_r (- ' r) (x - y) ('r + y)).
  assert (- ' r + (' r + y) == y) as E by ring. rewrite E.
  assert (x - y + (' r + y) == x + ' r)%CR as F by ring. rewrite F...
 rewrite (CRplus_le_r (x - y) (' r) (y - 'r)).
 assert (x - y + (y - ' r) == x - ' r) as E by ring. rewrite E.
 assert (' r + (y - ' r) == y) as F by ring. rewrite F...
Qed.

  (* And the same for gball: *)
Lemma in_CRgball (r: Q) (x y: CR): x - ' r <= y /\ y <= x + ' r <-> ball r x y.
Proof with intuition.
  apply in_CRball.
Qed.  

Lemma CRgball_plus (x x' y y': CR) e1 e2:
  ball e1 x x' -> ball e2 y y' -> ball (e1 + e2) (x + y)%CR (x' + y')%CR.
Proof with auto.
 do 3 rewrite <- in_CRgball.
 intros [A B] [C D].
 CRring_replace (x + y - ' (e1 + e2)%Q) (x - ' e1 + (y - ' e2)).
 CRring_replace (x + y + ' (e1 + e2)%Q) (x + ' e1 + (y + ' e2)).
 split; apply CRplus_le_compat...
Qed.

Lemma Qlt_from_CRlt (a b: Q): (' a < ' b)%CR -> (a < b)%Q.
Proof with auto.
 unfold CRltT.
 unfold CRpos.
 intros [[e p] H].
 revert H.
 simpl.
 rewrite CRminus_Qminus.
 rewrite CRle_Qle.
 intros.
 apply Qlt_le_trans with (a + e)%Q. 
  rewrite <-(Qplus_0_r a) at 1.
  apply Qplus_lt_r...
 apply Q.Qplus_le_l with (-a)%Q.
 ring_simplify.
 rewrite Qplus_comm...
Qed.

Lemma CRlt_trans (x y z: CR): x < y -> y < z -> x < z.
Proof.
 destruct CRisCOrdField.
 destruct ax_less_strorder.
specialize (so_trans x y z). (* Coq hangs here*)
  apply so_trans.
Qed.

Lemma CRle_lt_trans (x y z: CR): x <= y -> y < z -> x < z.
Proof with auto.
 intros ? [e ?]. exists e.
 apply CRle_trans with (z - y)%CR...
 assert (z - x - (z - y) == y - x)%CR as E by ring.
 unfold CRle.
 rewrite E...
Qed.

Lemma CRlt_le_trans (x y z: CR): x < y -> y <= z -> x < z.
Proof with auto.
 intros [e ?] ?. exists e.
 apply CRle_trans with (y - x)%CR...
 assert (z - x - (y - x) == z - y)%CR as E by ring.
 unfold CRle.
 rewrite E...
Qed.

Lemma CRlt_le_weak (x y: CR): (x < y -> x <= y)%CR.
Proof. intros. apply CRpos_nonNeg. assumption. Qed.

Lemma lower_CRapproximation (x: CR) (e: Qpos): ' (approximate x e - proj1_sig e)%Q <= x.
Proof.
 intros. rewrite <- CRminus_Qminus.
 apply CRplus_le_r with ('proj1_sig e)%CR.
 ring_simplify. rewrite CRplus_comm.
 apply in_CRball, ball_approx_r.
Qed.

Lemma upper_CRapproximation (x: CR) (e: Qpos): x <= ' (approximate x e + proj1_sig e)%Q.
Proof.
 intros. rewrite <- CRplus_Qplus.
 apply CRplus_le_r with (-'proj1_sig e)%CR.
 assert (' approximate x e + 'proj1_sig e - 'proj1_sig e == ' approximate x e)%CR as E by ring. rewrite E.
 apply (in_CRball (proj1_sig e) x ('approximate x e)), ball_approx_r.
Qed.

Hint Immediate lower_CRapproximation upper_CRapproximation.

Lemma CRlt_Qmid (x y: CR): x < y -> sigT (λ q: Q, x < 'q and 'q < y).
Proof with auto.
 intros [q E].
 set (quarter := ((1#4)*q)%Qpos).
 exists (proj1_sig quarter + (approximate x quarter + proj1_sig quarter))%Q.
 split.
  apply CRle_lt_trans with (' (0 + (approximate x quarter + proj1_sig quarter))%Q)%CR...
   rewrite Qplus_0_l...
  apply CRlt_Qlt.
  apply Qplus_lt_l...
 apply CRlt_le_trans with (x + 'proj1_sig q)%CR.
  apply CRlt_le_trans with (' (approximate x quarter - proj1_sig quarter + proj1_sig q)%Q)%CR.
   apply CRlt_Qlt.
   setoid_replace (proj1_sig q)
     with (proj1_sig quarter + proj1_sig quarter + proj1_sig quarter + proj1_sig quarter)%Q.
    ring_simplify.
    apply Qplus_lt_l.
    apply Qmult_lt_compat_r...
    reflexivity.
   simpl. ring.
  rewrite <- CRplus_Qplus.
  apply CRplus_le_compat...
  apply CRle_refl.
 apply CRplus_le_r with (-x)%CR.
 CRring_replace (x + 'proj1_sig q - x) ('proj1_sig q)...
Qed.

Lemma CRle_not_lt (x y: CR): (x <= y)%CR <-> Not (y < x)%CR.
Proof.
 destruct CRisCOrdField.
 simpl in def_leEq.
 apply def_leEq.
Qed.

Lemma CRnonNeg_le_0 x: CRnonNeg x <-> 0 <= x.
Proof.
 unfold CRle.
 assert (x - 0 == x)%CR as E by ring.
 rewrite E.
 intuition.
Qed.

Lemma CRnonNeg_0: CRnonNeg (0)%CR.
Proof.
 unfold CRnonNeg. simpl. intros.
 apply (Qopp_le_compat 0). apply Qpos_nonneg.
Qed.

Hint Immediate CRnonNeg_0.

Definition CRle_lt_dec: forall x y, DN ((x <= y)%CR + (y < x)%CR).
Proof with auto.
  intros.
  apply (DN_fmap (@DN_decisionT (y < x)%CR)).
  intros [A | B]...
  left.
  apply (leEq_def CRasCOrdField x y)...
Qed.

Definition CRle_dec: forall (x y: CR), DN ((x<=y)%CR + (y<=x)%CR).
Proof with auto.
 intros. apply (DN_fmap (CRle_lt_dec x y)).
 intros [A | B]...
 right.
 apply CRlt_le_weak...
Qed.

Lemma approximate_CRminus (x y: CR) (e: QposInf):
  approximate (x - y)%CR e =
  (approximate x (Qpos2QposInf (1 # 2) * e)%QposInf - approximate y (Qpos2QposInf (1 # 2) * e)%QposInf)%Q.
Proof. destruct e; reflexivity. Qed.


Lemma CRnonNeg_criterion (x: CR): (forall q, (x <= ' q)%CR -> 0 <= q)%Q -> CRnonNeg x.
Proof with auto with qarith.
 unfold CRle.
 unfold CRnonNeg.
 intros.
 apply Q.Qplus_le_l with (proj1_sig e).
 ring_simplify.
 apply H.
 intros.
 rewrite approximate_CRminus.
 simpl.
 cut (approximate x ((1 # 2) * e0)%Qpos - approximate x e <= proj1_sig e0 + proj1_sig e)%Q.
 - intros.
  apply Q.Qplus_le_l with (proj1_sig e0 + approximate x ((1#2)*e0)%Qpos - approximate x e)%Q.
  simpl. ring_simplify... 
 - apply Qle_trans with (Qabs (approximate x ((1 # 2) * e0)%Qpos - approximate x e))%Q.
   apply Qle_Qabs.
   apply Qle_trans with (proj1_sig ((1#2)*e0)%Qpos + proj1_sig e)%Q...
  pose proof (regFun_prf x ((1#2)*e0)%Qpos e).
  apply Qball_Qabs in H0...
 apply Qplus_le_compat.
  simpl.
  rewrite <- (Qmult_1_r (proj1_sig e0)) at 2.
  rewrite (Qmult_comm (proj1_sig e0)).
  apply Qmult_le_compat_r...
 apply Qle_refl.
Qed.

(* Similarly, we can derive non-strict inequalities between reals from
 non-strict inequalities which approximate it by a rational on one or both sides. *)

Lemma Qle_CRle_r (x y: CR): (forall y', y <= ' y' -> x <= ' y') <-> x <= y.
Proof with auto.
 split; intros. 2: apply CRle_trans with y...
 apply from_DN.
 apply (DN_bind (CRle_lt_dec x y)).
 intros [?|W]. apply DN_return...
 exfalso.
 destruct (CRlt_Qmid _ _ W) as [w [A B]].
 pose proof (H w (CRlt_le_weak _ _ A)).
 apply (CRle_not_lt x ('w)%CR)...
Qed.

Lemma Qle_CRle_l (x y: CR): (forall x', ' x' <= x -> ' x' <= y) <-> x <= y.
Proof with auto.
 intros.
 rewrite CRle_opp.
 rewrite <- Qle_CRle_r.
 split; intros.
  rewrite CRle_opp, CRopp_opp, CRopp_Qopp.
  apply H.
  rewrite CRle_opp, CRopp_Qopp, Qopp_opp...
 rewrite CRle_opp, CRopp_Qopp.
 apply H.
 rewrite CRle_opp, CRopp_Qopp, CRopp_opp, Qopp_opp...
Qed.

Lemma Qle_CRle (x y: CR): (forall x' y', ' x' <= x -> y <= ' y' -> (x' <= y')%Q) <-> x <= y.
Proof with auto.
 split; intros. 
  apply (proj1 (Qle_CRle_l _ _)). intros.
  apply (proj1 (Qle_CRle_r _ _)). intros.
  apply CRle_Qle...
 apply CRle_Qle.
 apply CRle_trans with x...
 apply CRle_trans with y...
Qed.

Lemma CRnonNegQpos : forall e : Qpos, CRnonNeg (' ` e).
Proof.
 intros [e e_pos]; apply CRnonNeg_criterion; simpl.
 intros q A; apply Qlt_le_weak, Qlt_le_trans with (y := e); trivial.
 now apply CRle_Qle.
Qed.

Lemma scale_0 x: scale 0 x == 0.
Proof. rewrite <- CRmult_scale. ring. Qed.

Lemma scale_CRplus (q: Q) (x y: CR): scale q (x + y) == scale q x + scale q y.
Proof. intros. do 3 rewrite <- CRmult_scale. ring. Qed.

Lemma scale_CRopp (q: Q) (x: CR): scale q (-x) == - scale q x.
Proof. intros. do 2 rewrite <- CRmult_scale. ring. Qed.

(** This returs GT if x is clearly greater than e, returns LT if x
is clearly less than (-e), and returns Eq otherwise. *)
Definition CR_epsilon_sign_dec (e:Qpos) (x:CR) : comparison :=
let z := approximate x e in
 match Q.Qle_dec ((2#1) * proj1_sig e) z with
 | left p => Gt
 | right _ =>
  match Q.Qle_dec z (-(2#1) * proj1_sig e)%Q with
  | left p => Datatypes.Lt
  | right _ => Eq
  end
 end.

(** This helper lemma reduces a CRpos problem to a sigma type with
a simple equality proposition. *)
Lemma CR_epsilon_sign_dec_pos : forall x,
{e:Qpos | CR_epsilon_sign_dec e x ≡ Gt} -> CRpos x.
Proof.
 intros x [e H].
 apply (@CRpos_char e).
 abstract (unfold CR_epsilon_sign_dec in H; destruct (Q.Qle_dec ((2#1) * proj1_sig e) (approximate x e)) as [A|A];
  [assumption | destruct (Q.Qle_dec (approximate x e) (- (2#1) * proj1_sig e)) as [B|B]; discriminate H]).
Defined.

Lemma CR_epsilon_sign_dec_Gt (e:Qpos) (x:CR) : 
  ((2#1) * proj1_sig e <= approximate x e)%Q -> CR_epsilon_sign_dec e x ≡ Gt.
Proof.
  intros.
  unfold CR_epsilon_sign_dec.
  destruct Q.Qle_dec; intuition.
Qed.

(* nasty because approximate is not Proper *)
Lemma CR_epsilon_sign_dec_pos_rev (x : CR) (e : Qpos) :
  ('proj1_sig e <= x)%CR -> CR_epsilon_sign_dec ((1#4) * e) x ≡ Gt.
Proof.
  intros E.
  apply CR_epsilon_sign_dec_Gt.
  apply Qplus_le_l with (-proj1_sig e)%Q.
  simpl (2 * ` ((1 # 4)%Q ↾ eq_refl * e)%Qpos + - ` e)%Q.
  setoid_replace ((2#1) * ((1 # 4) * proj1_sig e) + - proj1_sig e)%Q
           with (-((1#2) * proj1_sig e))%Q
    by ring.
  replace ((1#4) * e)%Qpos with ((1#2) * ((1#2) * e))%Qpos.
   now apply (E ((1#2) * e))%Qpos.
  apply Qpos_hprop.
  now destruct e as [[[ | | ] ?] ?].
Qed.

(* Type class versions of a lot of the above *)
Close Scope CR_scope.
Local Opaque CR.

Instance: Ring CR.
Proof. apply (rings.from_stdlib_ring_theory CR_ring_theory). Qed.

(* We need the (1#4) because CR_epsilon_sign_dec_pos_rev is nasty *)
Instance CRlt: Lt CR := λ x y, 
  ∃ n : nat, CR_epsilon_sign_dec ((1#4) * Qpos_power (2#1) (-cast nat Z n)) (y - x) ≡ Gt.

Lemma CR_lt_ltT x y : x < y IFF CRltT x y.
Proof.
  split.
   intros E.
   apply CR_epsilon_sign_dec_pos.
   apply constructive_indefinite_description_nat in E. 
    destruct E as [n En].
    now exists ((1#4) * Qpos_power (2#1) (-cast nat Z n))%Qpos.
   intros. now apply comparison_eq_dec.
  intros [ε Eε].
  exists (Z.nat_of_Z (-Qdlog2 ('ε))).
  apply CR_epsilon_sign_dec_pos_rev.
  apply CRle_trans with ('proj1_sig ε); auto.
  apply CRle_Qle. simpl.
  destruct (decide (proj1_sig ε ≤ 1)).
   rewrite Z.nat_of_Z_nonneg.
    rewrite Z.opp_involutive.
    apply Qdlog2_spec.
    now destruct ε.
   apply Z.opp_nonneg_nonpos.
   now apply Qdlog2_nonpos.
  rewrite Z.nat_of_Z_nonpos.
   now apply Qlt_le_weak, Qnot_le_lt.
  apply Z.opp_nonpos_nonneg.
  apply Qdlog2_nonneg.
  now apply Qlt_le_weak, Qnot_le_lt.
Qed.

Instance CRapart: Apart CR := λ x y, x < y ∨ y < x.

Lemma CR_apart_apartT x y : x ≶ y IFF CRapartT x y.
Proof.
  split.
   intros E.
   set (f (n : nat) := CR_epsilon_sign_dec ((1#4) * Qpos_power (2#1) (-cast nat Z n))).
   assert (∃ n, f n (y - x) ≡ Gt ∨ f n (x - y) ≡ Gt) as E2.
    now destruct E as [[n En] | [n En]]; exists n; [left | right].
   apply constructive_indefinite_description_nat in E2.
    destruct E2 as [n E2].
    destruct (comparison_eq_dec (f n (y - x)) Gt) as [En|En].
     left. apply CR_epsilon_sign_dec_pos. 
     now exists ((1#4) * Qpos_power (2#1) (-cast nat Z n))%Qpos.
    right. apply CR_epsilon_sign_dec_pos. 
    exists ((1#4) * Qpos_power (2#1) (-cast nat Z n))%Qpos.
    destruct E2; tauto.
   intros n. 
   destruct (comparison_eq_dec (f n (y - x)) Gt); auto.
   destruct (comparison_eq_dec (f n (x - y)) Gt); tauto.
  intros [E|E].
   left. now apply CR_lt_ltT.
  right. now apply CR_lt_ltT.
Qed.

Instance: StrongSetoid CR.
Proof with auto; try solve [now apply CR_apart_apartT].
  split.
     intros x E. 
     destruct (ap_irreflexive _ x)...
    intros x y E. 
    apply CR_apart_apartT.
    apply: ap_symmetric...
   intros x y E z.
   destruct (ap_cotransitive _ x y) with z; [|left|right]...
  intros x y; split; intros E.
   apply ap_tight. intros E2. destruct E...
  intros E2. destruct (proj2 (ap_tight _ x y))...
Qed.

Instance: StrongSetoid_BinaryMorphism CRmult.
Proof with auto; try solve [now apply CR_apart_apartT].
  split; try apply _.
  intros x₁ y₁ x₂ y₂ E.
  destruct (CRmult_strext x₁ x₂ y₁ y₂); [|left|right]...
Qed.

Instance: FullPseudoOrder CRle CRlt.
Proof with eauto; try solve [eapply CR_lt_ltT; eauto].
  split.
   split; try apply _.
     intros x y [E1 E2].
     destruct (less_antisymmetric_unfolded _ x y)...
    intros x y E z.
    pose proof E as Ed.
    apply CR_lt_ltT in Ed.
    destruct (less_cotransitive _ x y Ed z);
     [ left | right]...
   reflexivity.
  intros x y; split.
   intros E1 E2.
   apply (leEq_def _ x y)...
  intros E1. apply (leEq_def _ x y).
  intros E2. destruct E1...
Qed.

Instance: FullPseudoSemiRingOrder CRle CRlt.
Proof with eauto; try solve [eapply CR_lt_ltT; eauto].
  apply rings.from_full_pseudo_ring_order. 
    repeat (split; try apply _).
    intros x y E.
    apply CR_lt_ltT, (plus_resp_less_lft _ x y z)...
   apply _.
  intros x y E1 E2.
  apply CR_lt_ltT, (mult_resp_pos _ x y)...
Qed.

Program Instance CRinv: Recip CR := λ x, CRinvT x _.
Next Obligation. apply CR_apart_apartT. now destruct x. Qed.

Instance: Field CR.
Proof.
  split; try apply _.
    apply CR_apart_apartT.
    now apply: ring_non_triv.
   split; try apply _.
   intros [x Px] [y Py] E.
   now apply: CRinvT_wd.
  intros x.
  now apply: field_mult_inv.
Qed.

Instance: StrongSetoid_Morphism inject_Q_CR.
Proof. 
  apply strong_setoids.dec_strong_morphism.
  split; try apply _.
Qed.

Instance: StrongSemiRing_Morphism inject_Q_CR.
Proof.
  repeat (split; try apply _); intros; try reflexivity; symmetry.
   now apply CRplus_Qplus.
  now apply CRmult_Qmult.
Qed.

Instance: StrongInjective inject_Q_CR.
Proof.
  repeat (split; try apply _); intros.
  apply CR_apart_apartT.
  now apply: Qap_CRap.
Qed.

Instance: OrderEmbedding inject_Q_CR.
Proof. repeat (split; try apply _); now apply CRle_Qle. Qed.

Instance: StrictOrderEmbedding inject_Q_CR.
Proof. split; apply _. Qed.

