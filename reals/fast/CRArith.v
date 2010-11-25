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
Require Import Qabs.
Require Import Qround.
Require Export CRreal.
Require Import Complete.
Require Export CRFieldOps.
Require Import Qring.
Require Import CRing_Homomorphisms.
Require Import Qmetric.
Require Import CornTac.
Require Import Stability.

Set Automatic Introduction.

Open Local Scope CR_scope.

(** Operations on rational numbers over CR are the same as the operations
on rational numbers. *)
Lemma CReq_Qeq : forall (x y:Q), inject_Q x == inject_Q y <-> (x == y)%Q.
Proof.
 intros x y.
 apply Cunit_eq.
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

Lemma CRplus_Qplus : forall (x y:Q), inject_Q x + inject_Q y == inject_Q (x + y)%Q.
Proof.
 intros x y e1 e2; apply ball_refl.
Qed.

Hint Rewrite <- CRplus_Qplus : toCRring.

Lemma CRopp_Qopp : forall (x:Q), - inject_Q x == inject_Q (- x)%Q.
Proof.
 intros x e1 e2; apply ball_refl.
Qed.
(* begin hide *)
Hint Rewrite CRopp_Qopp : CRfast_compute.
Hint Rewrite <- CRopp_Qopp : toCRring.
(* end hide *)
Lemma CRminus_Qminus : forall (x y:Q), inject_Q x - inject_Q y == inject_Q (x - y)%Q.
Proof.
 intros x y e1 e2; apply ball_refl.
Qed.
(* begin hide *)
Hint Rewrite <- CRminus_Qminus : toCRring.
(* end hide *)
Lemma CRmult_Qmult : forall (x y:Q), inject_Q x * inject_Q y == inject_Q (x * y)%Q.
Proof.
 intros x y.
 rewrite -> CRmult_scale.
 intros e1 e2; apply ball_refl.
Qed.
(* begin hide *)
Hint Rewrite <- CRmult_Qmult : toCRring.
(* end hide *)
Lemma Qap_CRap : forall (x y:Q), (~(x==y))%Q -> (' x)><(' y).
Proof.
 intros x y Hxy.
 destruct (Q_dec x y) as [[H|H]|H]; try contradiction;
   destruct (Qpos_lt_plus H) as [c Hc];[left|right]; exists c; abstract (rewrite -> CRminus_Qminus;
     rewrite -> CRle_Qle; rewrite -> Hc; ring_simplify; apply Qle_refl).
Defined.

Lemma CRinv_Qinv : forall (x:Q) x_, CRinv (inject_Q x) x_ == inject_Q (/x).
Proof.
 intros x [[c x_]|[c x_]];
   [change (' c <= ' 0%Q + - ' x)%CR in x_|change (' c <= ' x + - ' 0%Q)%CR in x_]; unfold CRinv;
     rewrite -> CRopp_Qopp, CRplus_Qplus, CRle_Qle in x_; try rewrite -> CRopp_Qopp;
       rewrite -> (@CRinv_pos_Qinv c).
    rewrite -> CRopp_Qopp.
    rewrite -> CReq_Qeq.
    assert (~x==0)%Q.
     intros H.
     rewrite -> H in x_.
     apply (Qle_not_lt _ _ x_).
     apply Qpos_prf.
    field.
    intros X; apply H.
    assumption.
   rewrite -> Qplus_0_l in x_.
   assumption.
  reflexivity.
 rewrite -> Qplus_0_r in x_.
 assumption.
Qed.

Lemma inject_Q_product (l: list Q): (' cr_Product l) [=] cr_Product (map inject_Q l).
Proof.
 induction l.
  reflexivity.
 change (' (a * cr_Product l)[=]cr_Product (map inject_Q (a :: l))).
 rewrite <- CRmult_Qmult.
 rewrite IHl.
 reflexivity.
Qed.

Lemma inject_Qred_ap (x y: Q): Qred x <> Qred y -> ' x [#] ' y.
Proof with auto.
 intro.
 apply Qap_CRap.
 intro.
 apply H.
 apply Qred_complete...
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
         apply: cm_lft_unit_unfolded.
        apply: cag_commutes_unfolded.
       apply: plus_assoc_unfolded.
      apply: one_mult.
     apply: mult_commut_unfolded.
    apply: mult_assoc_unfolded.
   intros x y z;generalize z x y;apply: ring_distl_unfolded.
  reflexivity.
 apply: cg_minus_correct.
Qed.

Lemma inject_Q_strext : fun_strext inject_Q.
Proof.
 intros x y [Hxy|Hxy].
  apply: Qlt_not_eq.
  apply Qnot_le_lt.
  intros H.
  absurd ('y[<=]'x).
   rewrite -> leEq_def.
   auto with *.
  rewrite -> CRle_Qle.
  auto.
 apply ap_symmetric.
 apply: Qlt_not_eq.
 apply Qnot_le_lt.
 intros H.
 absurd ('x[<=]'y).
  rewrite -> leEq_def.
  auto with *.
 rewrite -> CRle_Qle.
 auto.
Qed.

Definition inject_Q_csf := Build_CSetoid_fun _ _ _ inject_Q_strext.

Lemma inject_Q_hom : RingHom Q_as_CRing CRasCRing.
Proof.
 exists (inject_Q_csf).
   apply: CRplus_Qplus.
  intros x y.
  apply eq_symmetric.
  apply CRmult_Qmult.
 apply eq_reflexive.
Defined.

Lemma CR_Q_ring_morphism :
 ring_morph (inject_Q 0%Q) (inject_Q 1%Q) (ucFun2 CRplus) CRmult
 (fun x y => (x + - y)) CRopp (@st_eq CR)
  (0%Q) (1%Q) Qplus Qmult Qminus Qopp Qeq_bool (inject_Q).
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
  | (inject_Q ?z) => Qcst z
  | _ => NotConstant
  end.

Ltac CRring_pre := autorewrite with toCRring.

Lemma CR_ring_eq_ext : ring_eq_ext (ucFun2 CRplus) CRmult CRopp (@st_eq CR).
Proof.
 split.
   apply ucFun2_wd.
  apply CRmult_wd.
 apply uc_wd.
Qed.

Add Ring CR_ring : CR_ring_theory (morphism CR_Q_ring_morphism, setoid (@st_isSetoid (@msp_is_setoid CR)) CR_ring_eq_ext, constants [CRcst], preprocess [CRring_pre]).

(** Relationship between strict and nonstrict positivity *)
Lemma CRpos_nonNeg : forall x, CRpos x -> CRnonNeg x.
Proof.
 intros x [c Hx].
 cut ('0 <= x)%CR.
  unfold CRle.
  intros H.
  assert (x == x - '0)%CR. ring. rewrite -> H0.
  assumption.
 apply CRle_trans with (' c)%CR; auto with *.
 rewrite -> CRle_Qle; auto with *.
Qed.

Lemma CRneg_nonPos : forall x, CRneg x -> CRnonPos x.
Proof.
 intros x [c Hx].
 cut (x <= '0)%CR.
  unfold CRle.
  intros H.
  assert ('0 - x == -x)%CR. ring. rewrite -> H0 in H.
  intros e.
  rewrite <- (Qopp_involutive e).
  rewrite <- (Qopp_involutive (approximate x e)).
  apply Qopp_le_compat.
  apply H.
 apply CRle_trans with (' - c)%CR; auto with *.
 rewrite -> CRle_Qle; auto with *.
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

Lemma CRplus_opp (x: CR): (x  + - x == ' 0)%CR.
Proof. intros. ring. Qed.

Lemma CRopp_0: (-'0 == '0)%CR.
Proof. intros. ring. Qed.

Lemma CRplus_0_l (x: CR): ('0 + x == x)%CR.
Proof. intros. ring. Qed.

Lemma CRplus_0_r (x: CR): (x + '0 == x)%CR.
Proof. intros. ring. Qed.

Lemma approximate_CRplus (x y: CR) (e: Qpos):
 approximate (x + y)%CR e = (approximate x ((1#2) * e)%Qpos + approximate y ((1#2) * e)%Qpos)%Q.
Proof. reflexivity. Qed.

Lemma CRnonNeg_CRplus (x y: CR): CRnonNeg x -> CRnonNeg y -> CRnonNeg (x + y)%CR.
Proof.
 unfold CRnonNeg. intros. rewrite approximate_CRplus.
 setoid_replace (- e)%Q with (- ((1#2)*e)%Qpos + - ((1#2)*e)%Qpos)%Q by (simpl; ring).
 apply Qplus_le_compat; auto.
Qed.

Lemma CRplus_comm (x y: CR): x + y == y + x.
Proof. intros. ring. Qed.

Lemma CRplus_assoc (x y z: CR): x + (y + z) == (x + y) + z.
Proof. intros. ring. Qed.

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
 intros. rewrite (CRplus_le_r x y z) (CRplus_comm x) (CRplus_comm y). reflexivity.
Qed.

Lemma CRplus_le_compat (x x' y y': CR): x <= x' -> y <= y' -> x+y <= x'+y'.
Proof.
 unfold CRle. intros.
 assert (x' + y' - (x + y) == (x' - x) + (y' - y)) as E by ring. rewrite E.
 apply CRnonNeg_CRplus; assumption.
Qed.

Lemma CRlt_irrefl (x: CR): x < x -> False.
Proof with auto.
 unfold CRlt.
 intro.
 assert (x - x == ' 0)%CR by ring.
 intros.
 generalize (CRpos_wd H0 H).
 unfold CRpos.
 intros.
 destruct H1.
 destruct x0.
 simpl in c.
 assert (x0 <= 0)%Q.
  rewrite <- CRle_Qle...
 apply Qlt_irrefl with 0.
 apply Qlt_le_trans with x0...
Qed.

Lemma in_CRball (r: Qpos) (x y : CR): x - ' r <= y /\ y <= x + ' r <-> ball r x y.
  (* A characterization of ball in terms of <=, similar to CRAbsSmall. *)
Proof with intuition.
 intros.
 cut (AbsSmall (' r) (x - y) <-> (x - ' r <= y /\ y <= x + ' r)).
  pose proof (CRAbsSmall_ball x y r)...
 unfold AbsSmall.
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
Lemma in_CRgball (r: Q) (x y: CR): x - ' r <= y /\ y <= x + ' r <-> gball r x y.
Proof with intuition.
 unfold gball.
 destruct Qdec_sign as [[?|?]|?].
   intuition.
   generalize (CRle_trans H0 H1).
   rewrite <- CRplus_le_l.
   rewrite CRopp_Qopp.
   rewrite CRle_Qle.
   clear H0 H1.
   intros.
   apply Qlt_irrefl with 0.
   apply Qlt_le_trans with (-r)%Q.
    change (- 0 < - r)%Q.
    apply Qopp_lt_compat...
   apply Qle_trans with r...
  rewrite <- in_CRball...
 rewrite q CRopp_Qopp CRplus_0_r CRle_def...
Qed.  

Lemma CRgball_plus (x x' y y': CR) e1 e2:
  gball e1 x x' -> gball e2 y y' -> gball (e1 + e2) (x + y)%CR (x' + y')%CR.
Proof with auto.
 do 3 rewrite <- in_CRgball.
 intros [A B] [C D].
 CRring_replace (x + y - ' (e1 + e2)) (x - ' e1 + (y - ' e2)).
 CRring_replace (x + y + ' (e1 + e2)) (x + ' e1 + (y + ' e2)).
 split; apply CRplus_le_compat...
Qed.

Lemma Qlt_from_CRlt (a b: Q): (' a < ' b)%CR -> (a < b)%Q.
Proof with auto.
 unfold CRlt.
 unfold CRpos.
 intros [[e p] H].
 revert H.
 simpl.
 rewrite CRminus_Qminus.
 rewrite CRle_Qle.
 intros.
 apply Qlt_le_trans with (a + e)%Q.
  pose proof (Qplus_resp_Qlt _ _ p a).
  ring_simplify in H0...
 apply Q.Qplus_le_l with (-a)%Q.
 ring_simplify.
 rewrite Qplus_comm...
Qed.

Lemma CRlt_trans (x y z: CR): x < y -> y < z -> x < z.
Proof.
 destruct CRisCOrdField.
 destruct ax_less_strorder.
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

Lemma lower_CRapproximation (x: CR) (e: Qpos): ' (approximate x e - e) <= x.
Proof.
 intros. rewrite <- CRminus_Qminus.
 apply CRplus_le_r with ('e)%CR.
 ring_simplify. rewrite CRplus_comm.
 apply in_CRball, ball_approx_r.
Qed.

Lemma upper_CRapproximation (x: CR) (e: Qpos): x <= ' (approximate x e + e).
Proof.
 intros. rewrite <- CRplus_Qplus.
 apply CRplus_le_r with (-'e)%CR.
 assert (' approximate x e + 'e - 'e == ' approximate x e)%CR as E by ring. rewrite E.
 apply in_CRball, ball_approx_r.
Qed.

Hint Immediate lower_CRapproximation upper_CRapproximation.

Lemma CRlt_Qmid (x y: CR): x < y -> { q: Q & x < 'q and 'q < y }.
Proof with auto.
 intros [q E].
 set (quarter := ((1#4)*q)%Qpos).
 exists (quarter + (approximate x quarter + quarter))%Q.
 split.
  apply CRle_lt_trans with (' (0 + (approximate x quarter + quarter)))%CR...
   rewrite Qplus_0_l...
  apply CRlt_Qlt.
  apply Qplus_resp_Qlt...
 apply CRlt_le_trans with (x + 'q)%CR.
  apply CRlt_le_trans with (' (approximate x quarter - quarter + q))%CR.
   apply CRlt_Qlt.
   setoid_replace (QposAsQ q) with (quarter + quarter + quarter + quarter)%Q.
    ring_simplify.
    apply Qplus_resp_Qlt.
    apply Qmult_lt_compat_r...
    reflexivity.
   simpl. ring.
  rewrite <- CRplus_Qplus.
  apply CRplus_le_compat...
  apply CRle_refl.
 apply CRplus_le_r with (-x)%CR.
 CRring_replace (x + 'q - x) ('q)...
Qed.

Lemma CRle_not_lt (x y: CR): (x <= y)%CR <-> Not (y < x)%CR.
Proof.
 destruct CRisCOrdField.
 simpl in def_leEq.
 apply def_leEq.
Qed.

Lemma CRnonNeg_le_0 x: CRnonNeg x <-> '0 <= x.
Proof.
 unfold CRle.
 assert (x - '0 == x)%CR as E by ring.
 rewrite E.
 intuition.
Qed.

Lemma CRnonNeg_0: CRnonNeg ('0)%CR.
Proof.
 unfold CRnonNeg. simpl. intros.
 rewrite <- (Qopp_opp 0).
 apply Qopp_le_compat.
 change (0 <= e)%Q. auto.
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
 apply Q.Qplus_le_l with e.
 ring_simplify.
 apply H.
 intros.
 rewrite approximate_CRminus.
 simpl.
 cut (approximate x ((1 # 2) * e0)%Qpos - approximate x e <= e0 + e)%Q.
  intros.
  apply Q.Qplus_le_l with (e0 + approximate x ((1#2)*e0)%Qpos - approximate x e)%Q.
  ring_simplify...
 apply Qle_trans with (Qabs (approximate x ((1 # 2) * e0)%Qpos - approximate x e))%Q.
  apply Qle_Qabs.
 apply Qle_trans with (((1#2)*e0)%Qpos + e)%Q...
  pose proof (regFun_prf x ((1#2)*e0)%Qpos e).
  apply Qball_Qabs in H0...
 apply Qplus_le_compat.
  simpl.
  rewrite <- (Qmult_1_r e0) at 2.
  rewrite (Qmult_comm e0).
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
  rewrite CRle_opp CRopp_opp CRopp_Qopp.
  apply H.
  rewrite CRle_opp CRopp_Qopp Qopp_opp...
 rewrite CRle_opp CRopp_Qopp.
 apply H.
 rewrite CRle_opp CRopp_Qopp CRopp_opp Qopp_opp...
Qed.

Lemma Qle_CRle (x y: CR): (forall x' y', ' x' <= x -> y <= ' y' -> (x' <= y')%Q) <-> x <= y.
Proof with auto.
 split; intros.
  apply Qle_CRle_l. intros.
  apply Qle_CRle_r. intros.
  apply CRle_Qle...
 apply CRle_Qle.
 apply CRle_trans with x...
 apply CRle_trans with y...
Qed.

Lemma scale_0 x: scale 0 x == '0.
Proof. rewrite <- CRmult_scale. ring. Qed.

Lemma scale_CRplus (q: Q) (x y: CR): scale q (x + y) == scale q x + scale q y.
Proof. intros. do 3 rewrite <- CRmult_scale. ring. Qed.

Lemma scale_CRopp (q: Q) (x: CR): scale q (-x) == - scale q x.
Proof. intros. do 2 rewrite <- CRmult_scale. ring. Qed.
