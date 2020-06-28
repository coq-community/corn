(*
Copyright © 2008 Russell O’Connor

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
Require Import CoRN.model.totalorder.QposMinMax.
Require Import CoRN.reals.fast.CRArith.
Require Import CoRN.stdlib_omissions.List.
Require Import CoRN.model.metric2.Qmetric.
Require Import CoRN.model.rings.Qring.
Require Import CoRN.tactics.Qauto.
Require Import CoRN.tactics.CornTac.

Local Open Scope Q_scope.

Definition CRsum_list_raw (l:list CR) (e:QposInf) : Q :=
fold_left Qplus
match l with
| nil => nil
| cons h t =>
  let e' := QposInf_mult (Qpos2QposInf (1#(P_of_succ_nat (length t))))%Qpos e in
   (map (fun x => approximate x e') l)
end
0.

Lemma CRsum_list_prf : forall l, is_RegularFunction (CRsum_list_raw l).
Proof.
 intros [|a t] e1 e2.
  apply ball_refl. apply (Qpos_nonneg (e1 + e2)).
 unfold CRsum_list_raw.
 simpl.
 set (p:=P_of_succ_nat (@length (RegularFunction Q_as_MetricSpace) t)).
 set (e1':=((1 # p) * e1)%Qpos).
 set (e2':=((1 # p) * e2)%Qpos).
 simpl in e1'. fold e1'.
 simpl in e2'. fold e2'.
 assert (Qball (proj1_sig e1' + proj1_sig e2') (0 + approximate a e1') (0 + approximate a e2')).
 { ring_simplify. apply (regFun_prf a). }
  assert (X:forall e:Qpos, proj1_sig ((1 # p) * e)%Qpos*(length t)
                      + proj1_sig ((1 # p) * e)%Qpos <= proj1_sig e).
 { intros e.
  autorewrite with QposElim.
  replace LHS with (((1#p)*(length t) + (1#p))* proj1_sig e) by simpl; ring.
  rewrite -> Qmake_Qdiv.
  field_simplify (Zpos 1 / p * length t + 1%positive / p);[|unfold Qeq; auto with *].
  setoid_replace ((length t + 1) / p) with 1.
   rewrite Qmult_1_l.
   auto with *.
  unfold p.
  change 1 with (1%nat:Q).
  rewrite <- injz_plus.
  rewrite <- inj_plus.
  rewrite plus_comm.
  simpl.
  field.
  discriminate. }
 generalize (X e1) (X e2).
 simpl ((1 # p) * e1)%Qpos. simpl ((1 # p) * e2)%Qpos.
 fold e1' e2'. 
 unfold e1' at 1 3.
 unfold e2' at 1 3.
 generalize (Qpos_mult
               (@exist Q (Qlt {| Qnum := Z0; Qden := xH |})
                       {| Qnum := xH; Qden := p |} (@eq_refl comparison Lt)) e1)
            (Qpos_mult
               (@exist Q (Qlt {| Qnum := Z0; Qden := xH |})
                       {| Qnum := xH; Qden := p |} (@eq_refl comparison Lt)) e2)
            e1' e2'
            (0 + approximate a e1') (0 + approximate a e2') H.
 clear - t.
 induction t; intros e1'' e2'' e1' e2' x y Hxy H1 H2.
  simpl in *.
  ring_simplify in H1.
  ring_simplify in H2.
  apply (@ball_weak_le Q_as_MetricSpace (proj1_sig e1' + proj1_sig e2')); auto.
  apply Qplus_le_compat; auto.
 simpl in *.
 change (Zpos (P_of_succ_nat (length t))) with (Z_of_nat (1+(length t))) in H1.
 change (Zpos (P_of_succ_nat (length t))) with (Z_of_nat (1+(length t))) in H2.
 rewrite ->  inj_plus in *.
 rewrite ->  injz_plus in *.
 ring_simplify in H1.
 ring_simplify in H2.
 apply (IHt e1'' e2'' (e1'' + e1')%Qpos (e2'' + e2')%Qpos);
   try (autorewrite with QposElim; ring_simplify; assumption).
 unfold Qball.
 autorewrite with QposElim.
 unfold QAbsSmall.
 setoid_replace (x + approximate a e1'' - (y + approximate a e2''))%Q
   with ((x - y) + (approximate a e1'' - approximate a e2'')).
 2: ring.
 simpl.
 setoid_replace (proj1_sig e1'' + proj1_sig e1' + (proj1_sig e2'' + proj1_sig e2'))%Q
   with ((proj1_sig e1' + proj1_sig e2') + (proj1_sig e1'' + proj1_sig e2''))%Q.
 2: ring.
 apply QAbsSmall_plus.
  auto.
 apply: (regFun_prf a).
 simpl. rewrite Qplus_assoc. assumption.
 simpl. rewrite Qplus_assoc. assumption.
Qed.

Definition CRsum_list (l:list CR) : CR := Build_RegularFunction (CRsum_list_prf l).

Lemma CRsum_correct : forall l, (CRsum_list l == fold_right (fun x y => x + y) 0 l)%CR.
Proof.
 induction l.
  apply: regFunEq_e; intros e.
  apply ball_refl. apply (Qpos_nonneg (e+e)).
 simpl (fold_right (fun x y : CR => (x + y)%CR) 0%CR (a :: l)).
 rewrite <- IHl.
 clear -l.
 apply: regFunEq_e; intros e.
 simpl.
 unfold Cap_raw.
 simpl.
 unfold CRsum_list_raw.
 simpl.
 destruct l; simpl.
  ring_simplify.
  setoid_replace (proj1_sig e+proj1_sig e)
    with (proj1_sig ((1 # 1) *e + (1 # 2) * e + (1 # 2) * e))%Qpos
         by (simpl; ring).
  apply: ball_weak. apply Qpos_nonneg.
  apply regFun_prf.
 set (n:=  (@length (RegularFunction Q_as_MetricSpace) l)).
 cut (forall (z1:Q) (e3 e5 e1 e2 e4 e6:Qpos) (z2 z3:Q),
         ball (proj1_sig e5) z1 z2 ->
         (z3 == approximate a e3 + z1)
         -> (proj1_sig e1*n + proj1_sig e2*n +proj1_sig e3 + proj1_sig e4 + proj1_sig e5  <= proj1_sig e6)
         -> Qball (proj1_sig e6) (fold_left Qplus
     (map (fun x : RegularFunction Q_as_MetricSpace => approximate x e1) l) z3) (approximate a e4 +
       fold_left Qplus (map (fun x : RegularFunction Q_as_MetricSpace => approximate x e2) l) z2)).
 { intros H.
  apply (H (approximate s ((1 # Pos.succ (P_of_succ_nat n)) * e)%Qpos)
           ((1 # Pos.succ (P_of_succ_nat n)) * e)%Qpos
           ((1 # Pos.succ (P_of_succ_nat n)) * e +
            (1 # P_of_succ_nat n) * ((1 # 2) * e))%Qpos
           _ _ _ (e+e)%Qpos).
    rewrite -> Qplus_0_l.
    apply: regFun_prf.
    rewrite Qplus_0_l. reflexivity.
    simpl.
  replace LHS with ((1 # Pos.succ (P_of_succ_nat n)) * (2+n) *proj1_sig e +
                    ((1 # P_of_succ_nat n) * (1 + n) * ((1 # 2) * proj1_sig e)  + (1 # 2) * proj1_sig e))
      by simpl; ring.
  setoid_replace ((1 # Pos.succ (Pos.of_succ_nat n)) * (2 + n)) with 1.
  setoid_replace ((1 # Pos.of_succ_nat n) * (1 + n)) with 1.
  field_simplify.
  setoid_replace (8 # 4) with 2 by reflexivity. apply Qle_refl.
  unfold Qmult, inject_Z, Qplus, Qeq, Qnum, Qden.
  ring_simplify. rewrite Pos.mul_1_r.
  rewrite Z.P_of_succ_nat_Zplus. reflexivity.
  unfold Qmult, inject_Z, Qplus, Qeq, Qnum, Qden.
  ring_simplify. rewrite Pos.mul_1_r.
  rewrite <- SuccNat2Pos.inj_succ.
  rewrite Z.P_of_succ_nat_Zplus.
  replace (S n) with (1+n)%nat by reflexivity.
  rewrite Nat2Z.inj_add.
  rewrite (Z.add_comm 1%nat). rewrite <- Z.add_assoc. reflexivity. }
 unfold n.
 clear n.
 induction l; intros z1 e3 e5 e1 e2 e4 e6 z2 z3 Hz H0 H.
  simpl in *.
  ring_simplify in H.
  ring_simplify.
  rewrite -> H0.
  unfold Qball.
  unfold QAbsSmall.
  setoid_replace (approximate a e3 + z1 - (approximate a e4 + z2))
    with ((approximate a e3 - approximate a e4) + (z1 - z2)). 2: ring.
  pose proof (@ball_weak_le Q_as_MetricSpace
                       (proj1_sig e3 + proj1_sig e4 + proj1_sig e5)
                       (proj1_sig e6)
                       (approximate a e3 - approximate a e4 + (z1 - z2)) 0).
  simpl in H1. unfold Qball, QAbsSmall in H1.
  unfold Qminus in H1. rewrite Qplus_0_r in H1.
  apply H1. exact H.
  apply QAbsSmall_plus; auto.
  apply: (regFun_prf a).
 simpl.
 apply (IHl (z1 + approximate a0 e1) e3 (e5 + (e1 + e2))%Qpos).
   simpl.
   unfold Qball.
   unfold QAbsSmall.
   setoid_replace (z1 + approximate a0 e1 - (z2 + approximate a0 e2))
     with ((z1 - z2) + (approximate a0 e1 - approximate a0 e2)). 2: ring.
   apply QAbsSmall_plus.
    auto.
   apply (regFun_prf a0).
  rewrite -> H0.
  ring.
  simpl.
 simpl in H.
 set (n:=  (@length (RegularFunction Q_as_MetricSpace) l)) in *.
 change (Zpos (P_of_succ_nat n)) with (Z_of_nat (1+n)) in H.
 rewrite inj_plus in H.
 rewrite -> injz_plus in H.
 replace LHS with (proj1_sig e1 * (1 + n) + proj1_sig e2 * (1 + n) + proj1_sig e3 + proj1_sig e4 + proj1_sig e5) by simpl; ring.
 auto.
Qed.
