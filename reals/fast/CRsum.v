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
Require Import CRArith.
Require Import List.
Require Import Qmetric.
Require Import Qring.
Require Import Qauto.
Require Import CornTac.

Open Local Scope Q_scope.

Definition CRsum_list_raw (l:list CR) (e:QposInf) : Q :=
fold_left Qplus
match l with
| nil => nil
| cons h t =>
  let e' := QposInf_mult (1#(P_of_succ_nat (length t)))%Qpos e in
   (map (fun x => approximate x e') l)
end
0.

Lemma CRsum_list_prf : forall l, is_RegularFunction (CRsum_list_raw l).
Proof.
 intros [|a t] e1 e2.
  apply ball_refl.
 unfold CRsum_list_raw.
 simpl.
 set (p:=P_of_succ_nat (@length (RegularFunction Q_as_MetricSpace) t)).
 set (e1':=((1 # p) * e1)%Qpos).
 set (e2':=((1 # p) * e2)%Qpos).
 assert (Qball (e1' + e2') (0 + approximate a e1') (0 + approximate a e2')).
  ring_simplify.
  apply (regFun_prf a).
 assert (X:forall e:Qpos, ((1 # p) * e)%Qpos*(length t) + ((1 # p) * e)%Qpos <= e).
  intros e.
  autorewrite with QposElim.
  replace LHS with (((1#p)*(length t) + (1#p))*e) by simpl; ring.
  rewrite -> Qmake_Qdiv.
  field_simplify (1%positive / p * length t + 1%positive / p);[|unfold Qeq; auto with *].
  setoid_replace ((length t + 1) / p) with 1.
   auto with *.
  unfold p.
  change 1 with (1%nat:Q).
  rewrite <- injz_plus.
  rewrite <- inj_plus.
  rewrite plus_comm.
  simpl.
  field.
  discriminate.
 generalize (X e1) (X e2).
 fold e1' e2'.
 unfold e1' at 1 3.
 unfold e2' at 1 3.
 generalize ((1 # p) * e1)%Qpos ((1 # p) * e2)%Qpos e1' e2' (0 + approximate a e1') (0 + approximate a e2') H.
 clear - t.
 induction t; intros e1'' e2'' e1' e2' x y Hxy H1 H2.
  simpl in *.
  ring_simplify in H1.
  ring_simplify in H2.
  apply (@ball_weak_le Q_as_MetricSpace (e1' + e2')); auto.
  autorewrite with QposElim.
  apply Qplus_le_compat; auto.
 simpl in *.
 change ('P_of_succ_nat (length t))%Z with (Z_of_nat (1+(length t))) in H1.
 change ('P_of_succ_nat (length t))%Z with (Z_of_nat (1+(length t))) in H2.
 rewrite ->  inj_plus in *.
 rewrite ->  injz_plus in *.
 ring_simplify in H1.
 ring_simplify in H2.
 apply (IHt e1'' e2'' (e1'' + e1')%Qpos (e2'' + e2')%Qpos);
   try (autorewrite with QposElim; ring_simplify; assumption).
 unfold Qball.
 autorewrite with QposElim.
 replace RHS with ((x - y) + (approximate a e1'' - approximate a e2'')) by simpl; ring.
 replace LHS with ((e1' + e2') + (e1'' + e2'')) by simpl; ring.
 apply AbsSmall_plus.
  auto.
 apply: (regFun_prf a).
Qed.

Definition CRsum_list (l:list CR) : CR := Build_RegularFunction (CRsum_list_prf l).

Lemma CRsum_correct : forall l, (CRsum_list l == fold_right (fun x y => x + y) ('0) l)%CR.
Proof.
 induction l.
  apply: regFunEq_e; intros e.
  apply ball_refl.
 simpl (fold_right (fun x y : CR => (x + y)%CR) (' 0)%CR (a :: l)).
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
  setoid_replace (e+e)%Qpos with ((1 # 1) *e + (1 # 2) * e + (1 # 2) * e)%Qpos by QposRing.
  apply: ball_weak.
  apply regFun_prf.
 set (n:=  (@length (RegularFunction Q_as_MetricSpace) l)).
 cut (forall (z1:Q) (e3 e5 e1 e2 e4 e6:Qpos) (z2 z3:Q), ball e5 z1 z2 ->
   (z3 == approximate a e3 + z1) -> (e1*n + e2*n +e3 +e4 + e5  <= e6) -> Qball e6 (fold_left Qplus
     (map (fun x : RegularFunction Q_as_MetricSpace => approximate x e1) l) z3) (approximate a e4 +
       fold_left Qplus (map (fun x : RegularFunction Q_as_MetricSpace => approximate x e2) l) z2)).
  intros H.
  apply (H (approximate s ((1 # Psucc (P_of_succ_nat n)) * e)%Qpos)
    ((1 # Psucc (P_of_succ_nat n)) * e)%Qpos ((1 # Psucc (P_of_succ_nat n)) * e +
      (1 # P_of_succ_nat n) * ((1 # 2) * e))%Qpos).
    simpl.
    rewrite -> Qplus_0_l.
    apply: regFun_prf.
   ring.
  autorewrite with QposElim.
  replace LHS with ((1 # Psucc (P_of_succ_nat n)) * (2+n) *e +
    ((1 # P_of_succ_nat n) * (1 + n) * ((1 # 2) * e)  + (1 # 2) * e)) by simpl; ring.
  repeat rewrite -> Qmake_Qdiv.
  change (Zpos (Psucc (P_of_succ_nat n))) with (Z_of_nat (1+1+n)).
  change (Zpos (P_of_succ_nat n)) with (Z_of_nat (1+n)).
  repeat rewrite -> inj_plus.
  repeat rewrite -> injz_plus.
  field_simplify.
   apply Qle_shift_div_r; auto with *.
   field_simplify.
   apply Qle_refl.
  clear - n.
  rewrite <- (injz_plus 1 n).
  rewrite <- (injz_plus 2 n).
  assert (forall (z:Z), ~z=0%Z -> ~z==0).
   intros [|z|z]; auto with *.
  auto with *.
 unfold n.
 clear n.
 induction l; intros z1 e3 e5 e1 e2 e4 e6 z2 z3 Hz H0 H.
  simpl in *.
  ring_simplify in H.
  ring_simplify.
  rewrite -> H0.
  unfold Qball.
  replace RHS with ((approximate a e3 - approximate a e4) + (z1 - z2)) by simpl; ring.
  apply AbsSmall_leEq_trans with (e3 + e4 + e5); auto.
  apply AbsSmall_plus; auto.
  apply: (regFun_prf a).
 simpl.
 apply (IHl (z1 + approximate a0 e1) e3 (e5 + (e1 + e2))%Qpos).
   simpl.
   unfold Qball.
   replace RHS with ((z1 - z2) + (approximate a0 e1 - approximate a0 e2)) by simpl; ring.
   rewrite Q_Qpos_plus.
   apply AbsSmall_plus.
    auto.
   apply (regFun_prf a0).
  rewrite -> H0.
  ring.
 autorewrite with QposElim.
 simpl in H.
 set (n:=  (@length (RegularFunction Q_as_MetricSpace) l)) in *.
 change (Zpos (P_of_succ_nat n)) with (Z_of_nat (1+n)) in H.
 rewrite inj_plus in H.
 rewrite -> injz_plus in H.
 replace LHS with (e1 * (1 + n) + e2 * (1 + n) + e3 + e4 + e5) by simpl; ring.
 auto.
Qed.
