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

Require Import Cauchy_IR.
Require Import CornTac.
Require Import Omega.
Require Import Qmetric.
Require Import QMinMax.
Require Import Qabs.
Require Export CRFieldOps.

Opaque Qmin Qmax.

(**
** Isomorphism between CR and Cauchy_IR
In prove that CR is a real number structure, we must climb the algebraic
heirarchy.  The easiest way of doing this is to construct an isomorphism
between Cauchy_IR and CR because they are similar strucutres.
Then we can leverage the proofs that Cauchy_IR is a real number structure.

*** CR to Cauchy_IR
*)

Definition CRasCauchy_IR_raw (x:CR) (n:nat) := approximate x (1 # P_of_succ_nat n)%Qpos.

Lemma CRasCauchy_IR_raw_is_Cauchy : forall (x:CR),
Cauchy_prop (R:=Q_as_COrdField) (CRasCauchy_IR_raw x).
Proof.
 intros x e He.
 rewrite <- (QposAsmkQpos He).
 generalize (mkQpos He).
 clear e He.
 intros [en ed].
 unfold CRasCauchy_IR_raw.
 exists (pred (nat_of_P (2*ed))).
 rewrite <- anti_convert_pred_convert.
 intros m Hm.
 change (ball (en#ed) (approximate x (1 # P_of_succ_nat m)%Qpos) (approximate x (1#(2*ed)))%Qpos).
 apply: ball_weak_le;[|apply regFun_prf].
 autorewrite with QposElim.
 apply Qle_trans with (((1 # P_of_succ_nat (pred (nat_of_P (2*ed)))) + (1 # 2 * ed)))%Q.
  apply: plus_resp_leEq.
  change (P_of_succ_nat (pred (nat_of_P (2*ed))) <= P_of_succ_nat m)%Z.
  destruct (Z_lt_le_dec (P_of_succ_nat m)(P_of_succ_nat (pred (nat_of_P (2 * ed)))))%Z.
   elim (le_not_lt _ _ Hm).
   apply surj_lt.
   repeat rewrite succ_nat in z.
   omega.
  assumption.
 rewrite <- anti_convert_pred_convert.
 stepl ((2#1)*(1#(2*ed)))%Q; [|simpl; ring].
 change ((2#1)*((1/2)*(1/ed)) <= en#ed)%Q.
 ring_simplify.
 change ((2#2)*(1/ed)<=en#ed)%Q.
 setoid_replace (2#2)%Q  with 1%Q by constructor.
 ring_simplify.
 auto with *.
Qed.

Definition CRasCauchy_IR (x:CR) : Cauchy_IR :=
Build_CauchySeq _ _ (CRasCauchy_IR_raw_is_Cauchy x).

Lemma CRasCauchy_IR_wd : forall (x y:CR), (x==y)%CR -> CRasCauchy_IR x[=]CRasCauchy_IR y.
Proof.
 intros x y Hxy.
 apply: Eq_alt_2_2.
 intros e He.
 rewrite <- (QposAsmkQpos He).
 generalize (mkQpos He).
 clear He e.
 intros [en ed].
 exists (pred(nat_of_P (2*ed))).
 intros m Hm.
 simpl.
 unfold CRasCauchy_IR_raw.
 set (d:=(1 # P_of_succ_nat m)%Qpos).
 change (ball (en#ed)%Qpos (approximate x d) (approximate y d)).
 apply: ball_weak_le;[|apply Hxy].
 unfold d.
 autorewrite with QposElim.
 ring_simplify.
 apply Qle_trans with ((2#1)*(1#(2 * ed)))%Q.
  apply: mult_resp_leEq_lft;try discriminate.
  change ((2*ed)<=P_of_succ_nat m)%Z.
  rewrite <- Zpos_mult_morphism.
  rewrite (anti_convert_pred_convert (2*ed)).
  do 2 rewrite <- POS_anti_convert.
  apply inj_le.
  auto with *.
 change (1#2*ed)%Q with ((1#2)*(1#ed))%Q.
 ring_simplify.
 auto with *.
Qed.

(**
*** Cauchy_IR to CR
*)

Definition Cauchy_IRasCR_raw (x:Cauchy_IR) (e:QposInf) : Q.
Proof.
 intros x [e|];[|exact 0%Q].
 destruct x as [f Hf].
 unfold Cauchy_prop in Hf.
 destruct (Hf (e:Q) (Qpos_prf e)) as [n Hn].
 exact (f n).
Defined.

Lemma Cauchy_IRasCR_is_Regular : forall (x:Cauchy_IR),
is_RegularFunction (Cauchy_IRasCR_raw x).
Proof.
 intros [f Hf] e1 e2.
 simpl.
 destruct (Hf (e1:Q) (Qpos_prf e1)) as [n1 Hn1].
 destruct (Hf (e2:Q) (Qpos_prf e2)) as [n2 Hn2].
 cut (forall (e1 e2:Qpos) n1 n2, n2 <= n1 ->
   (forall m : nat, n1 <= m -> AbsSmall (R:=Q_as_COrdField) (e1:Q) (f m[-]f n1)) ->
     (forall m : nat, n2 <= m -> AbsSmall (R:=Q_as_COrdField) (e2:Q) (f m[-]f n2)) ->
       Qball (e1 + e2) (f n1) (f n2)).
  intros H.
  destruct (le_ge_dec n1 n2).
   apply: ball_sym;simpl.
   setoid_replace (e1+e2)%Qpos with (e2+e1)%Qpos by QposRing.
   apply H; assumption.
  auto.
 clear - Hf.
 intros e1 e2 n1 n2 H Hn1 Hn2.
 setoid_replace (e1+e2)%Qpos with (e2+e1)%Qpos by QposRing.
 apply: ball_weak.
 apply: Hn2.
 assumption.
Qed.

Definition Cauchy_IRasCR (x:Cauchy_IR) : CR :=
Build_RegularFunction (Cauchy_IRasCR_is_Regular x).

Lemma Cauchy_IRasCR_wd : forall (x y:Cauchy_IR), x[=]y -> (Cauchy_IRasCR x==Cauchy_IRasCR y)%CR.
Proof.
 intros [x Hx] [y Hy] Hxy.
 apply: regFunEq_e.
 intros e.
 apply ball_closed.
 intros d.
 simpl.
 destruct (Hx (e:Q) (Qpos_prf e)) as [a Ha].
 destruct (Hy (e:Q) (Qpos_prf e)) as [b Hb].
 destruct (Eq_alt_2_1 _ _ _ Hxy _ (Qpos_prf d)) as [c Hc].
 simpl in Hc.
 unfold Qball.
 set (n:=max (max a b) c).
 stepr ((x a - x n) + (y n - y b) + (x n - y n))%Q; [| simpl; ring].
 autorewrite with QposElim.
 repeat (apply: AbsSmall_plus).
   apply AbsSmall_minus.
   apply Ha;unfold n;apply le_trans with (max a b); auto with *.
  apply Hb; unfold n;apply le_trans with (max a b); auto with *.
 apply Hc; unfold n;auto with *.
Qed.

(** Composition is the identity *)
Lemma CRasCR : forall x:CR, (Cauchy_IRasCR (CRasCauchy_IR x)==x)%CR.
Proof.
 intros x.
 apply: regFunEq_e.
 intros e.
 simpl.
 destruct (CRasCauchy_IR_raw_is_Cauchy x (e:Q) (Qpos_prf e)) as [n Hn].
 unfold CRasCauchy_IR_raw in *.
 apply: ball_closed.
 intros [dn dd].
 setoid_replace (e+e+(dn#dd))%Qpos with (e+((dn#dd)+e))%Qpos by QposRing.
 apply ball_triangle with (approximate x (1#P_of_succ_nat (n+(nat_of_P dd))))%Qpos.
  apply ball_sym.
  apply: Hn;auto with *.
 apply: ball_weak_le;[|apply regFun_prf].
 autorewrite with QposElim.
 apply: plus_resp_leEq;simpl.
 apply Qle_trans with (1#dd)%Q.
  change (dd <= P_of_succ_nat (n + nat_of_P dd))%Z.
  destruct n.
   simpl.
   rewrite P_of_succ_nat_o_nat_of_P_eq_succ.
   rewrite Pplus_one_succ_r.
   rewrite Zpos_plus_distr.
   auto with *.
  rewrite <- nat_of_P_o_P_of_succ_nat_eq_succ.
  rewrite <- nat_of_P_plus_morphism.
  rewrite P_of_succ_nat_o_nat_of_P_eq_succ.
  rewrite Pplus_one_succ_r.
  repeat rewrite Zpos_plus_distr.
  rewrite <- Zplus_assoc.
  rewrite Zplus_comm.
  rewrite <- Zplus_assoc.
  rewrite <- Zpos_plus_distr.
  rewrite <- Pplus_one_succ_l.
  change (dd+0 <=  dd + Psucc (P_of_succ_nat n))%Z.
  auto with *.
 change (dd <= dn*dd)%Z.
 auto with *.
Qed.

Lemma Cauchy_IRasCauchy_IR : forall x:Cauchy_IR, CRasCauchy_IR (Cauchy_IRasCR x)[=]x.
Proof.
 intros [x Hx].
 apply: Eq_alt_2_2.
 intros e He.
 rewrite <- (QposAsmkQpos He).
 set (e':=(mkQpos He)).
 clearbody e'.
 clear e He.
 assert (Z:(0<(1#2)*e')%Q).
  rewrite <- (Qmult_0_r (1#2)).
  apply: mult_resp_less_lft.
   apply Qpos_prf.
  constructor.
 destruct (Hx _ Z) as [n Hn].
 destruct e' as [en ed].
 exists (max n (nat_of_P ed)).
 intros m Hm.
 simpl.
 destruct (Hx ((1 # P_of_succ_nat m)%Qpos:Q) (Qpos_prf (1 # P_of_succ_nat m)%Qpos)) as [n' Hn'].
 apply AbsSmall_minus.
 destruct (le_lt_dec n' m) as [H|H].
  apply: AbsSmall_trans;[|apply Hn';assumption].
  change (ed < en*(P_of_succ_nat m))%Z.
  apply Zlt_le_trans with (P_of_succ_nat m).
   rewrite <- POS_anti_convert.
   rewrite Zpos_eq_Z_of_nat_o_nat_of_P.
   apply inj_lt.
   apply le_lt_n_Sm.
   apply le_trans with (max n (nat_of_P ed));auto with *.
  change (1*P_of_succ_nat m <= en * P_of_succ_nat m)%Z.
  apply Zmult_lt_0_le_compat_r;auto with *.
 stepl ((1#2)*(en#ed)%Qpos+(1#2)*(en#ed)%Qpos)%Q; [| simpl; ring].
 rstepr ((x m[-]x n)[+](x n[-]x n')).
 assert (Y:n <= m).
  apply le_trans with (max n (nat_of_P ed));auto with *.
 apply AbsSmall_plus.
  apply Hn.
  assumption.
 apply AbsSmall_minus; auto with *.
Qed.

(** Equalities are well defined. *)
Lemma Cauchy_IR_eq_as_CR_eq : forall (x y:Cauchy_IR),
((Cauchy_IRasCR x) == (Cauchy_IRasCR y))%CR <-> x[=]y.
Proof.
 intros x y.
 split;[|apply Cauchy_IRasCR_wd].
 intros H.
 stepl (CRasCauchy_IR (Cauchy_IRasCR x)); [| apply Cauchy_IRasCauchy_IR].
 stepr (CRasCauchy_IR (Cauchy_IRasCR y)); [| apply Cauchy_IRasCauchy_IR].
 apply CRasCauchy_IR_wd.
 assumption.
Qed.

Lemma CR_eq_as_Cauchy_IR_eq : forall (x y:CR),
(CRasCauchy_IR x [=] CRasCauchy_IR y) <-> (x==y)%CR.
Proof.
 intros x y.
 set (x':=CRasCauchy_IR x).
 set (y':=CRasCauchy_IR y).
 rewrite <- (CRasCR x).
 rewrite <- (CRasCR y).
 symmetry.
 apply Cauchy_IR_eq_as_CR_eq.
Qed.

Open Local Scope uc_scope.
(**
*** Functions preserved by isomorphism.
*)
Lemma reverse_iso_wd_fun : forall
(f:Cauchy_IR -> Cauchy_IR)
(g:CR -> CR),
(forall x y, (x==y -> g x == g y)%CR) ->
(forall (x:Cauchy_IR),
(g (Cauchy_IRasCR x) == Cauchy_IRasCR (f x))%CR) ->
forall (x:CR),
(f (CRasCauchy_IR x) [=] CRasCauchy_IR (g x)).
Proof.
 intros f g g_wd H x.
 stepl (CRasCauchy_IR (Cauchy_IRasCR (f (CRasCauchy_IR x)))); [| apply Cauchy_IRasCauchy_IR].
 apply CRasCauchy_IR_wd.
 symmetry.
 transitivity (g (Cauchy_IRasCR (CRasCauchy_IR x))); try apply H.
 apply g_wd.
 symmetry.
 apply CRasCR.
Qed.

Lemma reverse_iso_uc_fun : forall
(f:Cauchy_IR -> Cauchy_IR)
(g:CR --> CR),
(forall (x:Cauchy_IR),
(g (Cauchy_IRasCR x) == Cauchy_IRasCR (f x))%CR) ->
forall (x:CR),
(f (CRasCauchy_IR x) [=] CRasCauchy_IR (g x)).
Proof.
 intros f g H x.
 apply reverse_iso_wd_fun.
  apply uc_wd.
 assumption.
Qed.

Lemma reverse_iso_bin_wd_fun : forall
(f:Cauchy_IR -> Cauchy_IR -> Cauchy_IR)
(g:CR -> CR -> CR),
(forall w x, (w == x)%CR -> forall y z, (y == z -> g w y == g x z)%CR) ->
(forall (x y:Cauchy_IR),
(g (Cauchy_IRasCR x) (Cauchy_IRasCR y) == Cauchy_IRasCR (f x y))%CR) ->
forall (x y:CR),
(f (CRasCauchy_IR x) (CRasCauchy_IR y) [=] CRasCauchy_IR (g x y)).
Proof.
 intros f g g_wd H x y.
 stepl (CRasCauchy_IR (Cauchy_IRasCR (f (CRasCauchy_IR x) (CRasCauchy_IR y))));
   [| apply Cauchy_IRasCauchy_IR].
 apply CRasCauchy_IR_wd.
 symmetry.
 transitivity (g (Cauchy_IRasCR (CRasCauchy_IR x)) (Cauchy_IRasCR (CRasCauchy_IR y))); [|apply H].
 apply g_wd; symmetry; apply CRasCR.
Qed.

Lemma reverse_iso_bin_uc_fun : forall
(f:Cauchy_IR -> Cauchy_IR -> Cauchy_IR)
(g:CR --> CR --> CR),
(forall (x y:Cauchy_IR),
(g (Cauchy_IRasCR x) (Cauchy_IRasCR y) == Cauchy_IRasCR (f x y))%CR) ->
forall (x y:CR),
(f (CRasCauchy_IR x) (CRasCauchy_IR y) [=] CRasCauchy_IR (g x y)).
Proof.
 intros f g H x y.
 apply (reverse_iso_bin_wd_fun f (ucFun2 g)).
  apply ucFun2_wd.
 assumption.
Qed.

(** injection of rationals is preserved. *)
Lemma Cauchy_IR_inject_Q_as_CR_inject_Q : forall x:Q,
(' x == Cauchy_IRasCR (Cauchy_CReals.inject_Q _ x))%CR.
Proof.
 intros x.
 apply: regFunEq_e.
 intros e.
 simpl.
 destruct (CS_seq_const Q_as_COrdField x (e:Q) (Qpos_prf e)).
 apply: ball_refl.
Qed.

Hint Rewrite Cauchy_IR_inject_Q_as_CR_inject_Q : CRtoCauchy_IR.

Lemma CR_inject_Q_as_Cauchy_IR_inject_Q : forall x:Q,
Cauchy_CReals.inject_Q _ x [=] CRasCauchy_IR (' x)%CR.
Proof.
 intros x.
 apply: Eq_alt_2_2.
 simpl.
 intros e He.
 exists 0.
 intros m Hm.
 unfold cg_minus.
 rstepr (Zero:Q).
 apply zero_AbsSmall.
 apply Qlt_le_weak.
 assumption.
Qed.

(** plus is preserved. *)
Lemma Cauchy_IR_plus_as_CR_plus : forall x y:Cauchy_IR,
(Cauchy_IRasCR x + Cauchy_IRasCR y == Cauchy_IRasCR (x[+]y))%CR.
Proof.
 intros [x Hx] [y Hy].
 apply: regFunEq_e.
 intros e.
 simpl.
 unfold Cap_raw.
 simpl.
 destruct (Hx (((1 # 2) * e)%Qpos:Q) (Qpos_prf ((1 # 2) * e)%Qpos)) as [n1 Hn1].
 destruct (Hy (((1 # 2) * e)%Qpos:Q) (Qpos_prf ((1 # 2) * e)%Qpos)) as [n2 Hn2].
 destruct (CS_seq_plus Q_as_COrdField x y Hx Hy (e:Q) (Qpos_prf e)) as [n3 Hn3].
 set (n:= max n3 (max n1 n2)).
 change (ball (e+e) (x n1 + y n2) (x n3 + y n3))%Q.
 apply ball_triangle with (x n + y n)%Q.
  setoid_replace e with (((1 # 2) * e +(1 # 2) * e)%Qpos ) by QposRing.
  apply ball_triangle with (x n1 + y n)%Q; simpl; unfold Qball.
   stepr (y n2 - y n)%Q; [| simpl; ring].
   apply AbsSmall_minus.
   apply Hn2.
   unfold n.
   rewrite max_assoc.
   auto with *.
  stepr (x n1 - x n)%Q; [| simpl; ring].
  apply AbsSmall_minus.
  apply Hn1.
  unfold n.
  rewrite (max_comm n1).
  rewrite max_assoc.
  auto with *.
 apply: Hn3; unfold n; auto with *.
Qed.

Hint Rewrite Cauchy_IR_plus_as_CR_plus : CRtoCauchy_IR.

Lemma CR_plus_as_Cauchy_IR_plus : forall x y:CR,
CRasCauchy_IR x [+] CRasCauchy_IR y [=] CRasCauchy_IR (x+y)%CR.
Proof.
 apply reverse_iso_bin_uc_fun.
 apply Cauchy_IR_plus_as_CR_plus.
Qed.

(** opp is preserved. *)
Lemma Cauchy_IR_opp_as_CR_opp : forall x:Cauchy_IR,
(-Cauchy_IRasCR x == Cauchy_IRasCR ([--]x))%CR.
Proof.
 intros [x Hx].
 apply: regFunEq_e.
 intros e.
 simpl.
 destruct (Hx (e:Q) (Qpos_prf e)) as [n1 Hn1].
 destruct (CS_seq_inv Q_as_COrdField x Hx (e:Q) (Qpos_prf e)) as [n2 Hn2].
 set (n:=(max n1 n2)).
 change (ball (e+e) (- x n1) (- x n2))%Q.
 apply ball_triangle with (- x n)%Q; simpl; unfold Qball;
   [stepr (x n - x n1)%Q; [| simpl; ring];apply Hn1| apply Hn2]; unfold n; auto with*.
Qed.

Hint Rewrite Cauchy_IR_opp_as_CR_opp : CRtoCauchy_IR.

Lemma CR_opp_as_Cauchy_IR_opp : forall x:CR,
[--](CRasCauchy_IR x) [=] CRasCauchy_IR (- x)%CR.
Proof.
 apply reverse_iso_uc_fun.
 apply Cauchy_IR_opp_as_CR_opp.
Qed.

(** le is preserved. *)
Lemma Cauchy_IR_le_as_CR_le : forall (x y:Cauchy_IR),
(Cauchy_IRasCR x <= Cauchy_IRasCR y)%CR <-> x[<=]y.
Proof.
 intros [x Hx] [y Hy].
 split.
  intros H1 [n [e He H2]].
  assert (H1':=H1 ((1#3)*(mkQpos He))%Qpos).
  clear H1.
  simpl in H1'.
  unfold Cap_raw in H1'; simpl in H1'.
  destruct (Hy (((1 # 2) * ((1#3)*  mkQpos He))%Qpos:Q)
    (Qpos_prf ((1 # 2) * ((1#3)*mkQpos He))%Qpos)) as [n1 Hn1].
  destruct (Hx (((1 # 2) * ((1#3)* mkQpos He))%Qpos:Q)
    (Qpos_prf ((1 # 2) * ((1#3)*mkQpos He))%Qpos)) as [n2 Hn2].
  simpl in H2.
  set (m:=max n (max n1 n2)).
  assert (m1:n<=m);[unfold m; auto with *|].
  assert (m2:n1<=m);[unfold m; apply le_trans with (max n1 n2); auto with *|].
  assert (m3:n2<=m);[unfold m; apply le_trans with (max n1 n2); auto with *|].
  apply (Qle_not_lt _ _ H1').
  apply: inv_cancel_less;simpl.
  clear H1'.
  autorewrite with QposElim in *.
  apply Qlt_le_trans with ((2#3)*e)%Q.
   ring_simplify.
   apply: mult_resp_less.
    constructor.
   assumption.
  stepl (e + - ((1#2)*((1#3)*e)) + - ((1#2)*((1#3)*e)))%Q; [| simpl; ring].
  stepr ((x m - y m) + (y m - y n1) + -(x m - x n2))%Q; [| simpl; ring].
  apply: plus_resp_leEq_both.
   apply plus_resp_leEq_both.
    apply H2; assumption.
   refine (proj1 (Hn1 m _));assumption.
  apply inv_resp_leEq.
  refine (proj2 (Hn2 m _));assumption.
 (*Other Direction*)
 intros H e.
 simpl.
 unfold Cap_raw; simpl.
 destruct (Hy (((1 # 2) * e)%Qpos:Q) (Qpos_prf ((1 # 2) * e)%Qpos)) as [n1 Hn1].
 destruct (Hx (((1 # 2) * e)%Qpos:Q) (Qpos_prf ((1 # 2) * e)%Qpos)) as [n2 Hn2].
 apply Qnot_lt_le.
 intros A.
 apply H; clear H.
 exists (max n1 n2).
 simpl.
 set (n:=max n1 n2).
 exists (- e + - (y n1 + - x n2))%Q.
  rewrite <- Qlt_minus_iff.
  assumption.
 intros m Hm.
 unfold cg_minus.
 simpl.
 stepr ((x m - x n2) + -(y m - y n1) + -(y n1 + - x n2))%Q; [| simpl; ring].
 apply: plus_resp_leEq.
 stepl (-((1 # 2) * e) + - ((1 # 2) * e))%Q; [| simpl; ring].
 apply plus_resp_leEq_both.
  refine (proj1 (Hn2 _ _)).
  apply le_trans with n; [unfold n;auto with *|assumption].
 apply inv_resp_leEq.
 refine (proj2 (Hn1 _ _)).
 apply le_trans with n; [unfold n;auto with *|assumption].
Qed.

Hint Rewrite Cauchy_IR_le_as_CR_le : CRtoCauchy_IR.

Lemma CR_le_as_Cauchy_IR_le : forall (x y:CR),
CRasCauchy_IR x[<=]CRasCauchy_IR y <-> (x<=y)%CR.
Proof.
 intros x y.
 rewrite <- Cauchy_IR_le_as_CR_le.
 do 2 rewrite -> CRasCR.
 reflexivity.
Qed.

(** mult is preserved. *)
Lemma Cauchy_IR_mult_as_CRmult_bounded : forall x y:Cauchy_IR,
forall (z:Qpos) (N:nat), (forall i:nat, (N<=i) -> AbsSmall (z:Q) (CS_seq _ y i)) ->
(ucFun2 (CRmult_bounded z) (Cauchy_IRasCR x) (Cauchy_IRasCR y) == Cauchy_IRasCR (x[*]y))%CR.
Proof.
 intros [x Hx] y z N Hz.
 destruct y as [y Hy].
 apply: regFunEq_e.
 intros e.
 simpl.
 destruct (CS_seq_mult Q_as_COrdField x y Hx Hy (e:Q) (Qpos_prf e)) as [n3 Hn3].
 unfold Cap_raw.
 simpl in *.
 destruct (Hx (((1 # 2) * e / z)%Qpos:Q) (Qpos_prf ((1 # 2) * e / z)%Qpos)) as [n1 Hn1].
 apply Qscale_modulus_elim.
  intros Hxn1.
  pose (n:=(max n3 (max n1 N))).
  rewrite -> Hxn1.
  assert (Qeq (0 * Qmax (- z) (Qmin z
    (Cauchy_IRasCR_raw (Build_CauchySeq Q_as_COrdField y Hy)(QposInf_bind (fun e0 : Qpos => e0) QposInfinity))))%Q (0 * y n)%Q).
   ring.
  rewrite -> H. clear H.
  change (ball (e+e) (0 * y n) (x n3 * y n3))%Q.
  apply ball_triangle with (x n*y n)%Q;[|apply: Hn3; unfold n; auto with *].
  apply ball_sym.
  simpl.
  rewrite <- Hxn1.
  unfold Qball.
  stepr ((x n - x n1)*y n)%Q; [| simpl; ring].
  apply AbsSmall_trans with ((1#2)*e)%Q.
   apply half_3.
   apply Qpos_prf.
  stepl (((1#2)*e/z)*z)%Q; [| simpl;field;apply Qpos_nonzero].
  apply mult_AbsSmall;[apply Hn1|apply Hz]; unfold n; apply le_trans with (max n1 N); auto with *.
 intros w Hw.
 simpl.
 destruct (Hy (w:Q) (Qpos_prf w)) as [n2 Hn2].
 pose (n:=(max (max n1 n2) (max n3 N))).
 assert (n1 <= n);[unfold n; apply le_trans with (max n1 n2); auto with *|].
 assert (n2 <= n);[unfold n; apply le_trans with (max n1 n2); auto with *|].
 assert (n3 <= n);[unfold n; apply le_trans with (max n3 N); auto with *|].
 assert (N <= n);[unfold n; apply le_trans with (max n3 N); auto with *|].
 change (Qball (e+e)) with (@ball Q_as_MetricSpace (e + e)).
 apply ball_triangle with (x n * y n)%Q;[|apply: Hn3; assumption].
 clear Hn3.
 setoid_replace e with ((1#2)*e + (1#2)*e)%Qpos by QposRing.
 apply ball_triangle with (x n1 * y n)%Q; apply ball_sym; simpl; unfold Qball.
  stepr (x n1*(y n - Qmax (- z) (Qmin z (y n2))))%Q; [| simpl;ring].
  autorewrite with QposElim.
  stepl (((1#2)*e/w)*w)%Q; [| simpl;field;apply Qpos_nonzero].
  apply mult_AbsSmall;[apply Hw|].
  destruct (Hz n H2) as [X0 X1].
  destruct (Hn2 _ H0) as [X2 X3].
  unfold cg_minus in *.
  simpl in *.
  change (Qmax (- z) (Qmin z (y n2)))%Q with (QboundAbs z (y n2))%Q.
  assert (A0:(-w<=0)%Q).
   rewrite -> Qle_minus_iff.
   ring_simplify.
   apply Qpos_nonneg.
  rewrite -> Qle_minus_iff in *.
  clear - A0 X0 X1 X2 X3 Hn2 H0.
  ring_simplify in A0.
  ring_simplify in X0.
  ring_simplify in X1.
  ring_simplify in X2.
  ring_simplify in X3.
  apply QboundAbs_elim; intros I; try solve [apply Hn2;assumption]; rewrite -> Qle_minus_iff in I.
   apply AbsSmall_minus.
   unfold cg_minus;simpl.
   apply leEq_imp_AbsSmall.
    apply X1.
   rewrite -> Qle_minus_iff.
   stepr ((y n + (-1 # 1) * y n2 + w)+(y n2 + - z))%Q; [| simpl; ring].
   apply: plus_resp_nonneg; assumption.
  apply: leEq_imp_AbsSmall; simpl; ring_simplify.
   apply X0.
  rewrite -> Qle_minus_iff.
  stepr ((w + (-1 # 1) * y n + y n2)+(- z + - y n2))%Q; [| simpl; ring].
  apply: plus_resp_nonneg; assumption.
 stepr ((x n - x n1)*y n)%Q; [| simpl; ring].
 autorewrite with QposElim.
 stepl (((1#2)*e/z)*z)%Q; [| simpl; field; apply Qpos_nonzero].
 apply mult_AbsSmall;[apply Hn1;assumption|apply Hz;assumption].
Qed.

Lemma AbsSmall_Qabs : forall x y, (Qabs y <= x)%Q <-> AbsSmall x y.
Proof.
 cut (forall x y, (0 <= y)%Q -> ((Qabs y <= x)%Q <-> AbsSmall (R:=Q_as_COrdField) x y)).
  intros H x y.
  generalize (H x y) (H x (-y)%Q).
  clear H.
  rewrite -> Qabs_opp.
  apply Qabs_case; intros H H1 H2.
   auto.
  assert (X:AbsSmall (R:=Q_as_COrdField) x y <-> AbsSmall (R:=Q_as_COrdField) x (- y)%Q).
   split.
    apply inv_resp_AbsSmall.
   intros X.
   stepr (- - y)%Q; [| simpl; ring].
   apply inv_resp_AbsSmall.
   assumption.
  rewrite -> X.
  apply: H2.
  rewrite -> Qle_minus_iff in H.
  ring_simplify in H.
  ring_simplify.
  apply H.
 intros x y H.
 rewrite -> Qabs_pos;[|assumption].
 split.
  intros H0.
  apply leEq_imp_AbsSmall; assumption.
 intros [_ H0].
 assumption.
Qed.

Lemma Cauchy_IR_mult_as_CR_mult : forall x y:Cauchy_IR,
((Cauchy_IRasCR x)*(Cauchy_IRasCR y) == Cauchy_IRasCR (x[*]y))%CR.
Proof.
 intros x [y Hy].
 destruct (CS_seq_bounded _ y Hy) as [k Hk [n Hn]].
 set (y':=Build_CauchySeq Q_as_COrdField y Hy).
 set (k':=(mkQpos Hk)).
 transitivity ((ucFun2 (CRmult_bounded (CR_b (1 # 1) (Cauchy_IRasCR y')+k')%Qpos) (Cauchy_IRasCR x)
   (Cauchy_IRasCR y'))).
  apply CRmult_bounded_weaken.
    apply CR_b_lowerBound.
   apply CR_b_upperBound.
  autorewrite with QposElim.
  rewrite -> Qle_minus_iff.
  ring_simplify.
  discriminate.
 apply Cauchy_IR_mult_as_CRmult_bounded with n.
 intros i Hi.
 apply: AbsSmall_trans;[|apply Hn;assumption].
 simpl.
 rewrite -> Qlt_minus_iff.
 unfold k'.
 autorewrite with QposElim.
 ring_simplify.
 apply Qpos_prf.
Qed.

Hint Rewrite Cauchy_IR_mult_as_CR_mult : CRtoCauchy_IR.

Lemma CR_mult_as_Cauchy_IR_mult : forall x y:CR,
(CRasCauchy_IR x)[*](CRasCauchy_IR y) [=] CRasCauchy_IR (x*y)%CR.
Proof.
 apply reverse_iso_bin_wd_fun.
  apply CRmult_wd.
 apply Cauchy_IR_mult_as_CR_mult.
Qed.

(** lt is preserved. *)
Lemma Cauchy_IR_lt_as_CR_lt_1 : forall (x y:Cauchy_IR),
x[<]y -> (Cauchy_IRasCR x < Cauchy_IRasCR y)%CR.
Proof.
 intros x y [n [e He Hn]].
 exists (mkQpos He).
 abstract ( autorewrite with CRtoCauchy_IR; intros [m [d Hd Hm]];
   refine (Qle_not_lt _ _ (Hn (max n m) _) _);[auto with *|]; rewrite -> Qlt_minus_iff;
     apply Qlt_le_trans with d;[assumption|]; autorewrite with QposElim in Hm; apply: Hm; auto with *
       ).
Defined.

Lemma CR_lt_as_Cauchy_IR_lt_1 : forall (x y:CR),
(x < y)%CR -> (CRasCauchy_IR x)[<](CRasCauchy_IR y).
Proof.
 intros x y [e He].
 apply shift_zero_less_minus'.
 apply (less_leEq_trans _ Zero (Cauchy_CReals.inject_Q _ (e:Q))).
  apply: ing_lt.
  apply Qpos_prf.
 unfold cg_minus.
 stepr (CRasCauchy_IR (y-x))%CR.
  stepl (CRasCauchy_IR (' e)%CR).
   rewrite <- Cauchy_IR_le_as_CR_le.
   do 2 rewrite -> CRasCR.
   assumption.
  apply: CR_inject_Q_as_Cauchy_IR_inject_Q.
 stepl (CRasCauchy_IR y[+]CRasCauchy_IR(- x)%CR).
  apply plus_resp_eq.
  apply: CR_opp_as_Cauchy_IR_opp.
 apply: CR_plus_as_Cauchy_IR_plus.
Qed.

Lemma Cauchy_IR_lt_as_CR_lt_2 : forall (x y:Cauchy_IR),
((Cauchy_IRasCR x) < (Cauchy_IRasCR y))%CR -> x[<]y.
Proof.
 intros x y H.
 stepl (CRasCauchy_IR (Cauchy_IRasCR (x))); [| apply Cauchy_IRasCauchy_IR].
 stepr (CRasCauchy_IR (Cauchy_IRasCR (y))); [| apply Cauchy_IRasCauchy_IR].
 apply CR_lt_as_Cauchy_IR_lt_1.
 assumption.
Qed.

Lemma CR_lt_as_Cauchy_IR_lt_2 : forall (x y:CR),
(CRasCauchy_IR x)[<](CRasCauchy_IR y) -> (x < y)%CR.
Proof.
 intros x y H.
 eapply CRlt_wd;try apply CRasCR.
 apply Cauchy_IR_lt_as_CR_lt_1.
 assumption.
Qed.

(** appartness is preserved. *)
Lemma Cauchy_IR_ap_as_CR_ap_1 : forall (x y:Cauchy_IR),
x[#]y -> (CRapart (Cauchy_IRasCR x) (Cauchy_IRasCR y))%CR.
Proof.
 intros x y [H|H];[left|right];apply Cauchy_IR_lt_as_CR_lt_1; apply H.
Defined.

Lemma CR_ap_as_Cauchy_IR_ap_1 : forall (x y:CR),
CRapart x y -> (CRasCauchy_IR x) [#] (CRasCauchy_IR y).
Proof.
 intros x y [H|H];[left|right];apply CR_lt_as_Cauchy_IR_lt_1; apply H.
Defined.

Lemma Cauchy_IR_ap_as_CR_ap_2 : forall (x y:Cauchy_IR),
(CRapart (Cauchy_IRasCR x) (Cauchy_IRasCR y))%CR -> x[#]y.
Proof.
 intros x y [H|H];[left|right];apply Cauchy_IR_lt_as_CR_lt_2; apply H.
Qed.

Lemma CR_ap_as_Cauchy_IR_ap_2 : forall (x y:CR),
(CRasCauchy_IR x) [#] (CRasCauchy_IR y) -> CRapart x y.
Proof.
 intros x y [H|H];[left|right];apply CR_lt_as_Cauchy_IR_lt_2; apply H.
Defined.

(** inv is preserved. *)
Lemma Cauchy_IR_inv_as_CRinv_pos : forall (x:Cauchy_IR) x_,
forall (z:Qpos) (N:nat), (forall i:nat, (N<=i) -> (z <= (CS_seq _ x i))%Q) ->
(CRinv_pos z (Cauchy_IRasCR x) == Cauchy_IRasCR (f_rcpcl x (@inr _ _ x_)))%CR.
Proof.
 intros [x Hx] [a [d d_ x_]] z n Hn.
 apply: regFunEq_e.
 intros e.
 simpl.
 unfold Qinv_modulus.
 destruct (Hx ((z * z * e)%Qpos:Q) (Qpos_prf (z * z * e)%Qpos)) as [b Hb].
 destruct (CS_seq_recip Q_as_COrdField x Hx d d_ a (fun (n0 : nat) (H : le a n0) =>
   leEq_wdr Q_as_COrdField d (@cg_minus Q_as_CGroup (x n0) (Qmake Z0 xH)) (x n0) (x_ n0 H) (cg_inv_zero Q_as_CGroup (x n0))) (e:Q) (Qpos_prf e)) as [c Hc].
 set (y:=(CS_seq_recip_seq Q_as_COrdField x d d_ a (fun (n0 : nat) (H : le a n0) =>
   leEq_wdr Q_as_COrdField d (@cg_minus Q_as_CGroup (x n0) (Qmake Z0 xH)) (x n0) (x_ n0 H) (cg_inv_zero Q_as_CGroup (x n0))))) in *.
 unfold CS_seq_recip_seq in y.
 simpl in y.
 set (m:=max (max a n) (max b c)).
 assert (Hm1: c<=m).
  unfold m; apply le_trans with (max b c); auto with *.
 change (ball (e+e) (/ Qmax z (x b))%Q (y c)).
 apply ball_triangle with (y m);[|apply: Hc;assumption].
 clear Hc.
 unfold y.
 destruct (lt_le_dec m a) as [Z|Z].
  elim (le_not_lt _ _ Z).
  unfold m.
  apply lt_le_trans with (S (max a n)); auto with *.
 change (AbsSmall (e:Q) (/ Qmax z (x b)-1 * / x m))%Q.
 clear y.
 assert (T:(~ (x m == 0)%Q /\ ~ (Qmax z (x b) == 0)%Q)).
  split; apply (ap_symmetric_unfolded Q_as_CSetoid); apply: Qlt_not_eq.
   apply Qlt_le_trans with z.
    apply Qpos_prf.
   apply Hn.
   apply le_trans with (max a n).
    auto with *.
   unfold m; auto with *.
  apply Qlt_le_trans with z; auto with *.
 stepr ((/(Qmax z (x b))*/(x m))*(x m - (Qmax z (x b))))%Q; [| simpl; field; assumption].
 stepl ((/ Qmax z (x b) * / x m)*((Qmax z (x b))*(x m)*e))%Q; [| simpl;field; assumption].
 apply mult_resp_AbsSmall.
  assert (foo:forall q:Q, (0<=q -> 0<=/q)%Q).
   intros [[|p|p] q] qH; apply qH.
  apply mult_resp_nonneg.
   apply foo.
   apply Qle_trans with z.
    apply Qpos_nonneg.
   apply Qmax_ub_l.
  apply foo.
  apply Qle_trans with z.
   apply Qpos_nonneg.
  apply Hn.
  apply le_trans with (max a n); unfold m; auto with *.
 simpl in x_.
 apply (AbsSmall_leEq_trans _ (z*z*e)%Q).
  apply mult_resp_leEq_rht;[apply mult_resp_leEq_both|]; try apply Qpos_nonneg.
   apply Qmax_ub_l.
  apply Hn.
  apply le_trans with (max a n); unfold m; auto with *.
 assert (W:AbsSmall (R:=Q_as_COrdField) (z * z * e)%Q (x m - x b)%Q).
  apply Hb.
  apply le_trans with (max b c); unfold m; auto with *.
 apply Qmax_case;intros C;[|assumption].
 apply leEq_imp_AbsSmall.
  unfold Qminus.
  rewrite <- Qle_minus_iff.
  apply Hn.
  apply le_trans with (max a n); unfold m; auto with *.
 apply Qle_trans with (x m - x b)%Q.
  rewrite -> Qle_minus_iff.
  stepr (z + - x b)%Q; [| simpl; ring].
  rewrite <- Qle_minus_iff.
  assumption.
 destruct W; assumption.
Qed.

Lemma Cauchy_IR_nonZero_as_CR_nonZero_1 : forall (x:Cauchy_IR),
Dom (f_rcpcl' _) x -> (CRapart (Cauchy_IRasCR x) (inject_Q 0%Q))%CR.
Proof.
 intros x x_.
 eapply CRapart_wd.
   reflexivity.
  symmetry.
  apply Cauchy_IR_inject_Q_as_CR_inject_Q.
 apply Cauchy_IR_ap_as_CR_ap_1.
 assumption.
Defined.

Lemma CR_nonZero_as_Cauchy_IR_nonZero_1 : forall (x:CR),
(CRapart x (inject_Q 0%Q))%CR -> Dom (f_rcpcl' _) (CRasCauchy_IR x).
Proof.
 intros x x_.
 change ((CRasCauchy_IR x)[#]Zero).
 stepr (CRasCauchy_IR (inject_Q 0)).
  apply CR_ap_as_Cauchy_IR_ap_1.
  assumption.
 apply: CR_inject_Q_as_Cauchy_IR_inject_Q.
Defined.

Lemma Cauchy_IR_inv_as_CR_inv_short : forall (x:Cauchy_IR) x_,
(@CRinv (Cauchy_IRasCR x) (Cauchy_IR_nonZero_as_CR_nonZero_1 _ x_) == Cauchy_IRasCR (f_rcpcl x x_))%CR.
Proof.
 intros [x Hx] [H|H].
  set (x':=(Build_CauchySeq Q_as_COrdField x Hx)) in *.
  assert (H':(cm_unit Cauchy_IR)[<][--](x':Cauchy_IR)).
   apply inv_cancel_less.
   rstepl x'.
   assumption.
  set (y:= (Cauchy_IRasCR [--](f_rcpcl (F:=Cauchy_IR) ([--](x':Cauchy_IR)) (@inr _ _ H')))%CR).
  transitivity y.
   destruct H as [n [e He H]].
   change (-(CRinv_pos (mkQpos He) (- Cauchy_IRasCR (Build_CauchySeq Q_as_COrdField x Hx)))==y)%CR.
   unfold y.
   rewrite <- Cauchy_IR_opp_as_CR_opp.
   apply CRopp_wd.
   set (X := (Cauchy_IRasCR (f_rcpcl (F:=Cauchy_IR) [--](x':Cauchy_IR)
     (@inr (R_lt Q_as_COrdField [--](x':Cauchy_IR) (Zero:Cauchy_IR)) (Zero[<][--](x':Cauchy_IR)) H')))%CR).
   rewrite -> Cauchy_IR_opp_as_CR_opp.
   apply: Cauchy_IR_inv_as_CRinv_pos.
   intros i Hi.
   autorewrite with QposElim.
   simpl.
   stepr (0 - x i)%Q; [| simpl; ring].
   apply: H.
   apply Hi.
  unfold y.
  apply Cauchy_IRasCR_wd.
  apply: mult_cancel_lft.
   left.
   apply H.
  stepr (One:Cauchy_IR).
   eapply eq_transitive.
    apply cring_inv_mult_lft.
   apply eq_symmetric.
   eapply eq_transitive;[|apply cring_inv_mult_rht].
   apply eq_symmetric.
   apply x_div_x.
  apply eq_symmetric.
  apply x_div_x.
 destruct H as [n [e He H]].
 apply: Cauchy_IR_inv_as_CRinv_pos.
 intros i Hi.
 autorewrite with QposElim.
 simpl in *.
 stepr (x i- 0)%Q; [| simpl; ring].
 apply H.
 apply Hi.
Qed.

Hint Rewrite Cauchy_IR_inv_as_CR_inv_short : CRtoCauchy_IR.

Lemma Cauchy_IR_inv_as_CR_inv : forall (x:Cauchy_IR) x_ H,
(@CRinv (Cauchy_IRasCR x) H == Cauchy_IRasCR (f_rcpcl x x_))%CR.
Proof.
 intros x x_ H.
 rewrite <- Cauchy_IR_inv_as_CR_inv_short.
 apply CRinv_irrelvent.
Qed.

Lemma CR_inv_as_Cauchy_IR_inv : forall (x:CR) x_ H,
f_rcpcl (CRasCauchy_IR x) H [=] CRasCauchy_IR (@CRinv x x_).
Proof.
 intros x x_ H.
 stepl (CRasCauchy_IR (Cauchy_IRasCR (f_rcpcl (CRasCauchy_IR x) H))); [| apply Cauchy_IRasCauchy_IR].
 apply CRasCauchy_IR_wd.
 rewrite <- Cauchy_IR_inv_as_CR_inv_short.
 apply CRinv_wd.
 apply CRasCR.
Qed.

Lemma CR_inv_as_Cauchy_IR_inv_short : forall (x:CR) x_,
f_rcpcl (CRasCauchy_IR x) (CR_nonZero_as_Cauchy_IR_nonZero_1 _ x_) [=] CRasCauchy_IR (@CRinv x x_).
Proof.
 intros.
 apply CR_inv_as_Cauchy_IR_inv.
Qed.
