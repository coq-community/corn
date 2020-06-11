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
Require Import CoRN.model.totalorder.QposMinMax.
Require Import CoRN.logic.CLogic.
Require Export CoRN.model.lattice.CRlattice.
Require Import CoRN.model.totalorder.QMinMax.
Require Import Coq.QArith.Qabs.
Require Import CoRN.algebra.COrdAbs.
Require Import CoRN.model.ordfields.Qordfield.
Require Import CoRN.model.metric2.Qmetric.
Require Import CoRN.tactics.CornTac.
Require Import MathClasses.interfaces.canonical_names.

Set Implicit Arguments.

Local Open Scope Q_scope.
Local Open Scope uc_scope.
Opaque CR Qmin Qmax Qred.

(**
** Strict Inequality
First we defined positivity.  We define positivity to contain a
positive rational witness of a lower bound on x.  This seems the best
way because this witness contains exactly the information needed
for functions (such as inverse and logorithm) that have domains
restricted to the positive reals.
*)
Definition CRpos (x:CR) := sig (fun e:Qpos => ' proj1_sig e <= x)%CR.

Lemma CRpos_wd : forall x y, (x==y)%CR -> (CRpos x) -> (CRpos y).
Proof.
 intros x y Hxy [e H].
 exists e.
 abstract ( rewrite <- Hxy; assumption ).
Defined.

(** This is a characterization closer to Bishop's definiton.  If we
replace [2*e] with [e], the theorem still holds, but it could be
very expensive to call.  We prefer to avoid that. *)

Program Definition CRpos_char (e:Qpos) (x:CR) (H: (2#1)*e <= (approximate x e)): CRpos x := e.

Next Obligation.
 change (CRle (inject_Q_CR (proj1_sig e)) x).
 intros a.
 simpl.
 unfold Cap_raw.
 simpl.
 apply Qle_trans with (-(1#2)* proj1_sig a).
  rewrite -> Qle_minus_iff.
  ring_simplify.
  apply Qmult_le_0_compat; auto with *.
 rewrite -> Qle_minus_iff.
 destruct (regFun_prf x e ((1#2)*a)%Qpos) as [_ X].
 stepr (approximate x ((1 # 2) * a)%Qpos + (1#2)*proj1_sig a
        + proj1_sig e + - ((2#1)*proj1_sig e));
   [|simpl; ring].
 rewrite <- Qle_minus_iff; apply Qle_trans with (approximate x e); try assumption; simpl in X.
 rewrite -> Qle_minus_iff in X; rewrite -> Qle_minus_iff; autorewrite with QposElim in X.
 stepr (proj1_sig e + (1 # 2) * proj1_sig a
        + - (approximate x e - approximate x ((1 # 2) * a)%Qpos)). assumption.
 simpl. ring.
Qed.

(** Negative reals are defined similarly. *)
Definition CRneg (x:CR) := sig (fun e:Qpos => x <= ' (-proj1_sig e)%Q)%CR.

Lemma CRneg_wd : forall x y, (x==y)%CR -> (CRneg x) -> (CRneg y).
Proof.
 intros x y Hxy [e H].
 exists e.
 abstract ( rewrite <- Hxy; assumption ).
Defined.

Program Definition CRneg_char (e:Qpos) (x:CR) (H: (approximate x e) <= -(2#1)*e): CRneg x := e.

Next Obligation.
 change (x <= '(-proj1_sig e)%Q)%CR.
 intros a; simpl; unfold Cap_raw; simpl; apply Qle_trans with (-(1#2)*proj1_sig a).
  rewrite -> Qle_minus_iff; ring_simplify.
  apply Qmult_le_0_compat; auto with *.
 (rewrite -> Qle_minus_iff;
     destruct (regFun_prf x e ((1#2)*a)%Qpos) as [X _];
     (stepr ( - proj1_sig e + - approximate x ((1 # 2) * a)%Qpos
              + (1 # 2) * proj1_sig a + approximate x e + - approximate x e); [|simpl; ring]);
         rewrite <- Qle_minus_iff; apply Qle_trans with (-(2#1)*proj1_sig e); try assumption; simpl in X;
           rewrite -> Qle_minus_iff in X; rewrite -> Qle_minus_iff; autorewrite with QposElim in X;
             (stepr (approximate x e - approximate x ((1 # 2) * a)%Qpos +
               - - (proj1_sig e + (1 # 2) * proj1_sig a)); [| simpl; ring]); assumption).
Qed.

(** Strict inequality is defined in terms of positivity. *)
Definition CRltT (x y:CR) := CRpos (y-x)%CR.

Infix "<" := CRltT : CR_scope.

Lemma CRltT_wd : forall x1 x2, (x1==x2 -> forall y1 y2, y1==y2 -> x1 < y1 -> x2 < y2)%CR.
Proof.
 intros x1 x2 Hx y1 y2 Hy H.
 apply: CRpos_wd. 2:apply H.
 abstract ( rewrite <- Hx; rewrite <- Hy; reflexivity ).
Defined.

(**
** Apartness
*)
Definition CRapartT (x y:CR) := (x < y or y < x)%CR.

Notation "x >< y" := (CRapartT x y) (at level 70, no associativity) : CR_scope.

Lemma CRapartT_wd : forall x1 x2, (x1==x2 -> forall y1 y2, y1==y2 -> x1><y1 -> x2><y2)%CR.
Proof.
 intros x1 x2 Hx y1 y2 Hy [H|H];[left;apply (CRltT_wd Hx Hy)|right;apply (CRltT_wd Hy Hx)];assumption.
Defined.
(**
** Multiplication
The modulus of continuity for multiplication by a constant.
*)
Definition Qscale_modulus (a:Q) (e:Qpos) : QposInf :=
match a with
| 0 # _ => QposInfinity
| (Zpos an) # ad => Qpos2QposInf ((ad # an) * e)
| (Zneg an) # ad => Qpos2QposInf ((ad # an) * e)
end.

Lemma Qscale_modulus_elim : forall (P:QposInf -> Type) (x:Q) (e:Qpos),
(x==0 -> P QposInfinity)%Q ->
(forall y:Qpos, AbsSmall (proj1_sig e/proj1_sig y)%Q (x)%Q -> (P y)) ->
P (Qscale_modulus x e).
Proof.
 intros P [xn xd] e H1.
 cut (forall xn:positive, (forall y : Qpos, AbsSmall (proj1_sig e/proj1_sig y)%Q (xn#xd)%Q -> P y) ->
   P (Qscale_modulus (xn # xd) e)).
  intros H H2.
  destruct xn as [|xn|xn].
    apply H1.
    constructor.
   apply H.
   assumption.
  apply H.
  intros y Hy.
  apply H2.
  change (Zneg xn # xd)%Q with ([--](xn # xd))%Q.
  apply inv_resp_AbsSmall.
  assumption.
 clear xn H1.
 intros xn H2.
 simpl.
 apply H2.
 autorewrite with QposElim.
 stepl (/(xd#xn))%Q; [| simpl; field].
  change (/(xd#xn))%Q with (xn#xd)%Q.
  apply AbsSmall_reflexive.
  discriminate.
  split. destruct e. simpl. intro abs.
  clear H2. rewrite abs in q. exact (Qlt_irrefl 0 q).
  intro abs. inversion abs.
Qed.

Lemma Qscale_modulus_pos (a e: Qpos): exists P,
    Qscale_modulus (proj1_sig a) e
    ≡ Qpos2QposInf (exist (Qlt 0) (/ proj1_sig a * proj1_sig e)%Q P).
Proof.
 revert a.
 intros [[[] ad] P]; try discriminate.
 simpl. unfold Qpos_inv, Qpos_mult.
 eauto.
Qed.

(*
Lemma Qscale_modulus_pos : forall (a e:Qpos), Qscale_modulus a e = (Qpos_inv a*e)%Qpos.
Proof.
intros; reflexivity.
intros [an ad] e.
reflexivity.
simpl.
change (e / (an # ad))%Qpos with (e * (ad # an))%Qpos.
rewrite (@QposAsQ_injection ((ad # an) * e)%Qpos (e * (ad # an))%Qpos).
reflexivity.
autorewrite with QposElim.
destruct e as [en ed].
unfold Qmult.
simpl.
rewrite Pmult_comm.
rewrite (Pmult_comm an).
reflexivity.
Qed.

Lemma Qscale_modulus_neg : forall (a e:Qpos), Qscale_modulus (- a) e = (e / a)%Qpos.
Proof Qscale_modulus_pos.
*)

Lemma Qscale_uc_prf (a:Q) :
  @is_UniformlyContinuousFunction
   Q_as_MetricSpace Q_as_MetricSpace (fun b:Q => a*b) (Qscale_modulus a).
Proof.
 revert a.
 intros [[|an|an] ad] e b0 b1 H.
   simpl in *.
   setoid_replace ((0 # ad)) with 0 by constructor.
   unfold Qball.
   unfold QAbsSmall. setoid_replace (0 * b0 - 0 * b1) with 0.
   2: ring.
   apply zero_AbsSmall.
   simpl.
   auto with *.
  simpl in *.
  unfold Qball in *.
  autorewrite with QposElim.
  unfold QAbsSmall.
  setoid_replace ((an # ad) * b0 - (an # ad) * b1) with ((an#ad)*(b0-b1)).
  2: ring.
  apply (fun x y => (AbsSmall_cancel_mult _ x y (ad#an))).
   constructor.
  stepl (proj1_sig ((ad # an) * e)%Qpos); [| simpl; ring].
  stepr (b0 - b1).
   apply H.
  stepr ((an#ad)*(ad#an)*(b0-b1)); [| simpl; ring].
  simpl.
  setoid_replace ((an#ad)*(ad#an)) with 1.
   ring.
  simpl.
  unfold Qeq.
  simpl.
  rewrite Pmult_1_r.
  rewrite Pmult_comm.
  reflexivity.
 simpl in *.
 unfold Qball in *.
 autorewrite with QposElim.
 unfold QAbsSmall.
 setoid_replace ((Z.neg an # ad) * b0 - (Z.neg an # ad) * b1)
   with ((Zneg an#ad)*(b0-b1)). 2: ring.
 apply (fun x y => (AbsSmall_cancel_mult _ x y (ad#an))).
  constructor.
 stepl (proj1_sig ((ad # an) * e)%Qpos); [| simpl; ring].
 stepr (b1 - b0).
  apply AbsSmall_minus.
  apply H.
 stepr ((Zneg an#ad)*(ad#an)*(b0-b1)); [| simpl; ring].
 simpl.
 setoid_replace ((Zneg an#ad)*(ad#an)) with ([--]1).
  simpl; ring.
 simpl.
 unfold Qeq.
 simpl.
 rewrite Pmult_1_r.
 rewrite Pmult_comm.
 reflexivity.
Qed.

(** Scaling by a constant is [Qmult] lifted on one parameter. *)
Definition Qscale_uc (a:Q_as_MetricSpace) : Q_as_MetricSpace --> Q_as_MetricSpace :=
Build_UniformlyContinuousFunction (Qscale_uc_prf a).

Definition scale (a:Q) : CR --> CR := Cmap QPrelengthSpace (Qscale_uc a).

Instance Qscale_uc_Proper: Proper (Qeq ==> @st_eq _) Qscale_uc.
Proof. intros ?? E ?. simpl. rewrite E. reflexivity. Qed.

Instance scale_Proper: Proper (Qeq ==> @st_eq _) scale.
Proof. intros ?? E ?. simpl ucFun. rewrite E. reflexivity. Qed.

(** [CRboundAbs] clamps a real number between -c and c where c is
rational. *)
Definition QboundAbs (c:Qpos)
  := uc_compose (QboundBelow_uc (-proj1_sig c)) (QboundAbove_uc (proj1_sig c)).

Definition CRboundAbs (c:Qpos) := Cmap QPrelengthSpace (QboundAbs c).

Lemma QboundAbs_absorb: forall (a b:Qpos) (c:Q),
 proj1_sig a <= proj1_sig b ->
 QboundAbs b (QboundAbs a c) == QboundAbs a c.
Proof.
 intros a b c H.
 simpl.
 rewrite -> Qmin_max_distr_r.
 setoid_replace (Qmin (proj1_sig b) (-proj1_sig a)) with (-proj1_sig a).
  rewrite -> Qmax_assoc.
  rewrite <- Qmin_max_de_morgan.
  rewrite -> Qmin_assoc.
  setoid_replace (Qmin (proj1_sig b) (proj1_sig a)) with (proj1_sig a).
   reflexivity.
  rewrite <- Qle_min_r.
  assumption.
 rewrite <- Qle_min_r.
 rewrite -> Qle_minus_iff.
 ring_simplify.
 destruct a,b. simpl. rewrite <- (Qplus_0_l 0).
 apply Qplus_le_compat; apply Qlt_le_weak; assumption.
Qed.

(** Properties of CRboundAbs. *)
Lemma CRboundAbs_Eq : forall (a:Qpos) (x:CR),
 ('(-proj1_sig a)%Q <= x -> x <= ' proj1_sig a ->
 CRboundAbs a x == x)%CR.
Proof.
 intros a x Ha Hb.
 unfold CRboundAbs.
 transitivity (uc_compose (Cmap QPrelengthSpace (QboundBelow_uc (-proj1_sig a))) (Cmap QPrelengthSpace (QboundAbove_uc (proj1_sig a))) x).
  simpl.
  repeat rewrite -> Cmap_fun_correct.
  apply: MonadLaw2.
 simpl.
 change (boundBelow (-proj1_sig a) (boundAbove (proj1_sig a) x) == x)%CR.
 assert (X:(boundAbove (proj1_sig a) x==x)%CR).
  rewrite <- CRmin_boundAbove.
  rewrite <- CRle_min_r.
  assumption.
 rewrite -> X.
 rewrite <- CRmax_boundBelow.
 rewrite <- CRle_max_r.
 assumption.
Qed.

Lemma QboundAbs_elim : forall (z:Qpos) (a:Q) (P:Q->Prop),
((proj1_sig z <= a)%Q -> P (proj1_sig z)) ->
((a <= -proj1_sig z)%Q -> P (- proj1_sig z)%Q) ->
(AbsSmall (proj1_sig z) a -> P (a)) ->
P (QboundAbs z a).
Proof.
 intros z a P H1 H2 H3.
 simpl.
 apply Qmax_case; apply Qmin_case; intros Z0 Z1; try solve [apply H1;assumption|apply H2;assumption].
  elim (Qle_not_lt _ _ Z1).
  rewrite -> Qlt_minus_iff.
  ring_simplify.
  apply: mult_resp_pos.
   constructor.
   destruct z; exact q.
 apply H3.
 split;assumption.
Qed.

(** The modulus of continuity for multiplication depends on the
bound, c, on the second argument. *)
Definition Qmult_modulus (c:Qpos)(e:Qpos) : QposInf
  := Qpos2QposInf (e * Qpos_inv c).

Lemma Qmult_uc_prf (c:Qpos) : is_UniformlyContinuousFunction (fun a => uc_compose (Qscale_uc a) (QboundAbs c)) (Qmult_modulus c).
Proof with simpl in *; auto with *.
 intros e a0 a1 H. split. apply Qpos_nonneg. intro b.
 simpl in *.
 set (b' := Qmax (- proj1_sig c) (Qmin (proj1_sig c) b)).
 repeat rewrite -> (fun x => Qmult_comm x b').
 apply Qscale_uc_prf.
 assert (QposEq (e * Qpos_inv c) (Qpos_inv c*e)%Qpos)
   by (unfold QposEq; simpl; ring).
 apply (ball_wd _ H0 _ _ (reflexivity _) _ _ (reflexivity _)) in H. clear H0.
 apply ball_ex_weak_le with (Qpos_inv c*e)%Qpos;[|assumption].
 unfold b'.
 destruct c as [[cn cd] cpos].
 destruct cn as [|cn|cn]. inversion cpos. 2: inversion cpos.
 apply Qmax_case. intros. apply Qle_refl. simpl.
 apply Qmin_case. intros. apply Qle_refl.
 intros H1 H2.
 destruct b as [[|bn|bn] bd]...
 - apply Qmult_le_r. destruct e; exact q.
 apply Qle_shift_inv_r. reflexivity.
 rewrite <- Qmult_1_l in H1.
 apply Qle_shift_div_l in H1.
 apply (Qle_trans _ _ _ H1). rewrite Qmult_comm.
 apply Qmult_le_l. reflexivity. apply Z.le_refl. reflexivity.
 - apply Qmult_le_r. destruct e; exact q.
 apply Qle_shift_inv_r. reflexivity.
 apply Qopp_le_compat in H2. rewrite Qopp_involutive in H2.
 rewrite <- Qmult_1_l in H2.
 apply Qle_shift_div_l in H2. 2: reflexivity.
 apply (Qle_trans _ _ _ H2). rewrite Qmult_comm.
 apply Qmult_le_l. reflexivity. apply Z.le_refl.
Qed.

(* begin hide *)
Arguments Qmult_uc_prf : clear implicits.
(* end hide *)
Definition Qmult_uc (c:Qpos) :  Q_as_MetricSpace --> Q_as_MetricSpace --> Q_as_MetricSpace:=
Build_UniformlyContinuousFunction (Qmult_uc_prf c).

(** This multiply should be used when a bound on the absolute value of
the second argument is known. *)
Definition CRmult_bounded (c:Qpos) : CR --> CR --> CR :=
Cmap2 QPrelengthSpace QPrelengthSpace (Qmult_uc c).

Instance: Proper (QposEq ==> @st_eq _) Qmult_uc.
Proof.
 intros e1 e2 E x1 x2.
 apply ball_eq_iff. intros e epos.
 simpl. unfold QposEq in E. rewrite E.
 apply Qball_Reflexive. apply Qlt_le_weak, epos.
Qed.

Instance: Proper (QposEq ==> @st_eq _) CRmult_bounded.
Proof.
 intros e1 e2 E x1 x2. simpl. rewrite E. reflexivity.
Qed.

(** CR_b computes a rational bound on the absolute value of x *)

Hint Immediate Qabs_nonneg. (* todo: move *)

Lemma CR_b_pos (e : Qpos) (x : CR) : 0 < Qabs (approximate x e) + proj1_sig e.
Proof.
  assert (Qabs (approximate x e) + proj1_sig e
          == Qabs (approximate x e) - (-proj1_sig e)).
  ring. rewrite -> H. clear H.
  apply: shift_zero_less_minus.
  apply Qlt_le_trans with 0; auto with *.
  destruct e; simpl. apply (Qplus_lt_l _ _ x0).
  ring_simplify. exact q.
Qed.
 
Program Definition CR_b (e:Qpos) (x:CR) : Qpos
  := exist (Qlt 0) (Qabs (approximate x e) + proj1_sig e) _.
Next Obligation. apply CR_b_pos. Qed.

Lemma CR_b_lowerBound : forall e x, (' (-proj1_sig (CR_b e x))%Q <= x)%CR.
Proof.
 intros e x e'.
 unfold CR_b.
 autorewrite with QposElim.
 simpl.
 unfold Cap_raw.
 simpl.
 rewrite -> Qle_minus_iff.
 ring_simplify.
 destruct (regFun_prf x ((1#2)*e')%Qpos e) as [H _].
 simpl in H.
 rewrite -> Qle_minus_iff in H.
 ring_simplify in H.
 eapply Qle_trans.
  apply H.
 rewrite -> Qle_minus_iff.
 autorewrite with QposElim.
 ring_simplify.
 clear H.
 apply Qabs_case; intros H; [repeat apply: plus_resp_nonneg; try assumption |ring_simplify];
   apply: mult_resp_nonneg.
 discriminate. apply Qlt_le_weak. destruct e'; exact q.
 discriminate. apply Qlt_le_weak. destruct e'; exact q.
Qed.

Lemma CR_b_upperBound : forall e x, (x <= 'proj1_sig (CR_b e x))%CR.
Proof.
 intros e x e'.
 unfold CR_b.
 simpl.
 unfold Cap_raw.
 simpl.
 rewrite -> Qle_minus_iff.
 ring_simplify.
 destruct (regFun_prf x ((1#2)*e')%Qpos e) as [_ H].
 simpl in H.
 rewrite -> Qle_minus_iff in H.
 ring_simplify in H.
 eapply Qle_trans.
  apply H.
 rewrite -> Qle_minus_iff.
 ring_simplify.
 clear H.
 apply Qabs_case; intros H.
  ring_simplify;(apply: mult_resp_nonneg;[discriminate|apply Qlt_le_weak; destruct e'; exact q]).
 ring_simplify; repeat apply: plus_resp_nonneg;simpl.
  stepr ((2#1)*(-(approximate x e))); [| simpl; ring].
  apply: mult_resp_nonneg.
   discriminate.
  apply (Qopp_le_compat (approximate x e) 0).
  assumption.
 (apply: mult_resp_nonneg;[discriminate|apply Qlt_le_weak; destruct e'; exact q]).
Qed.

(** This version of multiply computes a bound on the second argument
just in time.  It should be avoided in favour of the bounded version
whenever possible. *)
Instance CRmult: Mult CR := λ x y, ucFun2 (CRmult_bounded (CR_b (1#1) y)) x y.

Infix "*" := CRmult : CR_scope.

Lemma CRmult_bounded_weaken : forall (c1 c2:Qpos) x y,
    ((' (-proj1_sig c1)%Q <= y) -> (y <= ' proj1_sig c1)
     -> (proj1_sig c1 <= proj1_sig c2)%Q ->
CRmult_bounded c1 x y == CRmult_bounded c2 x y)%CR.
Proof.
 intros c1 c2 x y Hc1a Hc1b Hc2.
 assert (Hy:=CRboundAbs_Eq _ Hc1a Hc1b).
 set (y':= (CRboundAbs c1 y)) in *.
 transitivity (ucFun2 (CRmult_bounded c2) x y'); [|rewrite -> Hy;reflexivity].
 assert (H:forall x:Qpos, proj1_sig (x*c1*Qpos_inv c2)%Qpos <= proj1_sig x).
 { intros a.
  simpl.
  rewrite <- (Qmult_1_r (`a)), <- Qmult_assoc, <- Qmult_assoc.
  apply Qmult_le_l. destruct a; exact q.
  rewrite Qmult_1_l. apply Qle_shift_div_r.
  destruct c2; exact q. rewrite Qmult_1_l. exact Hc2. }
 change (ucFun2 (CRmult_bounded c1) x y == ucFun2 (CRmult_bounded c2) x y')%CR.
 rewrite <- (QreduceApprox_Eq x).
 set (x''':=(QreduceApprox x)).
 set (x':=faster x''' (fun x => (x * c1 * Qpos_inv c2)%Qpos) H).
 transitivity (ucFun2 (CRmult_bounded c1) x' y).
  unfold x'.
  rewrite -> fasterIsEq.
  reflexivity.
 apply: regFunEq_e; intros e.
 intros.
 simpl.
 do 3 (unfold Cap_raw; simpl).
 assert (X:=fun c => QboundAbs_absorb _ _ c Hc2).
 unfold QboundAbs in X.
 simpl in X.
 rewrite -> X.
 clear X.
 assert (eq (Qpos_red ((1 # 2) * e * Qpos_inv c1 * c1 * Qpos_inv c2))
            (Qpos_red ((1 # 2) * e * Qpos_inv c2))).
 { apply Qpos_red_eq. unfold QposEq. simpl. field.
   split. intro abs. destruct c2. simpl in abs.
   apply (Qlt_not_le _ _ q). rewrite abs. apply Qle_refl.
   intro abs. destruct c1. simpl in abs.
   apply (Qlt_not_le _ _ q). rewrite abs. apply Qle_refl. }
 simpl. simpl in H0. rewrite H0. 
 do 2 rewrite QposInf_bind_id. apply ball_refl.
 apply (Qpos_nonneg (e+e)).
Qed.

Lemma CRmult_bounded_mult : forall (c:Qpos) (x y:CR),
 (' (-proj1_sig c)%Q <= y -> y <= ' proj1_sig c ->
  CRmult_bounded c x y == x*y)%CR.
Proof.
 intros c x y Hc1 Hc2.
 unfold CRmult.
 set (d:=(CR_b (1 # 1) y)).
 destruct (Qle_total (proj1_sig c) (proj1_sig d)).
  apply CRmult_bounded_weaken; assumption.
 symmetry.
 apply CRmult_bounded_weaken; try assumption.
  apply CR_b_lowerBound.
 apply CR_b_upperBound.
Qed.
(* begin hide *)
Add Morphism CRmult with signature (@st_eq _) ==> (@st_eq _) ==> (@st_eq _) as CRmult_wd.
Proof.
 intros x1 x2 Hx y1 y2 Hy.
 unfold CRmult.
 set (c:=(CR_b (1 # 1) y1)).
 set (d:=(CR_b (1 # 1) y2)).
 rewrite -> Hx.
 rewrite -> Hy.
 unfold d.
 apply CRmult_bounded_mult; rewrite <- Hy.
  apply CR_b_lowerBound.
 apply CR_b_upperBound.
Qed.
(* end hide *)
Lemma CRmult_scale : forall (a:Q) (y:CR), ((' a)*y==scale a y)%CR.
Proof.
 intros a y.
 unfold CRmult.
 unfold CRmult_bounded.
 unfold ucFun2.
 unfold Cmap2.
 unfold inject_Q_CR.
 simpl.
 rewrite -> Cap_fun_correct.
 repeat rewrite -> Cmap_fun_correct.
 rewrite -> MonadLaw3.
 rewrite -> StrongMonadLaw1.
 simpl.
 transitivity (uc_compose (Cmap QPrelengthSpace (Qscale_uc a))
   (Cmap QPrelengthSpace (QboundAbs (CR_b (1#1) y))) y).
  simpl.
  repeat rewrite -> Cmap_fun_correct.
  apply: MonadLaw2.
 simpl.
 repeat rewrite -> Cmap_fun_correct.
 change (Cmap_slow (Qscale_uc a) (Cmap_slow_fun (QboundAbs (CR_b (1 # 1) y)) y) ==
   Cmap_slow (Qscale_uc a) y)%CR.
 apply uc_wd.
 rewrite <- (Cmap_fun_correct (Y:=Q_as_MetricSpace) QPrelengthSpace).
 apply: CRboundAbs_Eq.
  apply CR_b_lowerBound.
 apply CR_b_upperBound.
Qed.
(* begin hide *)
Hint Rewrite CRmult_scale : CRfast_compute.
(* end hide *)
Lemma scale_Qmult : forall a b:Q, (scale a ('b)=='(a*b)%Q)%CR.
Proof.
 intros a b.
 unfold scale.
 simpl.
 rewrite -> Cmap_fun_correct.
 apply: MonadLaw3.
Qed.
(* begin hide *)
Hint Rewrite scale_Qmult : CRfast_compute.
(* end hide *)
(**
** Inverse
The modulus of continuity for inverse depends on a rational bound
away from 0 of x. *)
Definition Qinv_modulus (c:Qpos) (e:Qpos) : Qpos := (c*c*e)%Qpos.

Lemma Qpos_Qmax : forall (a:Qpos) (b:Q), 0<Qmax (proj1_sig a) b.
Proof.
 intros a b.
 apply Qmax_case; intros H.
 destruct a; exact q.
 apply Qlt_le_trans with (proj1_sig a).
 destruct a; exact q.
 assumption.
Qed.

Lemma Qinv_pos_uc_prf (c:Qpos) :
  @is_UniformlyContinuousFunction
    Q_as_MetricSpace Q_as_MetricSpace
    (fun a:Q => /(Qmax (proj1_sig c) a) ) (Qinv_modulus c).
Proof.
 intros e a0 a1 Ha.
 simpl in *.
 unfold Qball in *.
 assert (forall (a:Qpos) (b:Q), 0 < Qmax (`a) b) as max_pos.
 { intros. apply (Qlt_le_trans _ (`a)).
   destruct a; exact q. apply Qmax_ub_l. }
 eapply AbsSmall_cancel_mult.
 { instantiate (1:=(Qmax (proj1_sig c) a0)*(Qmax (proj1_sig c) a1)).
   simpl. apply (Qle_lt_trans _ (Qmax (`c) a0 *0)).
   rewrite Qmult_0_r. apply Qle_refl.
   apply Qmult_lt_l. apply max_pos. apply max_pos. }
 assert (H : forall (a:Qpos) b, ~(Qmax (proj1_sig a) b)==0).
 { intros a b. intro abs. pose proof (max_pos a b).
   rewrite abs in H. exact (Qlt_irrefl 0 H). }
 stepr (Qmax (proj1_sig c) a1 - Qmax (proj1_sig c) a0);
   [| simpl; field; repeat split; apply H].
 eapply AbsSmall_leEq_trans.
  instantiate (1:=(proj1_sig c*proj1_sig c* proj1_sig e)).
  rewrite -> Qmult_comm.
  apply mult_resp_leEq_lft;[|apply Qpos_nonneg].
  apply mult_resp_leEq_both; (apply Qpos_nonneg || apply Qmax_ub_l).
  change (@ball Q_as_MetricSpace (proj1_sig (c*c*e)%Qpos)
                (Qmax (proj1_sig c) a1) (Qmax (proj1_sig c) a0)).
 apply ball_sym.
 apply QboundBelow_uc_prf.
 apply Ha.
Qed.

Arguments Qinv_pos_uc_prf : clear implicits.

Definition Qinv_pos_uc (c:Qpos) : Q_as_MetricSpace --> Q_as_MetricSpace :=
Build_UniformlyContinuousFunction (Qinv_pos_uc_prf c).

Lemma Qinv_pos_uc_wd : forall (c1 c2:Qpos),
    (proj1_sig c1 <= proj1_sig c2) -> forall x, (proj1_sig c2 <= x) -> st_eq (Qinv_pos_uc c1 x) (Qinv_pos_uc c2 x).
Proof.
 intros c1 c2 Hc x Hx.
 simpl.
 setoid_replace (Qmax (proj1_sig c2) x) with x by (rewrite <- Qle_max_r; assumption).
 setoid_replace (Qmax (proj1_sig c1) x) with x.
  reflexivity.
 rewrite <- Qle_max_r.
 apply Qle_trans with (proj1_sig c2); assumption.
Qed.

(** [CRinv_pos] works for inputs greater than c *)
Definition CRinv_pos (c:Qpos) : CR --> CR := (Cmap QPrelengthSpace (Qinv_pos_uc c)).

Lemma CRinv_pos_weaken : forall (c1 c2:Qpos),
    proj1_sig c1 <= proj1_sig c2
    -> forall (x:CR), (' proj1_sig c2 <= x -> CRinv_pos c1 x == CRinv_pos c2 x)%CR.
Proof.
 intros c1 c2 Hc x Hx.
 assert (X:((boundBelow (proj1_sig c2) x)==x)%CR).
  rewrite <- CRmax_boundBelow.
  rewrite <- CRle_max_r.
  assumption.
 rewrite <- X.
 rewrite <- (QreduceApprox_Eq x).
 pose (f:=(fun e:Qpos => (c1*c1*Qpos_inv c2*Qpos_inv c2)*e)%Qpos).
 assert (Y:forall e:Qpos, proj1_sig (f e) <= proj1_sig e).
  intros e.
  unfold f.
  autorewrite with QposElim.
  apply: (mult_cancel_leEq _ (proj1_sig c1*proj1_sig c1/ proj1_sig c2/ proj1_sig c2*proj1_sig e)
                           (proj1_sig e) (proj1_sig c2*proj1_sig c2)).
   apply: mult_resp_pos;destruct c2; exact q.
  replace LHS with (proj1_sig e*(proj1_sig c1*proj1_sig c1)).
   apply mult_resp_leEq_lft;[|apply Qpos_nonneg].
   apply mult_resp_leEq_both;try assumption;apply Qpos_nonneg.
  simpl; field; apply Qpos_nonzero.
 transitivity (CRinv_pos c2 (boundBelow (proj1_sig c2) (faster (QreduceApprox x) f Y))).
  apply: regFunEq_e.
  intros e.
  assert (Z:=Qinv_pos_uc_wd _ _ Hc).
  simpl in Z.
  simpl.
  rewrite -> Z;[|apply Qmax_ub_l].
  unfold Qinv_modulus.
  replace (Qpos_red (c1 * c1 * e)) with (Qpos_red (f (c2 * c2 * e)%Qpos)); [apply: ball_refl|].
  apply (Qpos_nonneg (e+e)).
  apply Qpos_red_eq.
  unfold f.
  unfold QposEq.
  simpl.
  field.
  apply Qpos_nonzero.
 rewrite -> fasterIsEq.
 reflexivity.
Qed.

Instance CRinv_pos_uc_Proper : Proper (QposEq ==> @st_eq _ ==> @st_eq _) Qinv_pos_uc.
Proof.
  intros [c1 ?] [c2 ?] E x1 x2 F. unfold QposEq in E. simpl in *.
  rewrite E, F. reflexivity.
Qed.

Instance: Proper (QposEq ==> @st_eq _) CRinv_pos.
Proof.
  intros c1 c2 E x. simpl.
  setoid_replace (Qinv_pos_uc c1) with (Qinv_pos_uc c2).
   easy.
  intros y. now apply CRinv_pos_uc_Proper.
Qed.

Lemma CRinv_pos_Qinv : forall (c:Qpos) x,
    (proj1_sig c <= x)%Q -> (CRinv_pos c (' x) == (' (/x)))%CR.
Proof.
 intros c x H.
 apply: regFunEq_e.
 intros e.
 simpl.
 setoid_replace (Qmax (proj1_sig c) x) with x.
  apply: ball_refl.
  apply (Qpos_nonneg (e+e)).
 rewrite <- Qle_max_r.
 assumption.
Qed.

(** [CRinvT] works for inputs apart from 0 *)
Definition CRinvT (x:CR)(x_: (x >< 0)%CR) : CR.
Proof.
 revert x_.
 intros [[c H]|[c H]].
  exact ((-(CRinv_pos c (-x)))%CR).
 exact (CRinv_pos c x).
Defined.

Arguments CRinvT : clear implicits.

Lemma CRinvT_pos_inv : forall (c:Qpos) (x:CR) x_,
 ('proj1_sig c <= x ->
  CRinv_pos c x == CRinvT x x_)%CR.
Proof.
 intros c x [[e He]|[e He]] H.
  assert (X:(' proj1_sig e <= -x)%CR).
   rewrite <- (doubleSpeed_Eq x).
   intros d.
   eapply Qle_trans.
    apply He.
   simpl.
   do 2 (unfold Cap_raw;simpl).
   ring_simplify.
   apply Qle_refl.
  assert (' proj1_sig c <= ' (- proj1_sig e)%Q)%CR.
   eapply CRle_trans.
    apply H.
   intros d.
   eapply Qle_trans.
    apply X.
   simpl.
   do 2 (unfold Cap_raw;simpl).
   rewrite -> Qle_minus_iff.
   ring_simplify.
   apply Qle_refl.
   assert (0 < proj1_sig c) as cpos.
   { destruct c; exact q. }
  elim (Qlt_not_le _ _ cpos).
  assert (Y:=H0 (e)%Qpos).
  simpl in Y.
  do 2 (unfold Cap_raw in Y ;simpl in Y).
  rewrite -> Qle_minus_iff in Y.
  ring_simplify in Y.
  rewrite -> Qle_minus_iff.
  ring_simplify;assumption.
 assert (' proj1_sig e <= x)%CR.
  rewrite <- (doubleSpeed_Eq x).
  intros d.
  eapply Qle_trans.
   apply He.
  simpl.
  do 2 (unfold Cap_raw;simpl).
  ring_simplify.
  apply Qle_refl.
  destruct (Qle_total (proj1_sig c) (proj1_sig e));
    [|symmetry]; apply: CRinv_pos_weaken; assumption.
Qed.

Lemma CRinvT_wd : forall (x y:CR) x_ y_, (x == y -> CRinvT x x_ == CRinvT y y_)%CR.
Proof.
 assert (X:forall x, (0 + x == x)%CR).
  intros x.
  transitivity (doubleSpeed x);[|apply: doubleSpeed_Eq].
  apply: regFunEq_e.
  intros e.
  simpl.
  unfold Cap_raw; simpl.
  ring_simplify.
  apply: ball_refl. apply (Qpos_nonneg (e+e)).
 assert (Y:forall x, (x + - 0 == x)%CR).
  intros x.
  transitivity (doubleSpeed x);[|apply: doubleSpeed_Eq].
  apply: regFunEq_e.
  intros e.
  simpl.
  unfold Cap_raw; simpl.
  ring_simplify.
  apply: ball_refl. apply (Qpos_nonneg (e+e)).
 intros x y [[c x_]|[c x_]] [[d y_]|[d y_]] H.
    change (-(CRinv_pos c (-x))== (-(CRinv_pos d (-y))))%CR.
    rewrite -> H in *.
    rewrite -> X in *. intros.
    apply: CRopp_wd.
    destruct (Qle_total (proj1_sig c) (proj1_sig d));
      [|symmetry]; apply CRinv_pos_weaken; try assumption.
    assert (0 < proj1_sig c) as cpos.
   { destruct c; exact q. } 
   elim (Qlt_not_le _ _ cpos).
   rewrite -> X in *.
   rewrite -> Y in *.
   rewrite -> H in *.
   assert (Z:=Qplus_le_compat _ _ _ _ (x_ ((1#2)*d)%Qpos) (y_ ((1#2)*d)%Qpos)).
   simpl in Z.
   unfold Cap_raw in Z; simpl in Z.
   autorewrite with QposElim in Z.
   rewrite -> Qle_minus_iff in Z.
   ring_simplify in Z.
   rewrite -> Qle_minus_iff.
   ring_simplify.
   assumption.
    assert (0 < proj1_sig c) as cpos.
   { destruct c; exact q. } 
  elim (Qlt_not_le _ _ cpos).
  rewrite -> X in *.
  rewrite -> Y in *.
  rewrite -> H in *.
  assert (Z:=Qplus_le_compat _ _ _ _ (x_ ((1#2)*d)%Qpos) (y_ ((1#2)*d)%Qpos)).
  simpl in Z.
  unfold Cap_raw in Z; simpl in Z.
  autorewrite with QposElim in Z.
  rewrite -> Qle_minus_iff in Z.
  ring_simplify in Z.
  rewrite -> Qle_minus_iff.
  ring_simplify.
  assumption.
 change (CRinv_pos c x== (CRinv_pos d y))%CR.
 rewrite -> H in *.
 rewrite -> Y in *.
 destruct (Qle_total (proj1_sig c) (proj1_sig d));
   [|symmetry]; apply CRinv_pos_weaken; try assumption.
Qed.

Lemma CRinvT_irrelevant : forall x x_ x__, (CRinvT x x_ == CRinvT x x__)%CR.
Proof.
 intros.
 apply CRinvT_wd.
 reflexivity.
Qed.
