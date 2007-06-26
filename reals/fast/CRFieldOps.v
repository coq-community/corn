(*
Copyright © 2006 Russell O’Connor

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

Require Import CLogic.
Require Export CRlattice.
Require Import QMinMax.
Require Import Qabs.
Require Import COrdAbs.
Require Import Qordfield.
Require Import Qmetric.
Require Import CornTac.

Set Implicit Arguments.

Open Local Scope uc_scope.
Opaque CR Qmin Qmax Qred.

Definition CRpos (x:CR) := {e:Qpos | ' e <= x}%CR.

Lemma CRpos_wd : forall x y, (x==y)%CR -> (CRpos x) -> (CRpos y).
Proof.
intros x y Hxy [e H].
exists e.
abstract (
rewrite <- Hxy;
assumption
).
Defined.

Definition CRneg (x:CR) := {e:Qpos | x <= ' (-e)%Q}%CR.

Lemma CRneg_wd : forall x y, (x==y)%CR -> (CRneg x) -> (CRneg y).
Proof.
intros x y Hxy [e H].
exists e.
abstract (
rewrite <- Hxy;
assumption
).
Defined.

Definition CRlt (x y:CR) := CRpos (y-x)%CR.

Infix "<" := CRlt : CR_scope.

Lemma CRlt_wd : forall x1 x2, (x1==x2 -> forall y1 y2, y1==y2 -> x1 < y1 -> x2 < y2)%CR.
Proof.
intros x1 x2 Hx y1 y2 Hy H.
rapply CRpos_wd;[|apply H].
abstract (
rewrite <- Hx;
rewrite <- Hy;
reflexivity
).
Defined.

Definition CRapart (x y:CR) := (x < y or y < x)%CR.

Notation "x >< y" := (CRapart x y) (at level 70, no associativity) : CR_scope.

Lemma CRapart_wd : forall x1 x2, (x1==x2 -> forall y1 y2, y1==y2 -> x1><y1 -> x2><y2)%CR.
Proof.
intros x1 x2 Hx y1 y2 Hy [H|H];[left;apply (CRlt_wd Hx Hy)|right;apply (CRlt_wd Hy Hx)];assumption.
Defined.

Definition Qscale_modulus (a:Q) (e:Qpos) : QposInf :=
match a with
| 0 # _ => QposInfinity
| (Zpos an) # ad => Qpos2QposInf ((ad # an) * e)
| (Zneg an) # ad => Qpos2QposInf ((ad # an) * e)
end.

Lemma Qscale_modulus_elim : forall (P:QposInf -> Type) (x:Q) (e:Qpos),
(x==0 -> P QposInfinity)%Q ->
(forall y:Qpos, AbsSmall (e/y)%Q (x)%Q -> (P y)) ->
P (Qscale_modulus x e).
Proof.
intros P [xn xd] e H1.
cut (forall xn:positive, (forall y : Qpos, AbsSmall (e/y)%Q (xn#xd)%Q -> P y) ->
P (Qscale_modulus (xn # xd) e)).
intros H H2.
destruct xn as [|xn|xn].
apply H1.
constructor.
apply H.
assumption.
rapply H.
intros y Hy.
apply H2.
change (Zneg xn # xd)%Q with ([--](xn # xd))%Q.
rsapply inv_resp_AbsSmall.
assumption.
clear xn H1.
intros xn H2.
simpl.
apply H2.
autorewrite with QposElim.
stepl (/(xd#xn))%Q by (simpl;field).
change (/(xd#xn))%Q with (xn#xd)%Q.
apply AbsSmall_reflexive.
discriminate.
change (xd#xn==0)%Q with ((xd#xn)%Qpos==0)%Q.
split; apply Qpos_nonzero.
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

Lemma Qscale_uc_prf (a:Q) :  is_UniformlyContinuousFunction (fun b:Q => a*b) (Qscale_modulus a).
Proof.
intros [[|an|an] ad] e b0 b1 H.
simpl in *.
setoid_replace ((0 # ad)) with 0 by constructor.
unfold Qball.
stepr 0 by (simpl; ring).
rapply zero_AbsSmall.
simpl.
auto with *.

simpl in *.
unfold Qball in *.
autorewrite with QposElim.
stepr ((an#ad)*(b0-b1)) by (simpl; ring).
rsapply (fun x y => (AbsSmall_cancel_mult _ x y (ad#an))).
constructor.
stepl (((ad # an) * e)%Qpos:Q) by (simpl;QposRing).
stepr (b0 - b1).
apply H.
stepr ((an#ad)*(ad#an)*(b0-b1)) by (simpl;ring).
simpl.
setoid_replace ((an#ad)*(ad#an)) with 1.
ring.
unfold Qeq.
simpl.
rewrite Pmult_1_r.
rewrite Pmult_comm.
reflexivity.

simpl in *.
unfold Qball in *.
autorewrite with QposElim.
stepr ((Zneg an#ad)*(b0-b1)) by (simpl; ring).
rsapply (fun x y => (AbsSmall_cancel_mult _ x y (ad#an))).
constructor.
stepl (((ad # an) * e)%Qpos:Q) by (simpl;QposRing).
stepr (b1 - b0).
rapply AbsSmall_minus.
apply H.
stepr ((Zneg an#ad)*(ad#an)*(b0-b1)) by (simpl;ring).
simpl.
setoid_replace ((Zneg an#ad)*(ad#an)) with ([--]1).
simpl; ring.
unfold Qeq.
simpl.
rewrite Pmult_1_r.
rewrite Pmult_comm.
reflexivity.
Qed.

Definition Qscale_uc (a:Q_as_MetricSpace) : Q_as_MetricSpace --> Q_as_MetricSpace :=
Build_UniformlyContinuousFunction (Qscale_uc_prf a).

Definition scale (a:Q) : CR --> CR := Cmap QPrelengthSpace (Qscale_uc a).

Definition QboundAbs (c:Qpos) := uc_compose (QboundBelow_uc (-c)) (QboundAbove_uc c).

Definition CRboundAbs (c:Qpos) := Cmap QPrelengthSpace (QboundAbs c).

Lemma QboundAbs_absorb: forall (a b:Qpos) (c:Q),
 a <= b ->
 QboundAbs b (QboundAbs a c) == QboundAbs a c.
Proof.
intros a b c H.
simpl.
rewrite Qmin_max_distr_r.
setoid_replace (Qmin b (-a)) with (-a).
rewrite Qmax_assoc.
rewrite <- Qmin_max_de_morgan.
rewrite Qmin_assoc.
setoid_replace (Qmin b a) with (a:Q).
reflexivity.
rewrite <- Qle_min_r.
assumption.
rewrite <- Qle_min_r.
rewrite Qle_minus_iff.
ring_simplify.
auto with *.
Qed.

Lemma CRboundAbs_Eq : forall (a:Qpos) (x:CR),
 ('(-a)%Q <= x -> x <= ' a ->
 CRboundAbs a x == x)%CR.
Proof.
intros a x Ha Hb.
unfold CRboundAbs.
transitivity (uc_compose (Cmap QPrelengthSpace (QboundBelow_uc (-a))) (Cmap QPrelengthSpace (QboundAbove_uc a)) x).
rapply MonadLaw2.
simpl.
change (boundBelow (-a)%Q (boundAbove a x) == x)%CR.
assert (X:(boundAbove a x==x)%CR).
rewrite <- CRmin_boundAbove.
rewrite <- CRle_min_r.
assumption.
rewrite X.
rewrite <- CRmax_boundBelow.
rewrite <- CRle_max_r.
assumption.
Qed.

Lemma QboundAbs_elim : forall (z:Qpos) (a:Q) (P:Q->Prop),
((z <= a)%Q -> P z) ->
((a <= -z)%Q -> P (- z)%Q) ->
(AbsSmall (z:Q) a -> P (a)) ->
P (QboundAbs z a).
Proof.
intros z a P H1 H2 H3.
simpl.
apply Qmax_case; apply Qmin_case;
intros Z0 Z1; try solve [apply H1;assumption|apply H2;assumption].
elim (Qle_not_lt _ _ Z1).
rewrite Qlt_minus_iff.
ring_simplify.
rapply mult_resp_pos.
constructor.
apply Qpos_prf.
apply H3.
split;assumption.
Qed.

Definition Qmult_modulus (c:Qpos)(e:Qpos) : QposInf := (e / c)%Qpos.

Lemma Qmult_uc_prf (c:Qpos) : is_UniformlyContinuousFunction (fun a => uc_compose (Qscale_uc a) (QboundAbs c)) (Qmult_modulus c).
Proof.
intros c e a0 a1 H b.
simpl in *.
set (b' := Qmax (- c) (Qmin c b)).
repeat rewrite (fun x => Qmult_comm x b').
apply Qscale_uc_prf.
setoid_replace (e/c)%Qpos with (Qpos_inv c*e)%Qpos in H by QposRing.
apply ball_ex_weak_le with (Qpos_inv c*e)%Qpos;[|assumption].
unfold b'.
apply Qmax_case.
intros H1.
rapply Qle_refl.
apply Qmin_case; intros H1 H2.
rapply Qle_refl.
destruct b as [[|bn|bn] bd]; simpl; try constructor;
(autorewrite with QposElim;
rapply mult_resp_leEq_rht;
[change ((One[/](c:Q)[//](@Qpos_nonzero c))[<=](One[/](bn#bd)[//](@Qpos_nonzero (bn#bd)%Qpos)));
 rsapply recip_resp_leEq;
 [apply (@Qpos_prf (bn#bd)%Qpos)
 |]
|apply Qpos_nonneg]).
assumption.
replace LHS with (- (- (bn # bd))) by ring.
replace RHS with (- (- c)) by ring.
rsapply inv_resp_leEq.
apply H2.
Qed.

Implicit Arguments Qmult_uc_prf [].

Definition Qmult_uc (c:Qpos) :  Q_as_MetricSpace --> Q_as_MetricSpace --> Q_as_MetricSpace:=
Build_UniformlyContinuousFunction (Qmult_uc_prf c).

Definition CRmult_bounded (c:Qpos) : CR --> CR --> CR :=
Cmap2 QPrelengthSpace QPrelengthSpace (Qmult_uc c).

Definition CR_b (e:Qpos) (x:CR) : Qpos.
intros e x.
refine (@mkQpos (Qabs (approximate x e) + e:Q) _).
abstract (
(replace RHS with (Qabs (approximate x e) - (-e)) by ring);
rsapply shift_zero_less_minus;
apply Qlt_le_trans with 0;[constructor|apply Qabs_nonneg]
).
Defined.

Lemma CR_b_lowerBound : forall e x, (' (-CR_b e x)%Q <= x)%CR.
Proof.
intros e x e'.
unfold CR_b.
autorewrite with QposElim.
simpl.
unfold Cap_raw.
simpl.
rewrite Qle_minus_iff.
ring_simplify.
destruct (regFun_prf x ((1#2)*e')%Qpos e) as [H _].
simpl in H.
rewrite Qle_minus_iff in H.
ring_simplify in H.
eapply Qle_trans.
apply H.
rewrite Qle_minus_iff.
autorewrite with QposElim.
ring_simplify.
clear H.
apply Qabs_case; intros H;
[repeat rsapply plus_resp_nonneg; try assumption
|ring_simplify];
(rsapply mult_resp_nonneg;[discriminate|apply Qpos_nonneg]).
Qed.

Lemma CR_b_upperBound : forall e x, (x <= 'CR_b e x)%CR.
Proof.
intros e x e'.
unfold CR_b.
autorewrite with QposElim.
simpl.
unfold Cap_raw.
simpl.
rewrite Qle_minus_iff.
ring_simplify.
destruct (regFun_prf x ((1#2)*e')%Qpos e) as [_ H].
simpl in H.
rewrite Qle_minus_iff in H.
ring_simplify in H.
eapply Qle_trans.
apply H.
rewrite Qle_minus_iff.
autorewrite with QposElim.
ring_simplify.
clear H.
apply Qabs_case; intros H.
ring_simplify;(rsapply mult_resp_nonneg;[discriminate|apply Qpos_nonneg]).
ring_simplify;
repeat rsapply plus_resp_nonneg.
replace RHS with ((2#1)*(-(approximate x e))) by ring.
rsapply mult_resp_nonneg.
discriminate.
apply (Qopp_le_compat (approximate x e) 0).
assumption.
(rsapply mult_resp_nonneg;[discriminate|apply Qpos_nonneg]).
Qed.

Definition CRmult x y := ucFun2 (CRmult_bounded (CR_b (1#1) y)) x y.

Infix "*" := CRmult : CR_scope.

Lemma CRmult_bounded_weaken : forall (c1 c2:Qpos) x y,
((' (-c1)%Q <= y) -> (y <= ' c1) -> (c1 <= c2)%Q ->
CRmult_bounded c1 x y == CRmult_bounded c2 x y)%CR.
Proof.
intros c1 c2 x y Hc1a Hc1b Hc2.
assert (Hy:=CRboundAbs_Eq Hc1a Hc1b).
set (y':= (CRboundAbs c1 y)) in *.
transitivity (ucFun2 (CRmult_bounded c2) x y');
[|unfold y';rewrite Hy;try assumption;reflexivity].
assert (H:forall x:Qpos, (x*c1/c2)%Qpos <= x).
intros a.
autorewrite with QposElim.
change (((a* c1)[/](c2:Q)[//]@Qpos_nonzero c2)[<=](a:Q)).
rsapply shift_div_leEq'.
apply Qpos_prf.
rewrite Qmult_comm.
rsapply mult_resp_leEq_rht.
assumption.
apply Qpos_nonneg.
change (ucFun2 (CRmult_bounded c1) x y == ucFun2 (CRmult_bounded c2) x y')%CR.
rewrite <- (QreduceApprox_Eq x).
set (x''':=(QreduceApprox x)).
set (x':=faster x''' (fun x => (x * c1 /c2)%Qpos) H).
transitivity (ucFun2 (CRmult_bounded c1) x' y).
unfold x'.
rewrite fasterIsEq.
reflexivity.
rapply regFunEq_e; intros e.
intros.
simpl.
do 3 (unfold Cap_raw; simpl).
assert (X:=fun c => QboundAbs_absorb c Hc2).
unfold QboundAbs in X.
simpl in X.
rewrite X.
clear X.
replace (QposRed ((1 # 2) * e / c1 * c1 / c2)%Qpos)
 with (QposRed ((1 # 2) * e / c2)%Qpos);
 [repeat rewrite QposInf_bind_id;rapply ball_refl|].
apply QposRed_complete.
autorewrite with QposElim.
field.
split;apply Qpos_nonzero.
Qed.

Lemma CRmult_bounded_mult : forall (c:Qpos) (x y:CR),
 (' (-c)%Q <= y -> y <= ' c ->
  CRmult_bounded c x y == x*y)%CR.
Proof.
intros c x y Hc1 Hc2.
unfold CRmult.
set (d:=(CR_b (1 # 1) y)).
destruct (Qle_total c d).
rapply CRmult_bounded_weaken; assumption.
symmetry.
rapply CRmult_bounded_weaken; try assumption.
rapply CR_b_lowerBound.
rapply CR_b_upperBound.
Qed.

Add Morphism CRmult with signature ms_eq ==> ms_eq ==> ms_eq as CRmult_wd.
Proof.
intros x1 x2 Hx y1 y2 Hy.
unfold CRmult.
set (c:=(CR_b (1 # 1) y1)).
set (d:=(CR_b (1 # 1) y2)).
rewrite Hx.
rewrite Hy.
unfold d.
rapply CRmult_bounded_mult;
rewrite <- Hy.
rapply CR_b_lowerBound.
rapply CR_b_upperBound.
Qed.

Lemma CRmult_scale : forall (a:Q) (y:CR), ((' a)*y==scale a y)%CR.
Proof.
intros a y.
unfold CRmult.
unfold CRmult_bounded.
unfold ucFun2.
unfold Cmap2.
unfold inject_Q.
simpl.
rewrite MonadLaw3.
rewrite StrongMonadLaw1.
simpl.
transitivity (uc_compose (Cmap QPrelengthSpace (Qscale_uc a))
                        (Cmap QPrelengthSpace (QboundAbs (CR_b (1#1) y))) y).
rapply MonadLaw2.
simpl.
change (Cmap QPrelengthSpace (Qscale_uc a)
   (Cmap_fun QPrelengthSpace (QboundAbs (CR_b (1 # 1) y)) y) ==
 Cmap QPrelengthSpace (Qscale_uc a) y)%CR.
rapply uc_wd.
rapply CRboundAbs_Eq.
apply CR_b_lowerBound.
apply CR_b_upperBound.
Qed.

Definition Qinv_modulus (c:Qpos) (e:Qpos) : Qpos := (c*c*e)%Qpos.

Lemma Qpos_Qmax : forall (a:Qpos) (b:Q), 0<Qmax a b.
Proof.
intros a b.
apply Qmax_case; intros H.
apply Qpos_prf.
apply Qlt_le_trans with a.
apply Qpos_prf.
assumption.
Qed.

Lemma Qinv_pos_uc_prf (c:Qpos) :  is_UniformlyContinuousFunction (fun a:Q => /(Qmax c a) ) (Qinv_modulus c).
Proof.
intros c e a0 a1 Ha.
simpl in *.
unfold Qball in *.
rsapply AbsSmall_cancel_mult.
instantiate (1:=(Qmax c a0)*(Qmax c a1)).
rewrite <- (QposAsmkQpos (Qpos_Qmax c a0)).
rewrite <- (QposAsmkQpos (Qpos_Qmax c a1)).
rewrite <- Q_Qpos_mult.
apply Qpos_prf.
assert (H : forall (a:Qpos) b, ~(Qmax a b)==0).
intros a b.
rewrite <- (QposAsmkQpos (Qpos_Qmax a b)).
apply Qpos_nonzero.
stepr (Qmax c a1 - Qmax c a0) by
 simpl; field; repeat split; apply H.
rsapply AbsSmall_leEq_trans.
instantiate (1:=(c*c*e)).
rewrite Qmult_comm.
rsapply mult_resp_leEq_lft;[|apply Qpos_nonneg].
rsapply mult_resp_leEq_both; (apply Qpos_nonneg || apply Qmax_ub_l).
change (ball (c*c*e) (Qmax c a1) (Qmax c a0)).
apply ball_sym.
apply QboundBelow_uc_prf.
apply Ha.
Qed.

Implicit Arguments Qinv_pos_uc_prf [].

Definition Qinv_pos_uc (c:Qpos) : Q_as_MetricSpace --> Q_as_MetricSpace :=
Build_UniformlyContinuousFunction (Qinv_pos_uc_prf c).

Lemma Qinv_pos_uc_wd : forall (c1 c2:Qpos), (c1 <= c2) -> forall x, (c2 <= x) -> ms_eq (Qinv_pos_uc c1 x) (Qinv_pos_uc c2 x).
Proof.
intros c1 c2 Hc x Hx.
simpl.
setoid_replace (Qmax c2 x) with x by
 (rewrite <- Qle_max_r; assumption).
setoid_replace (Qmax c1 x) with x.
reflexivity.
rewrite <- Qle_max_r.
apply Qle_trans with c2; assumption.
Qed.

Definition CRinv_pos (c:Qpos) : CR --> CR := (Cmap QPrelengthSpace (Qinv_pos_uc c)).

Lemma CRinv_pos_weaken : forall (c1 c2:Qpos), c1 <= c2 -> forall (x:CR), (' c2 <= x -> CRinv_pos c1 x == CRinv_pos c2 x)%CR.
Proof.
intros c1 c2 Hc x Hx.
assert (X:((boundBelow c2 x)==x)%CR).
rewrite <- CRmax_boundBelow.
rewrite <- CRle_max_r.
assumption.
rewrite <- X.
rewrite <- (QreduceApprox_Eq x).
pose (f:=(fun e:Qpos => (c1*c1/c2/c2)*e)%Qpos).
assert (Y:forall e:Qpos, f e <= e).
intros e.
unfold f.
autorewrite with QposElim.
rsapply (mult_cancel_leEq _ (c1*c1/c2/c2*e) (e:Q) (c2*c2:Q)).
rapply mult_resp_pos;apply Qpos_prf.
replace LHS with (e*(c1*c1)) by (field;rapply Qpos_nonzero).
rapply mult_resp_leEq_lft;[|rapply Qpos_nonneg].
rapply mult_resp_leEq_both;try assumption;apply Qpos_nonneg.
transitivity (CRinv_pos c2 (boundBelow c2  (faster (QreduceApprox x) f Y))).
rapply regFunEq_e.
intros e.
assert (Z:=Qinv_pos_uc_wd Hc).
simpl in Z.
simpl.
rewrite Z;[apply Qmax_ub_l|].
replace (QposRed (c1 * c1 * e))
 with (QposRed (f (c2 * c2 * e)%Qpos));
 [rapply ball_refl|].
apply QposRed_complete.
unfold f.
autorewrite with QposElim.
field.
apply Qpos_nonzero.
rewrite fasterIsEq.
reflexivity.
Qed.

Lemma CRinv_pos_Qinv : forall (c:Qpos) x, (c <= x)%Q -> (CRinv_pos c (' x) == (' (/x)))%CR.
Proof.
intros c x H.
rapply regFunEq_e.
intros e.
simpl.
setoid_replace (Qmax c x) with x.
rapply ball_refl.
rewrite <- Qle_max_r.
assumption.
Qed.

Definition CRinv (x:CR)(x_: (x >< ' 0)%CR) : CR.
intros x [[c H]|[c H]].
exact ((-(CRinv_pos c (-x)))%CR).
exact (CRinv_pos c x).
Defined.

Implicit Arguments CRinv [].

Lemma CRinv_pos_inv : forall (c:Qpos) (x:CR) x_,
 (inject_Q c <= x ->
  CRinv_pos c x == CRinv x x_)%CR.
Proof.
intros c x [[e He]|[e He]] H.
assert (X:(' e <= -x)%CR).
rewrite <- (doubleSpeed_Eq x).
intros d.
eapply Qle_trans.
apply He.
simpl.
do 2 (unfold Cap_raw;simpl).
ring_simplify.
apply Qle_refl.
assert (' c <= ' (-e)%Q)%CR.
eapply CRle_trans.
apply H.
intros d.
eapply Qle_trans.
apply X.
simpl.
do 2 (unfold Cap_raw;simpl).
rewrite Qle_minus_iff.
ring_simplify.
apply Qle_refl.
elim (Qlt_not_le _ _ (Qpos_prf c)).
assert (Y:=H0 (e)%Qpos).
simpl in Y.
do 2 (unfold Cap_raw in Y ;simpl in Y).
rewrite Qle_minus_iff in Y.
ring_simplify in Y.
rewrite Qle_minus_iff.
ring_simplify.
assumption.

assert (' e <= x)%CR.
rewrite <- (doubleSpeed_Eq x).
intros d.
eapply Qle_trans.
apply He.
simpl.
do 2 (unfold Cap_raw;simpl).
ring_simplify.
apply Qle_refl.
destruct (Qle_total c e);[|symmetry];
rapply CRinv_pos_weaken;
assumption.
Qed.

Lemma CRinv_wd : forall (x y:CR) x_ y_, (x == y -> CRinv x x_ == CRinv y y_)%CR.
Proof.
assert (X:forall x, ((' 0%Q) + x == x)%CR).
intros x.
transitivity (doubleSpeed x);[|rapply doubleSpeed_Eq].
rapply regFunEq_e.
intros e.
simpl.
unfold Cap_raw; simpl.
ring_simplify.
rapply ball_refl.
assert (Y:forall x, (x + - (' 0%Q) == x)%CR).
intros x.
transitivity (doubleSpeed x);[|rapply doubleSpeed_Eq].
rapply regFunEq_e.
intros e.
simpl.
unfold Cap_raw; simpl.
ring_simplify.
rapply ball_refl.

intros x y [[c x_]|[c x_]] [[d y_]|[d y_]] H.
change (-(CRinv_pos c (-x))== (-(CRinv_pos d (-y))))%CR.
rewrite H in *.
rewrite X in *.
apply CRopp_wd.
destruct (Qle_total c d);[|symmetry];
 apply CRinv_pos_weaken; try assumption.

elim (Qlt_not_le _ _ (Qpos_prf c)).
rewrite X in *.
rewrite Y in *.
rewrite H in *.
assert (Z:=Qplus_le_compat _ _ _ _ (x_ ((1#2)*d)%Qpos) (y_ ((1#2)*d)%Qpos)).
simpl in Z.
unfold Cap_raw in Z; simpl in Z.
autorewrite with QposElim in Z.
rewrite Qle_minus_iff in Z.
ring_simplify in Z.
rewrite Qle_minus_iff.
ring_simplify.
assumption.

elim (Qlt_not_le _ _ (Qpos_prf c)).
rewrite X in *.
rewrite Y in *.
rewrite H in *.
assert (Z:=Qplus_le_compat _ _ _ _ (x_ ((1#2)*d)%Qpos) (y_ ((1#2)*d)%Qpos)).
simpl in Z.
unfold Cap_raw in Z; simpl in Z.
autorewrite with QposElim in Z.
rewrite Qle_minus_iff in Z.
ring_simplify in Z.
rewrite Qle_minus_iff.
ring_simplify.
assumption.

change (CRinv_pos c x== (CRinv_pos d y))%CR.
rewrite H in *.
rewrite Y in *.
destruct (Qle_total c d);[|symmetry];
 apply CRinv_pos_weaken; try assumption.
Qed.

Lemma CRinv_irrelvent : forall x x_ x__, (CRinv x x_ == CRinv x x__)%CR.
Proof.
intros.
apply CRinv_wd.
reflexivity.
Qed.
