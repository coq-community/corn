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

Require Export CauchySeq.
Require Import iso_CReals.
Require Import R_morphism.
Require Import CRArith.
Require Export CRreal.
Require Import CornTac.

Opaque CR inject_Q.

Lemma CRIR_iso : Isomorphism CRasCReals IR.
Proof.
apply Canonic_Isomorphism_between_CReals.
Qed.

Definition CRasIR : CR -> IR := iso_map_lft _ _ CRIR_iso.
Definition IRasCR : IR -> CR := iso_map_rht _ _ CRIR_iso.

Lemma CRasIRasCR_id : forall (x:CR), (IRasCR (CRasIR x)==x)%CR.
Proof.
rapply (inversity_rht _ _ CRIR_iso).
Qed.

Lemma IRasCRasIR_id : forall (x:IR), (CRasIR (IRasCR x)[=]x).
Proof.
rapply (inversity_lft _ _ CRIR_iso).
Qed.

Lemma IRasCR_wd : forall x y, x[=]y -> (IRasCR x == IRasCR y)%CR.
Proof.
rapply map_wd_unfolded.
Qed.

Lemma IR_Zero_as_CR : (IRasCR Zero==Zero)%CR.
Proof.
rapply map_pres_zero_unfolded.
Qed.

Lemma IR_plus_as_CR : forall x y,
 (IRasCR (x[+]y)== IRasCR x + IRasCR y)%CR.
Proof.
rapply map_pres_plus.
Qed.

Lemma IR_Sum0_as_CR : forall m x, 
 (IRasCR (Sum0 m x)==Sum0 m (fun n => IRasCR (x n)))%CR.
Proof.
intros m x.
induction m.
rapply IR_Zero_as_CR.
simpl in *.
set (a:=Sum0 (G:=CRasCAbGroup) m (fun n : nat => IRasCR (x n))) in *.
clearbody a.
change CR in a.
rewrite <- IHm.
rapply IR_plus_as_CR.
Qed.

Lemma IR_opp_as_CR : forall x,
 (IRasCR ([--]x)== - IRasCR x)%CR.
Proof.
rapply map_pres_minus.
Qed.

Lemma IR_One_as_CR : (IRasCR One==One)%CR.
Proof.
rapply map_pres_one_unfolded.
Qed.

Lemma IR_mult_as_CR : forall x y, 
 (IRasCR (x[*]y)==(IRasCR x * IRasCR y))%CR.
Proof.
rapply map_pres_mult.
Qed.

Lemma IR_div_as_CR : forall x y y_ y__, 
 (IRasCR (x[/]y[//]y_)==(IRasCR x[/]IRasCR y[//]y__))%CR.
Proof.
intros x y y_ y__.
rapply mult_cancel_lft.
apply (map_pres_ap_zero _ _ (iso_map_rht _ _ CRIR_iso) y y_).
change ((IRasCR y[*]IRasCR (x[/]y[//]y_):CR)==IRasCR y*((IRasCR x[/]IRasCR y[//]y__):CR))%CR.
rewrite <- IR_mult_as_CR.
transitivity (IRasCR x).
apply IRasCR_wd.
rational.
symmetry.
change (IRasCR y[*](IRasCR x[/]IRasCR y[//]y__)[=]IRasCR x).
rapply div_1'.
Qed.

Lemma IR_div_as_CR_1 :forall x y y_,
 (IRasCR (x[/]y[//]y_)==(IRasCR x[/]IRasCR y[//](map_pres_ap_zero _ _ (iso_map_rht _ _ CRIR_iso) y y_)))%CR.
Proof.
intros; rapply IR_div_as_CR.
Qed.

Lemma IR_nring_as_CR : forall n, 
 (IRasCR (nring n)==nring n)%CR.
Proof.
induction n.
apply IR_Zero_as_CR.
simpl in *.
set (a:= (nring (R:=CRasCRing) n)) in *.
clearbody a.
change CR in a.
rewrite IR_plus_as_CR.
rewrite IHn.
rewrite IR_One_as_CR.
reflexivity.
Qed.

Lemma IR_pring_as_CR : forall p, 
 (IRasCR (pring _ p)==pring _ p)%CR.
Proof.
unfold pring.
intros p.
cut (IRasCR One == One)%CR;[|apply IR_One_as_CR].
generalize (One:IR).
generalize (One:CR).
induction p;intros a b Hab.

simpl.
assert (IRasCR ((Zero[+]One[+]One)[*]b)== (Zero[+]One[+]One)[*]a)%CR.
simpl.
rewrite IR_mult_as_CR.
repeat rewrite IR_plus_as_CR.
repeat rewrite IR_One_as_CR.
simpl.
rewrite IR_Zero_as_CR.
simpl.
rewrite Hab.
reflexivity.
assert (X:= (IHp _ _ H)).
simpl in X.
set (c:=pring_aux CRasCRing p ((' 0 + ' 1 + ' 1) * a)%CR) in *.
clearbody c.
change CR in c.
rewrite <- X.
rewrite IR_plus_as_CR.
rewrite Hab.
reflexivity.

simpl.
assert (IRasCR ((Zero[+]One[+]One)[*]b)== (Zero[+]One[+]One)[*]a)%CR.
simpl.
rewrite IR_mult_as_CR.
repeat rewrite IR_plus_as_CR.
repeat rewrite IR_One_as_CR.
simpl.
rewrite IR_Zero_as_CR.
simpl.
rewrite Hab.
reflexivity.
rapply (IHp _ _ H).

simpl.
assumption.
Qed.

Lemma IR_zring_as_CR : forall z, 
 (IRasCR (zring z)==zring z)%CR.
Proof.
intros [|p|p].
apply IR_Zero_as_CR.
rapply IR_pring_as_CR.
change ((IRasCR [--](pring IR p) == - ((pring CRasCRing p):CR))%CR).
rewrite IR_opp_as_CR.
apply CRopp_wd.
apply IR_pring_as_CR.
Qed.

Lemma IR_inj_Q_as_CR : forall (a:Q), (IRasCR (inj_Q IR a)==('a))%CR.
Proof.
intros [n d].
unfold inj_Q.
rewrite IR_div_as_CR_1.
generalize (map_pres_ap_zero IR CRasCReals (iso_map_rht CRasCReals IR CRIR_iso) (nring (R:=IR) d)
    (den_is_nonzero IR (n # d)%Q)).
intros d_.
change ((((IRasCR (zring (R:=IR) n)[/]IRasCR (nring (R:=IR) d)[//]d_):CR) == ' (n # d))%CR).
rewrite Qmake_Qdiv.
change ((((IRasCR (zring (R:=IR) n)[/]IRasCR (nring (R:=IR) d)[//]d_):CR) ==
 ' ((n # 1) * / (d # 1)))%CR).
rewrite <- CRmult_Qmult.
assert (d__:('d><'0%Q)%CR).
apply Qap_CRap.
discriminate.
change ((((IRasCR (zring (R:=IR) n)[/]IRasCR (nring (R:=IR) d)[//]d_):CR) ==
 ' (n # 1) * ' (/ (d # 1)))%CR).
rewrite <- (CRinv_Qinv d d__).
unfold cf_div.

assert (X:(forall (n:positive), IRasCR (nring (R:=IR) n) == ' ('n)%Z)%CR).
intros x.
clear -x.
rewrite <- convert_is_POS.
induction (nat_of_P x); clear x.
apply IR_Zero_as_CR.
simpl.
rewrite IR_plus_as_CR.
rewrite IHn.
rewrite IR_One_as_CR.
simpl.
rewrite CRplus_Qplus.
rewrite CReq_Qeq.
unfold Qeq.
simpl.
rewrite Pmult_1_r.
rewrite <- POS_anti_convert.
ring_simplify.
symmetry.
rewrite Zplus_comm.
apply (inj_plus 1 n).

rsapply mult_wd;[|rsapply f_rcpcl_wd;apply (X d)].
destruct n as [|p|p];[apply IR_Zero_as_CR| |];simpl.
transitivity (IRasCR (nring p)).
apply IRasCR_wd.
apply pring_convert.
apply (X p).
transitivity (IRasCR [--](nring p)).
apply IRasCR_wd.
rapply csf_wd_unfolded.
apply pring_convert.
rewrite IR_opp_as_CR.
rewrite X.
rewrite CRopp_Qopp.
reflexivity.
Qed.

Lemma IR_Cauchy_prop_as_CR : forall (x:CauchySeq IR),
(Cauchy_prop (fun n => (IRasCR (x n)))).
Proof.
intros x.
assert (X:=map_pres_Lim _ _ (iso_map_rht CRasCReals IR CRIR_iso) _ _ (Cauchy_complete x)).
intros e He.
destruct (X _ (pos_div_two _ _ He)) as [n Hn].
exists n.
intros m Hm.
assert (A:=Hn m Hm).
assert (B:=Hn n (le_n n)).
set (a:=(IRasCR (x m))) in  *.
set (b:=IRasCR (Lim (IR:=IR) x)) in *.
set (c:=IRasCR (x n)) in *.
rstepr ((a[-]b)[+](b[-]c)).
rapply AbsSmall_eps_div_two.
assumption.
rapply AbsSmall_minus.
assumption.
Qed.

Lemma IR_Lim_as_CR : forall (x:CauchySeq IR),
(IRasCR (Lim x)==Lim (Build_CauchySeq _ _ (IR_Cauchy_prop_as_CR x)))%CR.
Proof.
intros x.
rapply SeqLimit_unique.
rapply (map_pres_Lim _ _ (iso_map_rht CRasCReals IR CRIR_iso) _ _ (Cauchy_complete x)).
Qed.
