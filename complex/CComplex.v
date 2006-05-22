(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(* $Id$ *)

(** printing Re %\ensuremath{\Re}% #&real;# *)
(** printing Im %\ensuremath{\Im}% #&image;# *)
(** printing CC %\ensuremath{\mathbb C}% #<b>C</b># *)
(** printing II %\ensuremath{\imath}% #i# *)
(** printing [+I*] %\ensuremath{+\imath}% *)
(** printing AbsCC %\ensuremath{|\cdot|_{\mathbb C}}% *)
(** printing CCX %\ensuremath{\mathbb C[X]}% #<b>C</b>[X]# *)

Require Export NRootIR.

(** * Complex Numbers
** Algebraic structure
*)

Section Complex_Numbers.
Record CC_set : Type :=
  {Re : IR;
   Im : IR}.

Definition cc_ap (x y : CC_set) : CProp := Re x [#] Re y or Im x [#] Im y.

Definition cc_eq (x y : CC_set) : Prop := Re x [=] Re y /\ Im x [=] Im y.

Lemma cc_is_CSetoid : is_CSetoid _ cc_eq cc_ap.
apply Build_is_CSetoid.
unfold irreflexive in |- *.
intros. elim x. intros x1 x2. unfold cc_ap in |- *. simpl in |- *.
intro H. elim H; clear H; intros H.
cut (Not (x1 [#] x1)). intros H0. elim (H0 H). apply ap_irreflexive_unfolded.
cut (Not (x2 [#] x2)). intros H0. elim (H0 H). apply ap_irreflexive_unfolded.
unfold Csymmetric in |- *.
intros x y. elim x. intros x1 x2. elim y. intros y1 y2. unfold cc_ap in |- *.
simpl in |- *. intros H. elim H; clear H; intros H.
left. apply ap_symmetric_unfolded. auto.
right. apply ap_symmetric_unfolded. auto.
unfold cotransitive in |- *.
intros x y. elim x. intros x1 x2. elim y. intros y1 y2. unfold cc_ap in |- *.
simpl in |- *. intro H. intro. elim z. intros z1 z2. simpl in |- *. intros.
elim H; clear H; intros H.
cut (x1 [#] z1 or z1 [#] y1). intro H0.
elim H0; clear H0; intros H0. left. left. auto. right. left. auto.
apply ap_cotransitive_unfolded. auto.
cut (x2 [#] z2 or z2 [#] y2). intro H0.
elim H0; clear H0; intros H0. left. right. auto. right. right. auto.
apply ap_cotransitive_unfolded. auto.
unfold tight_apart in |- *.
intros x y. elim x. intros x1 x2. elim y. intros y1 y2.
unfold cc_ap in |- *. unfold cc_eq in |- *. simpl in |- *. split.
intros. split.
apply not_ap_imp_eq. intro. apply H. left. auto.
apply not_ap_imp_eq. intro. apply H. right. auto.
intros. elim H. clear H. intros H H0. intro H1. elim H1; clear H1; intros H1.
cut (Not (x1 [#] y1)). intro. elim (H2 H1). apply eq_imp_not_ap. auto.
cut (Not (x2 [#] y2)). intro. elim (H2 H1). apply eq_imp_not_ap. auto.
Qed.

Definition cc_csetoid := Build_CSetoid CC_set cc_eq cc_ap cc_is_CSetoid.

Definition cc_plus x y := Build_CC_set (Re x[+]Re y) (Im x[+]Im y).

Definition cc_mult x y := Build_CC_set (Re x[*]Re y[-]Im x[*]Im y) (Re x[*]Im y[+]Im x[*]Re y).

Definition cc_zero := Build_CC_set ZeroR ZeroR.

Definition cc_one := Build_CC_set OneR ZeroR.

Definition cc_i := Build_CC_set ZeroR OneR.

Definition cc_inv (x : CC_set) : CC_set := Build_CC_set [--] (Re x) [--] (Im x).

(* not needed anymore
Lemma cc_plus_op_proof : (bin_op_wd cc_csetoid cc_plus).
Unfold bin_op_wd. Unfold bin_fun_wd.
Intros x1 x2 y1 y2. Elim x1. Elim x2. Elim y1. Elim y2.
Simpl. Unfold cc_eq. Simpl. Intros.
Elim H. Clear H. Intros. Elim H0. Clear H0. Intros.
Split; Algebra.
Qed.

Lemma cc_mult_op_proof : (bin_op_wd cc_csetoid cc_mult).
Unfold bin_op_wd. Unfold bin_fun_wd.
Intros x1 x2 y1 y2. Elim x1. Elim x2. Elim y1. Elim y2.
Simpl. Unfold cc_eq. Simpl. Intros.
Elim H. Clear H. Intros. Elim H0. Clear H0. Intros.
Split; Algebra.
Qed.

Lemma cc_inv_op_proof : (un_op_wd cc_csetoid cc_inv).
Unfold un_op_wd. Unfold fun_wd.
Intros x y. Elim x. Elim y.
Simpl. Unfold cc_eq. Simpl. Intros.
Elim H. Clear H. Intros.
Split; Algebra.
Qed.
*)

Lemma cc_inv_strext : un_op_strext cc_csetoid cc_inv.
unfold un_op_strext in |- *. unfold fun_strext in |- *.
intros x y. elim x. elim y.
simpl in |- *. unfold cc_ap in |- *. simpl in |- *. do 4 intro. intro H.
elim H; clear H; intros.
left. apply un_op_strext_unfolded with (cg_inv (c:=IR)). auto.
right. apply un_op_strext_unfolded with (cg_inv (c:=IR)). auto.
Qed.

Lemma cc_plus_strext : bin_op_strext cc_csetoid cc_plus.
unfold bin_op_strext in |- *. unfold bin_fun_strext in |- *.
intros x1 x2 y1 y2. elim x1. elim x2. elim y1. elim y2.
simpl in |- *. unfold cc_ap in |- *. simpl in |- *. do 8 intro. intro H.
elim H; clear H; intros H.
elim (bin_op_strext_unfolded _ _ _ _ _ _ H); intros.
left. left. auto. right. left. auto.
elim (bin_op_strext_unfolded _ _ _ _ _ _ H); intros.
left. right. auto. right. right. auto.
Qed.

Lemma cc_mult_strext : bin_op_strext cc_csetoid cc_mult.
unfold bin_op_strext in |- *. unfold bin_fun_strext in |- *.
intros x1 x2 y1 y2. elim x1. elim x2. elim y1. elim y2.
simpl in |- *. unfold cc_ap in |- *. simpl in |- *. do 8 intro. intro H.
elim H; clear H; intros H.
elim (bin_op_strext_unfolded _ (cg_minus_is_csetoid_bin_op _) _ _ _ _ H);
 intros H0.
elim (bin_op_strext_unfolded _ _ _ _ _ _ H0); intros H1.
left. left. auto. right. left. auto.
cut (Im3[*]Im1 [#] Im2[*]Im0). intro H1.
elim (bin_op_strext_unfolded _ _ _ _ _ _ H1); intros H2.
left. right. auto. right. right. auto.
auto.
elim (bin_op_strext_unfolded _ _ _ _ _ _ H); intros H0.
elim (bin_op_strext_unfolded _ _ _ _ _ _ H0); intros H1.
left. left. auto. right. right. auto.
elim (bin_op_strext_unfolded _ _ _ _ _ _ H0); intros.
left. right. auto. right. left. auto.
Qed.

Definition cc_inv_op := Build_CSetoid_un_op _ _ cc_inv_strext.

Definition cc_plus_op := Build_CSetoid_bin_op _ _ cc_plus_strext.

Definition cc_mult_op := Build_CSetoid_bin_op _ _ cc_mult_strext.

Lemma cc_csg_associative : associative cc_plus_op.
unfold associative in |- *. intros. elim x. elim y. elim z. intros.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; Algebra.
Qed.

Lemma cc_cr_mult_associative : associative cc_mult_op.
unfold associative in |- *. intros. elim x. elim y. elim z. intros.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; rational.
Qed.

Definition cc_csemi_grp := Build_CSemiGroup cc_csetoid _ cc_csg_associative.

Lemma cc_cm_proof : is_CMonoid cc_csemi_grp cc_zero.
apply Build_is_CMonoid.
unfold is_rht_unit in |- *. intros. elim x. intros.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; Algebra.
unfold is_lft_unit in |- *. intros. elim x. intros.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; Algebra.
Qed.

Definition cc_cmonoid := Build_CMonoid _ _ cc_cm_proof.

Lemma cc_cg_proof : is_CGroup cc_cmonoid cc_inv_op.
unfold is_CGroup in |- *. intros. elim x. intros.
split.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; Algebra.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; Algebra.
Qed.

Lemma cc_cr_dist : distributive cc_mult_op cc_plus_op.
unfold distributive in |- *. intros. elim x. elim y. elim z. intros.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; rational.
Qed.

Lemma cc_cr_non_triv : cc_ap cc_one cc_zero.
unfold cc_ap in |- *. simpl in |- *. left. apply Greater_imp_ap. apply pos_one.
Qed.

Definition cc_cgroup := Build_CGroup cc_cmonoid cc_inv_op cc_cg_proof.

Definition cc_cabgroup : CAbGroup.
apply Build_CAbGroup with cc_cgroup.
red in |- *; unfold commutes in |- *.
intros.
elim x; elim y; split; simpl in |- *; Algebra.
Defined.

Lemma cc_cr_mult_mon : is_CMonoid
   (Build_CSemiGroup (csg_crr cc_cgroup) _ cc_cr_mult_associative) cc_one.
apply Build_is_CMonoid.
unfold is_rht_unit in |- *.
intros. elim x. intros. simpl in |- *. unfold cc_eq in |- *. simpl in |- *.
split; rational.
unfold is_lft_unit in |- *.
intros. elim x. intros. simpl in |- *. unfold cc_eq in |- *. simpl in |- *.
split; rational.
Qed.

Lemma cc_mult_commutes : commutes cc_mult_op.
unfold commutes in |- *.
intros. elim x. intros. simpl in |- *. unfold cc_eq in |- *. simpl in |- *.
split; rational.
Qed.

Lemma cc_isCRing : is_CRing cc_cabgroup cc_one cc_mult_op.
apply Build_is_CRing with cc_cr_mult_associative.
exact cc_cr_mult_mon.
exact cc_mult_commutes.
exact cc_cr_dist.
exact cc_cr_non_triv.
Qed.

Definition cc_cring : CRing := Build_CRing _ _ _ cc_isCRing.

Lemma cc_ap_zero : forall z : cc_cring, z [#] Zero -> Re z [#] Zero or Im z [#] Zero.
intro z. unfold cc_ap in |- *. intuition.
Qed.

Lemma cc_inv_aid : forall x y : IR, x [#] Zero or y [#] Zero -> x[^]2[+]y[^]2 [#] Zero.
intros x y H. 
apply Greater_imp_ap.
elim H; clear H; intros.
apply plus_resp_pos_nonneg. apply pos_square. auto. apply sqr_nonneg.
apply plus_resp_nonneg_pos. apply sqr_nonneg. apply pos_square. auto.
Qed.

(**
If [x [~=] Zero] or [y [~=] Zero], then  [x [/] x[^]2 [+] y[^]2 [~=] Zero] or
[[--]y[/]x[^]2[+]y[^]2 [~=] Zero].
*)

Lemma cc_inv_aid2 : forall (x y : IR) (H : x [#] Zero or y [#] Zero),
 (x[/] _[//]cc_inv_aid _ _ H) [#] Zero or ( [--]y[/] _[//]cc_inv_aid _ _ H) [#] Zero.
intros x y H.
elim H; intro H0.
left. 
apply div_resp_ap_zero_rev. auto.
right. apply div_resp_ap_zero_rev. apply inv_resp_ap_zero. auto.
Qed.

(*
REMARK KEPT FOR SENTIMENTAL REASONS...

This definition seems clever.  Even though we *cannot* construct an
element of (NonZeros cc_cring) (a Set) by deciding which part of the
input (Re or Im) is NonZero (a Prop), we manage to construct the
actual function.
*)

Definition cc_recip : forall z : cc_cring, z [#] Zero -> cc_cring.
intros z z_.
apply
 (Build_CC_set (Re z[/] _[//]cc_inv_aid _ _ z_)
    ( [--] (Im z) [/] _[//]cc_inv_aid _ _ z_)).
Defined.

Lemma cc_cfield_proof : is_CField cc_cring cc_recip.
unfold is_CField in |- *. unfold is_inverse in |- *.
intro. elim x. intros x1 x2 Hx.
split; simpl in |- *; unfold cc_eq in |- *; simpl in |- *; split; rational.
Qed.


Lemma cc_Recip_proof : forall x y x_ y_, cc_recip x x_ [#] cc_recip y y_ -> x [#] y.
intro. elim x. intros x1 x2 y.
intro Hx. elim y. intros y1 y2 Hy.
simpl in |- *. unfold cc_ap in |- *. simpl in |- *. intros H.
elim H; clear H; intros H.
cut (x1 [#] y1 or x1[^]2[+]x2[^]2 [#] y1[^]2[+]y2[^]2). intro H0.
elim H0; clear H0; intros H0.
left. auto.
cut (x1[^]2 [#] y1[^]2 or x2[^]2 [#] y2[^]2). intro H1.
elim H1; clear H1; intros.
left. apply un_op_strext_unfolded with (nexp_op (R:=IR) 2). auto.
right. apply un_op_strext_unfolded with (nexp_op (R:=IR) 2). auto.
apply bin_op_strext_unfolded with (csg_op (c:=IR)). auto.
apply div_strext with (cc_inv_aid x1 x2 Hx) (cc_inv_aid y1 y2 Hy). auto.
cut ( [--]x2 [#] [--]y2 or x1[^]2[+]x2[^]2 [#] y1[^]2[+]y2[^]2). intro H0.
elim H0; clear H0; intros H0.
right. apply un_op_strext_unfolded with (cg_inv (c:=IR)). auto.
cut (x1[^]2 [#] y1[^]2 or x2[^]2 [#] y2[^]2). intro H1.
elim H1; clear H1; intros H1.
left. apply un_op_strext_unfolded with (nexp_op (R:=IR) 2). auto.
right. apply un_op_strext_unfolded with (nexp_op (R:=IR) 2). auto.
apply bin_op_strext_unfolded with (csg_op (c:=IR)). auto.
apply div_strext with (cc_inv_aid x1 x2 Hx) (cc_inv_aid y1 y2 Hy). auto.
Qed.

Opaque cc_recip.
Opaque cc_inv.

Definition cc_cfield := Build_CField _ _ cc_cfield_proof cc_Recip_proof.

Definition CC := cc_cfield.

(**
Maps from reals to complex and vice-versa are defined, as well as conjugate,
absolute value and the imaginary unit [I] *)

Definition cc_set_CC : IR -> IR -> CC := Build_CC_set.

Definition cc_IR (x : IR) : CC := cc_set_CC x Zero.

Definition CC_conj : CC -> CC := fun z : CC_set =>
  match z with
  | Build_CC_set Re0 Im0 => Build_CC_set Re0 [--]Im0
  end.

(* old def
Definition CC_conj' : CC->CC := [z:CC_set] (CC_set_rec [_:CC_set]CC_set [Re0,Im0:IR] (Build_CC_set Re0 [--]Im0) z).
*)

Definition AbsCC (z : CC) : IR := sqrt (Re z[^]2[+]Im z[^]2) (cc_abs_aid _ (Re z) (Im z)).

Lemma TwoCC_ap_zero : (Two:CC) [#] Zero.
simpl in |- *. unfold cc_ap in |- *.
simpl in |- *. left.
astepl (Two:IR).
apply Greater_imp_ap. apply pos_two.
Qed.

End Complex_Numbers.

(* begin hide *)
Notation CCX := (cpoly_cring CC).
(* end hide *)

Definition II : CC := cc_i.

Infix "[+I*]" := cc_set_CC (at level 48, no associativity).

(** ** Properties of [II] *)

Section I_properties.

Lemma I_square : II[*]II [=] [--]One.
simpl in |- *. unfold cc_mult in |- *. simpl in |- *. unfold cc_inv in |- *. simpl in |- *.
split. simpl in |- *. rational. simpl in |- *. rational.
Qed.

Hint Resolve I_square: algebra.

Lemma I_square' : II[^]2 [=] [--]One.
Step_final (II[*]II).
Qed.

Lemma I_recip_lft : [--]II[*]II [=] One.
astepl ( [--] (II[*]II)).
Step_final ( [--][--] (One:CC)).
Qed.

Lemma I_recip_rht : II[*][--]II [=] One.
astepl ( [--] (II[*]II)).
Step_final ( [--][--] (One:CC)).
Qed.

Lemma mult_I : forall x y : IR, (x[+I*]y) [*]II [=] [--]y[+I*]x.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; rational.
Qed.

Lemma I_wd : forall x x' y y' : IR, x [=] x' -> y [=] y' -> x[+I*]y [=] x'[+I*]y'.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. Algebra.
Qed.

(** ** Properties of [Re] and [Im] *)

Lemma calculate_norm : forall x y : IR, (x[+I*]y) [*]CC_conj (x[+I*]y) [=] cc_IR (x[^]2[+]y[^]2).
intros. simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; rational.
Qed.

Lemma calculate_Re : forall c : CC, cc_IR (Re c) [*]Two [=] c[+]CC_conj c.
intros. elim c. intros x y. intros.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; rational.
Qed.

Lemma calculate_Im : forall c : CC, cc_IR (Im c) [*] (Two[*]II) [=] c[-]CC_conj c.
intros. elim c. intros x y. intros.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; rational.
Qed.

Lemma Re_wd : forall c c' : CC, c [=] c' -> Re c [=] Re c'.
intros c c'. elim c. intros x y. elim c'. intros x' y'.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. intros. elim H. auto.
Qed.

Lemma Im_wd : forall c c' : CC, c [=] c' -> Im c [=] Im c'.
intros c c'. elim c. intros x y. elim c'. intros x' y'.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. intros. elim H. auto.
Qed.

Lemma Re_resp_plus : forall x y : CC, Re (x[+]y) [=] Re x[+]Re y.
intros. elim x. intros x1 x2. elim y. intros y1 y2.
simpl in |- *. unfold cc_eq in |- *. Algebra.
Qed.

Lemma Re_resp_inv : forall x y : CC, Re (x[-]y) [=] Re x[-]Re y.
intros. elim x. intros x1 x2. elim y. intros y1 y2.
simpl in |- *. unfold cc_eq in |- *. Algebra.
Qed.

Lemma Im_resp_plus : forall x y : CC, Im (x[+]y) [=] Im x[+]Im y.
intros. elim x. intros x1 x2. elim y. intros y1 y2.
simpl in |- *. unfold cc_eq in |- *. Algebra.
Qed.

Lemma Im_resp_inv : forall x y : CC, Im (x[-]y) [=] Im x[-]Im y.
intros. elim x. intros x1 x2. elim y. intros y1 y2.
simpl in |- *. unfold cc_eq in |- *. Algebra.
Qed.

Lemma cc_calculate_square : forall x y, (x[+I*]y) [^]2 [=] (x[^]2[-]y[^]2) [+I*]x[*]y[*]Two.
intros. simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; rational.
Qed.

End I_properties.

Hint Resolve I_square I_square' I_recip_lft I_recip_rht mult_I calculate_norm
  cc_calculate_square: algebra.
Hint Resolve I_wd Re_wd Im_wd: algebra_c.

(** ** Properties of conjugation *)

Section Conj_properties.

Lemma CC_conj_plus : forall c c' : CC, CC_conj (c[+]c') [=] CC_conj c[+]CC_conj c'.
intros c c'. elim c. intros x y. elim c'. intros x' y'.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; Algebra.
Qed.

Lemma CC_conj_mult : forall c c' : CC, CC_conj (c[*]c') [=] CC_conj c[*]CC_conj c'.
intros c c'. elim c. intros x y. elim c'. intros x' y'.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; rational.
Qed.

Hint Resolve CC_conj_mult: algebra.

Lemma CC_conj_strext : forall c c' : CC, CC_conj c [#] CC_conj c' -> c [#] c'.
intros c c'. elim c. intros x y. elim c'. intros x' y'.
simpl in |- *. unfold cc_ap in |- *. simpl in |- *. intros H.
elim H; clear H; intros.
left. auto.
right. apply un_op_strext_unfolded with (cg_inv (c:=IR)). auto.
Qed.

Lemma CC_conj_conj : forall c : CC, CC_conj (CC_conj c) [=] c.
intros. elim c. intros x y. simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; Algebra.
Qed.

Lemma CC_conj_zero : CC_conj Zero [=] Zero.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; Algebra.
Qed.

Lemma CC_conj_one : CC_conj One [=] One.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; Algebra.
Qed.

Hint Resolve CC_conj_one: algebra.

Lemma CC_conj_nexp : forall (c : CC) n, CC_conj (c[^]n) [=] CC_conj c[^]n.
intros. induction  n as [| n Hrecn]; intros.
astepl (CC_conj One).
Step_final (One:CC).
astepl (CC_conj (c[^]n[*]c)).
astepl (CC_conj (c[^]n) [*]CC_conj c).
Step_final (CC_conj c[^]n[*]CC_conj c).
Qed.

End Conj_properties.

Hint Resolve CC_conj_plus CC_conj_mult CC_conj_nexp CC_conj_conj
  CC_conj_zero: algebra.

(** ** Properties of the real axis *)

Section cc_IR_properties.

Lemma Re_cc_IR : forall x : IR, Re (cc_IR x) [=] x.
intro x. simpl in |- *. apply eq_reflexive.
Qed.

Lemma Im_cc_IR : forall x : IR, Im (cc_IR x) [=] Zero.
intro x. simpl in |- *. apply eq_reflexive.
Qed.

Lemma cc_IR_wd : forall x y : IR, x [=] y -> cc_IR x [=] cc_IR y.
intros. simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; Algebra.
Qed.

Hint Resolve cc_IR_wd: algebra_c.

Lemma cc_IR_resp_ap : forall x y : IR, x [#] y -> cc_IR x [#] cc_IR y.
intros. simpl in |- *. unfold cc_ap in |- *. simpl in |- *. left. auto.
Qed.

Lemma cc_IR_mult : forall x y : IR, cc_IR x[*]cc_IR y [=] cc_IR (x[*]y).
intros. simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; rational.
Qed.

Hint Resolve cc_IR_mult: algebra.

Lemma cc_IR_mult_lft : forall x y z, (x[+I*]y) [*]cc_IR z [=] x[*]z[+I*]y[*]z.
intros. simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; rational.
Qed.

Lemma cc_IR_mult_rht : forall x y z, cc_IR z[*] (x[+I*]y) [=] z[*]x[+I*]z[*]y.
intros. simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; rational.
Qed.

Lemma cc_IR_plus : forall x y : IR, cc_IR x[+]cc_IR y [=] cc_IR (x[+]y).
intros. simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; Algebra.
Qed.

Hint Resolve cc_IR_plus: algebra.

Lemma cc_IR_minus : forall x y : IR, cc_IR x[-]cc_IR y [=] cc_IR (x[-]y).
intros. simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; Algebra.
Qed.

Lemma cc_IR_zero : cc_IR Zero [=] Zero.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; Algebra.
Qed.

Hint Resolve cc_IR_zero: algebra.

Lemma cc_IR_one : cc_IR One [=] One.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; Algebra.
Qed.

Hint Resolve cc_IR_one: algebra.

Lemma cc_IR_nring : forall n : nat, cc_IR (nring n) [=] nring n.
intros. induction  n as [| n Hrecn]; intros.
astepl (cc_IR Zero).
Step_final (Zero:CC).
astepl (cc_IR (nring n[+]One)).
astepl (cc_IR (nring n) [+]cc_IR One).
Step_final (nring n[+] (One:CC)).
Qed.

Lemma cc_IR_nexp : forall (x : IR) (n : nat), cc_IR x[^]n [=] cc_IR (x[^]n).
intros. induction  n as [| n Hrecn]; intros.
astepl (One:CC).
Step_final (cc_IR One).
astepl (cc_IR x[^]n[*]cc_IR x).
astepl (cc_IR (x[^]n) [*]cc_IR x).
Step_final (cc_IR (x[^]n[*]x)).
Qed.

End cc_IR_properties.

Hint Resolve Re_cc_IR Im_cc_IR: algebra.
Hint Resolve cc_IR_wd: algebra_c.
Hint Resolve cc_IR_mult cc_IR_nexp cc_IR_mult_lft cc_IR_mult_rht cc_IR_plus
  cc_IR_minus: algebra.
Hint Resolve cc_IR_nring cc_IR_zero: algebra.

(** ** [CC] has characteristic zero *)

Load "Transparent_algebra".
Lemma char0_CC : Char0 CC.
unfold Char0 in |- *.
intros.
astepl (cc_IR (nring n)).
simpl in |- *.
unfold cc_ap in |- *.
simpl in |- *.
left.
apply char0_IR.
auto.
Qed.
Load "Opaque_algebra".

Lemma poly_apzero_CC : forall f : CCX, f [#] Zero -> {c : CC | f ! c [#] Zero}.
intros.
apply poly_apzero.
exact char0_CC.
auto.
Qed.

Lemma poly_CC_extensional : forall p q : CCX, (forall x, p ! x [=] q ! x) -> p [=] q.
intros.
apply poly_extensional.
exact char0_CC.
auto.
Qed.
