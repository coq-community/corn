(* $Id$ *)

(** printing Re %\ensuremath{\Re}% #&real;# *)
(** printing Im %\ensuremath{\Im}% #&image;# *)
(** printing CC %\ensuremath{\mathbb C}% *)
(** printing II %\ensuremath{\imath}% #i# *)
(** printing [+I*] %\ensuremath{+\imath}% *)
(** printing AbsCC %\ensuremath{|\cdot|_{\mathbb C}}% *)

Require Export NRootIR.

Opaque IR.

(**
* Complex Numbers
** Algebraic structure
*)

Section Complex_Numbers.
Record CC_set : Type :=  {Re : IR; Im : IR}.

Definition cc_ap (x y : CC_set) : CProp := Re x[#]Re y or Im x[#]Im y.
Definition cc_eq (x y : CC_set) : Prop := Re x[=]Re y /\ Im x[=]Im y.

Lemma cc_is_CSetoid : is_CSetoid _ cc_eq cc_ap.
apply Build_is_CSetoid.
unfold irreflexive in |- *.
intros. elim x. intros x1 x2. unfold cc_ap in |- *. simpl in |- *.
intro H. elim H; clear H; intros H.
cut (Not (x1[#]x1)). intros H0. elim (H0 H). apply ap_irreflexive_unfolded.
cut (Not (x2[#]x2)). intros H0. elim (H0 H). apply ap_irreflexive_unfolded.
unfold Csymmetric in |- *.
intros x y. elim x. intros x1 x2. elim y. intros y1 y2. unfold cc_ap in |- *.
simpl in |- *. intros H. elim H; clear H; intros H.
left. apply ap_symmetric_unfolded. auto.
right. apply ap_symmetric_unfolded. auto.
unfold cotransitive in |- *.
intros x y. elim x. intros x1 x2. elim y. intros y1 y2. unfold cc_ap in |- *.
simpl in |- *. intro H. intro. elim z. intros z1 z2. simpl in |- *. intros.
elim H; clear H; intros H.
cut (x1[#]z1 or z1[#]y1). intro H0.
elim H0; clear H0; intros H0. left. left. auto. right. left. auto.
apply ap_cotransitive_unfolded. auto.
cut (x2[#]z2 or z2[#]y2). intro H0.
elim H0; clear H0; intros H0. left. right. auto. right. right. auto.
apply ap_cotransitive_unfolded. auto.
unfold tight_apart in |- *.
intros x y. elim x. intros x1 x2. elim y. intros y1 y2.
unfold cc_ap in |- *. unfold cc_eq in |- *. simpl in |- *. split.
intros. split.
apply not_ap_imp_eq. intro. apply H. left. auto.
apply not_ap_imp_eq. intro. apply H. right. auto.
intros. elim H. clear H. intros H H0. intro H1. elim H1; clear H1; intros H1.
cut (Not (x1[#]y1)). intro. elim (H2 H1). apply eq_imp_not_ap. auto.
cut (Not (x2[#]y2)). intro. elim (H2 H1). apply eq_imp_not_ap. auto.
Qed.

Definition cc_csetoid := Build_CSetoid CC_set cc_eq cc_ap cc_is_CSetoid.

Definition cc_plus (x y : CC_set) : CC_set :=
  Build_CC_set (Re x[+]Re y) (Im x[+]Im y).

Definition cc_mult (x y : CC_set) : CC_set :=
  Build_CC_set (Re x[*]Re y[-]Im x[*]Im y) (Re x[*]Im y[+]Im x[*]Re y).

Definition cc_zero := Build_CC_set ZeroR ZeroR.
Definition cc_one := Build_CC_set OneR ZeroR.
Definition cc_i := Build_CC_set ZeroR OneR.
Definition cc_inv (x : CC_set) : CC_set := Build_CC_set [--](Re x) [--](Im x).

(* not needed anymore
Lemma cc_plus_op_proof : (bin_op_well_def cc_csetoid cc_plus).
Unfold bin_op_well_def. Unfold bin_fun_well_def.
Intros x1 x2 y1 y2. Elim x1. Elim x2. Elim y1. Elim y2.
Simpl. Unfold cc_eq. Simpl. Intros.
Elim H. Clear H. Intros. Elim H0. Clear H0. Intros.
Split; Algebra.
Qed.

Lemma cc_mult_op_proof : (bin_op_well_def cc_csetoid cc_mult).
Unfold bin_op_well_def. Unfold bin_fun_well_def.
Intros x1 x2 y1 y2. Elim x1. Elim x2. Elim y1. Elim y2.
Simpl. Unfold cc_eq. Simpl. Intros.
Elim H. Clear H. Intros. Elim H0. Clear H0. Intros.
Split; Algebra.
Qed.

Lemma cc_inv_op_proof : (un_op_well_def cc_csetoid cc_inv).
Unfold un_op_well_def. Unfold fun_well_def.
Intros x y. Elim x. Elim y.
Simpl. Unfold cc_eq. Simpl. Intros.
Elim H. Clear H. Intros.
Split; Algebra.
Qed.
*)

Lemma cc_inv_strext : un_op_strong_ext cc_csetoid cc_inv.
unfold un_op_strong_ext in |- *. unfold fun_strong_ext in |- *.
intros x y. elim x. elim y.
simpl in |- *. unfold cc_ap in |- *. simpl in |- *. do 4 intro. intro H.
elim H; clear H; intros.
left. apply un_op_strext_unfolded with (cg_inv (c:=IR)). auto.
right. apply un_op_strext_unfolded with (cg_inv (c:=IR)). auto.
Qed.

Lemma cc_plus_strext : bin_op_strong_ext cc_csetoid cc_plus.
unfold bin_op_strong_ext in |- *. unfold bin_fun_strong_ext in |- *.
intros x1 x2 y1 y2. elim x1. elim x2. elim y1. elim y2.
simpl in |- *. unfold cc_ap in |- *. simpl in |- *. do 8 intro. intro H.
elim H; clear H; intros H.
elim (bin_op_strext_unfolded _ _ _ _ _ _ H); intros.
left. left. auto. right. left. auto.
elim (bin_op_strext_unfolded _ _ _ _ _ _ H); intros.
left. right. auto. right. right. auto.
Qed.

Lemma cc_mult_strext : bin_op_strong_ext cc_csetoid cc_mult.
unfold bin_op_strong_ext in |- *. unfold bin_fun_strong_ext in |- *.
intros x1 x2 y1 y2. elim x1. elim x2. elim y1. elim y2.
simpl in |- *. unfold cc_ap in |- *. simpl in |- *. do 8 intro. intro H.
elim H; clear H; intros H.
elim (bin_op_strext_unfolded _ (cg_minus_is_csetoid_bin_op _) _ _ _ _ H);
 intros H0.
elim (bin_op_strext_unfolded _ _ _ _ _ _ H0); intros H1.
left. left. auto. right. left. auto.
cut (Im3[*]Im1[#]Im2[*]Im0). intro H1.
elim (bin_op_strext_unfolded _ _ _ _ _ _ H1); intros H2.
left. right. auto. right. right. auto.
auto.
elim (bin_op_strext_unfolded _ _ _ _ _ _ H); intros H0.
elim (bin_op_strext_unfolded _ _ _ _ _ _ H0); intros H1.
left. left. auto. right. right. auto.
elim (bin_op_strext_unfolded _ _ _ _ _ _ H0); intros.
left. right. auto. right. left. auto.
Qed.

Definition cc_inv_op := Build_CSetoid_un_op cc_csetoid cc_inv cc_inv_strext.
Definition cc_plus_op :=
  Build_CSetoid_bin_op cc_csetoid cc_plus cc_plus_strext.
Definition cc_mult_op :=
  Build_CSetoid_bin_op cc_csetoid cc_mult cc_mult_strext.

Lemma cc_csg_associative : associative cc_plus_op.
unfold associative in |- *. intros. elim x. elim y. elim z. intros.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; Algebra.
Qed.

Lemma cc_cr_mult_associative : associative cc_mult_op.
unfold associative in |- *. intros. elim x. elim y. elim z. intros.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; rational.
Qed.

Definition cc_csemi_grp :=
  Build_CSemiGroup cc_csetoid cc_plus_op cc_csg_associative.

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

Lemma cc_cr_mult_mon :
 is_CMonoid
   (Build_CSemiGroup (csg_crr cc_cgroup) cc_mult_op cc_cr_mult_associative)
   cc_one.
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

Definition cc_cring : CRing :=
  Build_CRing cc_cabgroup cc_one cc_mult_op cc_isCRing.

Lemma cc_ap_zero :
 forall z : cc_cring, z[#]Zero -> Re z[#]Zero or Im z[#]Zero.
intro z. unfold cc_ap in |- *. intuition.
Qed.

Lemma cc_inv_aid :
 forall x y : IR, x[#]Zero or y[#]Zero -> x[^]2[+]y[^]2[#]Zero.
intros x y H. 
apply Greater_imp_ap.
elim H; clear H; intros.
apply plus_resp_pos_nonneg. apply pos_square. auto. apply sqr_nonneg.
apply plus_resp_nonneg_pos. apply sqr_nonneg. apply pos_square. auto.
Qed.

(**
If $x\noto 0$#x <> 0# or $y\noto 0$#y <> 0#, then  $\frac{x}{x^2 + y^2} \noto 0$#x/(x^2 + y^2) <> 0# or
$\frac{-y}{x^2 + y^2} \noto 0$#(-y)/(x^2 + y^2) <> 0#.
*)

Lemma cc_inv_aid2 :
 forall (x y : IR) (h : x[#]Zero or y[#]Zero),
 (x[/] _[//]cc_inv_aid _ _ h)[#]Zero
 or ([--]y[/] _[//]cc_inv_aid _ _ h)[#]Zero.
intros x y H.
elim H; intro H0.
left. 
apply div_resp_ap_zero_rev. auto.
right. apply div_resp_ap_zero_rev. apply inv_resp_ap_zero. auto.
Qed.

(*
This definition seems clever.  Even though we *cannot* construct an
element of (NonZeros cc_cring) (a Set) by deciding which part of the
input (re or im) is NonZero (a Prop), we manage to construct the
actual function.
*)

Definition cc_recip : forall z : cc_cring, z[#]Zero -> cc_cring.
intros z z_.
apply
 (Build_CC_set (Re z[/] _[//]cc_inv_aid _ _ z_)
    ([--](Im z)[/] _[//]cc_inv_aid _ _ z_)).
Defined.

Lemma cc_cfield_proof : is_CField cc_cring cc_recip.
unfold is_CField in |- *. unfold is_inverse in |- *.
intro. elim x. intros x1 x2 Hx.
split; simpl in |- *; unfold cc_eq in |- *; simpl in |- *; split; rational.
Qed.


Lemma cc_Recip_proof :
 forall x y x_ y_, cc_recip x x_[#]cc_recip y y_ -> x[#]y.
intro. elim x. intros x1 x2 y.
intro Hx. elim y. intros y1 y2 Hy.
simpl in |- *. unfold cc_ap in |- *. simpl in |- *. intros H.
elim H; clear H; intros H.
cut (x1[#]y1 or x1[^]2[+]x2[^]2[#]y1[^]2[+]y2[^]2). intro H0.
elim H0; clear H0; intros H0.
left. auto.
cut (x1[^]2[#]y1[^]2 or x2[^]2[#]y2[^]2). intro H1.
elim H1; clear H1; intros.
left. apply un_op_strext_unfolded with (nexp_op (R:=IR) 2). auto.
right. apply un_op_strext_unfolded with (nexp_op (R:=IR) 2). auto.
apply bin_op_strext_unfolded with (csg_op (c:=IR)). auto.
apply div_strong_ext with (cc_inv_aid x1 x2 Hx) (cc_inv_aid y1 y2 Hy). auto.
cut ([--]x2[#][--]y2 or x1[^]2[+]x2[^]2[#]y1[^]2[+]y2[^]2). intro H0.
elim H0; clear H0; intros H0.
right. apply un_op_strext_unfolded with (cg_inv (c:=IR)). auto.
cut (x1[^]2[#]y1[^]2 or x2[^]2[#]y2[^]2). intro H1.
elim H1; clear H1; intros H1.
left. apply un_op_strext_unfolded with (nexp_op (R:=IR) 2). auto.
right. apply un_op_strext_unfolded with (nexp_op (R:=IR) 2). auto.
apply bin_op_strext_unfolded with (csg_op (c:=IR)). auto.
apply div_strong_ext with (cc_inv_aid x1 x2 Hx) (cc_inv_aid y1 y2 Hy). auto.
Qed.


Opaque cc_recip.
Opaque cc_inv.


Definition cc_cfield :=
  Build_CField cc_cring cc_recip cc_cfield_proof cc_Recip_proof.
Definition CC := cc_cfield.

(**
Maps from reals to complex and vice-versa are defined, as well as conjugate,
absolute value and the imaginary unit [I] *)

Definition cc_set_CC : IR -> IR -> CC := Build_CC_set.
Definition cc_IR (x : IR) : CC := cc_set_CC x Zero.

Definition CC_conj : CC -> CC :=
  fun z : CC_set =>
  match z with
  | Build_CC_set Re0 Im0 => Build_CC_set Re0 [--]Im0
  end.

(* old def
Definition CC_conj' : CC->CC := [z:CC_set](CC_set_rec [_:CC_set]CC_set [Re0,Im0:IR](Build_CC_set Re0 [--]Im0) z).
*)

Definition AbsCC (z : CC) : IR :=
  sqrt (Re z[^]2[+]Im z[^]2) (cc_abs_aid _ (Re z) (Im z)).

Lemma TwoCC_ap_zero : (Two:CC)[#]Zero.
simpl in |- *. unfold cc_ap in |- *.
simpl in |- *. left.
AStepl (Two:IR).
apply Greater_imp_ap. apply pos_two.
Qed.

End Complex_Numbers.

Definition II : CC := cc_i.

Infix "[+I*]" := cc_set_CC (at level 48, no associativity).

(** ** Properties of [II] *)

Section I_properties.

Lemma I_square : II[*]II[=][--]One.
simpl in |- *. unfold cc_mult in |- *. simpl in |- *. unfold cc_inv in |- *. simpl in |- *.
split. simpl in |- *. rational. simpl in |- *. rational.
Qed.

Hint Resolve I_square: algebra.

Lemma I_square' : II[^]2[=][--]One.
Step_final (II[*]II).
Qed.

Lemma I_recip_lft : [--]II[*]II[=]One.
AStepl ([--](II[*]II)).
Step_final ([--][--](One:CC)).
Qed.

Lemma I_recip_rht : II[*][--]II[=]One.
AStepl ([--](II[*]II)).
Step_final ([--][--](One:CC)).
Qed.

Lemma mult_I : forall x y : IR, (x[+I*]y)[*]II[=][--]y[+I*]x.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; rational.
Qed.

Lemma I_wd : forall x x' y y' : IR, x[=]x' -> y[=]y' -> x[+I*]y[=]x'[+I*]y'.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. Algebra.
Qed.

(** ** Properties of [Re] and [Im] *)

Lemma calculate_norm :
 forall x y : IR, (x[+I*]y)[*]CC_conj (x[+I*]y)[=]cc_IR (x[^]2[+]y[^]2).
intros. simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; rational.
Qed.

Lemma calculate_Re : forall c : CC, cc_IR (Re c)[*]Two[=]c[+]CC_conj c.
intros. elim c. intros x y. intros.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; rational.
Qed.

Lemma calculate_Im : forall c : CC, cc_IR (Im c)[*](Two[*]II)[=]c[-]CC_conj c.
intros. elim c. intros x y. intros.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; rational.
Qed.

Lemma Re_wd : forall c c' : CC, c[=]c' -> Re c[=]Re c'.
intros c c'. elim c. intros x y. elim c'. intros x' y'.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. intros. elim H. auto.
Qed.

Lemma Im_wd : forall c c' : CC, c[=]c' -> Im c[=]Im c'.
intros c c'. elim c. intros x y. elim c'. intros x' y'.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. intros. elim H. auto.
Qed.

Lemma Re_resp_plus : forall x y : CC, Re (x[+]y)[=]Re x[+]Re y.
intros. elim x. intros x1 x2. elim y. intros y1 y2.
simpl in |- *. unfold cc_eq in |- *. Algebra.
Qed.

Lemma Re_resp_inv : forall x y : CC, Re (x[-]y)[=]Re x[-]Re y.
intros. elim x. intros x1 x2. elim y. intros y1 y2.
simpl in |- *. unfold cc_eq in |- *. Algebra.
Qed.

Lemma Im_resp_plus : forall x y : CC, Im (x[+]y)[=]Im x[+]Im y.
intros. elim x. intros x1 x2. elim y. intros y1 y2.
simpl in |- *. unfold cc_eq in |- *. Algebra.
Qed.

Lemma Im_resp_inv : forall x y : CC, Im (x[-]y)[=]Im x[-]Im y.
intros. elim x. intros x1 x2. elim y. intros y1 y2.
simpl in |- *. unfold cc_eq in |- *. Algebra.
Qed.

Lemma cc_calculate_square :
 forall x y : IR, (x[+I*]y)[^]2[=](x[^]2[-]y[^]2)[+I*]x[*]y[*]Two.
intros. simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; rational.
Qed.

End I_properties.

Hint Resolve I_square I_square' I_recip_lft I_recip_rht mult_I calculate_norm
  cc_calculate_square: algebra.
Hint Resolve I_wd Re_wd Im_wd: algebra_c.

(** ** Properties of conjugation *)

Section Conj_properties.

Lemma CC_conj_plus :
 forall c c' : CC, CC_conj (c[+]c')[=]CC_conj c[+]CC_conj c'.
intros c c'. elim c. intros x y. elim c'. intros x' y'.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; Algebra.
Qed.

Lemma CC_conj_mult :
 forall c c' : CC, CC_conj (c[*]c')[=]CC_conj c[*]CC_conj c'.
intros c c'. elim c. intros x y. elim c'. intros x' y'.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; rational.
Qed.

Hint Resolve CC_conj_mult: algebra.

Lemma CC_conj_strext : forall c c' : CC, CC_conj c[#]CC_conj c' -> c[#]c'.
intros c c'. elim c. intros x y. elim c'. intros x' y'.
simpl in |- *. unfold cc_ap in |- *. simpl in |- *. intros H.
elim H; clear H; intros.
left. auto.
right. apply un_op_strext_unfolded with (cg_inv (c:=IR)). auto.
Qed.

Lemma CC_conj_conj : forall c : CC, CC_conj (CC_conj c)[=]c.
intros. elim c. intros x y. simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; Algebra.
Qed.

Lemma CC_conj_zero : CC_conj Zero[=]Zero.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; Algebra.
Qed.

Lemma CC_conj_one : CC_conj One[=]One.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; Algebra.
Qed.

Hint Resolve CC_conj_one: algebra.

Lemma CC_conj_nexp :
 forall (c : CC) (n : nat), CC_conj (c[^]n)[=]CC_conj c[^]n.
intros. induction  n as [| n Hrecn]; intros.
AStepl (CC_conj One).
Step_final (One:CC).
AStepl (CC_conj (c[^]n[*]c)).
AStepl (CC_conj (c[^]n)[*]CC_conj c).
Step_final (CC_conj c[^]n[*]CC_conj c).
Qed.

End Conj_properties.

Hint Resolve CC_conj_plus CC_conj_mult CC_conj_nexp CC_conj_conj
  CC_conj_zero: algebra.

(** ** Properties of the real axis *)

Section cc_IR_properties.

Lemma Re_cc_IR : forall x : IR, Re (cc_IR x)[=]x.
intro x. simpl in |- *. apply eq_reflexive.
Qed.

Lemma Im_cc_IR : forall x : IR, Im (cc_IR x)[=]Zero.
intro x. simpl in |- *. apply eq_reflexive.
Qed.

Lemma cc_IR_wd : forall x y : IR, x[=]y -> cc_IR x[=]cc_IR y.
intros. simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; Algebra.
Qed.

Hint Resolve cc_IR_wd: algebra_c.

Lemma cc_IR_resp_ap : forall x y : IR, x[#]y -> cc_IR x[#]cc_IR y.
intros. simpl in |- *. unfold cc_ap in |- *. simpl in |- *. left. auto.
Qed.

Lemma cc_IR_mult : forall x y : IR, cc_IR x[*]cc_IR y[=]cc_IR (x[*]y).
intros. simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; rational.
Qed.

Hint Resolve cc_IR_mult: algebra.

Lemma cc_IR_mult_lft :
 forall x y z : IR, (x[+I*]y)[*]cc_IR z[=]x[*]z[+I*]y[*]z.
intros. simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; rational.
Qed.

Lemma cc_IR_mult_rht :
 forall x y z : IR, cc_IR z[*](x[+I*]y)[=]z[*]x[+I*]z[*]y.
intros. simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; rational.
Qed.

Lemma cc_IR_plus : forall x y : IR, cc_IR x[+]cc_IR y[=]cc_IR (x[+]y).
intros. simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; Algebra.
Qed.

Hint Resolve cc_IR_plus: algebra.

Lemma cc_IR_minus : forall x y : IR, cc_IR x[-]cc_IR y[=]cc_IR (x[-]y).
intros. simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; Algebra.
Qed.

Lemma cc_IR_zero : cc_IR Zero[=]Zero.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; Algebra.
Qed.

Hint Resolve cc_IR_zero: algebra.

Lemma cc_IR_one : cc_IR One[=]One.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *. split; Algebra.
Qed.

Hint Resolve cc_IR_one: algebra.

Lemma cc_IR_nring : forall n : nat, cc_IR (nring n)[=]nring n.
intros. induction  n as [| n Hrecn]; intros.
AStepl (cc_IR Zero).
Step_final (Zero:CC).
AStepl (cc_IR (nring n[+]One)).
AStepl (cc_IR (nring n)[+]cc_IR One).
Step_final (nring n[+](One:CC)).
Qed.

Lemma cc_IR_nexp : forall (x : IR) (n : nat), cc_IR x[^]n[=]cc_IR (x[^]n).
intros. induction  n as [| n Hrecn]; intros.
AStepl (One:CC).
Step_final (cc_IR One).
AStepl (cc_IR x[^]n[*]cc_IR x).
AStepl (cc_IR (x[^]n)[*]cc_IR x).
Step_final (cc_IR (x[^]n[*]x)).
Qed.

End cc_IR_properties.

Hint Resolve Re_cc_IR Im_cc_IR: algebra.
Hint Resolve cc_IR_wd: algebra_c.
Hint Resolve cc_IR_mult cc_IR_nexp cc_IR_mult_lft cc_IR_mult_rht cc_IR_plus
  cc_IR_minus: algebra.
Hint Resolve cc_IR_nring cc_IR_zero: algebra.

(** ** Properties of absolute value *)

Section AbsCC_properties.

Lemma AbsCC_nonneg : forall x : CC, Zero[<=]AbsCC x.
unfold AbsCC in |- *. intros.
apply sqrt_nonneg.
Qed.

Lemma AbsCC_ap_zero_imp_pos : forall z : CC, AbsCC z[#]Zero -> Zero[<]AbsCC z.
intros z H.
apply leEq_not_eq.
apply AbsCC_nonneg.
apply ap_symmetric_unfolded. assumption.
Qed.

Lemma AbsCC_wd : forall x y : CC, x[=]y -> AbsCC x[=]AbsCC y.
intros x y. elim x. intros x1 x2. elim y. intros y1 y2.
simpl in |- *. unfold cc_eq in |- *. unfold AbsCC in |- *. simpl in |- *. intros.
change
  (sqrt (x1[^]2[+]x2[^]2) (cc_abs_aid _ x1 x2)[=]
   sqrt (y1[^]2[+]y2[^]2) (cc_abs_aid _ y1 y2)) in |- *.
elim H. clear H. intros.
apply sqrt_wd. Algebra.
Qed.

Hint Resolve AbsCC_wd: algebra_c.

Lemma cc_inv_abs : forall x : CC, AbsCC [--]x[=]AbsCC x.
intros.
unfold AbsCC in |- *.
apply sqrt_wd.
apply bin_op_wd_unfolded.
Step_final ([--](Re x)[^]2).
Step_final ([--](Im x)[^]2).
Qed.

Hint Resolve cc_inv_abs: algebra.

Lemma cc_minus_abs : forall x y : CC, AbsCC (x[-]y)[=]AbsCC (y[-]x).
intros.
apply eq_transitive_unfolded with (AbsCC [--](y[-]x)).
apply AbsCC_wd. rational.
apply cc_inv_abs.
Qed.

Lemma cc_mult_abs : forall x y : CC, AbsCC (x[*]y)[=]AbsCC x[*]AbsCC y.
intros x y. elim x. intros x1 x2. elim y. intros y1 y2. intros.
unfold AbsCC in |- *.
apply sqrt_mult_wd.
simpl in |- *.
rational.
Qed.

Hint Resolve cc_mult_abs: algebra.

Lemma AbsCC_minzero : forall x : CC, AbsCC (x[-]Zero)[=]AbsCC x.
intros.
apply AbsCC_wd.
Algebra.
Qed.

Lemma AbsCC_IR : forall x : IR, Zero[<=]x -> AbsCC (cc_IR x)[=]x.
intros. unfold AbsCC in |- *.
change (sqrt (x[^]2[+]Zero[^]2) (cc_abs_aid _ x Zero)[=]x) in |- *.
apply eq_transitive_unfolded with (sqrt (x[^]2) (sqr_nonneg _ x)).
apply sqrt_wd. rational.
apply sqrt_to_nonneg. auto.
Qed.

Hint Resolve AbsCC_IR: algebra.

Lemma cc_div_abs :
 forall (x y : CC) (y_ : y[#]Zero) (y'_ : AbsCC y[#]Zero),
 AbsCC (x[/] y[//]y_)[=](AbsCC x[/] AbsCC y[//]y'_).
intros x y nz anz.
RStepl (AbsCC y[*]AbsCC (x[/] y[//]nz)[/] AbsCC y[//]anz).
apply div_wd. 2: Algebra.
AStepl (AbsCC (y[*](x[/] y[//]nz))).
apply AbsCC_wd. rational.
Qed.

Lemma cc_div_abs' :
 forall (x : CC) (y : IR) (y_ : y[#]Zero) (y'_ : cc_IR y[#]Zero),
 Zero[<=]y -> AbsCC (x[/] cc_IR y[//]y'_)[=](AbsCC x[/] y[//]y_).
intros x y nz cnz H.
RStepl (y[*]AbsCC (x[/] cc_IR y[//]cnz)[/] y[//]nz).
apply div_wd. 2: Algebra.
AStepl (AbsCC (cc_IR y)[*]AbsCC (x[/] cc_IR y[//]cnz)).
AStepl (AbsCC (cc_IR y[*](x[/] cc_IR y[//]cnz))).
apply AbsCC_wd.
rational.
Qed.

Lemma AbsCC_zero : AbsCC Zero[=]Zero.
AStepl (AbsCC (cc_IR Zero)).
apply AbsCC_IR.
apply leEq_reflexive.
Qed.

Hint Resolve AbsCC_zero: algebra.

Lemma AbsCC_one : AbsCC One[=]One.
AStepl (AbsCC (cc_IR One)).
apply AbsCC_IR.
apply less_leEq. apply pos_one.
Qed.

Lemma cc_pow_abs : forall (x : CC) (n : nat), AbsCC (x[^]n)[=]AbsCC x[^]n.
intros. induction  n as [| n Hrecn]; intros.
simpl in |- *. apply AbsCC_one.
simpl in |- *. Step_final (AbsCC (x[^]n)[*]AbsCC x).
Qed.

Lemma AbsCC_pos : forall x : CC, x[#]Zero -> Zero[<]AbsCC x.
intro. elim x. intros x1 x2.
unfold AbsCC in |- *. simpl in |- *. unfold cc_ap in |- *. simpl in |- *. intros H.
change (Zero[<]sqrt (x1[^]2[+]x2[^]2) (cc_abs_aid _ x1 x2)) in |- *.
apply power_cancel_less with 2. apply sqrt_nonneg.
AStepl ZeroR.
AStepr (x1[^]2[+]x2[^]2).
elim H; clear H; intros.
apply plus_resp_pos_nonneg.
apply pos_square. auto. apply sqr_nonneg.
apply plus_resp_nonneg_pos.
apply sqr_nonneg. apply pos_square. auto.
Qed.

Lemma AbsCC_ap_zero : forall x : CC, Zero[#]AbsCC x -> x[#]Zero.
intro. elim x. intros x1 x2. simpl in |- *. unfold AbsCC in |- *. unfold cc_ap in |- *.
change
  (Zero[#]sqrt (x1[^]2[+]x2[^]2) (cc_abs_aid _ x1 x2) ->
   x1[#]Zero or x2[#]Zero) in |- *.
intros H.
cut (x1[^]2[#]Zero or x2[^]2[#]Zero). intro H0.
elim H0; clear H0; intros.
left.
apply cring_mult_ap_zero with x1.
AStepl (x1[^]2). auto.
right.
apply cring_mult_ap_zero with x2.
AStepl (x2[^]2). auto.
apply cg_add_ap_zero.
AStepl (sqrt (x1[^]2[+]x2[^]2) (cc_abs_aid _ x1 x2)[^]2).
apply nexp_resp_ap_zero.
apply ap_symmetric_unfolded. auto.
Qed.

Lemma AbsCC_small_imp_eq :
 forall x : CC, (forall e : IR, Zero[<]e -> AbsCC x[<]e) -> x[=]Zero.
intros x H.
apply not_ap_imp_eq. intro.
elim (less_irreflexive_unfolded _ (AbsCC x)).
apply H.
apply AbsCC_pos. auto.
Qed.

(* begin hide *)
Let l_1_1_2 :
  forall x y : IR, (x[+I*]y)[*](x[+I*][--]y)[=]cc_IR (x[^]2[+]y[^]2).
intros. apply calculate_norm with (x := x) (y := y).
Qed.
(* end hide *)

Hint Resolve l_1_1_2: algebra.

Lemma AbsCC_square_Re_Im :
 forall x y : IR, x[^]2[+]y[^]2[=]AbsCC (x[+I*]y)[^]2.
intros. unfold AbsCC in |- *.
Step_final (Re (x[+I*]y)[^]2[+]Im (x[+I*]y)[^]2).
Qed.

Hint Resolve AbsCC_square_Re_Im: algebra.

(* begin hide *)
Let l_1_2_3_CC :
  forall x y : IR, cc_IR (x[^]2[+]y[^]2)[=]cc_IR (AbsCC (x[+I*]y)[^]2).
intros. apply cc_IR_wd. apply AbsCC_square_Re_Im.
Qed.
(* end hide *)

Hint Resolve l_1_2_3_CC: algebra.

Lemma AbsCC_mult_conj : forall z : CC, z[*]CC_conj z[=]cc_IR (AbsCC z[^]2).
intro z. unfold cc_IR in |- *.
elim z. intros x y.
apply
 eq_transitive_unfolded with (S := cc_csetoid) (y := cc_IR (x[^]2[+]y[^]2)).
eapply l_1_1_2 with (x := x) (y := y).
split; simpl in |- *.
2: Algebra.
eapply AbsCC_square_Re_Im with (x := x) (y := y).
Qed.

Hint Resolve CC_conj_mult: algebra.

(* begin hide *)
Lemma l_2_1_2 :
 forall z1 z2 : CC,
 cc_IR (AbsCC (z1[*]z2)[^]2)[=]z1[*]z2[*]CC_conj z1[*]CC_conj z2.
intros z1 z2. apply eq_symmetric_unfolded.
apply eq_transitive_unfolded with (z1[*]z2[*]CC_conj (z1[*]z2)).
Step_final (z1[*]z2[*](CC_conj z1[*]CC_conj z2)).
apply AbsCC_mult_conj.
Qed.

Hint Resolve l_2_1_2: algebra.
(* end hide *)

Lemma AbsCC_mult_square :
 forall z1 z2 : CC, AbsCC (z1[*]z2)[^]2[=]AbsCC z1[^]2[*]AbsCC z2[^]2.
intros. RStepr ((AbsCC z1[*]AbsCC z2)[^]2). Algebra.
Qed.

Lemma AbsCC_square_ap_zero : forall z : CC, z[#]Zero -> AbsCC z[^]2[#]Zero.
intros z H.
AStepl (Re z[^]2[+]Im z[^]2).
apply (cc_inv_aid (Re z) (Im z) H).
apply AbsCC_square_Re_Im with (x := Re z) (y := Im z).
Qed.

Lemma cc_recip_char :
 forall (z : CC) (z_ : z[#]Zero) (z'_ : cc_IR (AbsCC z[^]2)[#]Zero),
 cc_recip z z_[=](CC_conj z[/] _[//]z'_).
intros z z_ HAbsCCz.
unfold cc_recip in |- *.
AStepl
 (Re z[+I*][--](Im z)[/] _[//]
  cc_IR_resp_ap _ _ (cc_inv_aid _ _ (cc_ap_zero _ z_))).
2: simpl in |- *; split; simpl in |- *; rational.
apply
 div_wd
  with
    (F := CC)
    (x := Re z[+I*][--](Im z))
    (y := cc_IR (Re z[^]2[+]Im z[^]2))
    (x' := CC_conj z)
    (y' := cc_IR (AbsCC z[^]2)).
elim z. intros x y. simpl in |- *. split; simpl in |- *; Algebra.
apply cc_IR_wd.
apply AbsCC_square_Re_Im with (x := Re z) (y := Im z).
Qed.

Lemma AbsCC_strext : fun_strong_ext AbsCC.
unfold fun_strong_ext in |- *.
intros z1 z2 H.
cut (AbsCC z1[^]2[#]AbsCC z2[^]2).
elim z1. intros x1 y1. elim z2. intros x2 y2.
intro H'.
assert (H'' : x1[^]2[+]y1[^]2[#]x2[^]2[+]y2[^]2).
AStepl (AbsCC (x1[+I*]y1)[^]2). AStepr (AbsCC (x2[+I*]y2)[^]2). assumption.

cut (x1[^]2[#]x2[^]2 or y1[^]2[#]y2[^]2).
intros H'''. elim H'''; intro H0.
cut (x1[#]x2).
intro H1.
simpl in |- *. unfold cc_ap in |- *. unfold Re, Im in |- *.
left.
assumption.
apply (nexp_strong_ext IR 2).
assumption.

simpl in |- *. unfold cc_ap in |- *. simpl in |- *.
right.
apply (nexp_strong_ext IR 2).
assumption.
apply (bin_op_strext_unfolded _ _ _ _ _ _ H'').
assert (H1 : AbsCC z1[-]AbsCC z2[#]Zero).
cut (AbsCC z1[-]AbsCC z2[#]AbsCC z2[-]AbsCC z2).
intro H0. AStepr (AbsCC z2[-]AbsCC z2). assumption.
apply minus_resp_ap_rht. assumption.

assert (H2 : AbsCC z1[+]AbsCC z2[#]Zero).
apply Greater_imp_ap.
assert (H0 : AbsCC z1[#]Zero or Zero[#]AbsCC z2).
apply ap_cotransitive_unfolded. assumption.
elim H0.
intro H'.
assert (H'' : Zero[<]AbsCC z1).
apply (AbsCC_ap_zero_imp_pos _ H').
apply leEq_less_trans with (y := AbsCC z2).
apply AbsCC_nonneg.
RStepl (AbsCC z2[+]Zero).
RStepr (AbsCC z2[+]AbsCC z1).
apply plus_resp_less_lft.
assumption.

intro H'.
assert (H'' : Zero[<]AbsCC z2).
apply AbsCC_ap_zero_imp_pos.
apply ap_symmetric_unfolded. assumption.
apply leEq_less_trans with (y := AbsCC z1).
apply AbsCC_nonneg.
RStepl (AbsCC z1[+]Zero).
apply plus_resp_less_lft.
assumption.
cut (AbsCC z1[^]2[-]AbsCC z2[^]2[#]Zero).
intro H3.
cut (AbsCC z1[^]2[-]AbsCC z2[^]2[#]AbsCC z2[^]2[-]AbsCC z2[^]2).
intro H4.
RStepl (AbsCC z1[^]2[-]AbsCC z2[^]2[+]AbsCC z2[^]2).
RStepr (Zero[+]AbsCC z2[^]2).

apply
 op_rht_resp_ap
  with (x := AbsCC z1[^]2[-]AbsCC z2[^]2) (y := ZeroR) (z := AbsCC z2[^]2).
RStepr (AbsCC z2[^]2[-]AbsCC z2[^]2).
assumption.

RStepr ZeroR.
assumption.

AStepl ((AbsCC z1[-]AbsCC z2)[*](AbsCC z1[+]AbsCC z2)).
apply mult_resp_ap_zero; assumption.
Qed.

Definition AbsSmallCC (e : IR) (x : CC) := AbsCC x[<=]e.

Lemma Cexis_AFS_CC :
 forall (x y : CC) (eps : IR),
 Zero[<]eps -> {y' : CC | AbsSmallCC eps (y'[-]y) | y'[#]x}.
unfold AbsSmallCC in |- *. intros.
set (e := cc_IR eps) in *.
elim (ap_cotransitive_unfolded _ (y[-]e) (y[+]e)) with x; try intro H0.
exists (y[-]e).
apply leEq_wdl with (AbsCC [--]e).
unfold e in |- *.
AStepl (AbsCC (cc_IR eps)).
apply eq_imp_leEq.
apply AbsCC_IR.
apply less_leEq; auto.
apply AbsCC_wd. rational.
auto.
exists (y[+]e).
apply leEq_wdl with (AbsCC e).
apply eq_imp_leEq.
unfold e in |- *; apply AbsCC_IR.
apply less_leEq; auto.
apply AbsCC_wd. rational.
apply ap_symmetric_unfolded. auto.
apply zero_minus_apart.
apply ap_well_def_lft_unfolded with (cc_IR ([--]Two[*]eps)).
AStepr (cc_IR Zero).
apply cc_IR_resp_ap. apply mult_resp_ap_zero.
apply inv_resp_ap_zero. apply two_ap_zero.
apply pos_ap_zero; auto.
unfold e in |- *.
AStepl (cc_IR [--]Two[*]cc_IR eps).
RStepr ([--]Two[*]cc_IR eps).
apply mult_wd_lft.
simpl in |- *. unfold cc_eq in |- *. simpl in |- *.
split; [ Algebra | rational ].
Qed.

(* The following lemmas are just auxiliary results *)

(* begin hide *)
Let l_4_1_2 :
  forall (z : CC) (H : z[#]Zero),
  z[*]cc_recip z H[=]
  (z[*]CC_conj z[/] _[//]cc_IR_resp_ap _ _ (AbsCC_square_ap_zero _ H)).
intros z H.
apply
 eq_transitive_unfolded
  with
    (S := cc_csetoid)
    (y := z[*]
          (CC_conj z[/] _[//]cc_IR_resp_ap _ _ (AbsCC_square_ap_zero _ H))).
2: Algebra.
AStepr (z[*](CC_conj z[/] _[//]cc_IR_resp_ap _ _ (AbsCC_square_ap_zero _ H))).
apply
 bin_op_wd_unfolded
  with
    (S := CC)
    (x1 := z)
    (x2 := z)
    (y1 := cc_recip z H)
    (y2 := CC_conj z[/] _[//]cc_IR_resp_ap _ _ (AbsCC_square_ap_zero _ H)).
Algebra.
apply cc_recip_char.
generalize H. clear H. elim z. intros x y H. simpl in |- *. split; simpl in |- *; rational.
Qed.

Let l_4_2_3 :
  forall (z : CC) (H : z[#]Zero),
  (z[*]CC_conj z[/] _[//]cc_IR_resp_ap _ _ (AbsCC_square_ap_zero _ H))[=]
  (cc_IR (AbsCC z[^]2)[/] _[//]cc_IR_resp_ap _ _ (AbsCC_square_ap_zero _ H)).
intros z H.
apply
 div_wd
  with
    (F := CC)
    (x := z[*]CC_conj z)
    (y := cc_IR (AbsCC z[^]2))
    (x' := cc_IR (AbsCC z[^]2))
    (y' := cc_IR (AbsCC z[^]2)).
apply AbsCC_mult_conj.
Algebra.
Qed.

Let l_4_3_4 :
  forall (z : CC) (H : z[#]Zero),
  (cc_IR (AbsCC z[^]2)[/] _[//]cc_IR_resp_ap _ _ (AbsCC_square_ap_zero _ H))[=]
  One.
intros.
rational.
Qed.
(* end hide *)

End AbsCC_properties.

(** ** [CC] has characteristic zero *)

Load "Transparent_algebra".
Lemma char0_CC : Char0 CC.
unfold Char0 in |- *.
intros.
AStepl (cc_IR (nring n)).
simpl in |- *.
unfold cc_ap in |- *.
simpl in |- *.
left.
apply char0_IR.
auto.
Qed.
Load "Opaque_algebra".

Lemma poly_apzero_CC :
 forall f : cpoly_cring CC, f[#]Zero -> {c : CC | f ! c[#]Zero}.
intros.
apply poly_apzero.
exact char0_CC.
auto.
Qed.

Lemma poly_CC_extensional :
 forall p q : cpoly_cring CC, (forall x : CC, p ! x[=]q ! x) -> p[=]q.
intros.
apply poly_extensional.
exact char0_CC.
auto.
Qed.

Hint Resolve AbsCC_wd: algebra_c.
Hint Resolve cc_inv_abs cc_mult_abs cc_div_abs cc_div_abs' cc_pow_abs
  AbsCC_zero AbsCC_one AbsCC_IR AbsCC_mult_conj AbsCC_mult_square
  cc_recip_char: algebra.