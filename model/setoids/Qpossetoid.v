(* $Id$ *)

Require Export Qsetoid.
Require Import CSetoidFun.
Require Export Qpossec.

(** *Example of a setoid: $\mathbb{Q}^{+}$ #Q<SUP>+</SUP>#
*)

(** **$\mathbb{Q}^{+}$ #Q<SUP>+</SUP>#
*)

(** We will examine the subsetoid of positive rationals of the setoid of 
rational numbers.
*)

Definition Qpos := Build_SubCSetoid Q_as_CSetoid (fun x : Q.Q => Q.ZERO{<Q}x).

(** One, two and four are elements of it.
*)

Definition QONEpos :=
  Build_subcsetoid_crr Q_as_CSetoid (fun x : Q_as_CSetoid => Q.ZERO{<Q}x)
    Q.ONE pos_QONE.

Definition QTWOpos :=
  Build_subcsetoid_crr Q_as_CSetoid (fun x : Q_as_CSetoid => Q.ZERO{<Q}x)
    QTWO pos_QTWO.

Definition QFOURpos :=
  Build_subcsetoid_crr Q_as_CSetoid (fun x : Q_as_CSetoid => Q.ZERO{<Q}x)
    QFOUR pos_QFOUR.

(** **Multiplication
*)

(** As we have seen, multiplication preserves positivity, so we can restrict it
 to the positive rationals. We see that this restricted multiplication has some
 nice properties.
*)

Lemma Qmult_pres_pos1 :
 bin_op_pres_pred Q_as_CSetoid (fun x : Q_as_CSetoid => Q.ZERO{<Q}x)
   Qmult_is_bin_fun.
unfold bin_op_pres_pred in |- *.
unfold Qmult_is_bin_fun in |- *.
simpl in |- *.
exact Qmult_pres_pos0.
Qed.

Definition Qpos_mult :=
  Build_SubCSetoid_bin_op Q_as_CSetoid (fun x : Q_as_CSetoid => Q.ZERO{<Q}x)
    Qmult_is_bin_fun Qmult_pres_pos1.

Lemma associative_Qpos_mult : associative Qpos_mult.
unfold associative in |- *.
intros x y z.
case x.
case y.
case z.
simpl in |- *.
intros.
apply Qmult_is_assoc.
Qed.

(** **Inverse
*)

(** We restrict the domain of the inverse to the set of positive rationals.
*)

Definition Qpos_inv : Qpos -> Q.Q.
intro x.
elim x.
intros y z.
set (i := Q.inv y) in *.
set (i0 := pos_imp_nonzero y z) in *.
exact (i i0).
Defined.

(** The restricted inverse preserves positivity.
*)

Lemma inv_pres_pos1 : forall x : Qpos, Q.ZERO{<Q}Qpos_inv x.
intro x.
unfold Qpos_inv in |- *.
simpl in |- *.
case x.
simpl in |- *.
apply inv_pres_pos0.
Qed.

(** Now, we can also restrict the co-domain.
*)

Definition Qpos_Qpos_inv : Qpos -> Qpos.
intro a.
simpl in |- *.
apply Build_subcsetoid_crr with (Qpos_inv a).
apply inv_pres_pos1.
Defined.

(** This restricted inverse map appears a setoid function.
*)

Lemma Qpos_Qpos_inv_strong_ext : fun_strong_ext Qpos_Qpos_inv.
unfold fun_strong_ext in |- *.
intros x y.
unfold Qpos_Qpos_inv in |- *.
simpl in |- *.
case x.
case y.
unfold Qpos_inv in |- *.
simpl in |- *.
unfold Q.ap in |- *.
intros scs_elem scs_prf scs_elem0 scs_prf0 X.
apply
 Qinv_is_extensional
  with
    (pos_imp_nonzero scs_elem0 scs_prf0)
    (pos_imp_nonzero scs_elem scs_prf).
exact X.
Qed.

Definition Qpos_Qpos_inv_op :=
  Build_CSetoid_un_op Qpos Qpos_Qpos_inv Qpos_Qpos_inv_strong_ext.

(** **Special multiplication and inverse
*)

(** We define [multdiv2]: $(x,y) \mapsto xy/2$ #(x,y) &#x21A6; xy/2#.
*)

Definition Qpos_div2 :=
  projected_bin_fun Qpos Qpos Qpos Qpos_mult (Qpos_Qpos_inv_op QTWOpos).

Definition multdiv2 :=
  compose_CSetoid_un_bin_fun Qpos Qpos Qpos Qpos_mult Qpos_div2.

Lemma associative_multdiv2 : associative multdiv2.
unfold associative in |- *.
intros x y z.
unfold multdiv2 in |- *.
unfold compose_CSetoid_un_bin_fun in |- *.
case x.
case y.
case z.
simpl in |- *.
intros.
set (a := Qmult_is_assoc) in *.
generalize a.
unfold associative in |- *.
unfold Qmult_is_bin_fun in |- *.
simpl in |- *.
intros a0.
set
 (i1 := a0 scs_elem1 (Q.inv QTWO (pos_imp_nonzero QTWO pos_QTWO)) scs_elem0)
 in *.
set (i2 := Qmult_sym scs_elem1 (Q.inv QTWO (pos_imp_nonzero QTWO pos_QTWO)))
 in *.
set
 (i3 :=
  Qmult_simpl (scs_elem1{*Q}Q.inv QTWO (pos_imp_nonzero QTWO pos_QTWO))
    (Q.inv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}scs_elem1) scs_elem0
    scs_elem0 i2 (refl_Qeq scs_elem0)) in *.
set
 (i4 := a0 (Q.inv QTWO (pos_imp_nonzero QTWO pos_QTWO)) scs_elem0 scs_elem)
 in *.
apply Qmult_simpl.
apply refl_Qeq.
set
 (i5 :=
  Qmult_simpl scs_elem1 scs_elem1
    (Q.inv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}(scs_elem0{*Q}scs_elem))
    ((Q.inv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}scs_elem0){*Q}scs_elem)
    (refl_Qeq scs_elem1) i4) in *.
set
 (i6 :=
  sym_Qeq
    (scs_elem1{*Q}
     (Q.inv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}(scs_elem0{*Q}scs_elem)))
    (scs_elem1{*Q}
     ((Q.inv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}scs_elem0){*Q}scs_elem))
    i5) in *.
apply
 trans_Qeq
  with
    (scs_elem1{*Q}
     ((Q.inv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}scs_elem0){*Q}scs_elem)).
exact i5.
set
 (i7 :=
  a0 scs_elem1 (Q.inv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}scs_elem0)
    scs_elem) in *.
apply
 trans_Qeq
  with
    ((scs_elem1{*Q}(Q.inv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}scs_elem0)){*Q}
     scs_elem).
exact i7.
apply Qmult_simpl.
2: apply refl_Qeq.
set
 (i8 := a0 (Q.inv QTWO (pos_imp_nonzero QTWO pos_QTWO)) scs_elem1 scs_elem0)
 in *.
set
 (i9 :=
  sym_Qeq
    (Q.inv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}(scs_elem1{*Q}scs_elem0))
    ((Q.inv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}scs_elem1){*Q}scs_elem0)
    i8) in *.
apply
 trans_Qeq
  with
    ((Q.inv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}scs_elem1){*Q}scs_elem0).
2: apply i9.
apply
 trans_Qeq
  with
    ((scs_elem1{*Q}Q.inv QTWO (pos_imp_nonzero QTWO pos_QTWO)){*Q}scs_elem0).
apply i1.
apply i3.
Qed.

(** And its inverse [multdiv4]: $x \mapsto 4/x$ #x &#x21A6; 4/x#.
*)

Definition mult4 := projected_bin_fun Qpos Qpos Qpos Qpos_mult QFOURpos.

Definition divmult4 :=
  compose_CSetoid_fun Qpos Qpos Qpos Qpos_Qpos_inv_op mult4.

