
Require Export CoRN.algebra.CRings.
Section FunRing.

Variable A : CSetoid.
Variable B : CRing.

Definition FSCSetoid := FS_as_CSetoid A B.

Definition FS_sg_op_pointwise : FSCSetoid -> FSCSetoid -> FSCSetoid.
  unfold FSCSetoid. intros f g.
  apply Build_CSetoid_fun with
    (csf_fun := (fun t : A => f t [+] g t)).
  intros ? ? Hsep.
  apply  csbf_strext in Hsep.
  destruct Hsep as [Hsep| Hsep];
    [destruct f | destruct g]; auto.
Defined.

Definition FS_sg_op_cs_pointwise : CSetoid_bin_op FSCSetoid.
  apply Build_CSetoid_bin_op with (csbf_fun := FS_sg_op_pointwise).
  intros f1 f2 g1 g2 Hsep.
  simpl in Hsep.
  unfold ap_fun in Hsep.
  destruct Hsep as [a Hsep].
  simpl in Hsep.
  apply  csbf_strext in Hsep.
  destruct Hsep;[left|right]; 
  simpl; unfold ap_fun; eexists; eauto.
Defined.

(** There is a [FS_as_CSemiGroup] located at
    [CoRN.algebra.CSemiGroups.FS_as_CSemiGroup]
    It is the semigroup where the operation is
    composition of functions. This semigroup
    is different; it is the poinwise version
    of the operation on B (co-domain) *)

Definition FS_as_PointWise_CSemiGroup : CSemiGroup.
  apply Build_CSemiGroup with (csg_crr := FSCSetoid)
                            (csg_op := FS_sg_op_cs_pointwise).
  unfold is_CSemiGroup.
  unfold associative.
  intros f g h. simpl.
  unfold FS_sg_op_cs_pointwise, FS_sg_op_pointwise, eq_fun.
  simpl. eauto  1 with algebra.
Defined.

Definition FS_cm_unit_pw : FSCSetoid.
  unfold FSCSetoid.
  apply Build_CSetoid_fun with
    (csf_fun := (fun t : A => [0])).
  intros ? ? Hsep.
  apply ap_irreflexive_unfolded in Hsep.
  contradiction.
Defined.


Definition FS_as_PointWise_CMonoid : CMonoid.
  apply Build_CMonoid with (cm_crr := FS_as_PointWise_CSemiGroup)
                          (cm_unit := FS_cm_unit_pw).
  split; simpl; unfold is_rht_unit; unfold is_rht_unit; 
  intros f; simpl; unfold eq_fun; simpl; intros a;
  eauto using cm_rht_unit_unfolded, 
    cm_lft_unit_unfolded.
Defined.

Definition FS_gr_inv_pw : FSCSetoid -> FSCSetoid.
  unfold FSCSetoid. intros f.
  apply Build_CSetoid_fun with
    (csf_fun := (fun t : A =>  [--](f t))).
  intros ? ? Hsep.
  eauto using csf_strext_unfolded, zero_minus_apart,
    csf_strext_unfolded.
Defined.

Definition FS_gr_inv_pw_cs : CSetoid_un_op FSCSetoid.
  apply Build_CSetoid_un_op with (csf_fun := FS_gr_inv_pw).
  intros f1 f2 Hsep. simpl.
  simpl in Hsep.
  unfold ap_fun in Hsep.
  destruct Hsep as [a Hsep].
  simpl in Hsep.
  exists a.
  eauto using zero_minus_apart, 
              minus_ap_zero, csf_strext_unfolded.
Defined.

Definition FS_as_PointWise_CGroup : CGroup.
  apply Build_CGroup with (cg_crr := FS_as_PointWise_CMonoid)
                          (cg_inv := FS_gr_inv_pw_cs).
  split; simpl;
  unfold eq_fun;
  unfold FS_sg_op_pointwise, FS_cm_unit_pw, FS_gr_inv_pw;
  simpl; eauto using cg_rht_inv_unfolded,
                     cg_lft_inv_unfolded.
Defined.

Definition FS_as_PointWise_CAbGroup : CAbGroup.
  apply Build_CAbGroup with (cag_crr := FS_as_PointWise_CGroup).
  unfold is_CAbGroup, commutes.
  intros f g. simpl. unfold eq_fun.
  simpl. eauto with algebra.
Defined.

Definition FS_mult_pointwise : 
    FSCSetoid -> FSCSetoid -> FSCSetoid.
  unfold FSCSetoid. intros f g.
  apply Build_CSetoid_fun with
    (csf_fun := (fun t : A => f t [*] g t)).
  intros ? ? Hsep.
  apply  csbf_strext in Hsep.
  destruct Hsep as [Hsep| Hsep];
    [destruct f | destruct g]; auto.
Defined.

Definition FS_mult_pointwise_cs : CSetoid_bin_op FSCSetoid.
  apply Build_CSetoid_bin_op with (csbf_fun := FS_mult_pointwise).
  intros f1 f2 g1 g2 Hsep.
  simpl in Hsep.
  unfold ap_fun in Hsep.
  destruct Hsep as [a Hsep].
  simpl in Hsep.
  apply  csbf_strext in Hsep.
  destruct Hsep;[left|right]; 
  simpl; unfold ap_fun; eexists; eauto.
Defined.

Definition FS_cg_one_pw : FSCSetoid.
  unfold FSCSetoid.
  apply Build_CSetoid_fun with
    (csf_fun := (fun t : A => [1])).
  intros ? ? Hsep.
  apply ap_irreflexive_unfolded in Hsep.
  contradiction.
Defined.

Lemma FS_mult_pointwise_assoc 
  : associative FS_mult_pointwise.
 unfold associative.
  intros f g h a. simpl.
  eauto  1 with algebra.
Defined.

(** To prove that the unit of multiplication
    is not the same as the unit of addition,
    ,i.e. [1] [#] [0], i.e. [ax_non_triv],
    [A] must be non-empty.
    Otherwise the extensional equality on 
    function space means that
    [fun _ => [0]] [=] [fun _ => [1]]
*)

Variable aa : A.

Definition FS_as_PointWise_CRing : CRing.
  apply Build_CRing with (cr_crr := FS_as_PointWise_CAbGroup)
                         (cr_mult := FS_mult_pointwise_cs)
                         (cr_one := FS_cg_one_pw).
  apply Build_is_CRing 
    with (ax_mult_assoc := FS_mult_pointwise_assoc);
  simpl.
- split; simpl; unfold is_rht_unit; unfold is_rht_unit; 
  intros f; simpl; unfold eq_fun; simpl; intros a;
  eauto using mult_one, one_mult.
- intros f g a. simpl. apply mult_commut_unfolded.
- intros f g h a. simpl. apply  ring_dist_unfolded.
- unfold ap_fun. exists aa. simpl.
  apply ring_non_triv.
Defined.

End FunRing.



