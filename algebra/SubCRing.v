Require Export CoRN.algebra.CRings.
Set Implicit Arguments.
Section SubRing.

Variable A : CRing.
Variable AProp : A -> Type.

Definition SubCSetoid := Build_SubCSetoid  A AProp.
Hint Resolve (scs_prf A AProp) : CoRN.

Variable AProp_closed_csg_op :
   forall {a1 a2 : A}, 
    AProp a1
    -> AProp a2
    -> AProp (a1 [+] a2).

Definition Sub_sg_op (a1 a2 : SubCSetoid) : SubCSetoid :=
{|
    scs_elem := a1[+]a2;
    scs_prf := AProp_closed_csg_op (scs_prf _ _ a1)
                                   (scs_prf _ _ a2) |}.

Definition Sub_sg_op_cs : CSetoid_bin_op SubCSetoid.
  apply Build_CSetoid_bin_op with (csbf_fun := Sub_sg_op).
  intros a b c d  Hsep.
  simpl in Hsep.
  destruct a,b,c,d.
  simpl. simpl in Hsep.
  apply  csbf_strext in Hsep.
  destruct Hsep;[left|right]; 
  simpl; unfold ap_fun; eauto.
Defined.

Definition SubCSemiGroup : CSemiGroup.
  apply Build_CSemiGroup with (csg_crr := SubCSetoid)
                            (csg_op := Sub_sg_op_cs).
  unfold is_CSemiGroup.
  unfold associative.
  intros. simpl.
  simpl. eauto  1 with algebra.
Defined.

Variable Aprop0 : AProp [0].

Definition Sub_cm_unit: SubCSetoid :=
  {| scs_elem := [0] ; scs_prf := Aprop0|}.


Definition SubCMonoid : CMonoid.
  apply Build_CMonoid with (cm_crr := SubCSemiGroup)
                          (cm_unit := Sub_cm_unit).
  split; simpl; unfold is_rht_unit; unfold is_rht_unit; 
  intros f; destruct f; simpl; unfold eq_fun; simpl;
  eauto using cm_rht_unit_unfolded, 
    cm_lft_unit_unfolded.
Defined.

Variable AProp_closed_cg_inv :
   forall {a : A}, 
    AProp a
    -> AProp ([--] a).

Definition Sub_gr_inv (a :SubCSetoid) : SubCSetoid :=
{| scs_elem := [--]a ; 
   scs_prf :=  AProp_closed_cg_inv (scs_prf _ _ a)|}.


Definition Sub_gr_inv_cs : CSetoid_un_op SubCSetoid.
  apply Build_CSetoid_un_op with (csf_fun := Sub_gr_inv).
  intros a1 a2 Hsep. destruct a1, a2.
  simpl in Hsep.
  simpl.
  eauto using zero_minus_apart, 
              minus_ap_zero, csf_strext_unfolded.
Defined.

Definition SubCGroup : CGroup.
  apply Build_CGroup with (cg_crr := SubCMonoid)
                          (cg_inv := Sub_gr_inv_cs).
  split; simpl;
  simpl; eauto using cg_rht_inv_unfolded,
                     cg_lft_inv_unfolded.
Defined.

Definition SubCAbGroup : CAbGroup.
  apply Build_CAbGroup with (cag_crr := SubCGroup).
  unfold is_CAbGroup, commutes.
  simpl. eauto with algebra.
Defined.

Variable AProp_closed_cr_mult :
   forall {a1 a2 : A}, 
    AProp a1
    -> AProp a2
    -> AProp (a1 [*] a2).

Definition Sub_cr_mult (a1 a2 : SubCSetoid) : SubCSetoid :=
{|
    scs_elem := a1[*]a2;
    scs_prf := AProp_closed_cr_mult (scs_prf _ _ a1)
                                    (scs_prf _ _ a2) |}.

Definition Sub_cr_mult_cs : CSetoid_bin_op SubCSetoid.
  apply Build_CSetoid_bin_op with (csbf_fun := Sub_cr_mult).
  intros a b c d  Hsep.
  simpl in Hsep.
  destruct a,b,c,d.
  simpl. simpl in Hsep.
  apply  csbf_strext in Hsep.
  destruct Hsep;[left|right]; 
  simpl; unfold ap_fun; eauto.
Defined.

Variable Aprop1 : AProp [1].

Definition Sub_cr_one: SubCSetoid :=
  {| scs_elem := [1] ; scs_prf := Aprop1|}.

Lemma Sub_mult_assoc : associative Sub_cr_mult_cs.
  unfold associative.
  intros f g h. simpl.
  eauto  1 with algebra.
Defined.


Definition SubCRing : CRing.
  apply Build_CRing with (cr_crr := SubCAbGroup)
                         (cr_mult := Sub_cr_mult_cs)
                         (cr_one := Sub_cr_one).
  apply Build_is_CRing 
    with (ax_mult_assoc := Sub_mult_assoc);
  simpl.
- split; simpl; unfold is_rht_unit; unfold is_rht_unit; 
  intros f; destruct f; simpl;
  eauto using mult_one, one_mult. 
- intros f g . simpl. apply mult_commut_unfolded.
- intros f g h. simpl. apply  ring_dist_unfolded.
- unfold ap_fun. 
  apply ring_non_triv.
Defined.

End SubRing.

