Require Export Ch6_cyc.
Require Export CGroups.

Definition invertible (M:CMonoid): M -> CProp :=
fun m =>{inv: (CSetoid_un_op M) | (is_inverse csg_op (@cm_unit M) m (inv m))}. 

Definition plus_nminus1:forall (n:Z)(H:(n>0)%Z)(H0:(0>=0)%Z),(CSetoid_un_op (C_as_CMonoid 0%Z n H H0)).
simpl.
intros n H H0.
unfold CSetoid_un_op.
apply projected_bin_fun with (C_as_CMonoid 0%Z n H H0).
apply (@csg_op (C_as_CMonoid 0%Z n H H0)).

simpl.
apply Build_ZF with (n-1)%Z.
intuition.
intuition.
Defined.

Definition c_n_minus_a:forall (n:Z)(H:(n>0)%Z)(H0:(0>=0)%Z)(a:(C_as_CMonoid 0%Z n H H0)),
(C_as_CMonoid 0%Z n H H0).
simpl.
intros n H H0 a.
elim a.
intros a' aprf0 aprf1.
set (H1:=(Z_eq_dec a' 0)).
elim H1.
clear H1.
intro H1.
apply Build_ZF with 0%Z.
intuition.
intuition.

clear H1.
intro H1.
apply Build_ZF with (n-a')%Z.
intuition.
intuition.
Defined.

Lemma C_0_n:(forall (n:Z)(H:(n>0)%Z)(H0:(0>=0)%Z)(a:(C_as_CMonoid 0%Z n H H0)),
(invertible (C_as_CMonoid 0%Z n H H0) a)):CProp.
simpl.
intros n H H0 a.
unfold invertible.
simpl.
unfold is_inverse.
simpl.
exists (Const_CSetoid_fun (C_as_CSetoid 0 n H H0)(C_as_CSetoid 0 n H H0) (c_n_minus_a n H H0 a)).
simpl.
unfold c_n_minus_a.
unfold ZF_rec.
unfold ZF_rect.
unfold sumbool_rec.
unfold sumbool_rect.
case a.
intros a' aprf0 aprf1.
simpl.
unfold ZF_rec.
unfold ZF_rect.
case ( Z_eq_dec a' 0 ).
unfold sumbool_rec.
unfold sumbool_rect.
case ( Z_lt_le_dec (a' + 0) n).
simpl.
unfold sumbool_rec.
unfold sumbool_rect.
case ( Z_lt_le_dec a' n).
simpl.
intuition.

simpl.
intuition.

simpl.
unfold sumbool_rec.
unfold sumbool_rect.
case (Z_lt_le_dec a' n).
simpl.
intuition.

simpl.
intros H1 H2 H3.
replace (a' +0 -0)%Z with a'.
replace (a'-0)%Z with a'.
cut ( 0%Z = (a' mod n)%Z).
intuition.

rewrite H3.
intuition.
intuition.
intuition.

unfold sumbool_rec.
unfold sumbool_rect.
case ( Z_lt_le_dec (a' + (n - a')) n).
simpl.
unfold sumbool_rec.
unfold sumbool_rect.
case ( Z_lt_le_dec (n - a' + a') n ).
simpl.
intuition.

simpl.
intuition.

simpl.
unfold sumbool_rec.
unfold sumbool_rect.
case (Z_lt_le_dec (n - a' + a') n).
simpl.
intuition.

simpl.
intros H1 H2 H3.
replace (a' + (n - a') - 0)%Z with (1*n+0)%Z.
replace (n - a' + a' - 0)%Z with (1*n+0)%Z.
cut ( 0%Z = ((1%positive * n + 0) mod n)%Z).
intuition.
cut (((1%positive * n + 0) mod n)%Z =0%Z).
intuition.
replace 0%Z with (0 mod n)%Z.
apply Zmod_cancel_multiple.
exact H.
intuition.
intuition.
intuition.
Qed.

Lemma Zgt_Zge: forall (n m:Z), (n>m)%Z -> (n>=m)%Z.
intros n m.
intuition.
Qed.

Lemma not_inv: 
forall (n k:Z)(H:(k>0)%Z)(H0:(n>0)%Z)
(a:(C_as_CMonoid k%Z n  H0 (Zgt_Zge k 0 H))),
a[#](@cm_unit (C_as_CMonoid k%Z n  H0 (Zgt_Zge k 0 H)))->
 Not (invertible (C_as_CMonoid k%Z n  H0 (Zgt_Zge k 0 H)) a).
simpl.
unfold ZFap.
simpl.
intros n k H H0 a.
elim a.
intros a' aprf0 aprf1.
intros H1 H2.
unfold invertible in H2.
elim H2.
simpl.
unfold is_inverse.
clear H2.
simpl.
unfold ZF_rec.
unfold ZF_rect.
unfold sumbool_rec.
unfold sumbool_rect.
simpl.
intro inv.
unfold CSetoid_un_op in inv.
elim inv.
intros inv' inv_strext.
simpl.
case ( inv' (Build_ZF (k+n) a' aprf0 aprf1)).
intros i iprf0 iprf1.
case ( Z_lt_le_dec (a' + i) (k+n)).
simpl.
unfold sumbool_rec.
unfold sumbool_rect.
case (Z_lt_le_dec (i + a') (k+n)).
simpl.
intuition.

simpl.
intuition.

simpl.
unfold sumbool_rec.
unfold sumbool_rect.
case (Z_lt_le_dec (i + a') (k+n)).
simpl.
intuition.

simpl.
set (H4:=(Z_mod_lt (a' +i -k) n  H0)).
intuition.
Qed.

Lemma unit_inv: 
(forall (n k:Z)(H:(k>=0)%Z)(H0:(n>0)%Z),
(invertible (C_as_CMonoid k%Z n  H0 H) (@cm_unit (C_as_CMonoid k%Z n  H0 H)))):
CProp.
intros n k H H0.
simpl.
unfold invertible.
exists (Const_CSetoid_fun (C_as_CSetoid k n H0 H)(C_as_CSetoid k n H0 H)
        (@cm_unit (C_as_CMonoid k n H0 H))).
unfold is_inverse.
simpl.
unfold sumbool_rec.
unfold sumbool_rect.
case (Z_lt_le_dec 0 (k + n)).
simpl.
intuition.

simpl.
intuition.
Qed.



