Require Export Ch6_cyc.
Require Export Ch6_bi.
Require Export Ch6_inf.

Section Th17.

Variable M:CMonoid.
Variable u:M.
Variable gen:(is_generator M u).

Theorem Th17_partI:
({k:nat | {l:nat |k<l and (power_CMonoid M u k [=] power_CMonoid M u l)
and (forall (k0 l0:nat), (k0<k or (k0=k and l0<l))-> 
(power_CMonoid M u k0 [#] power_CMonoid M u l0) )}}
 ->
{k:Z|{H0:(k>=0)%Z|{n:Z|{H:(n>0)%Z| (isomorphic M (C_as_CMonoid k n H H0))}}}}):
  CProp.
simpl.
intros H'.
elim H'.
clear H'.
intros k H'.
elim H'.
clear H'. 
intros l H'.
generalize H'.
exists (Z_of_nat k).
cut (k>=0).
intro H3.
set (H4:=(inj_ge k 0 H3)).
simpl in H4.
2: intuition.
exists H4.
exists (Z_of_nat (l- k))%Z.
cut (l-k>0).
2:intuition.
intro H5.
set (H6:=(inj_gt (l-k) 0 H5)).
simpl in H6.
exists H6.
unfold isomorphic.
cut ((l-k)%nat >0)%Z.
intro H7.
exists (to_C_as_csf M u k l  H7 H4 gen H').
2:intuition.
unfold isomorphism.
split.
unfold morphism.
split.
unfold H4.
unfold H6.
apply pres_zero.
intros a b.
unfold H4.
unfold H6.
apply pres_mult.

unfold bijective.
split.
apply (to_C_inj M u gen k l H' H7 H4).
apply (to_C_surj M u gen k l H' H7 H4).
Qed.

Theorem Th17_partII:
(((forall (k l:nat),k<l->
(power_CMonoid M u k [#] power_CMonoid M u l))
  :CProp)
 ->(isomorphic M nat_as_CMonoid)):CProp.
intros H'.
unfold isomorphic.
exists (cyc_to_nat_as_csf M u gen H').
unfold isomorphism.
split.
unfold morphism.
simpl.
split.
unfold cyc_to_nat.
unfold sigT_rec.
unfold sigT_rect.
(* generalize H'.*)
set (H88:= (weakly_inj2 M u)).
(* generalize H88.
case H.
intros c0 H0. 
simpl.
intros H88' H''.*)
case (gen Zero).
intros n Hn.
apply H88.
exact H'.
simpl.
exact Hn.

intros a b.
unfold cyc_to_nat.
unfold sigT_rec.
unfold sigT_rect.
(* generalize H'.*)
set (H88:= (weakly_inj2 M u)).
(* generalize H88.
case H.
intros c0 H0.
simpl.
intros H88' H''.*)
case (gen (csbf_fun M M M (csg_op (c:=M)) a b)).
case (gen a).
case (gen b).
intros n2 l2 n1 l1 n0 l0.
apply H88.
exact H'.
csetoid_rewrite (power_plus M u n1 n2).
csetoid_rewrite l2.
csetoid_rewrite l1.
exact l0.

unfold bijective.
split.
unfold injective.
intros a0 a1 H0.
unfold cyc_to_nat_as_csf.
simpl.
unfold cyc_to_nat.
unfold sigT_rec.
unfold sigT_rect.
(* generalize H'.
case H.
intros c0 H1.
simpl.
intro H''.*)
case (gen a0).
case (gen a1).
intros n1 Hn1 n0 Hn0.
unfold ap_nat.
cut (n0<>n1).
unfold not.
unfold CNot.
intros H4 H5.
elim H4.
exact H5.

apply power_inj with M u.
csetoid_rewrite Hn0.
csetoid_rewrite Hn1.
exact H0.

unfold surjective.
simpl.
intro b.
(* generalize H'.*)
set (H88:=(weakly_inj2 M u)).
(* generalize H88.
case H.
simpl.
intros c0 H0 H88' H'' .*)
exists (power_CMonoid M u b).
unfold cyc_to_nat.
unfold sigT_rec.
unfold sigT_rect.
case (gen (power_CMonoid M u b)). 
intros n H1.
apply H88.
exact H'.
exact H1.
Qed.

End Th17.
