Require Export Ch6_cyc.

Definition cyc_to_nat: forall (M:CMonoid)(u:M), 
(is_generator M u)->M->nat_as_CMonoid.
simpl.
intros M u gen m.
unfold is_generator in gen.
(* elim cyc.
clear cyc.
intros c0 cyc.*)
elim (gen m).
intros n genm.
exact n.
Defined.

Section CTN.
Variable M:CMonoid.
Variable u:M.
Variable gen:(is_generator M u).

Lemma cyc_to_nat_strext: (((forall (k l:nat),k<l->
(power_CMonoid M u k [#] power_CMonoid M u l))
:CProp)
->
(fun_strext (cyc_to_nat M u gen)):CProp):CProp.
intros inf.
unfold fun_strext.
intros a b.
unfold cyc_to_nat.
unfold sigT_rec.
unfold sigT_rect.
(* generalize inf.
case H.
intros c0 H' inf'.
simpl in inf'.*)
case (gen a).
case (gen b).
intros n1 Hn1 n0 Hn0 H3.  
simpl in H3.
unfold ap_nat in H3.
unfold CNot in H3.
set (H4:= (lt_eq_lt_dec n0 n1)).
elim H4.
clear H4.
intro H4.
elim H4.
clear H4.
intro H4.
csetoid_rewrite_rev Hn1.
csetoid_rewrite_rev Hn0.
apply inf.
exact H4.

intuition.
clear H4.
intro H4.
apply ap_symmetric_unfolded.
csetoid_rewrite_rev Hn1.
csetoid_rewrite_rev Hn0.
apply inf.
exact H4.
Qed.

Definition cyc_to_nat_as_csf 
(H0:(forall (k l:nat),k<l->(power_CMonoid M u k [#] power_CMonoid M u l))):=
(Build_CSetoid_fun M nat_as_CMonoid (cyc_to_nat M u gen) (cyc_to_nat_strext H0)).

Lemma weakly_inj2:forall (a b:nat),
(forall (k l:nat),k<l->(power_CMonoid M u k [#] power_CMonoid M u l))
->
(power_CMonoid M u a[=]power_CMonoid M u b )->
       a = b.
intros a b.
(* case H.
simpl.*)
intros (* c0 H0*) H1 H2.
set (H3:=(lt_eq_lt_dec a b)).
elim H3.
clear H3.
intro H3.
elim H3.
clear H3.
intro H3.
set (H4:=(H1 a b H3)).
set (H5:=(eq_imp_not_ap M (power_CMonoid M u a)(power_CMonoid M u b) H2)).
unfold Not in H5.
elim H5.
exact H4.

tauto.
clear H3.
intro H3.
set (H4:=(H1 b a H3)).
set (H5:=(eq_imp_not_ap M (power_CMonoid M u a)(power_CMonoid M u b) H2)).
unfold Not in H5.
elim H5.
apply ap_symmetric_unfolded.
exact H4.
Qed.

End CTN.
