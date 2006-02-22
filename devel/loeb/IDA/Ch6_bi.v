Require Export Ch6_cyc.

Definition Z_to_nat: forall (z:Z),(0<=z)%Z->nat.
intros z.
case z.
intro H.
exact 0.
intros p H.
exact (nat_of_P p). 

intros p H.
cut False.
intuition.
intuition.
Defined.

Lemma Z_to_nat_correct:forall (z:Z)(H:(0<=z)%Z),
z=(Z_of_nat (Z_to_nat z H)).
intro z.
case z.
intro H.
unfold Z_to_nat.
reflexivity.

intros p H.
unfold Z_to_nat.
cut ( Z_of_nat (nat_of_P p)= Zpos p).
intuition.
apply inject_nat_convert.
intros p H.
cut False.
intuition.
intuition.
Qed.

Section inj_surj.

Variable M:CMonoid.
Variable u:M.
Variable gen: (is_generator M u).
Variable k l:nat.
Variable smallest:k < l
      and power_CMonoid M u k[=]
          power_CMonoid M u l
          and (forall k0 l0 : nat,
               k0 < k or k0 = k and l0 < l ->
               power_CMonoid M u k0[#]
               power_CMonoid M u l0).
Variable H7:((l - k)%nat > 0)%Z.
Variable H4: (k >= 0)%Z.

Section IL.

Variable  a0 : M.
Variable  a1 : M.
Variable ap : a0[#]a1.
(* Variable  c0 : M.
Variable  H0 : (forall m : M, sigT (fun n : nat => power_CMonoid M c0 n[=]m)):CProp.*)
Variable  H1 : k < l.
(* Variable  smallest : power_CMonoid M c0 k[=]power_CMonoid M c0 l
       and (forall k0 l0 : nat,
            k0 < k or k0 = k and l0 < l ->
            power_CMonoid M c0 k0[#]power_CMonoid M c0 l0).*)
Variable  power_mod : forall (n : nat) (H2 : (Z_of_nat (l - k) > 0)%Z),
         k < n ->
         k < l
         and power_CMonoid M u k[=]power_CMonoid M u l
             and ((forall k0 l0 : nat,
                  (k0 < k or k0 = k and l0 < l) ->
                  power_CMonoid M u k0[#]power_CMonoid M u l0):CProp) ->
         power_CMonoid M u n[=]
         power_CMonoid M u (k + mod_nat (n - k) (l - k) H2).

Lemma power_inj: forall (n0 n1:nat),
(power_CMonoid M u n0[#]power_CMonoid M u n1)-> n0<>n1.
intros n0 n1 H2 H3.
rewrite H3 in H2.
set (H8:=(ap_imp_neq M (power_CMonoid M u n1)(power_CMonoid M u n1) H2)).
unfold cs_neq in H8.
apply H8.
apply eq_reflexive.
Qed.

Lemma to_C_inj1:forall(n0 : nat)
  (Hn0 : power_CMonoid M u n0[=]a0)
  (n1 : nat),
   l <= n1 ->
   power_CMonoid M u n1[=]a1 ->
   l <= n0 ->
   (k + (n1 - k)%nat mod (l - k)%nat)%Z <>
   (k + (n0 - k)%nat mod (l - k)%nat)%Z.
intros n0 Hn0 n1 l1 Hn1 l0.
cut (Z_of_nat (l - k) > 0)%Z.
intro H13.
set (H3:=(mod_nat_correct (n1-k)(l-k) H13)).
rewrite H3.
set (H5:=(mod_nat_correct (n0-k)(l-k) H13)).
rewrite H5.
rewrite<- (inj_plus k ((mod_nat (n1 - k) (l - k) H13))%Z).
rewrite<- (inj_plus k ((mod_nat (n0 - k) (l - k) H13))%Z).
apply inj_neq.
unfold neq.
apply power_inj.
csetoid_replace (power_CMonoid M u (k + mod_nat (n1 - k) (l - k) H13))
           (power_CMonoid M u n1).
csetoid_replace (power_CMonoid M u (k + mod_nat (n0 - k) (l - k) H13))
           (power_CMonoid M u n0).
csetoid_rewrite Hn0.
csetoid_rewrite Hn1.
apply ap_symmetric_unfolded.
exact ap.
apply eq_symmetric_unfolded.
apply power_mod.
intuition.
intuition.

apply eq_symmetric_unfolded.
intuition.
rewrite (inj_minus1 l k).
intuition.
intuition.
Qed.

Lemma to_C_inj2:forall(n0 : nat)
  (Hn0 : power_CMonoid M u n0[=]a0)
  (n1 : nat), n1 < l ->
   power_CMonoid M u n1[=]a1 ->
   l <= n0 ->
   Z_of_nat n1 <> (Z_of_nat k + Z_of_nat (n0 - k) mod Z_of_nat (l - k))%Z.
intros n0 Hn0 n1 l1 Hn1 l0.
cut (Z_of_nat (l - k) > 0)%Z.
intro H13.
set (H5:=(mod_nat_correct (n0-k)(l-k) H13)).
rewrite H5.
rewrite<- (inj_plus k ((mod_nat (n0 - k) (l - k) H13))%Z).
apply inj_neq.
unfold neq.
apply power_inj.
csetoid_replace (power_CMonoid M u (k + mod_nat (n0 - k) (l - k) H13))
           (power_CMonoid M u n0).
csetoid_rewrite Hn0.
csetoid_rewrite Hn1.
apply ap_symmetric_unfolded.
exact ap.
apply eq_symmetric_unfolded.
apply power_mod.
intuition.
intuition.
rewrite (inj_minus1 l k).
intuition.
intuition.
Qed.

End IL.

Lemma to_C_inj:injective (to_C_as_csf M u k l  H7 H4 gen smallest).
unfold to_C_as_csf.
unfold injective.
simpl.
unfold to_C.
unfold ZFap.
intros a0 a1 ap.
unfold sigT_rect.
elim smallest.
set (power_mod:= power_k_n M u k l).
(* generalize power_mod_gen.
case cyc.
intros c0.
simpl.
intros H0 power_mod H1 smallest.*)
case (gen a0).
intros n0 Hn0.
case (le_lt_dec l n0).
case (gen a1).
intros n1.
case (le_lt_dec l n1).

(* 1 *)

intros.
apply to_C_inj1 with a0 a1.
exact ap.
intuition.
intros.
apply power_mod.
exact gen.
intuition.
intuition.
exact Hn0.
exact l0.
exact c.
exact l1.

(* 2 *)

intros.
apply to_C_inj2 with a0 a1.
exact ap.
intuition.
intros.
apply power_mod.
exact gen.
intuition.
intuition.
exact Hn0.
exact l0.
exact c.
exact l1.

case (gen a1).
intro n1.
case (le_lt_dec l n1).

(* 3 *)

intros.
cut (Z_of_nat n0 <> (Z_of_nat k + Z_of_nat (n1 - k) mod Z_of_nat (l - k))%Z).
intuition.
apply to_C_inj2 with a1 a0.
apply ap_symmetric_unfolded.
exact ap.
intuition.
intros.
apply power_mod.
exact gen.
intuition.
intuition.
exact c.
exact l1.
exact Hn0.
exact l0.

(* 4 *)

intros.
apply inj_neq.
unfold neq.
apply power_inj.
csetoid_rewrite Hn0.
csetoid_rewrite c.
apply ap_symmetric_unfolded.
exact ap.
Qed.

Lemma to_C_surj:surjective (to_C_as_csf M u k l H7 H4 gen smallest).
unfold surjective.
simpl.
intro b.
case b.
intros b' brf0 bprf1.
simpl.
unfold to_C.
unfold sigT_rect.
(* generalize smallest_gen.*)
set (w_inj:= (weakly_inj1 M u k l)).
(* generalize w_inj_gen.*)
set (power_mod:=(power_k_n M u k l)).
(* generalize power_mod_gen.
case cyc.
intros c0 H0.
simpl.
intros power_mod w_inj smallest.*)
exists (power_CMonoid M u (Z_to_nat b' bprf1)).
case (gen (power_CMonoid M u (Z_to_nat b' bprf1))).
intros b'' Hb'.
case (le_lt_dec l b'').
simpl.
2:simpl.
intro H3.
cut (Z_of_nat (l - k) > 0)%Z.
intro H6.
set (H5:=(mod_nat_correct (b''-k) (l-k) H6)).
rewrite H5.
rewrite<- (inj_plus k  (mod_nat (b'' - k) (l - k) H6)).
rewrite (Z_to_nat_correct b' bprf1).
apply inj_eq.
apply w_inj.
exact gen.
apply surj_lt.
rewrite<- (Z_to_nat_correct b' bprf1).
replace (Z_of_nat k + Z_of_nat (l - k))%Z with (Z_of_nat l) in brf0.
exact brf0.

rewrite (inj_minus1 l k).
intuition.
intuition.

apply surj_lt.
rewrite (inj_plus k ( mod_nat (b'' - k) (l - k) H6)).
rewrite<- H5.
cut (Z_of_nat l - Z_of_nat k > 0)%Z. 
intro H9.
set (H8:= (Z_mod_lt (b''-k)(l-k)H9)).
rewrite (inj_minus1 b'' k).
elim H8.
clear H8.
intros H8 H8'.
rewrite (inj_minus1 l k).
intuition.
intuition.
intuition.
intuition.
intuition.
csetoid_replace  (power_CMonoid M u (k + mod_nat (b'' - k) (l - k) H6))
               ( power_CMonoid M u b'').
apply eq_symmetric_unfolded.
exact Hb'.

apply eq_symmetric_unfolded.
apply power_mod.
intuition.
intuition.
intuition.

intuition.
intro H3.
rewrite (Z_to_nat_correct b' bprf1).
apply inj_eq.
apply w_inj.
exact gen.
apply surj_lt.
rewrite<- (Z_to_nat_correct b' bprf1).
replace (Z_of_nat k + Z_of_nat (l - k))%Z with (Z_of_nat l) in brf0.
exact brf0.


rewrite (inj_minus1 l k).
intuition.
intuition.
exact H3.
intuition.
apply eq_symmetric_unfolded.
exact Hb'.
Qed.

End inj_surj.
