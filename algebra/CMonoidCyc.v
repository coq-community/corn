(* $Id$ *)

Require Export CMonoids.
Require Export csetoid_rewrite.
Require Export Zfinsetoid.
Require Export Nmonoid.
Require Export ZBasics.

(** *Cyclic CMonoids
Some specific lemmas about cyclic monoids.
*)

Definition C_as_CSetoid (k n :Z)(H:(n>0)%Z)(H0:(k>= 0)%Z):CSetoid 
             := ZCSetoid_of_less (k+n).


Definition C_plus (k n:Z) (H:(n>0)%Z)(H0:(k>=0)%Z): 
C_as_CSetoid k n H H0-> C_as_CSetoid k n H H0-> C_as_CSetoid k n H H0.
intros k n H H0.
simpl.
intros j i.
elim j.
intros j_ jprf jprf1.
elim i.
intros i_ iprf iprf1.
elim (Z_lt_le_dec (j_+i_) (k+n)).
intro H1.
apply Build_ZF with (j_+i_)%Z.
exact H1.
intuition.

intro H1.
apply Build_ZF with ( k + (Zmod (j_+i_-k) n))%Z.
apply Zcompat_lt_plus.
set (H2:=(Z_mod_lt (j_+i_-k) n H)).
elim H2.
intros H3 H4.
exact H4.

set (H2:=(Z_mod_lt (j_+i_-k) n H)).
elim H2.
intros H3 H4.
intuition.
Defined.

Lemma C_plus_strext:
forall (k n:Z)(H:(n>0)%Z)(H0:(k>=0)%Z),(bin_fun_strext (C_as_CSetoid k n H H0) 
(C_as_CSetoid k n H H0) (C_as_CSetoid k n H H0) (C_plus k n H H0)).
intros k n H H0.
unfold bin_fun_strext.
intros x1 x2 y1 y2.
elim x1.
intros x1_ x1prf x1prf1.
elim x2.
intros x2_ x2prf x2prf2.
elim y1.
intros y1_ y1prf y1prf1.
elim y2.
intros y2_ y2prf y2prf2.
simpl.
unfold ZFap.
unfold C_plus.
unfold sumbool_rec.
unfold sumbool_rect.
case (Z_lt_le_dec (x1_+y1_)(k+n)).
case (Z_lt_le_dec (x2_+y2_)(k+n)).
intros H6 H1 H2.
red in H2.
elim (Z_eq_dec x2_ x1_).
intro H3.
right.
intro H4.
apply H2.
rewrite H3.
rewrite H4.
reflexivity.

intro H3.
left.
exact H3.

intros H6 H1 H2.
red in H2.
elim (Z_eq_dec x2_ x1_).
intro H4.
right.
intro H5.
rewrite<- H4 in H1.
rewrite H5 in H6.
intuition.

intro H4.
left.
exact H4.

case (Z_lt_le_dec (x2_ + y2_)(k+n)).
intros H6 H1 H2.
red in H2.
elim (Z_eq_dec x2_ x1_).
intro H4.
right.
intro H5.
rewrite<- H4 in H1.
rewrite H5 in H6.
intuition.

intro H4.
left.
exact H4.

intros H6 H1 H2.
red in H2.
elim (Z_eq_dec x2_ x1_).
intro H3.
right.
red in |- *.
intros H4.
apply H2.
rewrite H3.
rewrite H4.
reflexivity.

intros H3.
left.
exact H3.
Qed.


Definition C_plus_as_bin_fun (k n:Z)(H:(n>0)%Z)(H0:(k>=0)%Z):=
(Build_CSetoid_bin_fun (C_as_CSetoid k n H H0) (C_as_CSetoid k n H H0) 
(C_as_CSetoid k n H H0) (C_plus k n H H0) (C_plus_strext k n H H0)).

Lemma C_plus_is_CSemiGroup:forall (k n:Z)(H:(n>0)%Z)(H0:(k>=0)%Z),
(is_CSemiGroup (C_as_CSetoid k n H H0)(C_plus_as_bin_fun k n H H0)).
intros k n H H0.
unfold is_CSemiGroup.
unfold associative.
simpl.
intros x y z.
case x.
intros x_ xprf xprf1.
case y.
intros y_ yprf yprf1.
case z.
intros z_ zprf zprf1.
unfold ZFeq.
simpl.
unfold ZF_rec.
unfold ZF_rect.
unfold sumbool_rec.
unfold sumbool_rect.
case (Z_lt_le_dec (y_ + z_)(k+n)).
case (Z_lt_le_dec (x_ + (y_ + z_))). 
case ( Z_lt_le_dec (x_ + y_)(k+n)).
simpl.
unfold sumbool_rec.
unfold sumbool_rect.
case (Z_lt_le_dec (x_+y_+z_)(k+n)).
intuition.

intros H1 H2 H3 H4.
intuition.

unfold C_plus.
unfold ZF_rec.
unfold ZF_rect.
unfold sumbool_rec.
unfold sumbool_rect.
case (Z_lt_le_dec (k + (x_ + y_ - k) mod n + z_) (k + n)).
intros H1 H2 H3 H4.
cut (Zmod (x_+y_ -k) n <n)%Z.
2:intuition.
intro H5.
cut (0 <= x_+y_ -k < n)%Z.
intro H6.
rewrite (Zmod_small n ( x_+y_ -k) H H6).
intuition.
intuition.

intros H1 H2 H3 H4.
intuition.

unfold C_plus.
unfold ZF_rec.
unfold ZF_rect.
case (Z_lt_le_dec (x_ + y_) (k + n)).
unfold sumbool_rec.
unfold sumbool_rect.
case ( Z_lt_le_dec (x_ + y_ + z_) (k + n)).
intuition.

intros H1 H2 H3 H4.
replace (x_ + y_ + z_ - k)%Z with  (x_ + (y_ + z_) - k)%Z. 
reflexivity.

intuition.

unfold sumbool_rec.
unfold sumbool_rect.
case (Z_lt_le_dec (k + (x_ + y_ - k) mod n + z_) (k + n)).
intros H1 H2 H3 H4.
set (H5:= (Zmod_plus_compat_lft n (x_+y_-k) z_ H)).
replace (x_ + (y_ + z_) - k)%Z with (x_ + y_+(z_ - k))%Z.
2:intuition.
replace (x_+y_+(z_ -k))%Z with (x_ + y_ -k +z_)%Z.
2:intuition.
rewrite H5.
cut ((((x_ + y_ - k) mod n + z_) mod n)<n)%Z.
intro H6.
cut (((x_ + y_ - k) mod n + z_)%Z =
   (((x_ + y_ - k) mod n + z_) mod n)%Z).
intuition.
cut (0<= ((Zmod (x_ + y_ - k) n )+ z_)<n)%Z.
intro H7.
rewrite (Zmod_small n ((x_ + y_ - k) mod n + z_) H H7).
reflexivity.
split.
2:intuition.
set (H7:= (Z_mod_lt (x_ + y_ -k) n H)).
intuition.

set (H6:= (Z_mod_lt ((x_ + y_ - k) mod n + z_) n H)).
intuition.

intros H1 H2 H3 H4.
replace (k +(Zmod (x_ + y_ - k)  n) + z_ - k)%Z with ((Zmod (x_+y_-k) n)+z_)%Z.
cut ((((x_ + y_ - k) mod n + z_) mod n)%Z =
   ((x_ + (y_ + z_) - k) mod n)%Z).
intro H5.
intuition.
2:intuition.
rewrite<- (Zmod_plus_compat_lft n (x_+y_-k)%Z z_ H).
replace (x_+y_ -k +z_)%Z with (x_ + ((y_ -k)+z_))%Z.
2:intuition.
replace (x_ + (y_ - k + z_))%Z with (x_+ (y_+z_ -k))%Z.
2:intuition.
replace (x_+(y_+z_ -k))%Z with (x_+(y_+z_)-k)%Z.
2:intuition.
reflexivity.

case (Z_lt_le_dec (x_ + (k + (y_ + z_ - k) mod n)) (k + n)).
unfold C_plus.
unfold ZF_rec.
unfold ZF_rect.
case (Z_lt_le_dec (x_ + y_) (k + n)).
unfold sumbool_rec.
unfold sumbool_rect.
case ( Z_lt_le_dec (x_ + y_ + z_) (k + n)).
intuition.

intros H1 H2 H3 H4.
set (H5:= (Zmod_plus_compat_rht n x_ (y_ + z_ - k) H)).
replace (x_ + (k + (y_ + z_ - k) mod n))%Z with ((x_ + k) + (y_ + z_ - k) mod n)%Z.
2:intuition.
replace (x_ + k + (y_ + z_ - k) mod n)%Z with (k+x_+ (y_ + z_ - k) mod n)%Z.
2:intuition.
replace (x_+y_+z_-k)%Z with (x_+(y_+z_ -k))%Z.
rewrite H5.
2:intuition.
cut (0<= (x_ + (y_ + z_ - k) mod n)<n)%Z.


3:unfold sumbool_rec.
3:unfold sumbool_rect.
3: case ( Z_lt_le_dec (k + (x_ + y_ - k) mod n + z_) (k + n)).
5:unfold C_plus.
5:unfold ZF_rec.
5:unfold ZF_rect.
5:case (Z_lt_le_dec (x_ + y_) (k + n)).
5:unfold sumbool_rec.
5: unfold sumbool_rect.
5: case (Z_lt_le_dec (x_ + y_ + z_) (k + n)).
7:unfold sumbool_rec.
7:unfold sumbool_rect.
7: case (Z_lt_le_dec (k + (x_ + y_ - k) mod n + z_) (k + n)).

intro H6.
set (H7:= (Zmod_small n  (x_ + (y_ + z_ - k) mod n) H H6)).
rewrite H7.
intuition.
set (H6:= (Z_mod_lt (y_+z_-k) n H)).
split.
intuition.
intuition.

intros H1 H2 H3 H4.
replace (y_ + z_ -k)%Z with (z_ +y_ -k)%Z.
2:intuition.
cut (0<= ((Zmod (x_+y_ -k)%Z n)+z_)<n)%Z.
intro H5.
set (H6:= (Zmod_small n ((Zmod (x_+y_ -k) n)%Z+ z_)%Z H H5)).
replace  (k + (x_ + y_ - k) mod n + z_)%Z with  
         (k + ((x_ + y_ - k) mod n + z_))%Z.
2:intuition.
rewrite<- H6.
cut (0<= z_< n)%Z.
intro H7.
set (H8:=(Zmod_small n z_ H H7)).
replace (k + ((x_ + y_ - k) mod n + z_) mod n)%Z with 
         (k + ((x_ + y_ - k) mod n + z_ mod n ) mod n)%Z. 
2:rewrite H8.
2:reflexivity.
set (H9:= (Zmod_plus_compat n (x_ + y_ - k)%Z z_ H)).
rewrite<- H9.


replace (x_ + (k + (z_ + y_ - k) mod n))%Z with
        (k + (((z_ + y_ - k) mod n)+ x_))%Z.
2:intuition.
cut (0<= ((Zmod (z_+y_ -k)%Z n)+x_)<n)%Z.
intro H10.
set (H11:= (Zmod_small n ((Zmod (z_+y_ -k) n)%Z+ x_)%Z H H10)).
rewrite<- H11.
cut (0<= x_< n)%Z.
intro H12.
set (H13:=(Zmod_small n x_ H H12)).
replace (k + ((z_ + y_ - k) mod n + x_) mod n)%Z with 
         (k + ((z_ + y_ - k) mod n + x_ mod n ) mod n)%Z. 
2:rewrite H13.
2:reflexivity.
set (H14:= (Zmod_plus_compat n (z_ + y_ - k)%Z x_ H)).
rewrite<- H14.
replace (x_ + y_ - k + z_)%Z with (z_ + y_ - k + x_)%Z.
reflexivity.
intuition.
split.
intuition.
cut ((x_ +  (y_ + z_ - k) mod n) <  n)%Z.
intro H13.
set (H14:= (Z_mod_lt (y_+z_-k)n H)).
intuition.

intuition.

split.
set (H10:=(Z_mod_lt (z_+y_-k)n H)).
intuition.

replace (z_+y_ -k)%Z with (y_+z_-k)%Z.
2:intuition.
intuition.

split.
intuition.
cut ((x_ + y_ - k) mod n + z_ <  n)%Z.
set (H7:=(Z_mod_lt (x_+y_-k)%Z n H)).
intuition.

intuition.

split.
set (H5:= (Z_mod_lt (x_+y_-k)%Z n H)).
intuition.

intuition.

intros H1 H2 H3 H4.
replace (k + (x_ + y_ - k) mod n + z_ - k)%Z with
        ((x_ + y_ - k) mod n + z_)%Z.
2:intuition.
cut (0<=(x_+ (y_+z_-k)mod n)%Z<n)%Z.
intro H5.
set (H6:=(Zmod_small n (x_+(y_+z_-k)mod n)%Z H H5)).
replace (x_ + (k + (y_ + z_ - k) mod n))%Z with
       (k + (x_ + (y_ + z_ - k) mod n))%Z.
2:intuition.
rewrite<- H6.
set (H7:=(Zmod_plus_compat_rht n x_ (y_+z_-k)%Z H )).
rewrite<- H7.
set (H8:=(Zmod_plus_compat_lft n (x_+y_-k)%Z z_ H)).
rewrite<- H8.
replace (x_ + y_ - k + z_)%Z with (x_ + (y_ + z_ - k))%Z.
reflexivity.

intuition.
set (H5:=(Z_mod_lt (y_ + z_ - k) n H)).
intuition.

intros H1 H2 H3 H4.
intuition.

intros H1 H2 H3 H4.
replace (x_ + (k + (y_ + z_ - k) mod n) - k)%Z with
      (x_ + (y_ + z_ - k) mod n)%Z.                                            
2:intuition.
set (H5:=(Zmod_plus_compat_rht n x_ (y_+z_-k) H)).
rewrite<- H5.
replace (x_ + y_ + z_ - k)%Z with (x_ + (y_ + z_ - k))%Z.
reflexivity.
intuition.

intros H1 H2 H3 H4.
replace (x_ + (k + (y_ + z_ - k) mod n) - k)%Z with
     (x_ + (y_ + z_ - k) mod n)%Z.                                             2:intuition.
cut (0<= ((x_ + y_ - k) mod n + z_)%Z <n)%Z.
intro H5.
set (H6:=(Zmod_small n ((x_ + y_ - k) mod n + z_))%Z H H5).
replace (k + (x_ + y_ - k) mod n + z_)%Z with 
    (k + ((x_ + y_ - k) mod n + z_))%Z.                                        2: intuition.  
rewrite<- H6.
cut (0<=z_<n)%Z.
intro H7.
set (H8:=(Zmod_small n z_ H H7)).
replace ((x_ + y_ - k) mod n + z_)%Z with ((x_ + y_ - k) mod n +(z_ mod n))%Z.
2:rewrite H8.
2:reflexivity.
set (H9:=(Zmod_plus_compat n (x_+y_-k) z_ H)).
rewrite<- H9.
set (H10:=(Zmod_plus_compat_rht n x_ (y_+z_-k) H)).
rewrite<- H10.
replace (x_ + y_ - k + z_)%Z with (x_ + (y_ + z_ - k))%Z.
reflexivity.
intuition.

split.
intuition.
set (H7:=(Z_mod_lt (x_+y_-k)n H)).
intuition.
set (H5:=(Z_mod_lt (x_+y_-k)n H)).
intuition.

intros H1 H2 H3 H4.
replace (k + (x_ + y_ - k) mod n + z_ - k)%Z with
   ((x_ + y_ - k) mod n + z_ )%Z.                                              
2:intuition.
replace (x_ + (k + (y_ + z_ - k) mod n) - k)%Z with   
        (x_ + (y_ + z_ - k) mod n)%Z.                              
2:intuition.
set (H5:= (Zmod_plus_compat_lft n (x_+y_-k)%Z z_ H)).
rewrite<- H5.
set (H6:= (Zmod_plus_compat_rht n x_ (y_+z_-k)%Z H)).
rewrite<- H6.
replace (x_ + y_ - k + z_)%Z with (x_ + (y_ + z_ - k))%Z.
reflexivity.
intuition.
Qed.

Definition C_as_CSemiGroup (k n :Z)(H:(n>0)%Z)(H0:(k>=0)%Z):=
 (Build_CSemiGroup (C_as_CSetoid k n H H0)(C_plus_as_bin_fun k n H H0)
(C_plus_is_CSemiGroup k n H H0)).

Definition C0 (k n:Z)(H:(n>0)%Z)(H0:(k>=0)%Z):(C_as_CSetoid k n H H0).
intros k n H H0.
simpl.
apply Build_ZF with 0%Z.
intuition.
intuition.
Defined.

Lemma O_is_rht_unit_C: forall (k n:Z)(H:(n>0)%Z)(H0:(k>=0)%Z),
(is_rht_unit (C_plus_as_bin_fun k n H H0) (C0 k n H H0)).
intros k n H H0.
unfold is_rht_unit.
simpl.
unfold C0.
unfold C_plus.
unfold ZF_rec.
unfold ZF_rect.
unfold sumbool_rec.
unfold sumbool_rect.
intro x.
case x.
intros y prf prf1.
unfold ZFeq.
case (Z_lt_le_dec (y + 0)(k+n)).
intuition.

intro H1.
intuition.
Qed.

Lemma O_is_lft_unit_C: forall (k n:Z)(H:(n>0)%Z)(H0:(k>=0)%Z),
(is_lft_unit (C_plus_as_bin_fun k n H H0) (C0 k n H H0)).
intros k n H H0.
unfold is_lft_unit.
simpl.
unfold ZF_rec.
unfold ZF_rect.
unfold sumbool_rec.
unfold sumbool_rect.
intro x.
case x.
intros y prf prf1.
unfold ZFeq.
case (Z_lt_le_dec y (k + n)).
reflexivity.

intuition.
Qed.

Definition C_is_CMonoid (k n:Z)(H:(n>0)%Z)(H0:(k>=0)%Z):= 
(Build_is_CMonoid (C_as_CSemiGroup k n H H0)(C0 k n H H0)
(O_is_rht_unit_C k n H H0)(O_is_lft_unit_C k n H H0)).

Definition C_as_CMonoid ( k n:Z)(H:(n>0)%Z)(H0:(k>=0)%Z):=
(Build_CMonoid (C_as_CSemiGroup k n H H0)(C0 k n H H0)(C_is_CMonoid k n H H0)).

Definition c (k n:Z)(H:(n>0)%Z)(H0:(k>=0)%Z)(H1:(1<k+n)%Z):
            (C_as_CSetoid k n H H0).                                  
intros k n H H0 H1.
simpl.
apply Build_ZF with 1%Z.
exact H1.
intuition.
Defined.

Definition cm (k n:Z)(m:nat)(H:(n>0)%Z)(H0:(k>=0)%Z)(H1:((Z_of_nat m)<k+n)%Z):
              (C_as_CSetoid k n H H0).                                      
intros k n m H H0 H1.
simpl.
apply Build_ZF with m%Z.
exact H1.
intuition.
Defined.

Lemma c_plus: forall(k n:Z)(m:nat)(H:(n>0)%Z)(H0:((Z_of_nat (S m))<k+n)%Z)
                (H1:((Z_of_nat m)<k+n)%Z)(H2:(k>=0)%Z)(H3:(1<k+n)%Z),          ((C_plus_as_bin_fun k n H H2)(cm k n m H H2 H1)(c k n H H2 H3))[=]
(cm k n (S m) H H2 H0).
simpl.
unfold sumbool_rec.
unfold sumbool_rect.
unfold ZFeq.
intros k n m.
case (Z_lt_le_dec (Z_of_nat m + 1) (k + n)).
simpl.
intros H1 H2 H3 H4 H5 H6.
2:simpl.
apply succ_nat.

intros H1 H2 H3 H4 H5 H6.
cut (0<= ((Z_of_nat m) + 1 - k)%Z <n)%Z.
intro H7.
set (H8:=(Zmod_small n (Z_of_nat m + 1 - k)%Z H2 H7)).
rewrite H8.
replace (k + (Z_of_nat m + 1 - k))%Z with (Z_of_nat m + 1)%Z.
2:intuition.
intuition.
split.
intuition.
cut (Zpos (P_of_succ_nat m)=(Z_of_nat m +1)%Z).
intuition.
apply succ_nat.
Qed.


Lemma power_C_plus:
forall (k n:Z) (m:nat)(H:(n>0)%Z)(H0:(1<k+n)%Z)(H1:(k>=0)%Z),
  @power_CMonoid (C_as_CMonoid k n H H1)(c k n H H1 H0)(S m)[=] 
  (@power_CMonoid (C_as_CMonoid k n H H1)(c k n H H1 H0) m)[+](c k n H H1 H0).
intros k n m.
Opaque Zplus.
simpl.
unfold ZFeq.
unfold ZF_rec.
unfold ZF_rect.
unfold sumbool_rec.
unfold sumbool_rect.
intros H H0 H1.
case (@power_CMonoid (C_as_CMonoid k n H H1) (c k n H H1 H0) m).
intros a prf prf1.
case ( Z_lt_le_dec (1 + a) (k + n)).
simpl.
unfold sumbool_rec.
unfold sumbool_rect.
case (Z_lt_le_dec (a + 1) (k + n)).
intuition.
intros H2 H3.
cut (0<= (a+1-k)%Z<n)%Z.
intro H4.
set (H5:= (Zmod_small n (a+1-k)%Z H H4)).
rewrite H5.
intuition.

intuition.

unfold C_plus.
unfold ZF_rec.
unfold ZF_rect.
unfold sumbool_rec.
unfold sumbool_rect.
simpl.
case (Z_lt_le_dec (a + 1) (k + n)).
intuition.

replace (a+1 -k)%Z with (1+a-k)%Z.
reflexivity.
intuition.
Qed.

Lemma power_c:forall (m:nat)(k n:Z)(H:(n>0)%Z)(H0:(1<k+n)%Z)
  (H1:(m<k+n)%Z)(H2:(k>=0)%Z),
  @power_CMonoid (C_as_CMonoid k n H H2)(c k n H H2 H0) m [=]
  (cm k n m H H2 H1).
intros m k n.
induction m.
simpl.
reflexivity.

intros  H H0 H1 H6.
set (H2:=(power_C_plus k n m  H H0 H6)).
cut (m<k+n)%Z.
intro H4.
set (H3:=(c_plus k n m H H1 H4 H6 H0)).
apply eq_transitive with 
         (csbf_fun (C_as_CSetoid k n H H6) (C_as_CSetoid k n H H6)
         (C_as_CSetoid k n H H6) (C_plus_as_bin_fun k n H H6) 
         (cm k n m H H6 H4) (c k n H H6 H0)).
2:exact H3.
set (H5:= (IHm H H0 H4 H6)).
stepr (csbf_fun (C_as_CSetoid k n H H6) (C_as_CSetoid k n H H6) 
     (C_as_CSetoid k n H H6) (C_plus_as_bin_fun k n H H6) 
    (@power_CMonoid (C_as_CMonoid k n H H6) (c k n H H6 H0) m) (c k n H H6 H0)).
2:intuition.
intuition.
set (H3:= (lt_succ_Z_of_nat m k n)).
apply H3.
exact H1.
Qed.


Lemma cyclic_C:(forall (k n:Z)(H:(n>0)%Z)(H0:(k>=0)%Z), 
             cyclic (C_as_CMonoid k n H H0)):CProp.                  
intros k n H H0.
unfold cyclic.
case (Z_le_gt_dec (k+n) 1).
intro H1.
exists (C0 k n H H0).
intro m.
case m.
simpl.
unfold ZFeq.
intros m' Hprf Hprf1.
exists 1.
case (@power_CMonoid (C_as_CMonoid k n H H0) (C0 k n H H0) 1).
intros m'' H2 H5.
intuition.

intro H1.
cut (1< k+n)%Z.
2:auto with zarith.
intro H2.
exists (c k n H H0 H2).
intro m.
case m.
intros m'.
case m'.
intros prf prf1.
exists 0.
simpl.
reflexivity.

intros p prf prf1.
exists (nat_of_P p).
set (H4:= (power_c (nat_of_P p) k n  H H2)).
cut ((Z_of_nat (nat_of_P p) < k + n)%Z).
intro H5.
set (H6:= (H4 H5 H0)).
unfold cm in H6.
set (H7:=(inject_nat_convert p)).
generalize prf prf1.
rewrite<- H7.
intuition.

set (H7:=(inject_nat_convert p)).
generalize prf prf1.
rewrite<- H7.
intuition.

intros p prf prf0.
cut False.
intuition.
intuition.
Qed.

Definition to_C:
  forall (M:CMonoid)(u:M)(k l:nat)(H2:((Z_of_nat (l-k))>0)%Z)
  (H3:((Z_of_nat k)>=0)%Z),(is_generator M u)->
  (k<l and 
  (power_CMonoid u  k [=] power_CMonoid u l)
  and ((forall (k0 l0:nat), (k0<k or (k0=k and l0<l))-> 
  (power_CMonoid u k0 [#] power_CMonoid u l0))))->
  M -> (C_as_CMonoid (Z_of_nat k)(Z_of_nat (l-k)) H2 H3).
intros M u  k l  H2 H3 H H1 m1.
simpl.
generalize H1.
clear H1.
unfold is_generator in H.
elim (H m1).
simpl.
clear H.
intros n H H1.
(* Here: suppose n<l then n, else k+ (n-k) mod (l-k) *)
case (le_lt_dec l n).
intro H4.
apply Build_ZF with ((Z_of_nat k)+(Z_of_nat (n-k))mod (Z_of_nat (l-k)))%Z.
cut ((Z_of_nat (l-k)>0))%Z.
intro H6.
set (H5:= (Z_mod_lt (Z_of_nat (n-k))(Z_of_nat (l-k))H6)).
intuition.

intuition.

cut ((Z_of_nat k)>=0)%Z.
2:intuition.
cut ((Z_of_nat (l-k)>0))%Z.
intro H6.
set (H5:= (Z_mod_lt (Z_of_nat (n-k))(Z_of_nat (l-k))H6)).
intuition.

elim H1.
clear H1.
intros H1 H5.
set (H6:=inj_minus1 l k (lt_le_weak k l H1)).
intuition.

intro H4.
apply Build_ZF with (Z_of_nat n)%Z.
set (H5:=(inj_plus k (l-k))).
rewrite<- H5.
apply inj_lt.
intuition.
intuition.
Defined.

Lemma to_C_strext:
  forall (M:CMonoid)(u:M)(k l:nat)(H2:((Z_of_nat (l-k))>0)%Z)
  (H3:((Z_of_nat k)>=0)%Z)(H:(is_generator M u))(H1:(k<l and 
  (power_CMonoid u  k [=] power_CMonoid u l)
  and ((forall (k0 l0:nat), (k0<k or (k0=k and l0<l))-> 
  (power_CMonoid u  k0 [#] power_CMonoid u l0))))),
  (fun_strext (to_C M u  k l H2 H3 H H1)):CProp.
intros M u k l H2 H3 H H1.
unfold fun_strext.
simpl.
intros x y.
unfold ZFap.
unfold to_C.
unfold sigT_rec.
unfold sigT_rect.
(* generalize H1.*)
set (H99:= (power_k_n M u)).
(* generalize H99.
clear H99.
clear H1.*)
(* case H.
simpl.
clear H.*)
unfold is_generator in H.
(* intros H99.*)
case (H x).
intros n0 prfn0.
case (H y).
intros n1 prfn1.
case (le_lt_dec l n0).
case ( le_lt_dec l n1).
elim H1.
clear H1.
intros H1' H1.
intros grl1 grl0 H4.
cut (x[=](power_CMonoid u (k+(mod_nat (n0-k)(l-k) H2)))).
intro H5.
csetoid_rewrite H5.
cut (y[=](power_CMonoid u (k+(mod_nat (n1-k)(l-k) H2)))).
intro H6.
csetoid_rewrite H6.
elim H1.
clear H1.
intros H1 H1''.
set (p:=(k + mod_nat (n0 - k) (l - k) H2)).
set (q:=(k + mod_nat (n1 - k) (l - k) H2)).
cut (p<>q).
intro H7.
cut ((p<q) or (q<p)).
intro H8.
elim H8.
clear H8.
intro H8.
cut (p+(l-q)<l).
intro H9.
cut (k<k or (k=k and (p+(l-q))<l)). 
intro H10.
set (H11:=( H1'' k (p+(l-q)) H10)).
generalize H11.
csetoid_rewrite H1.
clear H11.
intro H11.
cut (power_CMonoid u p[#]power_CMonoid u q or power_CMonoid u (l-q)[#]power_CMonoid u (l-q)).
intro H12.
elim H12.
tauto.
clear H12.
intro H12.
set (H15:=(ap_irreflexive_unfolded M (power_CMonoid u (l - q)))).
unfold Not in H15.
intuition.

apply bin_op_strext_unfolded with (@csg_op M).

set (H14:= (power_plus M u p (l-q))).
csetoid_rewrite_rev H14.
set (H15:=(power_plus M u q (l-q))).
csetoid_rewrite_rev H15.
replace (q+(l-q)) with l.
apply ap_symmetric_unfolded.
exact H11.

cut (Z_of_nat l - Z_of_nat k > 0)%Z.
2:intuition.
intro H17.
set (H16:=(Z_mod_lt (n1-k) (l-k) H17)).
unfold q.
set (H18:= (mod_nat_correct (n1-k) (l-k) H2)).

3:intuition.
apply surj_eq.
rewrite (inj_plus (k + mod_nat (n1 - k) (l - k) H2)  (l - (k + mod_nat (n1 - k) (l - k) H2))).
cut ((k + mod_nat (n1 - k) (l - k) H2)<=l).
intro H19.
rewrite (inj_minus1 l (k + mod_nat (n1 - k) (l - k) H2) H19).
intuition.

apply surj_le.
rewrite (inj_plus k ( mod_nat (n1 - k) (l - k) H2)).
rewrite<- H18.
elim H16.
clear H16.
intros H16 H16'.
cut (k<= n1).
2:intuition.
intro H19.
rewrite (inj_minus1 n1 k H19).
cut (k<=l).
2:intuition.
intro H20.
rewrite (inj_minus1 l k H20).
intuition.

intuition.
apply lt_lt_minus.
2:intuition.
3:apply not_or.
3:exact H7.
unfold q.
set (H9:= (mod_nat_correct (n1-k)(l-k) H2)).
apply surj_lt.
rewrite (inj_plus k ( mod_nat (n1 - k) (l - k) H2)).
rewrite<- H9.
cut ((l-k)>0)%Z.
intro H11.
set (H10:=(Z_mod_lt (n1-k) (l-k) H11)).
2:intuition.
cut (k<= n1).
intro H12.
2:intuition.
rewrite (inj_minus1 n1 k H12).
cut (k<= l).
intro H13.
2:intuition.
rewrite (inj_minus1 l k H13).
intuition.

clear H8.
intro H8.
cut (q+(l-p)<l).
intro H9.
cut (k<k or (k=k and (q+(l-p))<l)). 
intro H10.
set (H11:=( H1'' k (q+(l-p)) H10)).
generalize H11.
csetoid_rewrite H1.
clear H11.
intro H11.
cut (power_CMonoid u p[#]power_CMonoid u q or power_CMonoid u (l-p)[#]power_CMonoid u (l-p)).
intro H12.
elim H12.
tauto.
clear H12.
intro H12.
set (H15:=(ap_irreflexive_unfolded M (power_CMonoid u (l - p)))).
unfold Not in H15.
intuition.

apply bin_op_strext_unfolded with (@csg_op M).

set (H14:= (power_plus M u q (l-p))).
csetoid_rewrite_rev H14.
set (H15:=(power_plus M u p (l-p))).
csetoid_rewrite_rev H15.
replace (p+(l-p)) with l.
apply ap_symmetric_unfolded.
apply ap_symmetric_unfolded.
exact H11.

cut (Z_of_nat l - Z_of_nat k > 0)%Z.
2:intuition.
intro H17.
set (H16:=(Z_mod_lt (n0-k) (l-k) H17)).
unfold p.
set (H18:= (mod_nat_correct (n0-k) (l-k) H2)).

apply surj_eq.
rewrite (inj_plus (k + mod_nat (n0 - k) (l - k) H2)  (l - (k + mod_nat (n0 - k) (l - k) H2))).
cut ((k + mod_nat (n0 - k) (l - k) H2)<=l).
intro H19.
rewrite (inj_minus1 l (k + mod_nat (n0 - k) (l - k) H2) H19).
intuition.

apply surj_le.
rewrite (inj_plus k ( mod_nat (n0 - k) (l - k) H2)).
rewrite<- H18.
elim H16.
clear H16.
intros H16 H16'.
cut (k<= n0).
2:intuition.
intro H19.
rewrite (inj_minus1 n0 k H19).
cut (k<=l).
2:intuition.
intro H20.
rewrite (inj_minus1 l k H20).
intuition.

intuition.
apply lt_lt_minus.
2:intuition.
unfold p.
set (H9:= (mod_nat_correct (n0-k)(l-k) H2)).
apply surj_lt.
rewrite (inj_plus k ( mod_nat (n0 - k) (l - k) H2)).
rewrite<- H9.
cut ((l-k)>0)%Z.
intro H11.
set (H10:=(Z_mod_lt (n0-k) (l-k) H11)).
2:intuition.
cut (k<= n0).
intro H12.
2:intuition.
rewrite (inj_minus1 n0 k H12).
cut (k<= l).
intro H13.
2:intuition.
rewrite (inj_minus1 l k H13).
intuition.

apply surj_not.
unfold p.
unfold q.
rewrite (inj_plus k ( mod_nat (n0 - k) (l - k) H2)).
rewrite (inj_plus k ( mod_nat (n1 - k) (l - k) H2)).
rewrite<- (mod_nat_correct (n0-k)(l-k) H2).
rewrite<- (mod_nat_correct (n1-k)(l-k) H2).
intuition.

csetoid_rewrite_rev prfn1.
apply H99.
unfold is_generator.
exact H.
intuition.
intuition.

csetoid_rewrite_rev prfn0.
apply H99.
unfold is_generator.
exact H.
intuition.
intuition.

intros H4 H5 H6.
elim H1.
clear H1.
intros H1' H1.
cut (x[=](power_CMonoid u (k+(mod_nat (n0-k)(l-k) H2)))).
intro H7.
csetoid_rewrite H7.
csetoid_rewrite_rev prfn1.
elim H1.
clear H1.
intros H1 H1''.
set (p:=n1).
set (q:=(k + mod_nat (n0 - k) (l - k) H2)).
cut ((p<q) or (q<p)).
intro H8.
elim H8.
clear H8.
intro H8.
cut (p+(l-q)<l).
intro H9.
cut (k<k or (k=k and (p+(l-q))<l)). 
intro H10.
set (H11:=( H1'' k (p+(l-q)) H10)).
generalize H11.
csetoid_rewrite H1.
clear H11.
intro H11.
cut (power_CMonoid u p[#]power_CMonoid u q or power_CMonoid u (l-q)[#]power_CMonoid u (l-q)).
intro H12.
elim H12.
apply ap_symmetric_unfolded.
clear H12.
intro H12.
set (H15:=(ap_irreflexive_unfolded M (power_CMonoid u (l - q)))).
unfold Not in H15.
intuition.

apply bin_op_strext_unfolded with (@csg_op M).

set (H14:= (power_plus M u p (l-q))).
csetoid_rewrite_rev H14.
set (H15:=(power_plus M u q (l-q))).
csetoid_rewrite_rev H15.
replace (q+(l-q)) with l.
apply ap_symmetric_unfolded.
exact H11.

cut (Z_of_nat l - Z_of_nat k > 0)%Z.
2:intuition.
intro H17.
set (H16:=(Z_mod_lt (n0-k) (l-k) H17)).
unfold q.
set (H18:= (mod_nat_correct (n0-k) (l-k) H2)).

3:intuition.
apply surj_eq.
rewrite (inj_plus (k + mod_nat (n0 - k) (l - k) H2)  (l - (k + mod_nat (n0 - k) (l - k) H2))).
cut ((k + mod_nat (n0 - k) (l - k) H2)<=l).
intro H19.
rewrite (inj_minus1 l (k + mod_nat (n0 - k) (l - k) H2) H19).
intuition.

apply surj_le.
rewrite (inj_plus k ( mod_nat (n0 - k) (l - k) H2)).
rewrite<- H18.
elim H16.
clear H16.
intros H16 H16'.
cut (k<= n0).
2:intuition.
intro H19.
rewrite (inj_minus1 n0 k H19).
cut (k<=l).
2:intuition.
intro H20.
rewrite (inj_minus1 l k H20).
intuition.

intuition.
apply lt_lt_minus.
unfold q.
set (H9:= (mod_nat_correct (n0-k)(l-k) H2)).
apply surj_lt.
rewrite (inj_plus k ( mod_nat (n0 - k) (l - k) H2)).
rewrite<- H9.
cut ((l-k)>0)%Z.
intro H11.
set (H10:=(Z_mod_lt (n0-k) (l-k) H11)).
2:intuition.
cut (k<= n0).
intro H12.
2:intuition.
rewrite (inj_minus1 n0 k H12).
cut (k<= l).
intro H13.
2:intuition.
rewrite (inj_minus1 l k H13).
intuition.
exact H8.

clear H8.
intro H8.
cut (q+(l-p)<l).
intro H9.
cut (k<k or (k=k and (q+(l-p))<l)). 
intro H10.
set (H11:=( H1'' k (q+(l-p)) H10)).
generalize H11.
csetoid_rewrite H1.
clear H11.
intro H11.
cut (power_CMonoid u p[#]power_CMonoid u q or power_CMonoid u (l-p)[#]power_CMonoid  u (l-p)).
intro H12.
elim H12.
apply ap_symmetric_unfolded.
clear H12.
intro H12.
set (H15:=(ap_irreflexive_unfolded M (power_CMonoid u (l - p)))).
unfold Not in H15.
intuition.

apply bin_op_strext_unfolded with (@csg_op M).

set (H14:= (power_plus M u q (l-p))).
csetoid_rewrite_rev H14.
set (H15:=(power_plus M u p (l-p))).
csetoid_rewrite_rev H15.
replace (p+(l-p)) with l.
apply ap_symmetric_unfolded.
apply ap_symmetric_unfolded.
exact H11.

apply surj_eq.
rewrite (inj_plus p (l-p)).
unfold p.
cut (n1<= l).
intro H16.
2:intuition.
rewrite (inj_minus1 l n1 H16).
intuition.

intuition.

apply lt_lt_minus.
2:intuition.
unfold p.
exact H4.

apply not_or.
apply surj_not.
unfold p.
unfold q.
rewrite (inj_plus k ( mod_nat (n0 - k) (l - k) H2)).
rewrite<- (mod_nat_correct (n0-k)(l-k) H2).
intuition.

csetoid_rewrite_rev prfn0.
apply H99.
unfold is_generator.
exact H.
intuition.
intuition.

case (le_lt_dec l n1).
intros H4 H5 H6.
elim H1.
clear H1.
intros H1' H1.
cut (y[=](power_CMonoid u (k+(mod_nat (n1-k)(l-k) H2)))).
intro H7.
csetoid_rewrite H7.
csetoid_rewrite_rev prfn0.
elim H1.
clear H1.
intros H1 H1''.
set (p:=n0).
set (q:=(k + mod_nat (n1 - k) (l - k) H2)).
cut ((p<q) or (q<p)).
intro H8.
elim H8.
clear H8.
intro H8.
cut (p+(l-q)<l).
intro H9.
cut (k<k or (k=k and (p+(l-q))<l)). 
intro H10.
set (H11:=( H1'' k (p+(l-q)) H10)).
generalize H11.
csetoid_rewrite H1.
clear H11.
intro H11.
cut ( power_CMonoid u p[#]power_CMonoid u q or power_CMonoid u (l-q)[#]power_CMonoid u (l-q)).
intro H12.
elim H12.
tauto.
clear H12.
intro H12.
set (H15:=(ap_irreflexive_unfolded M (power_CMonoid u (l - q)))).
unfold Not in H15.
intuition.

apply bin_op_strext_unfolded with (@csg_op M).

set (H14:= (power_plus M u p (l-q))).
csetoid_rewrite_rev H14.
set (H15:=(power_plus M u q (l-q))).
csetoid_rewrite_rev H15.
replace (q+(l-q)) with l.
apply ap_symmetric_unfolded.
exact H11.

cut (Z_of_nat l - Z_of_nat k > 0)%Z.
2:intuition.
intro H17.
set (H16:=(Z_mod_lt (n1-k) (l-k) H17)).
unfold q.
set (H18:= (mod_nat_correct (n1-k) (l-k) H2)).

apply surj_eq.
rewrite (inj_plus (k + mod_nat (n1 - k) (l - k) H2)  (l - (k + mod_nat (n1 - k) (l - k) H2))).
cut ((k + mod_nat (n1 - k) (l - k) H2)<=l).
intro H19.
rewrite (inj_minus1 l (k + mod_nat (n1 - k) (l - k) H2) H19).
intuition.

apply surj_le.
rewrite (inj_plus k ( mod_nat (n1 - k) (l - k) H2)).
rewrite<- H18.
elim H16.
clear H16.
intros H16 H16'.
cut (k<= n1).
2:intuition.
intro H19.
rewrite (inj_minus1 n1 k H19).
cut (k<=l).
2:intuition.
intro H20.
rewrite (inj_minus1 l k H20).
intuition.

intuition.
apply lt_lt_minus.
unfold q.
set (H9:= (mod_nat_correct (n1-k)(l-k) H2)).
apply surj_lt.
rewrite (inj_plus k ( mod_nat (n1 - k) (l - k) H2)).
rewrite<- H9.
cut ((l-k)>0)%Z.
intro H11.
set (H10:=(Z_mod_lt (n1-k) (l-k) H11)).
2:intuition.
cut (k<= n1).
intro H12.
2:intuition.
rewrite (inj_minus1 n1 k H12).
cut (k<= l).
intro H13.
2:intuition.
rewrite (inj_minus1 l k H13).
intuition.
exact H8.

clear H8.
intro H8.
cut (q+(l-p)<l).
intro H9.
cut (k<k or (k=k and (q+(l-p))<l)). 
intro H10.
set (H11:=( H1'' k (q+(l-p)) H10)).
generalize H11.
csetoid_rewrite H1.
clear H11.
intro H11.
cut ( power_CMonoid u p[#]power_CMonoid u q or power_CMonoid u (l-p)[#]power_CMonoid u (l-p)).
intro H12.
elim H12.
tauto.
clear H12.
intro H12.
set (H15:=(ap_irreflexive_unfolded M (power_CMonoid u (l - p)))).
unfold Not in H15.
intuition.

apply bin_op_strext_unfolded with (@csg_op M).

set (H14:= (power_plus M u q (l-p))).
csetoid_rewrite_rev H14.
set (H15:=(power_plus M u p (l-p))).
csetoid_rewrite_rev H15.
replace (p+(l-p)) with l.
apply ap_symmetric_unfolded.
apply ap_symmetric_unfolded.
exact H11.

apply surj_eq.
rewrite (inj_plus p (l-p)).
unfold p.
cut (n0<= l).
intro H16.
2:intuition.
rewrite (inj_minus1 l n0 H16).
intuition.

intuition.

apply lt_lt_minus.
2:intuition.
unfold p.
exact H5.

apply not_or.
apply surj_not.
unfold p.
unfold q.
rewrite (inj_plus k ( mod_nat (n1 - k) (l - k) H2)).
rewrite<- (mod_nat_correct (n1-k)(l-k) H2).
intuition.

csetoid_rewrite_rev prfn1.
apply H99.
unfold is_generator.
exact H.
intuition.
intuition.

intros H4 H5 H6.
elim H1.
clear H1.
intros H1' H1.
csetoid_rewrite_rev prfn1.
csetoid_rewrite_rev prfn0.
elim H1.
clear H1.
intros H1 H1''.
set (p:=n1).
set (q:= n0).
cut ((p<q) or (q<p)).
intro H8.
elim H8.
clear H8.
intro H8.
cut (p+(l-q)<l).
intro H9.
cut (k<k or (k=k and (p+(l-q))<l)). 
intro H10.
set (H11:=( H1'' k (p+(l-q)) H10)).
generalize H11.
csetoid_rewrite H1.
clear H11.
intro H11.
cut ( power_CMonoid u p[#]power_CMonoid u q or power_CMonoid u (l-q)[#]power_CMonoid u (l-q)).
intro H12.
elim H12.
apply ap_symmetric_unfolded.
clear H12.
intro H12.
set (H15:=(ap_irreflexive_unfolded M (power_CMonoid u (l - q)))).
unfold Not in H15.
intuition.

apply bin_op_strext_unfolded with (@csg_op M).

set (H14:= (power_plus M u p (l-q))).
csetoid_rewrite_rev H14.
set (H15:=(power_plus M u q (l-q))).
csetoid_rewrite_rev H15.
replace (q+(l-q)) with l.
apply ap_symmetric_unfolded.
exact H11.


apply surj_eq.
rewrite (inj_plus q  (l - q)).
cut (q<=l).
intro H19.
rewrite (inj_minus1 l q  H19).
intuition.

intuition.

intuition.

apply lt_lt_minus.
unfold q.
intuition.

exact H8.

clear H8.
intro H8.
cut (q+(l-p)<l).
intro H9.
cut (k<k or (k=k and (q+(l-p))<l)). 
intro H10.
set (H11:=( H1'' k (q+(l-p)) H10)).
generalize H11.
csetoid_rewrite H1.
clear H11.
intro H11.
cut ( power_CMonoid u p[#]power_CMonoid u q or power_CMonoid u (l-p)[#]power_CMonoid u (l-p)).
intro H12.
elim H12.
apply ap_symmetric_unfolded.
clear H12.
intro H12.
set (H15:=(ap_irreflexive_unfolded M (power_CMonoid u (l - p)))).
unfold Not in H15.
intuition.

apply bin_op_strext_unfolded with (@csg_op M).

set (H14:= (power_plus M u q (l-p))).
csetoid_rewrite_rev H14.
set (H15:=(power_plus M u p (l-p))).
csetoid_rewrite_rev H15.
replace (p+(l-p)) with l.
apply ap_symmetric_unfolded.
apply ap_symmetric_unfolded.
exact H11.

apply surj_eq.
rewrite (inj_plus p (l-p)).
unfold p.
cut (n1<= l).
intro H16.
2:intuition.
rewrite (inj_minus1 l n1 H16).
intuition.

intuition.

apply lt_lt_minus.
2:intuition.
unfold p.
exact H4.

apply not_or.
apply surj_not.
unfold p.
unfold q.
exact H6.
Qed.

Definition to_C_as_csf (M:CMonoid)(u:M)(k l:nat)
(H2: ((Z_of_nat (l-k))>0)%Z)(H3:((Z_of_nat k)>=0)%Z)(H:(is_generator M u))
(H1:(k<l and 
(power_CMonoid u  k [=] power_CMonoid u l)
and ((forall (k0 l0:nat), (k0<k or (k0=k and l0<l))-> 
(power_CMonoid u k0 [#] power_CMonoid u l0)))))
:=
(Build_CSetoid_fun M  (C_as_CMonoid k (l - k)%nat H2 H3)
(to_C M u  k l H2 H3 H H1) (to_C_strext M u k l H2 H3 H H1)).

Lemma mod_nat_pi:forall (k l i:nat)(H:(k>0)%Z)(H0:(l>0)%Z),
k=l -> (mod_nat i k H)=(mod_nat i l H0).
intros k l i H H0 H1.
unfold mod_nat.
unfold COr_rec.
unfold COr_rect.
case (Zmod_pos i k H).
case (Zmod_pos i l H0).
reflexivity.

simpl.
unfold sigT_rec.
unfold sigT_rect.
intros H2.
elim H2.
clear H2.
intros p H2.
intro H3.
rewrite H1 in H3.
rewrite H2 in H3.
apply surj_eq.
rewrite (convert_is_POS p).
intuition.

unfold sigT_rec.
unfold sigT_rect.
intro H2.
elim H2.
clear H2.
intros p H2.
case (Zmod_pos i l H0).
intro H3.
rewrite H1 in H2.
rewrite H2 in H3.
apply surj_eq.
rewrite (convert_is_POS p).
exact H3.

intro H3.
elim H3.
clear H3.
intros q H3.
rewrite<- H1 in H3.
rewrite H2 in H3.
apply surj_eq.
rewrite (convert_is_POS p).
rewrite (convert_is_POS q).
exact H3.
Qed.

Section Char.
Variable M:CMonoid.
Variable k l:nat.
Variable H3: k>=0.
Variable H5: l-k>0.
Variable c0: cs_crr (csg_crr (cm_crr M)).
Variable power_mod:forall (k l n : nat) (H2 : (Z_of_nat (l - k) > 0)%Z),
        k < n ->
        k < l
        and power_CMonoid c0 k[=]power_CMonoid c0 l
            and (forall k0 l0 : nat,
                 k0 < k or k0 = k and l0 < l ->
                 power_CMonoid c0 k0[#]power_CMonoid c0 l0) ->
        power_CMonoid c0 n[=]
        power_CMonoid c0 (k + mod_nat (n - k) (l - k) H2).
Variable w_inj:forall k l a b : nat,
        a < l ->
        b < l ->
        k < l
        and power_CMonoid c0 k[=]power_CMonoid c0 l
            and (forall k0 l0 : nat,
                 k0 < k or k0 = k and l0 < l ->
                 power_CMonoid c0 k0[#]power_CMonoid c0 l0) ->
        power_CMonoid c0 a[=]power_CMonoid c0 b -> a = b.
Variable smallest: k < l
        and power_CMonoid c0 k[=]power_CMonoid c0 l
            and (forall k0 l0 : nat,
                 k0 < k or k0 = k and l0 < l ->
                 power_CMonoid c0 k0[#]power_CMonoid c0 l0).
Variable n0 n1 n2:nat.
Variable a b:cs_crr (csg_crr (cm_crr M)).
Variable Hn0:power_CMonoid c0 n0[=]
        csbf_fun (csg_crr (cm_crr M)) (csg_crr (cm_crr M))
          (csg_crr (cm_crr M)) (csg_op (c:=cm_crr M)) a b.
Variable Hn1:power_CMonoid c0 n1[=]a.
Variable Hn2: power_CMonoid c0 n2[=]b.


Lemma Char1:(k + (n1 - k)%nat mod (l - k)%nat + (k + (n2 - k)%nat mod (l - k)%nat) <
       k + (l - k)%nat)%Z->l<=n1 -> l<= n0 -> l<=n2 ->
 (k + (n1 - k)%nat mod (l - k)%nat + (k + (n2 - k)%nat mod (l - k)%nat))%Z =
   (k + (n0 - k)%nat mod (l - k)%nat)%Z.
intros z.
intros.
set (H11:= (power_plus M c0 n1 n2 )).
cut ( power_CMonoid c0 (n1 + n2)[=]power_CMonoid c0 n0).
2:csetoid_rewrite_cxt Hn1 H11.
2:csetoid_rewrite_cxt Hn2 H11.
2:csetoid_rewrite_cxt_rev Hn0 H11.
2: exact H11.
clear H11.
intro H11.
cut (Z_of_nat (l - k) > 0)%Z.
intro H13.
set (H12:=(mod_nat_correct (n1-k)(l-k) H13)).
rewrite H12.
set (H14:=(mod_nat_correct (n0-k)(l-k) H13)).
rewrite H14.
rewrite<- (inj_plus k (mod_nat (n1 - k) (l - k) H13)).
set (H15:=(mod_nat_correct (n2-k)(l-k) H13)).
rewrite H15.
rewrite<- (inj_plus k (mod_nat (n2 - k) (l - k) H13)).
rewrite<- (inj_plus (k + mod_nat (n1 - k) (l - k) H13)
           (k + mod_nat (n2 - k) (l - k) H13)). 
rewrite<- (inj_plus k (mod_nat (n0 - k) (l - k) H13)).
apply inj_eq.
apply w_inj with k l.
apply surj_lt.
rewrite (inj_plus (k + mod_nat (n1 - k) (l - k) H13)
         (k + mod_nat (n2 - k) (l - k) H13)).
rewrite (inj_plus k ( mod_nat (n1 - k) (l - k) H13)).
rewrite (inj_plus k (mod_nat (n2 - k) (l - k) H13)).
rewrite<- H12.
rewrite<- H15.
replace (Z_of_nat l) with (Z_of_nat k + Z_of_nat (l - k))%Z.
exact z.
cut (k<=l).
intro H16.
rewrite (inj_minus1 l k H16).
intuition.
intuition.

2:intuition.


apply surj_lt.
rewrite (inj_plus k (mod_nat (n0 - k) (l - k) H13)).
rewrite<- H14.
set (H16:=(Z_mod_lt (Z_of_nat (n0-k)) (Z_of_nat(l-k))H13)).
elim H16.
clear H16.
intros H16 H17.
cut ( Z_of_nat (n0 - k) mod Z_of_nat (l - k) < Z_of_nat l%Z -(Z_of_nat k))%Z.
intuition.
cut (k<=l).
intro H18.
rewrite<- (inj_minus1 l k H18).
exact H17.

intuition.

cut (k<n0).
intro H16.
cut ( power_CMonoid c0
     (k + mod_nat (n1 - k) (l - k) H13 + (k + mod_nat (n2 - k) (l - k) H13))[=]
   csbf_fun (csg_crr (cm_crr M)) (csg_crr (cm_crr M)) 
     (csg_crr (cm_crr M)) (csg_op (c:=cm_crr M)) (power_CMonoid c0 n1)
     (power_CMonoid c0 n2)).
csetoid_rewrite_rev (power_mod k l n0 H13 H16 smallest).
csetoid_rewrite_rev H11.
csetoid_rewrite (power_plus M c0 n1 n2).
tauto.
cut (k<n1).
intro H17.
csetoid_rewrite (power_mod k l n1 H13 H17 smallest).
cut (k<n2).
intro H18.
csetoid_rewrite (power_mod k l n2 H13 H18 smallest).
csetoid_rewrite_rev (power_plus M c0 (k + mod_nat (n1 - k) (l - k) H13)
                          (k + mod_nat (n2 - k) (l - k) H13)).          
apply eq_reflexive.
intuition.
intuition.
intuition.
rewrite (inj_minus1 l k).
intuition.
intuition.
Qed.


Lemma Char2:(Z_of_nat k + Z_of_nat (l - k) <=
       Z_of_nat k + Z_of_nat (n1 - k) mod Z_of_nat (l - k) +
       (Z_of_nat k + Z_of_nat (n2 - k) mod Z_of_nat (l - k)))%Z ->
l<=n1-> l<=n2 -> l<=n0->
(Z_of_nat k +
    (Z_of_nat k + Z_of_nat (n1 - k) mod Z_of_nat (l - k) +
     (Z_of_nat k + Z_of_nat (n2 - k) mod Z_of_nat (l - k)) - 
     Z_of_nat k) mod Z_of_nat (l - k))%Z =
   (Z_of_nat k + Z_of_nat (n0 - k) mod Z_of_nat (l - k))%Z.
intro z.
intros.
set (H11:= (power_plus M c0 n1 n2 )).
csetoid_rewrite_cxt Hn1 H11.
csetoid_rewrite_cxt Hn2 H11.
csetoid_rewrite_cxt_rev Hn0 H11.
simpl.
cut (Z_of_nat (l - k) > 0)%Z.
intro H13.
set (H12:=(mod_nat_correct (n1-k)(l-k) H13)).
rewrite H12.
set (H14:=(mod_nat_correct (n0-k)(l-k) H13)).
rewrite H14.
rewrite<- (inj_plus k (mod_nat (n1 - k) (l - k) H13)).
set (H15:=(mod_nat_correct (n2-k)(l-k) H13)).
rewrite H15.
rewrite<- (inj_plus k (mod_nat (n2 - k) (l - k) H13)).
rewrite<- (inj_plus (k + mod_nat (n1 - k) (l - k) H13)
           (k + mod_nat (n2 - k) (l - k) H13)). 
rewrite<- (inj_plus k (mod_nat (n0 - k) (l - k) H13)).
rewrite<- (inj_minus1 (k + mod_nat (n1 - k) (l - k) H13 + (k + mod_nat (n2 - k) (l - k) H13)) k).
rewrite (mod_nat_correct (k + mod_nat (n1 - k) (l - k) H13 + (k + mod_nat (n2 - k) (l - k) H13) -
       k) (l-k) H13).
rewrite<- (inj_plus k (mod_nat
         (k + mod_nat (n1 - k) (l - k) H13 +
          (k + mod_nat (n2 - k) (l - k) H13) - k) (l - k) H13)).
2:intuition.
2:intuition.
apply inj_eq.
apply w_inj with k l.
apply surj_lt.
rewrite (inj_plus k  (mod_nat
         (k + mod_nat (n1 - k) (l - k) H13 +
          (k + mod_nat (n2 - k) (l - k) H13) - k) (l - k) H13)).
rewrite<- (mod_nat_correct (k + mod_nat (n1 - k) (l - k) H13 +
          (k + mod_nat (n2 - k) (l - k) H13) - k) (l - k) H13).
set (H16:=(Z_mod_lt (Z_of_nat ((k + mod_nat (n1 - k) (l - k) H13 + (k + mod_nat (n2 - k) (l - k) H13) -
       k))) (Z_of_nat(l-k))H13)).
elim H16.
clear H16.
intros H16 H17.
cut ( Z_of_nat ((k + mod_nat (n1 - k) (l - k) H13 + (k + mod_nat (n2 - k) (l - k) H13) -
       k)) mod Z_of_nat (l - k) < Z_of_nat l%Z -(Z_of_nat k))%Z.
intuition.
cut (k<=l).
intro H18.
rewrite<- (inj_minus1 l k H18).
exact H17.

intuition.

apply surj_lt.
rewrite (inj_plus k (mod_nat (n0-k) (l-k) H13)).
rewrite<- H14.
cut (Z_of_nat l - Z_of_nat k > 0)%Z.
intro H17.
set (H16:= (Z_mod_lt (n0-k) (l-k) H17)).
rewrite (inj_minus1 n0 k).
rewrite (inj_minus1 l k).
intuition.
intuition.
intuition.
intuition.
exact smallest.

cut (k<(k + mod_nat (n1 - k) (l - k) H13 +
         (k + mod_nat (n2 - k) (l - k) H13))).
intro H16.
csetoid_rewrite_rev (power_mod k l (k + mod_nat (n1 - k) (l - k) H13 +
         (k + mod_nat (n2 - k) (l - k) H13)) H13 H16 smallest).

cut (k<n0).
intro H17.
csetoid_rewrite_rev (power_mod k l n0 H13 H17 smallest).
csetoid_rewrite_rev H11.
csetoid_rewrite (power_plus M c0 n1 n2).
cut (k<n1).
intro H18.
csetoid_rewrite (power_mod k l n1 H13 H18 smallest).
cut (k<n2).
intro H19.
csetoid_rewrite (power_mod k l n2 H13 H19 smallest).
csetoid_rewrite_rev (power_plus M c0 (k + mod_nat (n1 - k) (l - k) H13)
                          (k + mod_nat (n2 - k) (l - k) H13)).          
apply eq_reflexive.
intuition.
intuition.
intuition.
intuition.
rewrite (inj_minus1 l k).
intuition.
intuition.
Qed.

Lemma Char3:(Z_of_nat k + Z_of_nat (n1 - k) mod Z_of_nat (l - k) + Z_of_nat n2 <
    Z_of_nat k + Z_of_nat (l - k))%Z ->
   n2 < l ->
   l <= n1 ->
   l <= n0 ->
   (Z_of_nat k + Z_of_nat (n1 - k) mod Z_of_nat (l - k) + Z_of_nat n2)%Z =
   (Z_of_nat k + Z_of_nat (n0 - k) mod Z_of_nat (l - k))%Z.
intros.
set (H11:= (power_plus M c0 n1 n2 )).
csetoid_rewrite_cxt Hn1 H11.
csetoid_rewrite_cxt Hn2 H11.
csetoid_rewrite_cxt_rev Hn0 H11.
simpl.
cut (Z_of_nat (l - k) > 0)%Z.
intro H13.
set (H12:=(mod_nat_correct (n1-k)(l-k) H13)).
rewrite H12.
set (H14:=(mod_nat_correct (n0-k)(l-k) H13)).
rewrite H14.
rewrite<- (inj_plus k (mod_nat (n1 - k) (l - k) H13)).
rewrite<- (inj_plus k (mod_nat (n0 - k) (l - k) H13)).
rewrite<- (inj_plus (k + mod_nat (n1 - k) (l - k) H13) n2).
apply inj_eq.
apply w_inj with k l.
apply surj_lt.
rewrite (inj_plus (k + mod_nat (n1 - k) (l - k) H13) n2).
rewrite (inj_plus k ( mod_nat (n1 - k) (l - k) H13)).
rewrite<- H12.
set (H16:=(Z_mod_lt (Z_of_nat (n1-k)) (Z_of_nat(l-k))H13)).
elim H16.
clear H16.
intros H16 H17.
cut ( Z_of_nat (n1 - k) mod Z_of_nat (l - k) + Z_of_nat n2 <
    Z_of_nat l - Z_of_nat k)%Z.
intuition.
cut (k<=l).
intro H18.
rewrite<- (inj_minus1 l k H18).
intuition.
intuition.

apply surj_lt.
rewrite (inj_plus k ( mod_nat (n0 - k) (l - k) H13)).
rewrite<- H14.
cut (Z_of_nat l - Z_of_nat k > 0)%Z.
intro H16.
set (H15:=(Z_mod_lt (n0-k)(l-k) H16)).
cut (Z_of_nat (n0 - k) mod Z_of_nat (l - k) < Z_of_nat l- Z_of_nat k)%Z.
intuition.
cut (k<=l).
intro H18.
cut (k<=n0).
intro H19.
rewrite (inj_minus1 l k H18).
rewrite (inj_minus1 n0 k H19).
intuition.
intuition.
intuition.
intuition.

exact smallest.

cut (k<n0).
intro H16.
csetoid_rewrite_rev (power_mod k l n0 H13 H16 smallest).
csetoid_rewrite_rev H11.
csetoid_rewrite (power_plus M c0 n1 n2).
cut (k<n1).
intro H17.
csetoid_rewrite (power_mod k l n1 H13 H17 smallest).
csetoid_rewrite_rev (power_plus M c0 (k + mod_nat (n1 - k) (l - k) H13)
                          n2).          
apply eq_reflexive.
intuition.
intuition.
intuition.
rewrite (inj_minus1 l k).
intuition.
intuition.
Qed.

Lemma Char4:(Z_of_nat k + Z_of_nat (l - k) <=
    Z_of_nat k + Z_of_nat (n1 - k) mod Z_of_nat (l - k) + Z_of_nat n2)%Z ->
   n2 < l ->
   l <= n1 ->
   l <= n0 ->
   (Z_of_nat k +
    (Z_of_nat k + Z_of_nat (n1 - k) mod Z_of_nat (l - k) + Z_of_nat n2 -
     Z_of_nat k) mod Z_of_nat (l - k))%Z =
   (Z_of_nat k + Z_of_nat (n0 - k) mod Z_of_nat (l - k))%Z.
intros.
set (H11:= (power_plus M c0 n1 n2 )).
csetoid_rewrite_cxt Hn1 H11.
csetoid_rewrite_cxt Hn2 H11.
csetoid_rewrite_cxt_rev Hn0 H11.
simpl.
cut (Z_of_nat (l - k) > 0)%Z.
intro H13.
set (H12:=(mod_nat_correct (n1-k)(l-k) H13)).
rewrite H12.
set (H14:=(mod_nat_correct (n0-k)(l-k) H13)).
rewrite H14.
rewrite<- (inj_plus k (mod_nat (n1 - k) (l - k) H13)).
rewrite<- (inj_plus (k + mod_nat (n1 - k) (l - k) H13)
           n2). 
rewrite<- (inj_plus k (mod_nat (n0 - k) (l - k) H13)).
rewrite<- (inj_minus1 (k + mod_nat (n1 - k) (l - k) H13 + n2)  k).
rewrite (mod_nat_correct (k + mod_nat (n1 - k) (l - k) H13 + n2 -
       k) (l-k) H13).
rewrite<- (inj_plus k (mod_nat (k + mod_nat (n1 - k) (l - k) H13 + n2 - k) (l - k) H13)).
2:intuition.
2:intuition.
apply inj_eq.
apply w_inj with k l.
apply surj_lt.
rewrite (inj_plus k  (mod_nat
         (k + mod_nat (n1 - k) (l - k) H13 +
          n2 - k )(l - k) H13)).
rewrite<- (mod_nat_correct (k + mod_nat (n1 - k) (l - k) H13 +
          n2 - k) (l - k) H13).
set (H16:=(Z_mod_lt (Z_of_nat ((k + mod_nat (n1 - k) (l - k) H13 + n2 -
       k))) (Z_of_nat(l-k))H13)).
elim H16.
clear H16.
intros H16 H17.
cut ( Z_of_nat ((k + mod_nat (n1 - k) (l - k) H13 + n2 -
       k)) mod Z_of_nat (l - k) < Z_of_nat l%Z -(Z_of_nat k))%Z.
intuition.
cut (k<=l).
intro H18.
rewrite<- (inj_minus1 l k H18).
exact H17.

intuition.

apply surj_lt.
rewrite (inj_plus k (mod_nat (n0-k) (l-k) H13)).
rewrite<- H14.
cut (Z_of_nat l - Z_of_nat k > 0)%Z.
intro H17.
set (H16:= (Z_mod_lt (n0-k) (l-k) H17)).
rewrite (inj_minus1 n0 k).
rewrite (inj_minus1 l k).
intuition.
intuition.
intuition.
intuition.
exact smallest.

cut (k<(k + mod_nat (n1 - k) (l - k) H13 +
          n2 )).
intro H16.
csetoid_rewrite_rev (power_mod k l (k + mod_nat (n1 - k) (l - k) H13 +
         n2) H13 H16 smallest).

cut (k<n0).
intro H17.
csetoid_rewrite_rev (power_mod k l n0 H13 H17 smallest).
csetoid_rewrite_rev H11.
csetoid_rewrite (power_plus M c0 n1 n2).
cut (k<n1).
intro H18.
csetoid_rewrite (power_mod k l n1 H13 H18 smallest).
csetoid_rewrite_rev (power_plus M c0 (k + mod_nat (n1 - k) (l - k) H13)
                          n2).          
apply eq_reflexive.
intuition.
intuition.
intuition.
rewrite (inj_minus1 l k).
intuition.
intuition.
Qed.

Lemma Char5:(Z_of_nat n1 + Z_of_nat n2 < Z_of_nat k + Z_of_nat (l - k))%Z ->
   n2 < l ->
   power_CMonoid c0 n2[=]b ->
   n1 < l ->
   l <= n0 ->
   (Z_of_nat n1 + Z_of_nat n2)%Z =
   (Z_of_nat k + Z_of_nat (n0 - k) mod Z_of_nat (l - k))%Z.
intro z.
intros.
set (H11:= (power_plus M c0 n1 n2 )).
csetoid_rewrite_cxt Hn1 H11.
csetoid_rewrite_cxt Hn2 H11.
csetoid_rewrite_cxt_rev Hn0 H11.
simpl.
cut (Z_of_nat (l - k) > 0)%Z.
intro H13.
set (H14:=(mod_nat_correct (n0-k)(l-k) H13)).
rewrite H14.
rewrite<- (inj_plus k (mod_nat (n0 - k) (l - k) H13)).
rewrite<- (inj_plus n1 n2).
apply inj_eq.
apply w_inj with k l.
apply surj_lt.
rewrite (inj_plus n1 n2).
rewrite (inj_minus1 l k ) in z.
intuition.
intuition.

apply surj_lt.
rewrite (inj_plus k ( mod_nat (n0 - k) (l - k) H13)).
rewrite<- H14.
cut (Z_of_nat l - Z_of_nat k > 0)%Z.
intro H16.
set (H15:=(Z_mod_lt (n0-k)(l-k) H16)).
cut (Z_of_nat (n0 - k) mod Z_of_nat (l - k) < Z_of_nat l- Z_of_nat k)%Z.
intuition.
cut (k<=l).
intro H18.
cut (k<=n0).
intro H19.
rewrite (inj_minus1 l k H18).
rewrite (inj_minus1 n0 k H19).
intuition.
intuition.
intuition.
intuition.

exact smallest.

cut (k<n0).
intro H16.
csetoid_rewrite_rev (power_mod k l n0 H13 H16 smallest).
csetoid_rewrite_rev H11.
csetoid_rewrite (power_plus M c0 n1 n2).
apply eq_reflexive.
intuition.
rewrite (inj_minus1 l k).
intuition.
intuition.
Qed.


Lemma Char6:(Z_of_nat k + Z_of_nat (l - k) <= Z_of_nat n1 + Z_of_nat n2)%Z ->
 n2 < l ->
 power_CMonoid c0 n2[=]b ->
 n1 < l ->
 l <= n0 ->
 (Z_of_nat k + (Z_of_nat n1 + Z_of_nat n2 - Z_of_nat k) mod Z_of_nat (l - k))%Z =
 (Z_of_nat k + Z_of_nat (n0 - k) mod Z_of_nat (l - k))%Z.
intros.
set (H11:= (power_plus M c0 n1 n2 )).
csetoid_rewrite_cxt Hn1 H11.
csetoid_rewrite_cxt Hn2 H11.
csetoid_rewrite_cxt_rev Hn0 H11.
simpl.
cut (Z_of_nat (l - k) > 0)%Z.
intro H13.
set (H14:=(mod_nat_correct (n0-k)(l-k) H13)).
rewrite H14.
rewrite<- (inj_plus n1
           n2). 
rewrite<- (inj_plus k (mod_nat (n0 - k) (l - k) H13)).
rewrite<- (inj_minus1 (n1+ n2)  k).
rewrite (mod_nat_correct ( n1 + n2-k) (l-k) H13).
rewrite<- (inj_plus k (mod_nat (n1 + n2 - k) (l - k) H13)).
2:intuition.
apply inj_eq.
apply w_inj with k l.
apply surj_lt.
rewrite (inj_plus k  (mod_nat
         ( n1+
          n2 - k )(l - k) H13)).
rewrite<- (mod_nat_correct (n1 +
          n2 - k) (l - k) H13).
set (H16:=(Z_mod_lt (Z_of_nat (n1 + n2 -
       k))) (Z_of_nat(l-k))H13).
elim H16.
clear H16.
intros H16 H17.
cut ( Z_of_nat (n1 + n2 -
       k) mod Z_of_nat (l - k) < Z_of_nat l%Z -(Z_of_nat k))%Z.
intuition.
cut (k<=l).
intro H18.
rewrite<- (inj_minus1 l k H18).
exact H17.

intuition.

apply surj_lt.
rewrite (inj_plus k (mod_nat (n0-k) (l-k) H13)).
rewrite<- H14.
cut (Z_of_nat l - Z_of_nat k > 0)%Z.
intro H17.
set (H16:= (Z_mod_lt (n0-k) (l-k) H17)).
rewrite (inj_minus1 n0 k).
rewrite (inj_minus1 l k).
intuition.
intuition.
intuition.
intuition.
exact smallest.

cut (k<( n1 +
          n2 )).
intro H15.
csetoid_rewrite_rev (power_mod k l (n1+n2) H13 H15 smallest).
cut (k<n0).
intro H17.
csetoid_rewrite_rev (power_mod k l n0 H13 H17 smallest).
exact H11.
intuition.
intuition.
rewrite (inj_minus1 l k).
intuition.
intuition.
Qed.

Lemma Char7: (Z_of_nat k + Z_of_nat (n1 - k) mod Z_of_nat (l - k) +
  (Z_of_nat k + Z_of_nat (n2 - k) mod Z_of_nat (l - k)) <
  Z_of_nat k + Z_of_nat (l - k))%Z ->
 l <= n2 ->
 power_CMonoid c0 n2[=]b ->
 l <= n1 ->
 power_CMonoid c0 n1[=]a ->
 n0 < l ->
 (Z_of_nat k + Z_of_nat (n1 - k) mod Z_of_nat (l - k) +
  (Z_of_nat k + Z_of_nat (n2 - k) mod Z_of_nat (l - k)))%Z = 
 Z_of_nat n0.
intros z.
intros.
set (H11:= (power_plus M c0 n1 n2 )).
csetoid_rewrite_cxt Hn1 H11.
csetoid_rewrite_cxt Hn2 H11.
csetoid_rewrite_cxt_rev Hn0 H11.
simpl.
cut (Z_of_nat (l - k) > 0)%Z.
intro H13.
set (H12:=(mod_nat_correct (n1-k)(l-k) H13)).
rewrite H12.
rewrite<- (inj_plus k (mod_nat (n1 - k) (l - k) H13)).
set (H15:=(mod_nat_correct (n2-k)(l-k) H13)).
rewrite H15.
rewrite<- (inj_plus k (mod_nat (n2 - k) (l - k) H13)).
rewrite<- (inj_plus (k + mod_nat (n1 - k) (l - k) H13)
           (k + mod_nat (n2 - k) (l - k) H13)). 
apply inj_eq.
apply w_inj with k l.
apply surj_lt.
rewrite (inj_plus (k + mod_nat (n1 - k) (l - k) H13)
         (k + mod_nat (n2 - k) (l - k) H13)).
rewrite (inj_plus k ( mod_nat (n1 - k) (l - k) H13)).
rewrite (inj_plus k (mod_nat (n2 - k) (l - k) H13)).
rewrite<- H12.
rewrite<- H15.
replace (Z_of_nat l) with (Z_of_nat k + Z_of_nat (l - k))%Z.
exact z.
cut (k<=l).
intro H16.
rewrite (inj_minus1 l k H16).
intuition.
intuition.

intuition.
intuition.

csetoid_rewrite_rev H11.
csetoid_rewrite (power_plus M c0 n1 n2).
cut (k<n1).
intro H17.
csetoid_rewrite (power_mod k l n1 H13 H17 smallest).
cut (k<n2).
intro H18.
csetoid_rewrite (power_mod k l n2 H13 H18 smallest).
csetoid_rewrite_rev (power_plus M c0 (k + mod_nat (n1 - k) (l - k) H13)
                          (k + mod_nat (n2 - k) (l - k) H13)).          
apply eq_reflexive.
intuition.
intuition.
rewrite (inj_minus1 l k).
intuition.
intuition.
Qed.

Lemma Char8: (Z_of_nat k + Z_of_nat (l - k) <=
  Z_of_nat k + Z_of_nat (n1 - k) mod Z_of_nat (l - k) +
  (Z_of_nat k + Z_of_nat (n2 - k) mod Z_of_nat (l - k)))%Z ->
 l <= n2 ->
 power_CMonoid c0 n2[=]b ->
 l <= n1 ->
 power_CMonoid c0 n1[=]a ->
 n0 < l ->
 (Z_of_nat k +
  (Z_of_nat k + Z_of_nat (n1 - k) mod Z_of_nat (l - k) +
   (Z_of_nat k + Z_of_nat (n2 - k) mod Z_of_nat (l - k)) - 
   Z_of_nat k) mod Z_of_nat (l - k))%Z = Z_of_nat n0.
intro z.
intros.
set (H11:= (power_plus M c0 n1 n2 )).
csetoid_rewrite_cxt Hn1 H11.
csetoid_rewrite_cxt Hn2 H11.
csetoid_rewrite_cxt_rev Hn0 H11.
simpl.
cut (Z_of_nat (l - k) > 0)%Z.
intro H13.
set (H12:=(mod_nat_correct (n1-k)(l-k) H13)).
rewrite H12.
rewrite<- (inj_plus k (mod_nat (n1 - k) (l - k) H13)).
set (H15:=(mod_nat_correct (n2-k)(l-k) H13)).
rewrite H15.
rewrite<- (inj_plus k (mod_nat (n2 - k) (l - k) H13)).
rewrite<- (inj_plus (k + mod_nat (n1 - k) (l - k) H13)
           (k + mod_nat (n2 - k) (l - k) H13)).
rewrite<- (inj_minus1 (k + mod_nat (n1 - k) (l - k) H13 + (k + mod_nat (n2 - k) (l - k) H13)) k).
rewrite (mod_nat_correct (k + mod_nat (n1 - k) (l - k) H13 + (k + mod_nat (n2 - k) (l - k) H13) -
       k) (l-k) H13).
rewrite<- (inj_plus k (mod_nat
         (k + mod_nat (n1 - k) (l - k) H13 +
          (k + mod_nat (n2 - k) (l - k) H13) - k) (l - k) H13)).
2:intuition.
apply inj_eq.
apply w_inj with k l.
apply surj_lt.
rewrite (inj_plus k  (mod_nat
         (k + mod_nat (n1 - k) (l - k) H13 +
          (k + mod_nat (n2 - k) (l - k) H13) - k) (l - k) H13)).
rewrite<- (mod_nat_correct (k + mod_nat (n1 - k) (l - k) H13 +
          (k + mod_nat (n2 - k) (l - k) H13) - k) (l - k) H13).
set (H16:=(Z_mod_lt (Z_of_nat ((k + mod_nat (n1 - k) (l - k) H13 + (k + mod_nat (n2 - k) (l - k) H13) -
       k))) (Z_of_nat(l-k))H13)).
elim H16.
clear H16.
intros H16 H17.
cut ( Z_of_nat ((k + mod_nat (n1 - k) (l - k) H13 + (k + mod_nat (n2 - k) (l - k) H13) -
       k)) mod Z_of_nat (l - k) < Z_of_nat l%Z -(Z_of_nat k))%Z.
intuition.
cut (k<=l).
intro H18.
rewrite<- (inj_minus1 l k H18).
exact H17.

intuition.
intuition.
intuition.

cut (k<(k + mod_nat (n1 - k) (l - k) H13 +
         (k + mod_nat (n2 - k) (l - k) H13))).
intro H16.
csetoid_rewrite_rev (power_mod k l (k + mod_nat (n1 - k) (l - k) H13 +
         (k + mod_nat (n2 - k) (l - k) H13)) H13 H16 smallest).
csetoid_rewrite_rev H11.
csetoid_rewrite (power_plus M c0 n1 n2).
cut (k<n1).
intro H18.
csetoid_rewrite (power_mod k l n1 H13 H18 smallest).
cut (k<n2).
intro H19.
csetoid_rewrite (power_mod k l n2 H13 H19 smallest).
csetoid_rewrite_rev (power_plus M c0 (k + mod_nat (n1 - k) (l - k) H13)
                          (k + mod_nat (n2 - k) (l - k) H13)).          
apply eq_reflexive.
intuition.
intuition.
intuition.
rewrite (inj_minus1 l k).
intuition.
intuition.
Qed.

Lemma Char9: (Z_of_nat k + Z_of_nat (n1 - k) mod Z_of_nat (l - k) + Z_of_nat n2 <
  Z_of_nat k + Z_of_nat (l - k))%Z ->
 n2 < l ->
 power_CMonoid c0 n2[=]b ->
 l <= n1 ->
 power_CMonoid c0 n1[=]a ->
 n0 < l ->
 (Z_of_nat k + Z_of_nat (n1 - k) mod Z_of_nat (l - k) + Z_of_nat n2)%Z =
 Z_of_nat n0.
intros.
set (H11:= (power_plus M c0 n1 n2 )).
csetoid_rewrite_cxt Hn1 H11.
csetoid_rewrite_cxt Hn2 H11.
csetoid_rewrite_cxt_rev Hn0 H11.
simpl.
cut (Z_of_nat (l - k) > 0)%Z.
intro H13.
set (H12:=(mod_nat_correct (n1-k)(l-k) H13)).
rewrite H12.
rewrite<- (inj_plus k (mod_nat (n1 - k) (l - k) H13)).
rewrite<- (inj_plus (k + mod_nat (n1 - k) (l - k) H13) n2).
apply inj_eq.
apply w_inj with k l.
apply surj_lt.
rewrite (inj_plus (k + mod_nat (n1 - k) (l - k) H13) n2).
rewrite (inj_plus k ( mod_nat (n1 - k) (l - k) H13)).
rewrite<- H12.
set (H16:=(Z_mod_lt (Z_of_nat (n1-k)) (Z_of_nat(l-k))H13)).
elim H16.
clear H16.
intros H16 H17.
cut ( Z_of_nat (n1 - k) mod Z_of_nat (l - k) + Z_of_nat n2 <
    Z_of_nat l - Z_of_nat k)%Z.
intuition.
cut (k<=l).
intro H18.
rewrite<- (inj_minus1 l k H18).
intuition.
intuition.
intuition.
intuition.

csetoid_rewrite_rev H11.
csetoid_rewrite (power_plus M c0 n1 n2).
cut (k<n1).
intro H17.
csetoid_rewrite (power_mod k l n1 H13 H17 smallest).
csetoid_rewrite_rev (power_plus M c0 (k + mod_nat (n1 - k) (l - k) H13)
                          n2).          
apply eq_reflexive.
intuition.
rewrite (inj_minus1 l k).
intuition.
intuition.
Qed.

Lemma Char10:(Z_of_nat k + Z_of_nat (l - k) <=
  Z_of_nat k + Z_of_nat (n1 - k) mod Z_of_nat (l - k) + Z_of_nat n2)%Z ->
 n2 < l ->
 power_CMonoid c0 n2[=]b ->
 l <= n1 ->
 power_CMonoid c0 n1[=]a ->
 n0 < l ->
 (Z_of_nat k +
  (Z_of_nat k + Z_of_nat (n1 - k) mod Z_of_nat (l - k) + Z_of_nat n2 -
   Z_of_nat k) mod Z_of_nat (l - k))%Z = Z_of_nat n0.
intros.
set (H11:= (power_plus M c0 n1 n2 )).
csetoid_rewrite_cxt Hn1 H11.
csetoid_rewrite_cxt Hn2 H11.
csetoid_rewrite_cxt_rev Hn0 H11.
simpl.
cut (Z_of_nat (l - k) > 0)%Z.
intro H13.
set (H12:=(mod_nat_correct (n1-k)(l-k) H13)).
rewrite H12.
rewrite<- (inj_plus k (mod_nat (n1 - k) (l - k) H13)).
rewrite<- (inj_plus (k + mod_nat (n1 - k) (l - k) H13)
           n2). 
rewrite<- (inj_minus1 (k + mod_nat (n1 - k) (l - k) H13 + n2)  k).
rewrite (mod_nat_correct (k + mod_nat (n1 - k) (l - k) H13 + n2 -
       k) (l-k) H13).
rewrite<- (inj_plus k (mod_nat (k + mod_nat (n1 - k) (l - k) H13 + n2 - k) (l - k) H13)).
2:intuition.
apply inj_eq.
apply w_inj with k l.
apply surj_lt.
rewrite (inj_plus k  (mod_nat
         (k + mod_nat (n1 - k) (l - k) H13 +
          n2 - k )(l - k) H13)).
rewrite<- (mod_nat_correct (k + mod_nat (n1 - k) (l - k) H13 +
          n2 - k) (l - k) H13).
set (H16:=(Z_mod_lt (Z_of_nat ((k + mod_nat (n1 - k) (l - k) H13 + n2 -
       k))) (Z_of_nat(l-k))H13)).
elim H16.
clear H16.
intros H16 H17.
cut ( Z_of_nat ((k + mod_nat (n1 - k) (l - k) H13 + n2 -
       k)) mod Z_of_nat (l - k) < Z_of_nat l%Z -(Z_of_nat k))%Z.
intuition.
cut (k<=l).
intro H18.
rewrite<- (inj_minus1 l k H18).
exact H17.

intuition.
intuition.


exact smallest.

cut (k<(k + mod_nat (n1 - k) (l - k) H13 +
          n2 )).
intro H16.
csetoid_rewrite_rev (power_mod k l (k + mod_nat (n1 - k) (l - k) H13 +
         n2) H13 H16 smallest).

csetoid_rewrite_rev H11.
csetoid_rewrite (power_plus M c0 n1 n2).
cut (k<n1).
intro H18.
csetoid_rewrite (power_mod k l n1 H13 H18 smallest).
csetoid_rewrite_rev (power_plus M c0 (k + mod_nat (n1 - k) (l - k) H13)
                          n2).          
apply eq_reflexive.
intuition.
intuition.
rewrite (inj_minus1 l k).
intuition.
intuition.
Qed.

Lemma Char11:(Z_of_nat n1 + Z_of_nat n2 < Z_of_nat k + Z_of_nat (l - k))%Z ->
 n2 < l ->
 power_CMonoid c0 n2[=]b ->
 n1 < l ->
 power_CMonoid c0 n1[=]a ->
 n0 < l -> (Z_of_nat n1 + Z_of_nat n2)%Z = Z_of_nat n0.
intros H0 H1 H2 H4 H6 H7.
set (H11:= (power_plus M c0 n1 n2 )).
csetoid_rewrite_cxt Hn1 H11.
csetoid_rewrite_cxt Hn2 H11.
csetoid_rewrite_cxt_rev Hn0 H11.
simpl.
rewrite<- (inj_plus n1 n2).
apply inj_eq.
apply w_inj with k l.
apply surj_lt.
rewrite (inj_plus n1 n2).
rewrite (inj_minus1 l k ) in H0.
intuition.

intuition.
intuition.
intuition.
exact H11.
Qed.

Lemma Char12:(Z_of_nat k + Z_of_nat (l - k) <= Z_of_nat n1 + Z_of_nat n2)%Z ->
 n2 < l ->
 power_CMonoid c0 n2[=]b ->
 n1 < l ->
 power_CMonoid c0 n1[=]a ->
 n0 < l ->
 (Z_of_nat k + (Z_of_nat n1 + Z_of_nat n2 - Z_of_nat k) mod Z_of_nat (l - k))%Z =
 Z_of_nat n0.
intros.
set (H11:= (power_plus M c0 n1 n2 )).
csetoid_rewrite_cxt Hn1 H11.
csetoid_rewrite_cxt Hn2 H11.
csetoid_rewrite_cxt_rev Hn0 H11.
simpl.
rewrite<- (inj_plus n1
           n2). 
rewrite<- (inj_minus1 (n1 + n2)  k).
cut (Z_of_nat (l - k) > 0)%Z.
intro H13.
rewrite (mod_nat_correct ( n1 + n2 -
       k) (l-k) H13).
rewrite<- (inj_plus k (mod_nat (n1 + n2 - k) (l - k) H13)).
apply inj_eq.
apply w_inj with k l.
apply surj_lt.
rewrite (inj_plus k  (mod_nat
         ( n1 +
          n2 - k )(l - k) H13)).
rewrite<- (mod_nat_correct (n1 +
          n2 - k) (l - k) H13).
set (H16:=(Z_mod_lt (Z_of_nat ((n1+ n2 -
       k))) (Z_of_nat(l-k))H13)).
elim H16.
clear H16.
intros H16 H17.
cut ( Z_of_nat (( n1+ n2 -
       k)) mod Z_of_nat (l - k) < Z_of_nat l%Z -(Z_of_nat k))%Z.
intuition.
cut (k<=l).
intro H18.
rewrite<- (inj_minus1 l k H18).
exact H17.

intuition.
intuition.


exact smallest.

cut (k<( n1 +
          n2 )).
intro H16.
csetoid_rewrite_rev (power_mod k l (n1 +
         n2) H13 H16 smallest).

csetoid_rewrite_rev H11.
apply eq_reflexive.
intuition.
rewrite (inj_minus1 l k).
intuition.
intuition.
intuition.
Qed.

End Char.
Section MP.

Variable M:CMonoid.
Variable u:M.
Variable gen:(is_generator M u).
Variable k l:nat.
Variable smallest: k < l
      and power_CMonoid u  k[=]
          power_CMonoid u l
          and (forall k0 l0 : nat,
               k0 < k or k0 = k and l0 < l ->
               power_CMonoid u k0[#]
               power_CMonoid u l0).
Variable a b:cs_crr (csg_crr (cm_crr M)).
Variable H3: k >= 0.
Let H4:=(inj_ge k 0 H3 ).
Variable H7:((l - k)%nat > 0)%Z.
Variable H5: l - k > 0.
Let H6:=(inj_gt (l - k) 0 H5 ).

Lemma pres_mult:(
    csf_fun M (C_as_CMonoid k (l - k)%nat H6 H4)
      (to_C_as_csf M u k l  H7 H4 gen smallest) (csbf_fun M M M (csg_op (c:=M)) a b)[=]
    csbf_fun (C_as_CMonoid k (l - k)%nat H6 H4)
      (C_as_CMonoid k (l - k)%nat H6 H4) (C_as_CMonoid k (l - k)%nat H6 H4)
      (csg_op (c:=C_as_CMonoid k (l - k)%nat H6 H4))
      (csf_fun M (C_as_CMonoid k (l - k)%nat H6 H4)
         (to_C_as_csf M u k l H7 H4 gen smallest ) a)
      (csf_fun M (C_as_CMonoid k (l - k)%nat H6 H4)
         (to_C_as_csf M u k l H7 H4 gen smallest ) b)).
simpl.
unfold ZFeq.
unfold to_C.
unfold sigT_rec.
unfold sigT_rect.
(* generalize smallest_gen.*)
set (power_mod :=(power_k_n M u)).
set (w_inj:=(weakly_inj1 M u)).
(* generalize w_inj_gen.
generalize power_mod_gen.
clear power_mod_gen.
clear w_inj_gen.
case cyc.
simpl.
intros c0 H power_mod w_inj smallest.*)
case ( gen (csbf_fun M M M (csg_op (c:=M)) a b)).
intros n0 Hn0.
case (le_lt_dec l n0).
unfold C_plus.
unfold ZF_rec.
unfold ZF_rect.
case (gen a).
intros n1 Hn1.
case (le_lt_dec l n1).
case (gen b).
intros n2 Hn2.
case (le_lt_dec l n2).
unfold sumbool_rec.
unfold sumbool_rect.
case (Z_lt_le_dec
         (k + (n1 - k)%nat mod (l - k)%nat +
          (k + (n2 - k)%nat mod (l - k)%nat)) (k + (l - k)%nat)).
(* 1 *)
intros.
apply Char1 with M u a b.
exact H5.
intros.
apply power_mod.
exact gen.
exact H.
exact X.
intros.
apply w_inj with k0 l3.
exact gen.
exact H.
exact H0.
exact X.
exact H1.
exact smallest.
exact Hn0.
exact Hn1.
exact Hn2.
exact z.
exact l1.
exact l2.
exact l0.

(* 2 *)
intros.
apply Char2 with M u a b.
exact H5.
intros.
apply power_mod.
exact gen.
exact H.
exact X.
intros.
apply w_inj with k0 l3.
exact gen.
exact H.
exact H0.
exact X.
exact H1.
exact smallest.
exact Hn0.
exact Hn1.
exact Hn2.
exact z.
exact l1.
exact l0.
exact l2.

unfold sumbool_rec.
unfold sumbool_rect.
case (Z_lt_le_dec (k + (n1 - k)%nat mod (l - k)%nat + n2) (k + (l - k)%nat)).

(* 3 *)
intros.
apply Char3 with M u a b.
exact H5.
intros.
apply power_mod.
exact gen.
exact H.
exact X.
intros.
apply w_inj with k0 l3.
exact gen.
exact H.
exact H0.
exact X.
exact H1.
exact smallest.
exact Hn0.
exact Hn1.
exact Hn2.
exact z.
exact l0.
exact l1.
exact l2.

(* 4 *)
intros.
apply Char4 with M u a b.
exact H5.
intros.
apply power_mod.
exact gen.
exact H.
exact X.
intros.
apply w_inj with k0 l3.
exact gen.
exact H.
exact H0.
exact X.
exact H1.
exact smallest.
exact Hn0.
exact Hn1.
exact Hn2.
exact z.
exact l0.
exact l1.
exact l2.

case (gen b).
intros n2.
case (le_lt_dec l n2).
unfold sumbool_rec.
unfold sumbool_rect.
case ( Z_lt_le_dec (n1 + (k + (n2 - k)%nat mod (l - k)%nat))
         (k + (l - k)%nat)).

(* 5 *)
intros z l2 Hn2 l1 l0.
replace (n1 + (k + (n2 - k)%nat mod (l - k)%nat))%Z with
         ((k + (n2 - k)%nat mod (l - k)%nat)+ n1)%Z.
apply Char3 with M u b a.
exact H5.
intros.
apply power_mod.
exact gen.
exact H.
exact X.
intros.
apply w_inj with k0 l3.
exact gen.
exact H.
exact H0.
exact X.
exact H1.
exact smallest.
set (H8:= (cyc_imp_comm M (generator_imp_cyclic M u gen))).
unfold commutes in H8.
set (H9:= (H8 b a)).
csetoid_rewrite H9.
exact Hn0.
exact Hn2.
exact Hn1.
replace (k + (n2 - k)%nat mod (l - k)%nat + n1)%Z with 
	(n1 + (k + (n2 - k)%nat mod (l - k)%nat))%Z.                 
exact z.
intuition.
exact l1.
exact l2.
exact l0.
intuition.

(* 6 *)
intros z l2 Hn2 l1 l0.
replace (k + (n1 + (k + (n2 - k)%nat mod (l - k)%nat) - k) mod (l - k)%nat)%Z
 with (k + (k + (n2 - k)%nat mod (l - k)%nat+n1 - k) mod (l - k)%nat)%Z.
apply Char4 with M u b a.
exact H5.
intros.
apply power_mod.
exact gen.
exact H.
exact X.
intros.
apply w_inj with k0 l3.
exact gen.
exact H.
exact H0.
exact X.
exact H1.
exact smallest.
set (H8:= (cyc_imp_comm M (generator_imp_cyclic M u gen))).
unfold commutes in H8.
set (H9:= (H8 b a)).
csetoid_rewrite H9.
exact Hn0.
exact Hn2.
exact Hn1.
replace (k + (n2 - k)%nat mod (l - k)%nat + n1)%Z with 
	(n1 + (k + (n2 - k)%nat mod (l - k)%nat))%Z.                 
exact z.
intuition.
exact l1.
exact l2.
exact l0.
replace (k + (n2 - k)%nat mod (l - k)%nat + n1 - k)%Z with
          (n1 + (k + (n2 - k)%nat mod (l - k)%nat) - k)%Z.
reflexivity.
intuition.

unfold sumbool_rec.
unfold sumbool_rect.
case (Z_lt_le_dec (n1 + n2) (k + (l - k)%nat)).

(* 7 *)
intros z l2 Hn2 l1 l0.
apply Char5 with M u a b.
exact H5.
intros.
apply power_mod.
exact gen.
exact H.
exact X.
intros.
apply w_inj with k0 l3.
exact gen.
exact H.
exact H0.
exact X.
exact H1.
exact smallest.
exact Hn0.
exact Hn1.
exact Hn2.
exact z.
exact l2.
exact Hn2.
exact l1.
exact l0.

(* 8 *)
intros z l2 Hn2 l1 l0.
apply Char6 with M u a b.
exact H5.
intros.
apply power_mod.
exact gen.
exact H.
exact X.
intros.
apply w_inj with k0 l3.
exact gen .
exact H.
exact H0.
exact X.
exact H1.
exact smallest.
exact Hn0.
exact Hn1.
exact Hn2.
exact z.
exact l2.
exact Hn2.
exact l1.
exact l0.

unfold C_plus.
unfold ZF_rec.
unfold ZF_rect.
case (gen a).
intro n1.
case (le_lt_dec l n1).
case (gen b).
intro n2.
case (le_lt_dec l n2).
unfold sumbool_rec.
unfold sumbool_rect.
case ( Z_lt_le_dec
         (k + (n1 - k)%nat mod (l - k)%nat +
          (k + (n2 - k)%nat mod (l - k)%nat)) (k + (l - k)%nat)).

(* 9 *)
intros z l2 Hn2 l1 Hn1 l0.
apply Char7 with M u a b.
exact H5.
intros.
apply power_mod.
exact gen.
exact H.
exact X.
intros.
apply w_inj with k0 l3.
exact gen.
exact H.
exact H0.
exact X.
exact H1.
exact smallest.
exact Hn0.
exact Hn1.
exact Hn2.
exact z.
exact l2.
exact Hn2.
exact l1.
exact Hn1.
exact l0.

(* 10 *)
intros z l2 Hn2 l1 Hn1 l0.
apply Char8 with M u a b.
exact H5.
intros.
apply power_mod.
exact gen.
exact H.
exact X.
intros.
apply w_inj with k0 l3.
exact gen.
exact H.
exact H0.
exact X.
exact H1.
exact smallest.
exact Hn0.
exact Hn1.
exact Hn2.
exact z.
exact l2.
exact Hn2.
exact l1.
exact Hn1.
exact l0.

unfold sumbool_rec.
unfold sumbool_rect.
case ( Z_lt_le_dec (k + (n1 - k)%nat mod (l - k)%nat + n2) (k + (l - k)%nat)).

(* 11 *)
intros z l2 Hn2 l1 Hn1 l0.
apply Char9 with M u a b.
exact H5.
intros.
apply power_mod.
exact gen.
exact H.
exact X.
intros.
apply w_inj with k0 l3.
exact gen.
exact H.
exact H0.
exact X.
exact H1.
exact smallest.
exact Hn0.
exact Hn1.
exact Hn2.
exact z.
exact l2.
exact Hn2.
exact l1.
exact Hn1.
exact l0.

(* 12 *)
intros z l2 Hn2 l1 Hn1 l0.
apply Char10 with M u a b.
exact H5.
intros.
apply power_mod.
exact gen.
exact H.
exact X.
intros.
apply w_inj with k0 l3.
exact gen.
exact H.
exact H0.
exact X.
exact H1.
exact smallest.
exact Hn0.
exact Hn1.
exact Hn2.
exact z.
exact l2.
exact Hn2.
exact l1.
exact Hn1.
exact l0.

case (gen b).
intro n2.
case (le_lt_dec l n2).
unfold sumbool_rec.
unfold sumbool_rect.
case ( Z_lt_le_dec (n1 + (k + (n2 - k)%nat mod (l - k)%nat))
         (k + (l - k)%nat)).

(* 13 *)
intros z l2 Hn2 l1 Hn1 l0.
replace (n1 + (k + (n2 - k)%nat mod (l - k)%nat))%Z with
       (k + (n2 - k)%nat mod (l - k)%nat+ n1)%Z.
apply Char9 with M u b a.
exact H5.
intros.
apply power_mod.
exact gen.
exact H.
exact X.
intros.
apply w_inj with k0 l3.
exact gen.
exact H.
exact H0.
exact X.
exact H1.
exact smallest.
set (H8:= (cyc_imp_comm M (generator_imp_cyclic M u gen))).
unfold commutes in H8.
set (H9:= (H8 b a)).
csetoid_rewrite H9.
exact Hn0.
exact Hn2.
exact Hn1.
replace (k + (n2 - k)%nat mod (l - k)%nat + n1)%Z with 
	(n1 + (k + (n2 - k)%nat mod (l - k)%nat))%Z.                 
exact z.
intuition.
exact l1.
exact Hn1.
exact l2.
exact Hn2.
exact l0.
intuition.

(* 14 *)
intros z l2 Hn2 l1 Hn1 l0.
replace (k + (n1 + (k + (n2 - k)%nat mod (l - k)%nat) - k) mod (l - k)%nat)%Z
   with (k + (k + (n2 - k)%nat mod (l - k)%nat+n1 - k) mod (l - k)%nat)%Z.
apply Char10 with M u b a.
exact H5.
intros.
apply power_mod.
exact gen.
exact H.
exact X.
intros.
apply w_inj with k0 l3.
exact gen.
exact H.
exact H0.
exact X.
exact H1.
exact smallest.
set (H8:= (cyc_imp_comm M (generator_imp_cyclic M u gen))).
unfold commutes in H8.
set (H9:= (H8 b a)).
csetoid_rewrite H9.
exact Hn0.
exact Hn2.
exact Hn1.
replace (k + (n2 - k)%nat mod (l - k)%nat + n1)%Z with 
	(n1 + (k + (n2 - k)%nat mod (l - k)%nat))%Z.                 
exact z.
intuition.
exact l1.
exact Hn1.
exact l2.
exact Hn2.
exact l0.
replace ((k + (n2 - k)%nat mod (l - k)%nat + n1 - k) mod (l - k)%nat)%Z with
       ((n1 + (k + (n2 - k)%nat mod (l - k)%nat) - k) mod (l - k)%nat)%Z.
reflexivity.
set (q:=(k + (n2 - k)%nat mod (l - k)%nat)%Z).
replace (n1+q-k)%Z with (q+n1-k)%Z.
reflexivity.
intuition.

unfold sumbool_rec.
unfold sumbool_rect.
case (Z_lt_le_dec (n1 + n2) (k + (l - k)%nat)).

(* 15 *)
intros z l2 Hn2 l1 Hn1 l0.
apply Char11 with M k l u a b.
exact H5.
intros.
apply w_inj with k0 l3.
exact gen.
exact H.
exact H0.
exact X.
exact H1.
exact smallest.
exact Hn0.
exact Hn1.
exact Hn2.
exact z.
exact l2.
exact Hn2.
exact l1.
exact Hn1.
exact l0.

(* 16 *)
intros z l2 Hn2 l1 Hn1 l0.
apply Char12 with M u a b.
exact H5.
intros.
apply power_mod.
exact gen.
exact H.
exact X.
intros.
apply w_inj with k0 l3.
exact gen.
exact H.
exact H0.
exact X.
exact H1.
exact smallest.
exact Hn0.
exact Hn1.
exact Hn2.
exact z.
exact l2.
exact Hn2.
exact l1.
exact Hn1.
exact l0.
Qed.

End MP.

Section ZP.

Variable M:CMonoid.
Variable u:M.
Variable gen: (is_generator M u).
Variable l k: nat.
Variable smallest:k < l
      and power_CMonoid u k[=]
          power_CMonoid u l
          and (forall k0 l0 : nat,
               k0 < k or k0 = k and l0 < l ->
               power_CMonoid u k0[#]
               power_CMonoid u l0).
Variable H3:k >= 0.
Let H4:=(inj_ge k 0 H3).
Variable H7:((l - k)%nat > 0)%Z.
Variable H5:  l - k > 0.
Let H6:= (inj_gt (l - k) 0 H5).

Lemma pres_zero:csf_fun M (C_as_CMonoid k (l - k)%nat H6 H4)
     (to_C_as_csf M u k l H7 H4 gen smallest ) Zero[=]Zero.
simpl.
unfold ZFeq.
unfold to_C.
unfold sigT_rect.
set (power_mod:=(power_k_n M u)).
set (w_inj:=(weakly_inj1 M u)).
case (gen (@cm_unit M)).
intros i H2.

case (le_lt_dec l i).
intro H9.
elim smallest.
clear smallest.
intros H21 H20.
elim H20.
clear H20.
intros H20 H19.
set (H8:=(H19 0 i)).
cut (Cdecidable ( 0 < k or 0 = k and i < l)).
intro H10.
unfold Cdecidable in H10.
elim H10.
clear H10.
intro H10.
set (H11:= (H8 H10)).
simpl.
csetoid_replace_cxt (@cm_unit M) (power_CMonoid u 0) H2.
set (H12:=(eq_imp_not_ap M ( power_CMonoid u i)(power_CMonoid u 0)H2)).
set (H13:=(ap_symmetric_unfolded M (power_CMonoid u 0)(power_CMonoid u i)
H11)).
unfold Not in H12.
intuition.
simpl.
apply eq_reflexive.

intro H11.
cut (k=0).
simpl.
intro H12.
rewrite H12.
simpl.
set (H13:=(Z_eq_dec ((i - 0)%nat mod (l - 0)%nat)%Z 0)).
elim H13.
clear H13.
intro H13.
intuition.
clear H13.
intro H13.
cut False.
intuition.
csetoid_replace_cxt (@cm_unit M) (power_CMonoid u 0) H2.
cut (l>0)%Z.
intro H14.
cut ((power_CMonoid u 0)[=](power_CMonoid u (mod_nat i l H14))).
3:intuition.
intro H15.
cut ((mod_nat i l H14)<l)%Z.
intro H16.
set (H17:=(H19 0 (mod_nat i l H14))).
csetoid_rewrite_cxt H15 H2.
csetoid_rewrite_cxt_rev H2 H17.
csetoid_rewrite_cxt_rev H2 H15.
set (H18:=(eq_imp_not_ap M (power_CMonoid u 0)(power_CMonoid u i) H15)).
unfold Not in H18.
apply H18.
apply H17.
rewrite H12.
right.
intuition.

rewrite<- (mod_nat_correct i l H14).
cut (l>0)%Z.
intro H16.
set (H17:= (Z_mod_lt i l H16)).
intuition.

intuition.

csetoid_rewrite_rev H2.
cut (Z_of_nat (l - 0) > 0)%Z.
intro H15.
replace (mod_nat i l H14) with (0+(mod_nat (i-0)(l-0) H15)).
apply power_mod.
exact gen.
intuition.

split.
intuition.
split.
rewrite<- H12.
exact H20.

intuition.

replace (i-0) with i.
2:intuition.
simpl.
apply mod_nat_pi.
intuition.

replace (l-0) with l.
intuition.
intuition.

simpl.
apply eq_reflexive.

apply k_zero with i l.
exact H11.

apply lexi_dec.

(* i<l *)

intro H9.
simpl.
replace 0%Z with (Z_of_nat 0).
2:reflexivity.
apply inj_eq.
apply w_inj with k l.
exact gen.
intuition.
exact H9.
exact smallest.
simpl.
apply eq_symmetric_unfolded.
exact H2.
Qed.

End ZP.

Section inj_surj.

Variable M:CMonoid.
Variable u:M.
Variable gen: (is_generator M u).
Variable k l:nat.
Variable smallest:k < l
      and power_CMonoid u k[=]
          power_CMonoid u l
          and (forall k0 l0 : nat,
               k0 < k or k0 = k and l0 < l ->
               power_CMonoid u k0[#]
               power_CMonoid u l0).
Variable H7:((l - k)%nat > 0)%Z.
Variable H4: (k >= 0)%Z.

Section IL.

Variable  a0 : M.
Variable  a1 : M.
Variable ap : a0[#]a1.
Variable  H1 : k < l.
Variable  power_mod : forall (n : nat) (H2 : (Z_of_nat (l - k) > 0)%Z),
         k < n ->
         k < l
         and power_CMonoid u k[=]power_CMonoid u l
             and ((forall k0 l0 : nat,
                  (k0 < k or k0 = k and l0 < l) ->
                  power_CMonoid u k0[#]power_CMonoid u l0):CProp) ->
         power_CMonoid u n[=]
         power_CMonoid u (k + mod_nat (n - k) (l - k) H2).

Lemma power_inj: forall (n0 n1:nat),
(power_CMonoid u n0[#]power_CMonoid u n1)-> n0<>n1.
intros n0 n1 H2 H3.
rewrite H3 in H2.
set (H8:=(ap_imp_neq M (power_CMonoid u n1)(power_CMonoid u n1) H2)).
unfold cs_neq in H8.
apply H8.
apply eq_reflexive.
Qed.

Lemma to_C_inj1:forall(n0 : nat)
  (Hn0 : power_CMonoid u n0[=]a0)
  (n1 : nat),
   l <= n1 ->
   power_CMonoid u n1[=]a1 ->
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
csetoid_replace (power_CMonoid u (k + mod_nat (n1 - k) (l - k) H13))
           (power_CMonoid u n1).
csetoid_replace (power_CMonoid u (k + mod_nat (n0 - k) (l - k) H13))
           (power_CMonoid u n0).
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
  (Hn0 : power_CMonoid u n0[=]a0)
  (n1 : nat), n1 < l ->
   power_CMonoid u n1[=]a1 ->
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
csetoid_replace (power_CMonoid u (k + mod_nat (n0 - k) (l - k) H13))
           (power_CMonoid u n0).
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
exact c0.
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
exact c0.
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
exact c0.
exact l1.
exact Hn0.
exact l0.

(* 4 *)

intros.
apply inj_neq.
unfold neq.
apply power_inj.
csetoid_rewrite Hn0.
csetoid_rewrite c0.
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
set (w_inj:= (weakly_inj1 M u k l)).
set (power_mod:=(power_k_n M u k l)).
exists (power_CMonoid u (Z_to_nat bprf1)).
case (gen (power_CMonoid u (Z_to_nat bprf1))).
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
rewrite (Z_to_nat_correct  bprf1).
apply inj_eq.
apply w_inj.
exact gen.
apply surj_lt.
rewrite<- (Z_to_nat_correct bprf1).
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
csetoid_replace  (power_CMonoid u (k + mod_nat (b'' - k) (l - k) H6))
               ( power_CMonoid u b'').
apply eq_symmetric_unfolded.
exact Hb'.

apply eq_symmetric_unfolded.
apply power_mod.
intuition.
intuition.
intuition.

intuition.
intro H3.
rewrite (Z_to_nat_correct bprf1).
apply inj_eq.
apply w_inj.
exact gen.
apply surj_lt.
rewrite<- (Z_to_nat_correct bprf1).
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

Definition cyc_to_nat: forall (M:CMonoid)(u:M), 
(is_generator M u)->M->nat_as_CMonoid.
simpl.
intros M u gen m.
unfold is_generator in gen.
elim (gen m).
intros n genm.
exact n.
Defined.

Section CTN.
Variable M:CMonoid.
Variable u:M.
Variable gen:(is_generator M u).

Lemma cyc_to_nat_strext: (((forall (k l:nat),k<l->
(power_CMonoid u k [#] power_CMonoid u l))
:CProp)
->
(fun_strext (cyc_to_nat M u gen)):CProp):CProp.
intros inf.
unfold fun_strext.
intros a b.
unfold cyc_to_nat.
unfold sigT_rec.
unfold sigT_rect.
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
(H0:(forall (k l:nat),k<l->(power_CMonoid u k [#] power_CMonoid u l))):=
(Build_CSetoid_fun M nat_as_CMonoid (cyc_to_nat M u gen) (cyc_to_nat_strext H0)).

Lemma weakly_inj2:forall (a b:nat),
(forall (k l:nat),k<l->(power_CMonoid u k [#] power_CMonoid u l))
->
(power_CMonoid u a[=]power_CMonoid u b )->
       a = b.
intros a b.
intros  H1 H2.
set (H3:=(lt_eq_lt_dec a b)).
elim H3.
clear H3.
intro H3.
elim H3.
clear H3.
intro H3.
set (H4:=(H1 a b H3)).
set (H5:=(eq_imp_not_ap M (power_CMonoid u a)(power_CMonoid u b) H2)).
unfold Not in H5.
elim H5.
exact H4.

tauto.
clear H3.
intro H3.
set (H4:=(H1 b a H3)).
set (H5:=(eq_imp_not_ap M (power_CMonoid u a)(power_CMonoid u b) H2)).
unfold Not in H5.
elim H5.
apply ap_symmetric_unfolded.
exact H4.
Qed.

End CTN.

Section Th17.

Variable M:CMonoid.
Variable u:M.
Variable gen:(is_generator M u).

Theorem Th17_partI:
({k:nat | {l:nat |k<l and (power_CMonoid u k [=] power_CMonoid u l)
and (forall (k0 l0:nat), (k0<k or (k0=k and l0<l))-> 
(power_CMonoid u k0 [#] power_CMonoid u l0) )}}
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
(power_CMonoid u k [#] power_CMonoid u l))
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
set (H88:= (weakly_inj2 M u)).
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
set (H88:= (weakly_inj2 M u)).
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
set (H88:=(weakly_inj2 M u)).
exists (power_CMonoid u b).
unfold cyc_to_nat.
unfold sigT_rec.
unfold sigT_rect.
case (gen (power_CMonoid u b)). 
intros n H1.
apply H88.
exact H'.
exact H1.
Qed.

End Th17.

Definition plus_nminus1:forall (n:Z)(H:(n>0)%Z)(H0:(0>=0)%Z),
     (CSetoid_un_op (C_as_CMonoid 0%Z n H H0)).
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
case ( Z_lt_le_dec (a'+0)(0+ n)).
simpl.
case (Z_lt_le_dec (0 + a') (0 + n)).
simpl.
intuition.

simpl.
intuition.

simpl.
unfold sumbool_rec.
unfold sumbool_rect.
case (Z_lt_le_dec (0+a')(0+ n)).
simpl.
intuition.

simpl.
intros H1 H2 H3.
replace (a' +0 -0)%Z with a'.
replace (a'-0)%Z with a'.
cut ( 0%Z = (a' mod n)%Z).
intuition.
intuition.
intuition.
intuition.

case (Z_lt_le_dec (a' + 0) (0 + n)).
simpl.
unfold sumbool_rec.
unfold sumbool_rect.
case (Z_lt_le_dec (0 + a') (0 + n)).
simpl.
intuition.
simpl.
intuition.

simpl.
unfold sumbool_rec.
unfold sumbool_rect.
case ( Z_lt_le_dec (0 + a') (0 + n)).
simpl.
intuition.

simpl.
intuition.

unfold sumbool_rec.
unfold sumbool_rect.
case ( Z_lt_le_dec (a' + (n - a'))(0+ n)).
simpl.
unfold sumbool_rec.
unfold sumbool_rect.
case ( Z_lt_le_dec (n - a' + a')(0+ n) ).
simpl.
intuition.

simpl.
intuition.

simpl.
unfold sumbool_rec.
unfold sumbool_rect.
case (Z_lt_le_dec (n - a' + a')(0+n)).
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
case (Z_lt_le_dec (0+0) (k + n)).
simpl.
intuition.

simpl.
intuition.
Qed.

