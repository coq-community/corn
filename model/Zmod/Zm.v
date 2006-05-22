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


(* Zm.v, by Vince Barany *)

Require Export ZMod.
Require Export CFields.

(**
* Zm
Let m be a positive integer.
We will look at the integers modulo m and prove that they form a ring.
Eventually we will proof that Zp is even a field for p prime.
*)

(* Definition of rings Zm  *)

Open Scope Z_scope.

Section zm.

Variable m:positive.

Lemma m_gt_0 : m>0.
red; simpl; reflexivity.
Qed.
(* This was a "Local"! *)


(**
** Zm is a CSetoid
*)


Section zm_setoid.

Definition ZModeq (a b:Z) : Prop := (Zmodeq m a b).
Definition ZModap (a b:Z) : CProp := (CNot (Zmodeq m a b)).

Lemma Zmodeq_wd : forall a b:Z, a=b -> a mod m = b mod m.
intros a b Heq.
elim Heq.
auto.
Qed.

Lemma Zmodap_irreflexive: (irreflexive ZModap).
red.
intro x.
intro H.
elim H.
apply Zmodeq_refl.
Qed.

Lemma Zmodap_symmetric: (Csymmetric ZModap).
red.
intros x y H.
intro H0.
elim H.
apply Zmodeq_symm.
exact H0.
Qed.

Lemma Zmodap_cotransitive: (cotransitive ZModap).
red.
intros x y H.
intros z.
elim (Zmodeq_dec m x z).
elim (Zmodeq_dec m y z).
intros Hyz Hxz.
 elim H.
 apply (Zmodeq_trans _ _ _ _ Hxz (Zmodeq_symm _ _ _ Hyz)).
intros _ Hxz.
 right.
 intro Hzy.
 apply H.
 apply (Zmodeq_trans _ _ _ _ Hxz Hzy).
intro H_xz.
 left.
 intro Hxz.
 elim H_xz.
 exact Hxz.
Qed.

Lemma Zmodap_tight_apart: (tight_apart ZModeq ZModap).
red.
intros x y.
split.
elim (Zmodeq_dec m x y).
intros H Hnn.
 exact H.
intros Hn Hnn.
 elim Hnn.
 intro H.
 elim Hn.
 exact H.
intro H.
 intro Hnn.
 elim Hnn.
 exact H.
Qed.


(* Begin_Tex_Verb *)
Lemma Zm_is_CSetoid : (is_CSetoid _ ZModeq ZModap).
(* End_Tex_Verb *)
apply Build_is_CSetoid.
exact Zmodap_irreflexive.
exact Zmodap_symmetric.
exact Zmodap_cotransitive.
exact Zmodap_tight_apart.
Qed.

(* Begin_Tex_Verb *)
Definition Zm_csetoid :=
                    (Build_CSetoid Z ZModeq ZModap Zm_is_CSetoid).
(* End_Tex_Verb *)

End zm_setoid.

(**
** Zm is a CAbGroup
*)

Section zm_group.


Definition Zm_plus (a b:Zm_csetoid) : Zm_csetoid := (a+b).
 (* ? `((a%m)+(b%m))%m` ? *)


(* Begin_Tex_Verb *)
Lemma Zm_plus_strext : (bin_fun_strext _ _ _ Zm_plus).
(* End_Tex_Verb *)
red.
intros.
elim (Zmodeq_dec m x1 x2).
elim (Zmodeq_dec m y1 y2).
intros Hyeq Hxeq.
 elim X.
 auto with zarith.
intros Hyneq _.
 right.
 intro Hyeq.
 elim Hyneq.
 exact Hyeq.
intros Hxneq.
 left.
 intro Hxeq.
 elim Hxneq.
 exact Hxeq.
Qed.

(* Begin_Tex_Verb *)
Lemma Zm_plus_wd : (bin_fun_wd _ _ _ Zm_plus).
(* End_Tex_Verb *)
apply bin_fun_strext_imp_wd.
exact Zm_plus_strext.
Qed.

(* Begin_Tex_Verb *)
Definition Zm_plus_op :=
  (Build_CSetoid_bin_op _ _ Zm_plus_strext).
(* End_Tex_Verb *)


(* Begin_Tex_Verb *)
Lemma Zm_plus_associative : (associative Zm_plus_op).
(* End_Tex_Verb *)
red.
intros x y z.
simpl.
unfold ZModeq.
unfold Zm_plus.
rewrite Zplus_assoc.
apply Zmodeq_refl.
Qed.


(* Begin_Tex_Verb *)
Definition Zm_csemi_grp :=
    (Build_CSemiGroup Zm_csetoid Zm_plus_op Zm_plus_associative).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma Zm_plus_zero_rht: (is_rht_unit Zm_plus_op 0).
(* End_Tex_Verb *)
red; simpl.
intros.
unfold ZModeq.
unfold Zm_plus.
rewrite Zplus_0_r.
auto with zarith.
Qed.

(* Begin_Tex_Verb *)
Lemma Zm_plus_zero_lft: (is_lft_unit Zm_plus_op 0).
(* End_Tex_Verb *)
red; simpl.
intros.
unfold ZModeq.
auto with zarith.
Qed.

(* Begin_Tex_Verb *)
Lemma Zm_plus_commutes: (commutes Zm_plus_op).
(* End_Tex_Verb *)
red; simpl.
intros.
unfold ZModeq.
unfold Zm_plus.
rewrite Zplus_comm.
auto with zarith.
Qed.

(* Begin_Tex_Verb *)
Definition Zm_is_CMonoid :=
    (Build_is_CMonoid Zm_csemi_grp 0 Zm_plus_zero_rht Zm_plus_zero_lft).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition Zm_cmonoid := (Build_CMonoid _ _ Zm_is_CMonoid).
(* End_Tex_Verb *)

(* Tex_Prose
\subsection{Integers modulo m form a group}
*)

(* Begin_Tex_Verb *)
Definition Zm_opp (x:Zm_cmonoid) : Zm_cmonoid := -x.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma Zm_opp_strext : (un_op_strext _ Zm_opp).
(* End_Tex_Verb *)
red; red; simpl.
intros x y.
unfold ZModeq; unfold ZModap; unfold Zm_plus; unfold Zm_opp.
intro Hneq.
intro Heq.
apply Hneq.
apply Zmodeq_opp_elim.
exact Heq.
Qed.

(* Begin_Tex_Verb *)
Lemma Zm_opp_well_def : (un_op_wd _ Zm_opp).
(* End_Tex_Verb *)
unfold un_op_wd.
apply fun_strext_imp_wd.
exact Zm_opp_strext.
Qed.

(* Begin_Tex_Verb *)
Definition Zm_opp_op :=
  (Build_CSetoid_un_op _ _ Zm_opp_strext).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma Zm_is_CGroup : (is_CGroup _ Zm_opp_op).
(* End_Tex_Verb *)
unfold is_CGroup.
unfold is_inverse.
simpl.
unfold ZModeq; unfold Zm_plus; unfold Zm_opp.
intro.
rewrite Zplus_opp_r.
rewrite Zplus_opp_l.
auto with zarith.
Qed.

(* Begin_Tex_Verb *)
Definition Zm_cgroup := (Build_CGroup _ _ Zm_is_CGroup).
(* End_Tex_Verb *)

Lemma Zm_is_CAbGroup : (is_CAbGroup Zm_cgroup).
unfold is_CAbGroup.
exact Zm_plus_commutes.
Qed.

Definition Zm_cabgroup := (Build_CAbGroup _ Zm_is_CAbGroup).

End zm_group.

(**
** Zm is a CRing
*)

Section zm_ring.

Hypothesis Hnontriv: ~(m=xH).

Lemma m_gt_1: m>1.
unfold Zgt.
generalize Hnontriv.
case m; simpl; intros; auto.
elim Hnontriv0; auto.
Qed.

(* Dit was een Local! *)

Section zm_def.

(* Begin_Tex_Verb *)
Definition Zm_mult (x y:Zm_cabgroup) : Zm_cabgroup := x*y.
(* End_Tex_Verb *)


(* Begin_Tex_Verb *)
Lemma Zm_mult_strext : (bin_fun_strext _ _ _ Zm_mult).
(* End_Tex_Verb *)
red; simpl.
unfold ZModap;unfold Zm_mult; simpl.
intros x1 x2 y1 y2.
intro H.
elim (Zmodeq_dec m x1 x2).
elim (Zmodeq_dec m y1 y2).
intros Hyeq Hxeq.
 elim H.
 apply Zmodeq_mult_elim; auto with zarith.
intros Hyneq _.
 right.
 intro Hyeq.
 elim Hyneq.
 exact Hyeq.
intros Hxneq.
 left.
 intro Hxeq.
 elim Hxneq.
 exact Hxeq.
Qed.

(* Begin_Tex_Verb *)
Lemma Zm_mult_wd : (bin_fun_wd _ _ _ Zm_mult).
(* End_Tex_Verb *)
apply bin_fun_strext_imp_wd.
exact Zm_mult_strext.
Qed.


(* Begin_Tex_Verb *)
Definition Zm_mult_op := (Build_CSetoid_bin_op _ _ Zm_mult_strext).
(* End_Tex_Verb *)


(* Begin_Tex_Verb *)
Lemma Zm_mult_assoc : (associative Zm_mult_op).
(* End_Tex_Verb *)
unfold associative.
intros x y z.
simpl.
unfold ZModeq; unfold Zm_mult.
rewrite Zmult_assoc.
apply Zmodeq_refl.
Qed.


(* Begin_Tex_Verb *)
Lemma Zm_mult_commutative:  forall x y:Zm_cabgroup,
           (Zm_mult_op x y) [=] (Zm_mult_op y x).
(* End_Tex_Verb *)
intros x y.
simpl.
unfold ZModeq; unfold Zm_mult.
rewrite Zmult_comm.
apply Zmodeq_refl.
Qed.


(* Begin_Tex_Verb *)
Lemma Zm_mult_one : forall x:Zm_cabgroup, (Zm_mult_op x 1)[=]x.
(* End_Tex_Verb *)
intro.
simpl.
unfold ZModeq; unfold Zm_mult.
rewrite Zmult_1_r.
apply Zmodeq_refl.
Qed.

Lemma Zm_mult_onel : forall x:Zm_cabgroup, (Zm_mult_op 1 x)[=]x.
intro.
astepl (Zm_mult_op x 1).
exact (Zm_mult_one x).
exact (Zm_mult_commutative x 1).
Qed.

Definition Zm_mult_semigroup := (Build_CSemiGroup Zm_csetoid Zm_mult_op Zm_mult_assoc).

Lemma Zm_mult_one_r : is_rht_unit Zm_mult_op 1.
red.
exact Zm_mult_one.
Qed.

Lemma Zm_mult_one_l : is_lft_unit Zm_mult_op 1.
red.
exact Zm_mult_onel.
Qed.

(* Begin_Tex_Verb *)
Lemma Zm_mult_monoid: (is_CMonoid Zm_mult_semigroup 1).
(* End_Tex_Verb *)
apply Build_is_CMonoid.
exact Zm_mult_one_r.
exact Zm_mult_one_l.
Qed.

(* Begin_Tex_Verb *)
Lemma Zm_mult_plus_dist : (distributive Zm_mult_op Zm_plus_op).
(* End_Tex_Verb *)
red; simpl.
intros x y z.
unfold ZModeq; unfold Zm_mult; unfold Zm_plus.
rewrite <-Zmult_plus_distr_r.
apply Zmodeq_refl.
Qed.

(* Begin_Tex_Verb *)
Lemma Zm_non_triv : (ZModap 1 0).
(* End_Tex_Verb *)
unfold ZModap.
intro Hfalse.
generalize (Zmodeq_modeq _ _ _ Hfalse).
rewrite Zmod_zero_lft.
rewrite Zmod_one_lft; auto.
intro H.
assert False. discriminate. elim H0. 
(* Discriminate in itself caused an error in Coq *)
exact m_gt_1.
Qed.

(* Begin_Tex_Verb *)
Lemma Zm_is_CRing : (is_CRing Zm_cabgroup 1 Zm_mult_op).
(* End_Tex_Verb *)
apply Build_is_CRing with Zm_mult_assoc.
exact Zm_mult_monoid.
exact Zm_mult_commutative.
exact Zm_mult_plus_dist.
exact Zm_non_triv.
Qed.

End zm_def.

(* Begin_Tex_Verb *)
Definition Zm_cring :=  (Build_CRing _ _ _ Zm_is_CRing) : CRing.
Definition Zm := Zm_cring.
(* End_Tex_Verb *)



Section zm_ring_basics.


Definition Zm_mult_ord (a:Zm)(h:nat) := (a[^]h[=]One) /\ 
  forall k:nat, (lt k h)->~(a[^]k[=]One).




End zm_ring_basics.



End zm_ring.


(**
** Zp is a field
From now on m is prime.
*)


Section zp_def.

(* Dit was een Local!!! *)
Hypothesis Hprime: (Prime m).

Lemma p_not_1: ~m=xH.
unfold Prime in Hprime.
elim Hprime; intros; assumption.
Qed.

Lemma p_gt_0: m>0.
red; simpl; reflexivity.
Qed.

Lemma p_gt_1: m>1.
unfold Zgt.
generalize p_not_1.
case m; simpl; intro H; auto.
elim H; auto.
Qed.


Definition Zp := (Zm p_not_1).


(**
*** The inverse element in Zp
Let x in Zp, such that x is apart from Zero.
Then we will show that there is an inverse element y such that
x[*]y [=] One in Zp.
*)


Section zp_nonzero.

Variable x: Zp.
Hypothesis Hx: x[#]Zero.

Lemma Zp_nonz_mod: 0<(Zmod x m)<m.
generalize (Z_mod_lt x m); intro H; elim H; clear H; intros.
split.
elim (Zlt_asymmetric (Zmod x m) 0).
 intro Hfalse; elim Hx; elim Hfalse; clear Hfalse; intro Hfalse.
 elim H; apply Zlt_gt; auto. 
 simpl; rewrite <-Hfalse; auto with zarith.
 apply Zgt_lt.
assumption.
exact p_gt_0.
Qed.

Lemma Zp_nonz_relprime: (Zrelprime x m).
simpl in Hx. 
unfold ZModap in Hx; unfold ZModeq in Hx.
elim Zp_nonz_mod; intros Hxmod0 Hxmodp.
unfold Zrelprime.
rewrite <-Zgcd_mod_lft; auto. 
generalize Hxmod0.
set (d:=(Zmod x m)). 
cut (d=(Zmod x m)).
case d. 
intros _ Hfalse; 
 elim (Zlt_irref _ Hfalse). 
intros D HD _. 
 rewrite <-HD in Hxmodp.
 rewrite Zgcd_symm.
 elim (prime_rel_prime m Hprime D Hxmodp); auto.
intros D _ Hfalse;
 elim (Zge_0_NEG _ Hfalse).
auto.
exact p_gt_0.
Qed.

End zp_nonzero.



(* Begin_Tex_Verb *)
Definition Zp_inv (x:Zp)(Hx:(x[#]Zero)) : Zp := (Zgcd_coeff_a x m).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma Zp_inv_strext : forall (x y:Zp)(x_ y_:_), (((Zp_inv x x_)[#](Zp_inv y y_))->(x[#]y)).
(* End_Tex_Verb *)
intros x y Hx Hy.
simpl.
unfold ZModap; unfold Zp_inv.
intro Hinv.
intro Heq.
generalize (Zmodeq_modeq _ _ _ Heq); clear Heq; intro Heq.
elim Hinv.
apply Zmodeq_eqmod.
generalize (Zmod_relprime_inv m x p_gt_1 (Zp_nonz_relprime x Hx)).
rewrite <- (Zmod_relprime_inv m y p_gt_1 (Zp_nonz_relprime y Hy)).
rewrite (Zmod_mult_compat m x); auto.
rewrite (Zmod_mult_compat m y); auto.
(*unfold p.*)
rewrite Heq.
rewrite <-Zmod_mult_compat; auto.
rewrite <-Zmod_mult_compat; auto.
intro Hmult.
apply (Zmod_mult_elim_lft _ _ _ _ p_gt_0 (Zp_nonz_relprime y Hy) Hmult).
exact m_gt_0.
exact m_gt_0.
exact p_gt_0.
exact p_gt_0.
Qed.


(* Begin_Tex_Verb *)
Lemma Zp_is_CField: (is_CField Zp Zp_inv).
(* End_Tex_Verb *)
red; red.
intros x.
simpl; unfold ZModap; unfold ZModeq; unfold Zm_mult; unfold Zp_inv.
intros Hx.
elim (Zp_nonz_mod x Hx); intros Hxmod0 Hxmodp.
split.
apply Zmodeq_eqmod.
rewrite Zmod_one_lft; auto.
(*rewrite <-Zmod_mult_compat; auto.*)
(*rewrite Zmod_Zmod; auto.*)
apply Zmod_relprime_inv; auto.
exact p_gt_1.
apply Zrelprime_symm.
unfold Zrelprime.
rewrite <-Zgcd_mod_rht; auto. 
generalize Hxmod0.
set (d:=(Zmod x m)). 
cut (d=(Zmod x m)); auto.
case d.
intros _ Hfalse; 
 elim (Zlt_irref _ Hfalse). 
intros D HD _. 
 rewrite <-HD in Hxmodp.
 (*fold p;*) 
 (*rewrite <-HD.*) 
 elim (prime_rel_prime m Hprime D Hxmodp); auto.
intros D _ Hfalse;
 elim (Zge_0_NEG _ Hfalse).
exact p_gt_0.
exact p_gt_1.
(*rewrite Zm_mult_commutative.*)
apply Zmodeq_eqmod.
rewrite Zmod_one_lft; auto.
cut ((x * Zgcd_coeff_a x m) mod m = 1).
intro H; elim H. 
apply Zmodeq_wd.
apply Zmult_comm.
apply Zmod_relprime_inv; auto.
exact p_gt_1.
apply Zrelprime_symm.
unfold Zrelprime.
rewrite <-Zgcd_mod_rht; auto.
generalize Hxmod0.
set (d:=(Zmod x m)). 
cut (d=(Zmod x m)); auto.
case d.
intros _ Hfalse; 
 elim (Zlt_irref _ Hfalse). 
intros D HD _. 
 rewrite <-HD in Hxmodp.
 (*fold p; rewrite <-HD.*) 
 elim (prime_rel_prime m Hprime D Hxmodp); auto.
intros D _ Hfalse;
 elim (Zge_0_NEG _ Hfalse).
exact p_gt_0.
exact p_gt_1.
Qed.


(* Begin_Tex_Verb *)
Definition Fp : CField := (Build_CField _ _ Zp_is_CField Zp_inv_strext).
(* End_Tex_Verb *)

Definition Fp_inv (x:Fp)(Hx:x[#]Zero) : Fp := (Zp_inv x Hx).


End zp_def.



(* Basic properties of Zp *)

Section zp_prop.



End zp_prop.



End zm.




