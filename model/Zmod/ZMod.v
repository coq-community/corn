(* Copyright © 1998-2006
 * Henk Barendregt
 * Luís Cruz-Filipe
 * Herman Geuvers
 * Mariusz Giero
 * Rik van Ginneken
 * Dimitri Hendriks
 * Sébastien Hinderer
 * Bart Kirkels
 * Pierre Letouzey
 * Iris Loeb
 * Lionel Mamane
 * Milad Niqui
 * Russell O’Connor
 * Randy Pollack
 * Nickolay V. Shmyrev
 * Bas Spitters
 * Dan Synek
 * Freek Wiedijk
 * Jan Zwanenburg
 * 
 * This work is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * This work is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along
 * with this work; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 *) 
(* ZMod.v, by Vince Barany *)

Require Export ZGcd.


(**
* Working modulo a positive number over Z
** Facts on `mod'
*)


Section zmod.


Definition Zmod_same := Z_mod_same.

Lemma Zmod_zero_lft : forall m : Z, (0 mod m)%Z = 0%Z.
intro m.
case m; auto.
Qed.

Lemma Zmod_zero_rht : forall a : Z, (a mod 0)%Z = 0%Z.
intro a.
case a; auto.
Qed.

Lemma Zmod_Zmod :
 forall m a : Z, (m > 0)%Z -> ((a mod m) mod m)%Z = (a mod m)%Z.
intros m a Hm.
apply
 (Zdiv_remainder_unique (a mod m) m (a mod m / m) ((a mod m) mod m) 0
    (a mod m)).
rewrite Zmult_comm.
apply Z_div_mod_eq; auto.
apply Z_mod_lt; auto.
auto with zarith.
apply Z_mod_lt; auto.
Qed.

Lemma Zmod_cancel_multiple :
 forall m a b : Z, (m > 0)%Z -> ((b * m + a) mod m)%Z = (a mod m)%Z.
intros m a b Hm.
rewrite Zplus_comm. 
apply Z_mod_plus.
exact Hm.
Qed.

Lemma Zmod_multiple : forall m a : Z, (m > 0)%Z -> ((a * m) mod m)%Z = 0%Z.
intros m a Hm.
rewrite <- (Zplus_0_r (a * m)).
rewrite Zmod_cancel_multiple; auto.
Qed.

Lemma Zmod_minus_intro :
 forall m a b : Z,
 (m > 0)%Z -> ((a - b) mod m)%Z = 0%Z -> (a mod m)%Z = (b mod m)%Z.
intros m a b Hm H0.
assert (Hdiv : Zdivides m (a - b)); auto with zarith.
elim Hdiv; intros q Hq.
replace a with (q * m + b)%Z; auto with zarith.
apply Zmod_cancel_multiple.
assumption.
Qed.

Lemma Zmod_plus_compat :
 forall m a b : Z,
 (m > 0)%Z -> ((a + b) mod m)%Z = ((a mod m + b mod m) mod m)%Z.
intros m a b Hm.
rewrite <- (Zmod_Zmod m (a + b) Hm).
apply Zmod_minus_intro. 
exact Hm.
apply Zmod0_Zdivides. 
auto with zarith. 
replace (a mod m)%Z with (a - m * (a / m))%Z.
replace (b mod m)%Z with (b - m * (b / m))%Z.
replace ((a + b) mod m)%Z with (a + b - m * ((a + b) / m))%Z.
unfold Zminus in |- *; repeat rewrite Zplus_assoc.
repeat rewrite Zopp_plus_distr; repeat rewrite Zopp_involutive.
rewrite (Zplus_comm (a + b) (- (m * ((a + b) / m)))).
repeat rewrite <- Zplus_assoc.
apply Zdivides_plus_elim.
auto with zarith.
rewrite (Zplus_assoc (m * (a / m)) (- b) (m * (b / m))).
rewrite (Zplus_comm (m * (a / m)) (- b)).
rewrite <- (Zplus_assoc (- b) (m * (a / m)) (m * (b / m))).
rewrite (Zplus_assoc (- a) (- b) (m * (a / m) + m * (b / m))).
rewrite <- Zopp_plus_distr.
repeat rewrite Zplus_assoc.
rewrite Zplus_opp_r.
auto with zarith.
generalize (Z_div_mod_eq (a + b) m Hm); auto with zarith.
generalize (Z_div_mod_eq b m Hm); auto with zarith.
generalize (Z_div_mod_eq a m Hm); auto with zarith.
Qed.

Lemma Zmod_plus_compat_rht :
 forall m a b : Z, (m > 0)%Z -> ((a + b) mod m)%Z = ((a + b mod m) mod m)%Z.
intros m a b Hm.
rewrite (Zmod_plus_compat m a b Hm).
rewrite <- (Zmod_Zmod m (a + b mod m) Hm).
rewrite (Zmod_plus_compat m a (b mod m) Hm).
rewrite Zmod_Zmod; auto.
rewrite Zmod_Zmod; auto.
Qed.

Lemma Zmod_plus_compat_lft :
 forall m a b : Z, (m > 0)%Z -> ((a + b) mod m)%Z = ((a mod m + b) mod m)%Z.
intros m a b Hm.
rewrite (Zplus_comm a b).
rewrite (Zplus_comm (a mod m) b).
apply Zmod_plus_compat_rht.
auto.
Qed.

Lemma Zmod_opp_elim :
 forall m a : Z, (m > 0)%Z -> (- a mod m)%Z = ((m - a mod m) mod m)%Z.
intros m a Hm.
apply Zmod_minus_intro.
exact Hm.
replace (- a - (m - a mod m))%Z with (- m + (a mod m - a))%Z;
 auto with zarith.
replace (- m)%Z with (-1 * m)%Z; auto with zarith.
rewrite Zmod_cancel_multiple; auto.
replace (a mod m - a)%Z with (- (a / m) * m)%Z; auto with zarith.
generalize (Z_div_mod_eq a m Hm).
set (q := (a / m)%Z); set (r := (a mod m)%Z); intro Ha; rewrite Ha.
rewrite Zplus_comm; unfold Zminus in |- *; rewrite Zopp_plus_distr;
 rewrite Zplus_assoc; rewrite Zplus_opp_r; rewrite Zplus_0_l;
 rewrite Zopp_mult_distr_l_reverse; rewrite Zmult_comm; 
 reflexivity.
Qed.

Lemma Zmod_minus_elim :
 forall m a b : Z,
 (m > 0)%Z -> (a mod m)%Z = (b mod m)%Z -> ((a - b) mod m)%Z = 0%Z.
intros m a b Hm Heq.
unfold Zminus in |- *.
rewrite (Zmod_plus_compat m a (- b) Hm).
rewrite Heq.
rewrite Zmod_opp_elim; auto.
rewrite <- (Zmod_plus_compat m b (m - b mod m) Hm).
unfold Zminus in |- *.
rewrite Zplus_assoc.
rewrite (Zplus_comm b m).
rewrite <- Zplus_assoc.
fold (b - b mod m)%Z in |- *.
replace (b - b mod m)%Z with (b / m * m)%Z.
rewrite Zplus_comm.
rewrite Zmod_cancel_multiple; auto.
apply Zmod_same; auto.
set (q := (b / m)%Z); set (r := (b mod m)%Z).
rewrite (Z_div_mod_eq b m Hm).
fold q in |- *; fold r in |- *.
rewrite Zmult_comm.
unfold Zminus in |- *.
rewrite <- Zplus_assoc.
rewrite Zplus_opp_r.
auto with zarith.
Qed.

Lemma Zmod_mult_compat :
 forall m a b : Z,
 (m > 0)%Z -> ((a * b) mod m)%Z = ((a mod m * (b mod m)) mod m)%Z.
intros m a b Hm.
rewrite <- (Zmod_Zmod m (a * b) Hm).
apply Zmod_minus_intro; auto.
apply Zmod0_Zdivides. 
auto with zarith.
replace (a mod m)%Z with (a - m * (a / m))%Z.
replace (b mod m)%Z with (b - m * (b / m))%Z.
replace ((a * b) mod m)%Z with (a * b - m * (a * b / m))%Z.
unfold Zminus in |- *; repeat rewrite Zplus_assoc.
repeat rewrite Zmult_plus_distr_l.
repeat rewrite Zmult_plus_distr_r.
repeat rewrite Zopp_plus_distr; repeat rewrite Zopp_involutive.
rewrite (Zplus_comm (a * b)). 
repeat rewrite <- Zplus_assoc.
apply Zdivides_plus_elim.
auto with zarith.
repeat rewrite Zplus_assoc.
rewrite Zplus_opp_r.
repeat rewrite Zopp_mult_distr_l_reverse; repeat rewrite Zopp_mult_distr_r;
 repeat rewrite Zopp_involutive.
simpl in |- *.
apply Zdivides_plus_elim; auto with zarith.
generalize (Z_div_mod_eq (a * b) m Hm); auto with zarith.
generalize (Z_div_mod_eq b m Hm); auto with zarith.
generalize (Z_div_mod_eq a m Hm); auto with zarith.
Qed.

Lemma Zmod_mult_compat_rht :
 forall m a b : Z, (m > 0)%Z -> ((a * b) mod m)%Z = ((a * (b mod m)) mod m)%Z.
intros m a b Hm.
rewrite (Zmod_mult_compat m a b Hm).
rewrite <- (Zmod_Zmod m (a * (b mod m)) Hm).
rewrite (Zmod_mult_compat m a (b mod m) Hm).
rewrite Zmod_Zmod; auto.
rewrite Zmod_Zmod; auto.
Qed.

Lemma Zmod_mult_compat_lft :
 forall m a b : Z, (m > 0)%Z -> ((a * b) mod m)%Z = ((a mod m * b) mod m)%Z.
intros m a b Hm.
rewrite (Zmult_comm a b).
rewrite (Zmult_comm (a mod m) b).
apply Zmod_mult_compat_rht.
auto.
Qed.

Lemma Zmod_mult_elim_lft :
 forall m a b c : Z,
 (m > 0)%Z ->
 Zrelprime a m ->
 ((a * b) mod m)%Z = ((a * c) mod m)%Z -> (b mod m)%Z = (c mod m)%Z.
intros m a b c Hm Hrelprime Hmulteq.
assert (Hm0 : m <> 0%Z); auto with zarith.
generalize (Zdivides_Zmod0 _ _ Hm0 (Zmod_minus_elim m _ _ Hm Hmulteq));
 intro Hdiv.
rewrite (Zmult_comm a b) in Hdiv; rewrite (Zmult_comm a c) in Hdiv;
 rewrite <- BinInt.Zmult_minus_distr_r in Hdiv.
apply Zmod_minus_intro; auto.
apply Zmod0_Zdivides. auto with zarith.
apply (Zrelprime_div_mult_intro m a (b - c)).
apply Zrelprime_symm; assumption.
rewrite Zmult_comm; assumption.
Qed.

Lemma Zmod_mult_elim_rht :
 forall m a b c : Z,
 (m > 0)%Z ->
 Zrelprime a m ->
 ((b * a) mod m)%Z = ((c * a) mod m)%Z -> (b mod m)%Z = (c mod m)%Z.
intros m a b c; rewrite (Zmult_comm b a); rewrite (Zmult_comm c a);
 apply Zmod_mult_elim_lft.
Qed.

Lemma Zmod_opp_zero :
 forall m a : Z, (m > 0)%Z -> (a mod m)%Z = 0%Z -> (- a mod m)%Z = 0%Z.
intros m a Hm Ha.
rewrite (Zmod_opp_elim m a Hm).
rewrite Ha.
unfold Zminus in |- *; simpl in |- *; rewrite Zplus_0_r.
apply (Z_mod_same m Hm).
Qed.

Lemma Zmod_small :
 forall m a : Z, (m > 0)%Z -> (0 <= a < m)%Z -> (a mod m)%Z = a.
intros m a Hm Ha.
apply (Zmodeq_small (a mod m) a m).
apply (Z_mod_lt a m Hm).
exact Ha.
replace (a mod m - a)%Z with (- m * (a / m))%Z.
auto with zarith.
generalize (Z_div_mod_eq a m Hm). 
set (q := (a / m)%Z); set (r := (a mod m)%Z); intro H; rewrite H.
rewrite Zplus_comm; unfold Zminus in |- *; rewrite Zopp_plus_distr;
 rewrite Zplus_assoc; rewrite Zplus_opp_r; rewrite Zplus_0_l;
 rewrite Zopp_mult_distr_l_reverse; rewrite Zmult_comm; 
 reflexivity.
Qed.

Lemma Zmod_opp_nonzero :
 forall m a : Z,
 (m > 0)%Z -> (a mod m)%Z <> 0%Z -> (- a mod m)%Z = (m - a mod m)%Z.
intros m a Hm Ha.
rewrite (Zmod_opp_elim m a Hm).
apply Zmod_small.
exact Hm.
generalize (Z_mod_lt a m Hm); intro Hlt.
auto with zarith.
Qed.

Lemma Zmod_one_lft : forall m : Z, (m > 1)%Z -> (1 mod m)%Z = 1%Z.
intros m Hm.
apply Zmod_small; auto with zarith.
Qed.

Lemma Zmod_one_rht : forall a : Z, (a mod 1)%Z = 0%Z.
intro a.
generalize (Z_mod_lt a 1).
auto with zarith.
Qed.

Lemma Zmod_lin_comb :
 forall m a : Z,
 (m > 0)%Z -> (Zgcd a m < m)%Z -> ((a * Zgcd_coeff_a a m) mod m)%Z = Zgcd a m.
intros m a Hm Hgcd.
generalize (Zgcd_lin_comb a m); intro Hlincomb.
rewrite (Z_div_mod_eq (Zgcd_coeff_a a m * a) m Hm) in Hlincomb.
rewrite Zmult_comm in Hlincomb.
rewrite Zplus_comm in Hlincomb.
rewrite Zplus_assoc in Hlincomb.
rewrite <- Zmult_plus_distr_l in Hlincomb.
replace (Zgcd a m) with (Zgcd a m mod m)%Z.
rewrite Hlincomb.
rewrite Zmod_plus_compat; auto.
rewrite Zmod_Zmod; auto.
rewrite <- Zmod_plus_compat; auto.
apply Zmod_minus_intro; auto.
set (u := Zgcd_coeff_a a m).
set (v := Zgcd_coeff_b a m).
rewrite (Zplus_comm ((v + u * a / m) * m) (u * a)).
unfold Zminus in |- *.
rewrite Zopp_plus_distr.
rewrite Zplus_assoc.
rewrite (Zmult_comm a u).
rewrite Zplus_opp_r.
rewrite Zplus_0_l.
rewrite <- Zopp_mult_distr_l_reverse.
apply Zmod_multiple; auto.
apply Zmod_small; auto.
auto with zarith.
Qed.

Lemma Zmod_relprime_inv :
 forall m a : Z,
 (m > 1)%Z -> Zrelprime a m -> ((a * Zgcd_coeff_a a m) mod m)%Z = 1%Z.
intros m a Hm H1.
unfold Zrelprime in H1.
generalize (Zgcd_lin_comb a m).
intro Hlc.
rewrite H1 in Hlc.
rewrite (Zmult_comm (Zgcd_coeff_a a m) a) in Hlc.
assert (Hqr : (a * Zgcd_coeff_a a m)%Z = (- Zgcd_coeff_b a m * m + 1)%Z).
rewrite Zplus_comm.
rewrite Hlc.
rewrite <- Zplus_assoc.
rewrite Zopp_mult_distr_l_reverse.
auto with zarith.
generalize (Z_div_mod_eq (a * Zgcd_coeff_a a m) m); intro Hdivmod;
 assert (Hm0 : (m > 0)%Z); auto with zarith; generalize (Hdivmod Hm0);
 clear Hdivmod; intro Hdivmod.
rewrite (Zmult_comm m (a * Zgcd_coeff_a a m / m)) in Hdivmod.
apply (Zdiv_remainder_unique _ _ _ _ (- Zgcd_coeff_b a m) 1 Hdivmod).
apply Z_mod_lt.
auto with zarith.
exact Hqr.
auto with zarith.
Qed.

End zmod.


Hint Resolve Zmod_zero_lft: zarith.
Hint Resolve Zmod_zero_rht: zarith.
Hint Resolve Zmod_same: zarith.
Hint Resolve Zmod_Zmod: zarith.
Hint Resolve Zmod_cancel_multiple: zarith.
Hint Resolve Zmod_multiple: zarith.
Hint Resolve Zmod_minus_intro: zarith.
Hint Resolve Zmod_plus_compat: zarith.
Hint Resolve Zmod_plus_compat_lft: zarith.
Hint Resolve Zmod_plus_compat_rht: zarith.
Hint Resolve Zmod_opp_elim: zarith.
Hint Resolve Zmod_minus_elim: zarith.
Hint Resolve Zmod_mult_compat: zarith.
Hint Resolve Zmod_mult_compat_lft: zarith.
Hint Resolve Zmod_mult_compat_rht: zarith.
Hint Resolve Zmod_opp_zero: zarith.
Hint Resolve Zmod_small: zarith.
Hint Resolve Zmod_opp_nonzero: zarith.
Hint Resolve Zmod_one_lft: zarith.
Hint Resolve Zmod_one_rht: zarith.
Hint Resolve Zmod_lin_comb: zarith.
Hint Resolve Zmod_relprime_inv: zarith.

Definition pos2Z (p : positive) := Zpos p.

Coercion pos2Z : positive >-> Z.

(*
** Equality modulo m
Let m be a positive number.
*)

Section zmodeq.

Variable m : positive.

Definition Zmodeq (a b : Z) := Zdivides m (a - b).

Lemma Zmodeq_dec : forall a b : Z, {Zmodeq a b} + {~ Zmodeq a b}.
intros a b.
unfold Zmodeq in |- *.
apply Zdivides_dec. 
Qed.

Lemma Zmodeq_modeq : forall a b : Z, Zmodeq a b -> (a mod m)%Z = (b mod m)%Z.
intros a b H.
apply Zmod_minus_intro. 
auto with zarith.
unfold Zmodeq in H.
apply Zmod0_Zdivides.
intro Hfalse; inversion Hfalse.
assumption.
Qed.

Lemma Zmodeq_eqmod : forall a b : Z, (a mod m)%Z = (b mod m)%Z -> Zmodeq a b.
intros a b H.
unfold Zmodeq in |- *.
apply Zdivides_Zmod0.
intro Hfalse; inversion Hfalse.
apply Zmod_minus_elim; auto with zarith.
Qed.

Lemma Zmodeq_refl : forall a : Z, Zmodeq a a.
intros.
unfold Zmodeq in |- *.
unfold Zminus in |- *.
rewrite Zplus_opp_r.
apply Zdivides_zero_rht.
Qed.

Lemma Zmodeq_symm : forall a b : Z, Zmodeq a b -> Zmodeq b a.
unfold Zmodeq in |- *.
intros.
replace (b - a)%Z with (- (a - b))%Z; auto with zarith.
Qed.

Lemma Zmodeq_trans : forall a b c : Z, Zmodeq b a -> Zmodeq a c -> Zmodeq b c.
unfold Zmodeq in |- *.
intros.
replace (b - c)%Z with (b - a + (a - c))%Z; auto with zarith.
Qed.

Lemma Zmodeq_zero : forall a : Z, Zmodeq a 0 <-> Zdivides m a.
unfold Zmodeq in |- *; unfold Zdivides in |- *.
intros.
unfold Zminus in |- *.
simpl in |- *.
rewrite Zplus_0_r.
tauto.
Qed.

Lemma Zmodeq_rem : forall a : Z, Zmodeq a (a mod m).
intros.
unfold Zmodeq in |- *.
exists (a / m)%Z.
rewrite Zmult_comm.
generalize (Z_div_mod_eq a m).
cut (m > 0)%Z; auto with zarith.
Qed.

Lemma Zmodeq_plus_compat :
 forall a b c d : Z, Zmodeq a b -> Zmodeq c d -> Zmodeq (a + c) (b + d).
intros a b c d.
unfold Zmodeq in |- *.
unfold Zdivides in |- *.
intros Hab Hcd.
elim Hab.
intros q1 H1.
elim Hcd.
intros q2 H2.
exists (q1 + q2)%Z.
rewrite Zmult_plus_distr_l.
auto with zarith.
Qed.

Definition Zmodeq_plus_elim := Zmodeq_plus_compat.

Lemma Zmodeq_plus_elim_lft :
 forall a b c : Z, Zmodeq a b -> Zmodeq (c + a) (c + b).
intros.
apply Zmodeq_plus_compat.
apply Zmodeq_refl.
assumption.
Qed.

Lemma Zmodeq_plus_elim_rht :
 forall a b c : Z, Zmodeq a b -> Zmodeq (a + c) (b + c).
intros.
apply Zmodeq_plus_compat.
assumption.
apply Zmodeq_refl.
Qed.


Lemma Zmodeq_mult_elim_lft :
 forall a b c : Z, Zmodeq a b -> Zmodeq (c * a) (c * b).
intros.
unfold Zmodeq in |- *.
unfold Zminus in |- *.
rewrite (Zmult_comm c b).
rewrite <- Zopp_mult_distr_l_reverse.
rewrite (Zmult_comm c a).
rewrite <- Zmult_plus_distr_l.
fold (a - b)%Z in |- *.
apply Zdivides_mult_elim_rht.
assumption.
Qed.

Lemma Zmodeq_mult_elim_rht :
 forall a b c : Z, Zmodeq a b -> Zmodeq (a * c) (b * c).
intros.
rewrite (Zmult_comm a c).
rewrite (Zmult_comm b c).
apply Zmodeq_mult_elim_lft.
assumption.
Qed.

Lemma Zmodeq_mult_compat :
 forall a b c d : Z, Zmodeq a b -> Zmodeq c d -> Zmodeq (a * c) (b * d).
intros a b c d Hab Hcd.
apply (Zmodeq_trans (b * c)).
apply Zmodeq_mult_elim_rht; assumption.
apply Zmodeq_mult_elim_lft; assumption.
Qed.

Definition Zmodeq_mult_elim := Zmodeq_mult_compat.


Lemma Zmodeq_opp_elim : forall a b : Z, Zmodeq a b -> Zmodeq (- a) (- b).
intros a b H.
replace (- a)%Z with (-1 * a)%Z; auto with zarith.
replace (- b)%Z with (-1 * b)%Z; auto with zarith.
apply Zmodeq_mult_elim.
apply Zmodeq_refl.
exact H.
Qed.

Lemma Zmodeq_opp_intro : forall a b : Z, Zmodeq (- a) (- b) -> Zmodeq a b.
intros a b H.
rewrite <- (Zopp_involutive a).
rewrite <- (Zopp_involutive b).
apply (Zmodeq_opp_elim _ _ H).
Qed.


Lemma Zmodeq_gcd_compat_lft :
 forall a b : Z, Zmodeq a b -> Zgcd m a = Zgcd m b.
unfold Zmodeq in |- *.
intros a b H0.
elim H0; intros q Hq.
replace (Zgcd m b) with (Zgcd m (b + q * m)); auto with zarith.
rewrite Hq.
replace (b + (a - b))%Z with a; auto with zarith. 
Qed.

Lemma Zmodeq_gcd_compat_rht :
 forall a b : Z, Zmodeq a b -> Zgcd a m = Zgcd b m.
intros.
rewrite (Zgcd_symm a m).
rewrite (Zgcd_symm b m).
apply Zmodeq_gcd_compat_lft.
assumption.
Qed.

Lemma Zmodeq_relprime :
 forall a b : Z, Zmodeq a b -> Zrelprime a m -> Zrelprime b m.
intros a b H.
unfold Zrelprime in |- *.
rewrite (Zmodeq_gcd_compat_rht a b H).
tauto.
Qed.

Lemma Zmodeq_mod_elim :
 forall a b : Z, Zmodeq a b -> Zmodeq (a mod m) (b mod m).
intros a b H.
apply Zmodeq_eqmod.
rewrite Zmod_Zmod; auto with zarith.
rewrite Zmod_Zmod; auto with zarith.
apply Zmodeq_modeq.
exact H.
Qed.

Lemma Zmodeq_mod_elim_lft : forall a b : Z, Zmodeq a b -> Zmodeq (a mod m) b.
intros a b H.
apply Zmodeq_eqmod.
rewrite Zmod_Zmod; auto with zarith.
apply Zmodeq_modeq.
exact H.
Qed.

Lemma Zmodeq_mod_elim_rht : forall a b : Z, Zmodeq a b -> Zmodeq a (b mod m).
intros a b H.
apply Zmodeq_eqmod.
rewrite Zmod_Zmod; auto with zarith.
apply Zmodeq_modeq.
exact H.
Qed.

Lemma Zmodeq_mod_intro :
 forall a b : Z, Zmodeq (a mod m) (b mod m) -> Zmodeq a b.
intros a b H.
apply Zmodeq_eqmod.
rewrite <- (Zmod_Zmod m a); auto with zarith.
rewrite <- (Zmod_Zmod m b); auto with zarith.
apply Zmodeq_modeq.
exact H.
Qed.

Lemma Zmodeq_mod_intro_lft : forall a b : Z, Zmodeq (a mod m) b -> Zmodeq a b.
intros a b H.
apply Zmodeq_eqmod.
rewrite <- (Zmod_Zmod m a); auto with zarith.
apply Zmodeq_modeq.
exact H.
Qed.

Lemma Zmodeq_mod_intro_rht : forall a b : Z, Zmodeq a (b mod m) -> Zmodeq a b.
intros a b H.
apply Zmodeq_eqmod.
rewrite <- (Zmod_Zmod m b); auto with zarith.
apply Zmodeq_modeq.
exact H.
Qed.


End zmodeq.


Hint Resolve Zmodeq_dec: zarith.
Hint Resolve Zmodeq_modeq: zarith.
Hint Resolve Zmodeq_eqmod: zarith.
Hint Resolve Zmodeq_refl: zarith.
Hint Resolve Zmodeq_symm: zarith.
Hint Resolve Zmodeq_trans: zarith.
Hint Resolve Zmodeq_zero: zarith.
Hint Resolve Zmodeq_rem: zarith.
Hint Resolve Zmodeq_plus_compat: zarith.
Hint Resolve Zmodeq_plus_elim: zarith.
Hint Resolve Zmodeq_plus_elim_lft: zarith.
Hint Resolve Zmodeq_plus_elim_rht: zarith.
Hint Resolve Zmodeq_mult_elim_lft: zarith.
Hint Resolve Zmodeq_mult_elim_rht: zarith.
Hint Resolve Zmodeq_mult_compat: zarith.
Hint Resolve Zmodeq_mult_elim: zarith.
Hint Resolve Zmodeq_opp_intro: zarith.
Hint Resolve Zmodeq_opp_elim: zarith.
Hint Resolve Zmodeq_gcd_compat_lft: zarith.
Hint Resolve Zmodeq_gcd_compat_rht: zarith.
Hint Resolve Zmodeq_relprime: zarith.
Hint Resolve Zmodeq_mod_elim: zarith.
Hint Resolve Zmodeq_mod_elim_lft: zarith.
Hint Resolve Zmodeq_mod_elim_rht: zarith.
Hint Resolve Zmodeq_mod_intro: zarith.
Hint Resolve Zmodeq_mod_intro_lft: zarith.
Hint Resolve Zmodeq_mod_intro_rht: zarith.


(*
Notation " a ~ b  ( 'mod' m ) "  := (Zmodeq m a b) (at level 1, a,b,m at level 10).

Syntax constr level 5:
  Zmodeq_print [ (Zmodeq $c1 $c2 $c3) ] -> [ $c2 "~" $c3 "(" "mod" $c1 ")" ].
*)


