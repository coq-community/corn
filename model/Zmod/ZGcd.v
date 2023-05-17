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
(* ZGcd.v, by Vince Barany *)

Require Export CoRN.model.Zmod.ZDivides.
Require Export Coq.Init.Wf.
From Coq Require Import Lia.

(**
* The GCD-function over Z
In this file we will define a GCD-function over Z. To do that we first
look at a GCD-function over the positive numbers. At the end we will
also define what it is for two numbers to be relatively prime, and
what prime numbers are.
** GCD over `positive'
*)

Section pgcd.


Definition pp := (positive * positive)%type.

Definition pp_lt (x y : pp) :=
  let (a, b) := x in
  let (c, d) := y in (b ?= d)%positive = Datatypes.Lt.

Lemma pp_lt_wf : Wf.well_founded pp_lt.
Proof.
 red in |- *. intros x.
 assert (forall (n : nat) (a b : positive), nat_of_P b < n -> Acc pp_lt (a, b)).
  simple induction n.
   intros a b H0.
   elim (Nat.nlt_0_r _ H0).
  intros n0 Hind a b HSn0.
  assert (Hdisj : nat_of_P b < n0 \/ nat_of_P b = n0).
   lia.
  elim Hdisj.
   apply Hind.
  intro Heq.
  assert (Hy : forall y : pp, pp_lt y (a, b) -> Acc pp_lt y).
   intro y; elim y; intros c d Hdb.
   unfold pp_lt in Hdb.
   assert (Hd : nat_of_P d < n0).
    rewrite <- Heq.
    apply nat_of_P_lt_Lt_compare_morphism.
    exact Hdb.
   apply Hind.
   exact Hd.
  exact (Acc_intro (a, b) Hy).
 elim x; intros a b.
 apply (H (S (nat_of_P b))).
 auto.
Qed.

Lemma rem_lt :
 forall a b r : positive,
 (Zpos a mod Zpos b)%Z = Zpos r -> pp_lt (b, r) (a, b).
Proof.
 intros a b r Hr.
 generalize (Z_mod_lt (Zpos a) (Zpos b)).
 intro H; elim H; clear H.
  intros H0 H1.
  rewrite Hr in H1.
  unfold pp_lt in |- *.
  auto with zarith.
 auto with zarith.
Qed.

Lemma rem_dec :
 forall a b : positive,
 ((Zpos a mod Zpos b)%Z = 0%Z)
 or ({r : positive| (Zpos a mod Zpos b)%Z = Zpos r}).
Proof.
 intros a b.
 set (r := (Zpos a mod Zpos b)%Z) in *.
 assert (Hr : r = (Zpos a mod Zpos b)%Z); auto; generalize Hr.
 case (Zpos a mod Zpos b)%Z.
   intros; left; auto.
  intros p Hp; right; exists p; auto.
 intros p Hp; unfold r in Hp; elim (Zmod_POS_nonNEG _ _ _ Hp).
Defined.

(*
Eval compute in (rem_dec 3 2).
*)

Definition pp_gcd_ind (ab : pp) :
  (forall cd : pp, pp_lt cd ab -> positive * (Z * Z)) -> positive * (Z * Z) :=
  prod_rec
    (fun ab : positive * positive =>
     (forall cd : pp, pp_lt cd ab -> positive * (Z * Z)) ->
     positive * (Z * Z))
    (fun (a b : positive)
       (Hind : forall cd : pp, pp_lt cd (a, b) -> positive * (Z * Z)) =>
     match rem_dec a b with
     | inl _ => (b, (0%Z, 1%Z))
     | inr (existT _ r' Hr') =>
         let (d, uv) := Hind (b, r') (rem_lt a b r' Hr') in
         let (u, v) := uv in (d, (v, (u - Zpos a / Zpos b * v)%Z))
     end) ab.
(*
Eval compute in (pp_gcd_ind (3%positive, 2%positive)).
*)

Lemma pp_gcd_ind_ext :
 forall (x : pp) (f g : forall y : pp, pp_lt y x -> positive * (Z * Z)),
 (forall (y : pp) (p : pp_lt y x), f y p = g y p) ->
 pp_gcd_ind x f = pp_gcd_ind x g.
Proof.
 intros x; elim x; intros a b.
 intros f g Hext.
 simpl in |- *.
 case (rem_dec a b).
  auto.
 intro Hex; elim Hex; intros r Hr.
 rewrite Hext.
 auto.
Qed.

Definition p_gcd_duv (a b : positive) :=
  Fix pp_lt_wf (fun _: pp => (positive * (Z * Z))%type) pp_gcd_ind (a, b).
Definition p_gcd (a b : positive) := let (d, _) := p_gcd_duv a b in d.
Definition p_gcd_coeff_a (a b : positive) :=
  let (_, uv) := p_gcd_duv a b in let (u, _) := uv in u.
Definition p_gcd_coeff_b (a b : positive) :=
  let (_, uv) := p_gcd_duv a b in let (_, v) := uv in v.

Lemma p_gcd_duv_rec_zero :
    forall a b : positive,
    (Zpos a mod Zpos b)%Z = 0%Z -> p_gcd_duv a b = (b, (0%Z, 1%Z)).
Proof.
 intros a b Hr.
 unfold p_gcd_duv.
 rewrite Fix_eq.
  simpl.
  case (rem_dec a b).
   auto.
  intro Hex; elim Hex; intros r' Hr'.
  rewrite Hr in Hr'.
  discriminate.
 apply pp_gcd_ind_ext.
Qed.

Lemma p_gcd_rec_zero :
 forall a b : positive, (Zpos a mod Zpos b)%Z = 0%Z -> p_gcd a b = b.
Proof.
 intros a b H0.
 unfold p_gcd in |- *.
 rewrite p_gcd_duv_rec_zero.
  reflexivity.
 exact H0.
Qed.

Lemma p_gcd_coeff_a_rec_zero :
 forall a b : positive,
 (Zpos a mod Zpos b)%Z = 0%Z -> p_gcd_coeff_a a b = 0%Z.
Proof.
 intros a b H0.
 unfold p_gcd_coeff_a in |- *.
 rewrite p_gcd_duv_rec_zero.
  reflexivity.
 exact H0.
Qed.

Lemma p_gcd_coeff_b_rec_zero :
 forall a b : positive,
 (Zpos a mod Zpos b)%Z = 0%Z -> p_gcd_coeff_b a b = 1%Z.
Proof.
 intros a b H0.
 unfold p_gcd_coeff_b in |- *.
 rewrite p_gcd_duv_rec_zero.
  reflexivity.
 exact H0.
Qed.

Lemma
  p_gcd_duv_rec :
    forall a b r : positive,
    (Zpos a mod Zpos b)%Z = Zpos r ->
    p_gcd_duv a b =
    (let (d, uv) := p_gcd_duv b r in
     let (u, v) := uv in (d, (v, (u - Zpos a / Zpos b * v)%Z))).
Proof.
 intros a b r Hr.
 unfold p_gcd_duv.
 fold (p_gcd_duv b r).
 rewrite Fix_eq; simpl.
  case (rem_dec a b).
   rewrite Hr; intros; discriminate.
  intro Hex; elim Hex; intros r' Hr'.
  fold (p_gcd_duv b r').
  rewrite Hr in Hr'.
  inversion Hr'.
  auto.
 apply pp_gcd_ind_ext.
Qed.

Lemma p_gcd_rec :
 forall a b r : positive,
 (Zpos a mod Zpos b)%Z = Zpos r -> p_gcd a b = p_gcd b r.
Proof.
 intros a b r Hr.
 unfold p_gcd in |- *.
 rewrite (p_gcd_duv_rec a b r Hr).
 elim (p_gcd_duv b r); intros d uv; elim uv; intros u v.
 reflexivity.
Qed.

Lemma p_gcd_rec_coeff_a :
 forall a b r : positive,
 (Zpos a mod Zpos b)%Z = Zpos r -> p_gcd_coeff_a a b = p_gcd_coeff_b b r.
Proof.
 intros a b r Hr.
 unfold p_gcd_coeff_a in |- *.
 unfold p_gcd_coeff_b in |- *.
 rewrite (p_gcd_duv_rec a b r Hr).
 elim (p_gcd_duv b r); intros d uv; elim uv; intros u v.
 reflexivity.
Qed.

Lemma p_gcd_rec_coeff_b :
 forall a b r : positive,
 (Zpos a mod Zpos b)%Z = Zpos r ->
 p_gcd_coeff_b a b =
 (p_gcd_coeff_a b r - Zpos a / Zpos b * p_gcd_coeff_b b r)%Z.
Proof.
 intros a b r Hr.
 unfold p_gcd_coeff_a in |- *.
 unfold p_gcd_coeff_b in |- *.
 rewrite (p_gcd_duv_rec a b r Hr).
 elim (p_gcd_duv b r); intros d uv; elim uv; intros u v.
 reflexivity.
Qed.

Lemma pp_gcd_lin_comb :
 forall x : pp,
 let (a, b) := x in
 Zpos (p_gcd a b) =
 (p_gcd_coeff_a a b * Zpos a + p_gcd_coeff_b a b * Zpos b)%Z.
Proof.
 apply (well_founded_ind pp_lt_wf (fun x : pp => let (a, b) := x in Zpos (p_gcd a b) =
   (p_gcd_coeff_a a b * Zpos a + p_gcd_coeff_b a b * Zpos b)%Z)).
 intros x; elim x; intros a b.
 unfold p_gcd, p_gcd_coeff_a, p_gcd_coeff_b in |- *.
 intros Hind.
 case (rem_dec a b).
  intros Hr.
  rewrite (p_gcd_duv_rec_zero a b Hr).
  auto with zarith.
 intros Hr.
 elim Hr; clear Hr; intros r Hr.
 generalize (Hind (b, r) (rem_lt a b r Hr)).
 rewrite (p_gcd_duv_rec a b r Hr).
 elim (p_gcd_duv b r); intros d' uv'; elim uv'; intros u' v'.
 intro Hd'; rewrite Hd'.
 set (q := (Zpos a / Zpos b)%Z) in *.
 rewrite (Z_div_mod_eq_full (Zpos a) (Zpos b)).
  fold q in |- *.
  rewrite Hr.
  rewrite Zmult_plus_distr_r.
  rewrite BinInt.Zmult_minus_distr_r.
  rewrite (Zmult_assoc v' (Zpos b) q).
  rewrite (Zmult_comm (v' * Zpos b) q).
  rewrite (Zmult_assoc q v' (Zpos b)).
  lia.
Qed.

Lemma p_gcd_lin_comb :
 forall a b : positive,
 Zpos (p_gcd a b) =
 (p_gcd_coeff_a a b * Zpos a + p_gcd_coeff_b a b * Zpos b)%Z.
Proof.
 intros a b.
 apply (pp_gcd_lin_comb (a, b)).
Qed.

Lemma pp_gcd_is_divisor :
 forall ab : pp,
 let (a, b) := ab in
 Zdivides (Zpos (p_gcd a b)) (Zpos a) /\ Zdivides (Zpos (p_gcd a b)) (Zpos b).
Proof.
 apply (well_founded_ind pp_lt_wf (fun y : pp => let (u, v) := y in
   Zdivides (Zpos (p_gcd u v)) (Zpos u) /\ Zdivides (Zpos (p_gcd u v)) (Zpos v))).
 intro x; elim x; intros a b.
 unfold p_gcd, p_gcd_coeff_a, p_gcd_coeff_b in |- *.
 intros Hind.
 case (rem_dec a b).
  intros Hr.
  rewrite (p_gcd_duv_rec_zero a b Hr).
  auto with zarith.
 intros Hr; elim Hr; clear Hr; intros r Hr.
 generalize (Hind (b, r) (rem_lt a b r Hr)).
 rewrite (p_gcd_duv_rec a b r Hr).
 elim (p_gcd_duv b r); intros d' uv'; elim uv'; intros u' v'.
 intro Hd'.
 split.
  rewrite (Z_div_mod_eq_full (Zpos a) (Zpos b)).
   rewrite Hr.
   apply Zdivides_plus_elim.
    apply Zdivides_mult_elim_rht.
    tauto.
   tauto.
 tauto.
Qed.

Lemma p_gcd_is_divisor :
 forall a b : positive,
 Zdivides (Zpos (p_gcd a b)) (Zpos a) /\ Zdivides (Zpos (p_gcd a b)) (Zpos b).
Proof.
 intros a b.
 apply (pp_gcd_is_divisor (a, b)).
Qed.

Lemma p_gcd_duv_symm :
 forall a b : positive,
 a <> b ->
 p_gcd_duv a b = (p_gcd b a, (p_gcd_coeff_b b a, p_gcd_coeff_a b a)).
Proof.
 intros a b Hdiff.
 unfold p_gcd, p_gcd_coeff_a, p_gcd_coeff_b in |- *.
 set (rel := (Zpos a ?= Zpos b)%Z) in *.
 cut ((Zpos a ?= Zpos b)%Z = rel).
  case rel.
    intro Hegal.
    assert (Heq : Zpos a = Zpos b).
     apply Zle_antisymm.
      intro H; rewrite H in Hegal; discriminate.
     apply Z.le_ge; intro H; rewrite H in Hegal; discriminate.
    inversion Heq.
    tauto.
   intro Hlt.
   rewrite (p_gcd_duv_rec a b a).
    elim (p_gcd_duv b a); intros d uv; elim uv; intros u v.
    cut ((Zpos a / Zpos b)%Z = 0%Z).
     intros H0; rewrite H0.
     rewrite Zmult_0_l.
     unfold Zminus in |- *.
     simpl in |- *.
     rewrite Zplus_0_r.
     reflexivity.
    apply (Zdiv_lt_POS a b Hlt).
   apply (Zmod_lt_POS a b Hlt).
  intro Hgt.
  rewrite (p_gcd_duv_rec b a b).
   elim (p_gcd_duv a b); intros d uv; elim uv; intros u v.
   cut ((Zpos b / Zpos a)%Z = 0%Z).
    intros H0; rewrite H0.
    rewrite Zmult_0_l.
    unfold Zminus in |- *; simpl in |- *.
    rewrite Zplus_0_r.
    reflexivity.
   apply (Zdiv_lt_POS b a); apply Z.gt_lt; assumption.
  apply (Zmod_lt_POS b a); apply Z.gt_lt; assumption.
 auto.
Qed.

Lemma p_gcd_symm : forall a b : positive, p_gcd a b = p_gcd b a.
Proof.
 intros a b.
 case (Zdec (Zpos a - Zpos b)).
  intro H0.
  cut (Zpos a = Zpos b).
   intro Heq. inversion Heq. reflexivity.
   auto with zarith.
 intro Hdiff.
 cut (a <> b).
  intro Hneq.
  unfold p_gcd in |- *.
  rewrite (p_gcd_duv_symm a b Hneq).
  auto.
 intro Hfalse.
 apply Hdiff.
 rewrite Hfalse.
 auto with zarith.
Qed.
End pgcd.


(**
** GCD over Z
*)


Section zgcd.


Definition Zis_gcd (a b d : Z) :=
  (a = 0%Z -> b = 0%Z -> d = 0%Z) /\
  (a <> 0%Z \/ b <> 0%Z ->
   (d > 0)%Z /\
   Zdivides d a /\
   Zdivides d b /\
   (forall q : Z, Zdivides q a /\ Zdivides q b -> Zdivides q d)).

Lemma Zis_gcd_unique :
 forall a b d e : Z, Zis_gcd a b d -> Zis_gcd a b e -> d = e.
Proof.
 intros a b d e.
 unfold Zis_gcd in |- *.
 intros Hd He.
 elim Hd; intros Hdl Hdr.
 elim He; intros Hel Her.
 induction  a as [| p| p].
   induction  b as [| p| p].
     transitivity 0%Z.
      apply Hdl; reflexivity; reflexivity.
     symmetry  in |- *.
     apply Hel; reflexivity; reflexivity.
    elim Hdr. intros Hd0 Hddiv.
     elim Her. intros He0 Hediv.
      elim Hddiv; intros _ Hddiv2.
      elim Hddiv2; intros _ Hdgcd.
      elim Hediv; intros _ Hediv2.
      elim Hediv2; intros _ Hegcd.
      apply (Zdivides_antisymm _ _ Hd0 He0).
       apply Hegcd; tauto.
      apply Hdgcd; tauto.
     right; discriminate.
    right; discriminate.
   elim Hdr. intros Hd0 Hddiv.
    elim Her. intros He0 Hediv.
     elim Hddiv; intros _ Hddiv2.
     elim Hddiv2; intros _ Hdgcd.
     elim Hediv; intros _ Hediv2.
     elim Hediv2; intros _ Hegcd.
     apply (Zdivides_antisymm _ _ Hd0 He0).
      apply Hegcd; tauto.
     apply Hdgcd; tauto.
    right. discriminate.
    right. discriminate.
   elim Hdr. intros Hd0 Hddiv.
   elim Her. intros He0 Hediv.
    elim Hddiv; intros _ Hddiv2.
    elim Hddiv2; intros _ Hdgcd.
    elim Hediv; intros _ Hediv2.
    elim Hediv2; intros _ Hegcd.
    apply (Zdivides_antisymm _ _ Hd0 He0).
     apply Hegcd; tauto.
    apply Hdgcd; tauto.
   left. discriminate.
   left. discriminate.
  elim Hdr. intros Hd0 Hddiv.
  elim Her. intros He0 Hediv.
   elim Hddiv; intros _ Hddiv2.
   elim Hddiv2; intros _ Hdgcd.
   elim Hediv; intros _ Hediv2.
   elim Hediv2; intros _ Hegcd.
   apply (Zdivides_antisymm _ _ Hd0 He0).
    apply Hegcd; tauto.
   apply Hdgcd; tauto.
  left. discriminate.
  left. discriminate.
Qed.



Definition Zgcd_duv (a b : Z) :=
  match a, b with
  | Z0, Z0 => (0%Z, (0%Z, 0%Z))
  | Z0, Zpos b' => (Zpos b', (0%Z, 1%Z))
  | Z0, Zneg b' => (Zpos b', (0%Z, (-1)%Z))
  | Zpos a', Z0 => (Zpos a', (1%Z, 0%Z))
  | Zpos a', Zpos b' =>
      (Zpos (p_gcd a' b'), (p_gcd_coeff_a a' b', p_gcd_coeff_b a' b'))
  | Zpos a', Zneg b' =>
      (Zpos (p_gcd a' b'), (p_gcd_coeff_a a' b', (- p_gcd_coeff_b a' b')%Z))
  | Zneg a', Z0 => (Zpos a', ((-1)%Z, 0%Z))
  | Zneg a', Zpos b' =>
      (Zpos (p_gcd a' b'), ((- p_gcd_coeff_a a' b')%Z, p_gcd_coeff_b a' b'))
  | Zneg a', Zneg b' =>
      (Zpos (p_gcd a' b'),
      ((- p_gcd_coeff_a a' b')%Z, (- p_gcd_coeff_b a' b')%Z))
  end.

Definition Zgcd (a b : Z) := let (d, _) := Zgcd_duv a b in d.
Definition Zgcd_coeff_a (a b : Z) :=
  let (_, uv) := Zgcd_duv a b in let (u, _) := uv in u.
Definition Zgcd_coeff_b (a b : Z) :=
  let (_, uv) := Zgcd_duv a b in let (_, v) := uv in v.



Lemma Zgcd_duv_zero_rht :
 forall a : Z, Zgcd_duv a 0 = (Z.abs a, (Z.sgn a, 0%Z)).
Proof.
 intro a.
 case a; auto with zarith.
Qed.

Lemma Zgcd_zero_rht : forall a : Z, Zgcd a 0 = Z.abs a.
Proof.
 intro a.
 unfold Zgcd in |- *.
 rewrite Zgcd_duv_zero_rht.
 reflexivity.
Qed.

Lemma Zgcd_coeff_a_zero_rht : forall a : Z, Zgcd_coeff_a a 0 = Z.sgn a.
Proof.
 intro a.
 unfold Zgcd_coeff_a in |- *.
 rewrite Zgcd_duv_zero_rht.
 reflexivity.
Qed.

Lemma Zgcd_coeff_b_zero_rht : forall a : Z, Zgcd_coeff_b a 0 = 0%Z.
Proof.
 intro a.
 unfold Zgcd_coeff_b in |- *.
 rewrite Zgcd_duv_zero_rht.
 reflexivity.
Qed.

Lemma Zgcd_duv_Zopp_l :
 forall a b : Z,
 Zgcd_duv (- a) b =
 (let (d, uv) := Zgcd_duv a b in let (u, v) := uv in (d, ((- u)%Z, v))).
Proof.
 intros a b.
 case a; case b; intros; simpl in |- *; repeat rewrite Z.opp_involutive; reflexivity.
Qed.

Lemma Zgcd_Zopp_l : forall a b : Z, Zgcd (- a) b = Zgcd a b.
Proof.
 intros a b.
 case a; case b; auto with zarith.
Qed.

Lemma Zgcd_coeff_a_Zopp_l :
 forall a b : Z, Zgcd_coeff_a (- a) b = (- Zgcd_coeff_a a b)%Z.
Proof.
 intros.
 unfold Zgcd_coeff_a in |- *.
 rewrite Zgcd_duv_Zopp_l.
 elim (Zgcd_duv a b); intros d uv; elim uv; intros u v.
 reflexivity.
Qed.

Lemma Zgcd_coeff_b_Zopp_l :
 forall a b : Z, Zgcd_coeff_b (- a) b = Zgcd_coeff_b a b.
Proof.
 intros.
 unfold Zgcd_coeff_b in |- *.
 rewrite Zgcd_duv_Zopp_l.
 elim (Zgcd_duv a b); intros d uv; elim uv; intros u v.
 reflexivity.
Qed.

Lemma Zgcd_duv_Zopp_r :
 forall a b : Z,
 Zgcd_duv a (- b) =
 (let (d, uv) := Zgcd_duv a b in let (u, v) := uv in (d, (u, (- v)%Z))).
Proof.
 intros a b.
 case a; case b; intros; simpl in |- *; repeat rewrite Z.opp_involutive; reflexivity.
Qed.

Lemma Zgcd_Zopp_r : forall a b : Z, Zgcd a (- b) = Zgcd a b.
Proof.
 intros a b.
 case a; case b; auto with zarith.
Qed.

Lemma Zgcd_coeff_a_Zopp_r :
 forall a b : Z, Zgcd_coeff_a a (- b) = Zgcd_coeff_a a b.
Proof.
 intros.
 unfold Zgcd_coeff_a in |- *.
 rewrite Zgcd_duv_Zopp_r.
 elim (Zgcd_duv a b); intros d uv; elim uv; intros u v.
 reflexivity.
Qed.

Lemma Zgcd_coeff_b_Zopp_r :
 forall a b : Z, Zgcd_coeff_b a (- b) = (- Zgcd_coeff_b a b)%Z.
Proof.
 intros.
 unfold Zgcd_coeff_b in |- *.
 rewrite Zgcd_duv_Zopp_r.
 elim (Zgcd_duv a b); intros d uv; elim uv; intros u v.
 reflexivity.
Qed.

Lemma Zgcd_duv_abs :
 forall a b : Z,
 Zgcd_duv a b =
 (let (d, uv) := Zgcd_duv (Z.abs a) (Z.abs b) in
  let (u, v) := uv in (d, ((Z.sgn a * u)%Z, (Z.sgn b * v)%Z))).
Proof.
 intros a b.
 case a; case b; intros; unfold Z.abs, Z.sgn, Zgcd_duv in |- *;
   repeat (fold (- (1))%Z in |- *; rewrite <- Zopp_mult_distr_l);
     repeat rewrite Zmult_1_l; reflexivity.
Qed.

Lemma Zgcd_abs : forall a b : Z, Zgcd a b = Zgcd (Z.abs a) (Z.abs b).
Proof.
 intros a b.
 case a; case b; auto with zarith.
Qed.

Lemma Zgcd_coeff_a_abs :
 forall a b : Z,
 Zgcd_coeff_a a b = (Z.sgn a * Zgcd_coeff_a (Z.abs a) (Z.abs b))%Z.
Proof.
 intros.
 unfold Zgcd_coeff_a in |- *.
 rewrite Zgcd_duv_abs.
 elim (Zgcd_duv (Z.abs a) (Z.abs b)); intros d uv; elim uv; intros u v.
 reflexivity.
Qed.

Lemma Zgcd_coeff_b_abs :
 forall a b : Z,
 Zgcd_coeff_b a b = (Z.sgn b * Zgcd_coeff_b (Z.abs a) (Z.abs b))%Z.
Proof.
 intros.
 unfold Zgcd_coeff_b in |- *.
 rewrite Zgcd_duv_abs.
 elim (Zgcd_duv (Z.abs a) (Z.abs b)); intros d uv; elim uv; intros u v.
 reflexivity.
Qed.

Let Zgcd_duv_rec_subsubcase :
  forall a b : positive,
  Zgcd_duv (Zpos a) (Zpos b) =
  (let (d, uv) := Zgcd_duv (Zpos b) (Zpos a mod Zpos b) in
   let (u, v) := uv in (d, (v, (u - Zpos a / Zpos b * v)%Z))).
Proof.
 intros a b.
 unfold Zgcd_duv in |- *.
 unfold p_gcd, p_gcd_coeff_a, p_gcd_coeff_b in |- *.
 case (rem_dec a b).
  intro Hr.
  rewrite Hr.
  rewrite (p_gcd_duv_rec_zero a b Hr).
  rewrite Zmult_0_r.
  auto with zarith.
 intro Hr; elim Hr; clear Hr; intros r Hr.
 rewrite Hr.
 rewrite (p_gcd_duv_rec a b r Hr).
 elim (p_gcd_duv b r); intros d' uv'; elim uv'; intros u' v'.
 auto.
Qed.

Let Zgcd_duv_rec_subcase :
  forall (a : Z) (pb : positive),
  Zgcd_duv a (Zpos pb) =
  (let (d, uv) := Zgcd_duv (Zpos pb) (Z.abs a mod Zpos pb) in
   let (u, v) := uv in (d, ((Z.sgn a * v)%Z, (u - Z.abs a / Zpos pb * v)%Z))).
Proof.
 intros a pb.
 case a.
   unfold Zgcd_duv in |- *; simpl in |- *; reflexivity.
  intro pa.
  unfold Z.abs, Z.sgn in |- *.
  rewrite Zgcd_duv_rec_subsubcase.
  elim (Zgcd_duv (Zpos pb) (Zpos pa mod Zpos pb)); intros d uv; elim uv; intros u v.
  rewrite Zmult_1_l.
  reflexivity.
 intro pa.
 rewrite (Zgcd_duv_abs (Zneg pa) (Zpos pb)).
 unfold Z.abs, Z.sgn in |- *.
 rewrite Zgcd_duv_rec_subsubcase.
 elim (Zgcd_duv (Zpos pb) (Zpos pa mod Zpos pb)); intros d uv; elim uv; intros u v.
 rewrite Zmult_1_l.
 reflexivity.
Qed.

Lemma Zgcd_duv_rec :
 forall a b : Z,
 b <> 0%Z ->
 Zgcd_duv a b =
 (let (d, uv) := Zgcd_duv b (Z.abs a mod Z.abs b) in
  let (u, v) := uv in
  (d, ((Z.sgn a * v)%Z, (u - Z.sgn b * (Z.abs a / Z.abs b) * v)%Z))).
Proof.
 intros a b Hb.
 set (B := b) in *.
 cut (B = b).
  case b.
    intro HB'.
    rewrite HB' in Hb.
    elim Hb.
    reflexivity.
   intros pb HB'.
   rewrite HB'.
   rewrite Zgcd_duv_rec_subcase.
   unfold Z.abs, Z.sgn in |- *. fold (Z.abs a) in |- *. fold (Z.sgn a) in |- *.
   elim (Zgcd_duv (Zpos pb) (Z.abs a mod Zpos pb)); intros d uv; elim uv; intros u v.
   rewrite Zmult_1_l.
   reflexivity.
  intros pb HB'.
  rewrite HB'.
  fold (- Zpos pb)%Z in |- *.
  rewrite Zgcd_duv_Zopp_r.
  rewrite Zgcd_duv_Zopp_l.
  rewrite Zgcd_duv_rec_subcase.
  unfold Z.opp, Z.abs, Z.sgn in |- *. fold (Z.abs a) in |- *. fold (Z.sgn a) in |- *.
  elim (Zgcd_duv (Zpos pb) (Z.abs a mod Zpos pb)); intros d uv; elim uv; intros u v.
  fold (- u)%Z in |- *.
  rewrite Zopp_mult_distr_l_reverse.
  unfold Zminus in |- *.
  rewrite <- Zopp_plus_distr.
  auto with zarith.
 auto.
Qed.

Lemma Zgcd_rec :
 forall a b : Z, b <> 0%Z -> Zgcd a b = Zgcd b (Z.abs a mod Z.abs b).
Proof.
 intros a b Hb.
 unfold Zgcd in |- *.
 rewrite Zgcd_duv_rec.
  elim (Zgcd_duv b (Z.abs a mod Z.abs b)); intros d uv; elim uv; intros u v.
  reflexivity.
 exact Hb.
Qed.

Lemma Zgcd_coeff_a_rec :
 forall a b : Z,
 b <> 0%Z ->
 Zgcd_coeff_a a b = (Z.sgn a * Zgcd_coeff_b b (Z.abs a mod Z.abs b))%Z.
Proof.
 intros a b Hb.
 unfold Zgcd_coeff_a in |- *.
 unfold Zgcd_coeff_b in |- *.
 rewrite Zgcd_duv_rec.
  elim (Zgcd_duv b (Z.abs a mod Z.abs b)); intros d uv; elim uv; intros u v.
  reflexivity.
 exact Hb.
Qed.

Lemma Zgcd_coeff_b_rec :
 forall a b : Z,
 b <> 0%Z ->
 Zgcd_coeff_b a b =
 (Zgcd_coeff_a b (Z.abs a mod Z.abs b) -
  Z.sgn b * (Z.abs a / Z.abs b) * Zgcd_coeff_b b (Z.abs a mod Z.abs b))%Z.
Proof.
 intros a b Hb.
 unfold Zgcd_coeff_a in |- *.
 unfold Zgcd_coeff_b in |- *.
 rewrite Zgcd_duv_rec.
  elim (Zgcd_duv b (Z.abs a mod Z.abs b)); intros d uv; elim uv; intros u v.
  reflexivity.
 exact Hb.
Qed.

Lemma Zgcd_duv_divisor :
 forall a b : Z,
 a <> 0%Z -> Zdivides b a -> Zgcd_duv a b = (Z.abs b, (0%Z, Z.sgn b)).
Proof.
 intros a b Ha.
 case b.
   intros Hdiv.
   replace a with 0%Z; simpl in |- *; auto.
   symmetry  in |- *.
   auto with zarith.
  intros pb Hdiv.
  simpl in |- *.
  rewrite Zgcd_duv_rec_subcase.
  replace (Z.abs a mod Zpos pb)%Z with 0%Z.
   rewrite Zgcd_duv_zero_rht.
   rewrite Zmult_0_r.
   rewrite Zmult_0_r.
   simpl in |- *.
   reflexivity.
  symmetry  in |- *.
  auto with zarith.
 intros pb Hdiv.
 simpl in |- *.
 fold (- Zpos pb)%Z in |- *.
 rewrite Zgcd_duv_Zopp_r.
 rewrite Zgcd_duv_rec_subcase.
 replace (Z.abs a mod Zpos pb)%Z with 0%Z.
  rewrite Zgcd_duv_zero_rht.
  rewrite Zmult_0_r.
  rewrite Zmult_0_r.
  simpl in |- *.
  reflexivity.
 symmetry  in |- *.
 auto with zarith.
Qed.

Lemma Zgcd_divisor :
 forall a b : Z, a <> 0%Z -> Zdivides b a -> Zgcd a b = Z.abs b.
Proof.
 intros.
 unfold Zgcd in |- *.
 rewrite Zgcd_duv_divisor; auto.
Qed.

Lemma Zgcd_coeff_a_divisor :
 forall a b : Z, a <> 0%Z -> Zdivides b a -> Zgcd_coeff_a a b = 0%Z.
Proof.
 intros.
 unfold Zgcd_coeff_a in |- *.
 rewrite Zgcd_duv_divisor; auto.
Qed.

Lemma Zgcd_coeff_b_divisor :
 forall a b : Z, a <> 0%Z -> Zdivides b a -> Zgcd_coeff_b a b = Z.sgn b.
Proof.
 intros.
 unfold Zgcd_coeff_b in |- *.
 rewrite Zgcd_duv_divisor; auto.
Qed.

Lemma Zgcd_duv_symm :
 forall a b : Z,
 Z.abs a <> Z.abs b ->
 Zgcd_duv a b = (Zgcd b a, (Zgcd_coeff_b b a, Zgcd_coeff_a b a)).
Proof.
 intros a b.
 unfold Zgcd, Zgcd_coeff_a, Zgcd_coeff_b in |- *.
 cut (forall p q : positive, Zpos p <> Zpos q -> p <> q).
  case a; case b; simpl in |- *; intros; unfold p_gcd, p_gcd_coeff_a, p_gcd_coeff_b in |- *;
    try rewrite p_gcd_duv_symm; auto.
 intros p q Hneq; intro Hfalse.
 apply Hneq; rewrite Hfalse; auto.
Qed.

Lemma Zgcd_symm : forall a b : Z, Zgcd a b = Zgcd b a.
Proof.
 intros a b.
 case a; case b; simpl in |- *; intros; unfold Zgcd, Zgcd_duv in |- *; try rewrite p_gcd_symm; auto.
Qed.

Lemma Zgcd_coeff_a_symm :
 forall a b : Z, Z.abs a <> Z.abs b -> Zgcd_coeff_a a b = Zgcd_coeff_b b a.
Proof.
 intros a b Hneq.
 unfold Zgcd_coeff_a, Zgcd_coeff_b in |- *.
 rewrite (Zgcd_duv_symm a b Hneq).
 auto.
Qed.

Lemma Zgcd_coeff_b_symm :
 forall a b : Z, Z.abs a <> Z.abs b -> Zgcd_coeff_b a b = Zgcd_coeff_a b a.
Proof.
 intros a b Hneq.
 unfold Zgcd_coeff_a, Zgcd_coeff_b in |- *.
 rewrite (Zgcd_duv_symm a b Hneq).
 auto.
Qed.


Lemma Zgcd_is_divisor : forall a b : Z, Zdivides (Zgcd a b) a.
Proof.
 intros a b.
 case a.
   auto with zarith.
  case b.
    auto with zarith.
   intros pb pa; generalize (p_gcd_is_divisor pa pb); tauto.
  intros pb pa; generalize (p_gcd_is_divisor pa pb); tauto.
 case b.
   auto with zarith.
  intros pb pa; generalize (p_gcd_is_divisor pa pb); intro H.
  apply Zdivides_opp_intro_rht; simpl in |- *.
  tauto.
 intros pb pa; generalize (p_gcd_is_divisor pa pb); intro H.
 apply Zdivides_opp_intro_rht; simpl in |- *.
 tauto.
Qed.

Definition Zgcd_is_divisor_lft := Zgcd_is_divisor.
Lemma Zgcd_is_divisor_rht : forall a b : Z, Zdivides (Zgcd a b) b.
Proof.
 intros a b.
 rewrite Zgcd_symm.
 apply Zgcd_is_divisor_lft.
Qed.

Lemma Zgcd_lin_comb :
 forall a b : Z, Zgcd a b = (Zgcd_coeff_a a b * a + Zgcd_coeff_b a b * b)%Z.
Proof.
 intros a b.
 unfold Zgcd, Zgcd_coeff_a, Zgcd_coeff_b in |- *.
 case a; case b; simpl in |- *; intros; repeat rewrite Zmult_opp_comm;
   simpl in |- *; try rewrite p_gcd_lin_comb; auto.
Qed.

Lemma Zgcd_zero : forall a b : Z, Zgcd a b = 0%Z -> a = 0%Z /\ b = 0%Z.
Proof.
 intros a b.
 case a; case b; unfold Zgcd in |- *; simpl in |- *; intros; try discriminate; try tauto.
Qed.

Lemma Zgcd_nonneg : forall a b : Z, (0 <= Zgcd a b)%Z.
Proof.
 intros a b.
 case a; case b; unfold Zgcd in |- *; simpl in |- *; auto with zarith.
Qed.

(* Zgcd_nonneg says Zgcd is never negative, so it might as well return nat: *)

Definition Zgcd_nat (a b: Z): nat :=
 match Zgcd a b with
 | Zpos p => nat_of_P p
 | _ => 0%nat
 end.

Lemma Zgcd_nat_divides (a b: Z): exists c: Z, (c * Zgcd_nat a b = a)%Z.
Proof with auto.
 intros. unfold Zgcd_nat.
 pose proof (Zgcd_nonneg a b) as E.
 destruct (Zgcd_is_divisor a b) as [c ?].
 exists c.
 destruct (Zgcd a b)...
  rewrite inject_nat_convert...
 exfalso. apply E. reflexivity.
Qed.

Lemma Zgcd_nat_sym (a b: Z): Zgcd_nat a b = Zgcd_nat b a.
Proof. unfold Zgcd_nat. intros. rewrite Zgcd_symm. reflexivity. Qed.

Lemma Zgcd_nonzero : forall a b : Z, 0%Z <> Zgcd a b -> a <> 0%Z \/ b <> 0%Z.
Proof.
 intros a b.
 case a.
   case b.
     rewrite Zgcd_zero_rht; simpl in |- *; tauto.
    intros; right; intro; discriminate.
   intros; right; intro; discriminate.
  intros; left; intro; discriminate.
 intros; left; intro; discriminate.
Qed.

Lemma Zgcd_pos : forall a b : Z, a <> 0%Z \/ b <> 0%Z -> (0 < Zgcd a b)%Z.
Proof.
 intros a b Hab.
 generalize (Zgcd_nonneg a b); intro Hnonneg.
 cut (Zgcd a b <> 0%Z).
  auto with zarith.
 intro H0.
 generalize (Zgcd_zero a b H0).
 tauto.
Qed.

Lemma Zgcd_is_gcd : forall a b : Z, Zis_gcd a b (Zgcd a b).
Proof.
 intros a b.
 unfold Zis_gcd in |- *.
 split. intros Ha Hb; rewrite Ha; rewrite Hb; auto with zarith.
  intros Hab.
 split. generalize (Zgcd_pos a b Hab); auto with zarith.
  split. apply Zgcd_is_divisor_lft.
  split. apply Zgcd_is_divisor_rht.
  intros q Hq.
 rewrite Zgcd_lin_comb.
 apply Zdivides_plus_elim.
  apply Zdivides_mult_elim_lft; tauto.
 apply Zdivides_mult_elim_lft; tauto.
Qed.


Lemma Zgcd_intro : forall a b d : Z, Zis_gcd a b d -> Zgcd a b = d.
Proof.
 intros a b d Hisgcd.
 apply (Zis_gcd_unique a b (Zgcd a b) d).
  apply Zgcd_is_gcd.
 exact Hisgcd.
Qed.

Lemma Zgcd_intro_unfolded :
 forall a b d : Z,
 a <> 0%Z \/ b <> 0%Z ->
 (d > 0)%Z ->
 Zdivides d a ->
 Zdivides d b ->
 (forall q : Z, Zdivides q a /\ Zdivides q b -> Zdivides q d) -> Zgcd a b = d.
Proof.
 intros.
 apply Zgcd_intro.
 unfold Zis_gcd in |- *.
 tauto.
Qed.

Lemma Zdiv_gcd_elim_lft :
 forall a b q : Z, Zdivides a q -> Zdivides (Zgcd a b) q.
 intros a b q Hdiv; apply (Zdivides_trans (Zgcd a b) a q); [ apply Zgcd_is_divisor_lft | assumption ].
Qed.

Lemma Zdiv_gcd_elim_rht :
 forall a b q : Z, Zdivides b q -> Zdivides (Zgcd a b) q.
 intros a b q Hdiv; apply (Zdivides_trans (Zgcd a b) b q); [ apply Zgcd_is_divisor_rht | assumption ].
Qed.

Lemma Zdiv_gcd_elim :
 forall a b q : Z, Zdivides q a -> Zdivides q b -> Zdivides q (Zgcd a b).
Proof.
 intros a b q Ha Hb.
 cut (a <> 0%Z \/ b <> 0%Z -> Zdivides q (Zgcd a b)).
  case (Zdec a); case (Zdec b); auto.
  intros Hb0 Ha0; rewrite Ha0 in Ha; rewrite Ha0; rewrite Hb0.
  rewrite Zgcd_zero_rht; auto.
 intro Hnon0; generalize (Zgcd_is_gcd a b); unfold Zis_gcd in |- *; intro H;
   elim H; clear H; intros H0 H1; elim H1; clear H1.
  intros _ H1; elim H1; clear H1; intros _ H1; elim H1; clear H1; intros _ Hdiv.
  generalize (Hdiv q); intro Hq; auto.
 auto.
Qed.

Lemma Zgcd_mod0_lft :
 forall a b : Z, Zgcd a b <> 0%Z -> (a mod Zgcd a b)%Z = 0%Z.
Proof.
 intros; apply Zmod0_Zdivides; auto; apply Zgcd_is_divisor_lft.
Qed.

Lemma Zgcd_mod0_rht :
 forall a b : Z, Zgcd a b <> 0%Z -> (b mod Zgcd a b)%Z = 0%Z.
Proof.
 intros a b.
 rewrite Zgcd_symm.
 apply Zgcd_mod0_lft.
Qed.

Lemma Zgcd_div_mult_lft :
 forall a b : Z, Zgcd a b <> 0%Z -> a = (a / Zgcd a b * Zgcd a b)%Z.
Proof.
 intros a b H0.
 generalize (Zgcd_mod0_lft a b); intro Hmod0.
 rewrite <- Zplus_0_r.
 rewrite <- Hmod0.
  rewrite Zmult_comm.
  apply Z_div_mod_eq_full.
 assumption.
Qed.

Lemma Zgcd_div_mult_rht :
 forall a b : Z, Zgcd a b <> 0%Z -> b = (b / Zgcd a b * Zgcd a b)%Z.
Proof.
 intros a b.
 rewrite Zgcd_symm.
 apply Zgcd_div_mult_lft.
Qed.

Lemma Zgcd_idemp : forall a : Z, (a > 0)%Z -> Zgcd a a = a.
Proof.
 intros a Ha.
 rewrite Zgcd_rec.
  rewrite Z_mod_same.
   rewrite Zgcd_zero_rht.
   auto with zarith.
  replace (Z.abs a) with a.
   assumption.
  symmetry  in |- *; auto with zarith.
 auto with zarith.
Qed.

Lemma Zgcd_zero_lft : forall a : Z, Zgcd 0 a = Z.abs a.
Proof.
 intro a.
 rewrite Zgcd_symm.
 apply Zgcd_zero_rht.
Qed.

Lemma Zgcd_one_lft : forall a : Z, Zgcd 1 a = 1%Z.
Proof.
 intro a.
 generalize (Zgcd_is_divisor_lft 1 a).
 cut (0 < Zgcd 1 a)%Z.
  auto with zarith.
 apply Zgcd_pos.
 left; intro; discriminate.
Qed.

Lemma Zgcd_one_rht : forall a : Z, Zgcd a 1 = 1%Z.
Proof.
 intro a.
 rewrite Zgcd_symm.
 apply Zgcd_one_lft.
Qed.

Lemma Zgcd_le_lft : forall a b : Z, (a > 0)%Z -> (Zgcd a b <= a)%Z.
Proof.
 intros a b Ha.
 generalize (Zgcd_is_divisor_lft a b).
 auto with zarith.
Qed.

Lemma Zgcd_le_rht : forall a b : Z, (b > 0)%Z -> (Zgcd a b <= b)%Z.
Proof.
 intros.
 rewrite Zgcd_symm.
 apply Zgcd_le_lft.
 assumption.
Qed.

Lemma Zgcd_gcd_rl : forall a b : Z, Zgcd a (Zgcd a b) = Zgcd a b.
Proof.
 intros a b.
 case (Zdec a).
  intro H0; rewrite H0; repeat rewrite Zgcd_zero_lft; auto with zarith.
 intro H0.
 replace (Zgcd a b) with (Z.abs (Zgcd a b)).
  rewrite Zgcd_abs.
  replace (Z.abs (Z.abs (Zgcd a b))) with (Zgcd a b).
   apply Zgcd_divisor.
    auto with zarith.
   apply Zdivides_abs_elim_rht.
   apply Zgcd_is_divisor_lft.
  generalize (Zgcd_nonneg a b); rewrite Zabs_idemp; auto with zarith.
 generalize (Zgcd_nonneg a b); auto with zarith.
Qed.

Lemma Zgcd_gcd_rr : forall a b : Z, Zgcd b (Zgcd a b) = Zgcd a b.
Proof.
 intros a b; rewrite (Zgcd_symm a b); apply Zgcd_gcd_rl.
Qed.

Lemma Zgcd_gcd_ll : forall a b : Z, Zgcd (Zgcd a b) a = Zgcd a b.
Proof.
 intros a b; rewrite (Zgcd_symm (Zgcd a b) a); apply Zgcd_gcd_rl.
Qed.

Lemma Zgcd_gcd_lr : forall a b : Z, Zgcd (Zgcd a b) b = Zgcd a b.
 intros a b; rewrite (Zgcd_symm a b); rewrite (Zgcd_symm (Zgcd b a) b); apply Zgcd_gcd_rl.
Qed.

Lemma Zgcd_mult_elim_ll : forall a b : Z, Zgcd (b * a) a = Z.abs a.
Proof.
 intros a b.
 elim (Zdec (b * a)).
  intro Hab; rewrite Hab; rewrite Zgcd_zero_lft; reflexivity.
 intro Hab; apply Zgcd_divisor; auto with zarith.
Qed.

Lemma Zgcd_mult_elim_lr : forall a b : Z, Zgcd (a * b) a = Z.abs a.
Proof.
 intros.
 rewrite Zmult_comm.
 apply Zgcd_mult_elim_ll.
Qed.

Lemma Zgcd_mult_elim_rl : forall a b : Z, Zgcd a (b * a) = Z.abs a.
Proof.
 intros.
 rewrite Zgcd_symm.
 apply Zgcd_mult_elim_ll.
Qed.

Lemma Zgcd_mult_elim_rr : forall a b : Z, Zgcd a (a * b) = Z.abs a.
Proof.
 intros.
 rewrite Zmult_comm.
 rewrite Zgcd_symm.
 apply Zgcd_mult_elim_ll.
Qed.

Lemma Zgcd_plus_elim_rr :
 forall a b c : Z, Zdivides a c -> Zgcd a (b + c) = Zgcd a b.
Proof.
 intros a b c Hdiv.
 elim (Zdec a).
  intro H0; rewrite H0; repeat rewrite Zgcd_zero_lft.
  replace c with 0%Z. rewrite Zplus_0_r; auto.
   rewrite H0 in Hdiv.
  symmetry  in |- *.
  auto with zarith.
 intro Ha.
 apply Zdivides_antisymm.
    generalize (Zgcd_pos a (b + c)); auto with zarith.
   generalize (Zgcd_pos a b); auto with zarith.
  rewrite (Zgcd_lin_comb a b).
  apply Zdivides_plus_elim.
   apply Zdivides_mult_elim_lft.
   apply Zgcd_is_divisor_lft.
  apply Zdivides_mult_elim_lft.
  set (x := (b + c)%Z) in *; replace b with (b + c - c)%Z. unfold x in |- *.
   apply Zdivides_minus_elim.
    apply Zgcd_is_divisor_rht.
   apply (Zdivides_trans (Zgcd a (b + c)) a c).
    apply Zgcd_is_divisor_lft.
   assumption.
  lia.
 rewrite (Zgcd_lin_comb a (b + c)).
 apply Zdivides_plus_elim.
  apply Zdivides_mult_elim_lft.
  apply Zgcd_is_divisor_lft.
 apply Zdivides_mult_elim_lft.
 apply Zdivides_plus_elim.
  apply Zgcd_is_divisor_rht.
 apply (Zdivides_trans (Zgcd a b) a c).
  apply Zgcd_is_divisor_lft.
 assumption.
Qed.

Lemma Zgcd_plus_elim_rl :
 forall a b c : Z, Zdivides a c -> Zgcd a (c + b) = Zgcd a b.
Proof.
 intros a b c.
 rewrite Zplus_comm.
 apply Zgcd_plus_elim_rr.
Qed.

Lemma Zgcd_plus_elim_lr :
 forall a b c : Z, Zdivides b c -> Zgcd (a + c) b = Zgcd a b.
Proof.
 intros a b c.
 rewrite (Zgcd_symm a b).
 rewrite (Zgcd_symm (a + c) b).
 apply Zgcd_plus_elim_rr.
Qed.

Lemma Zgcd_plus_elim_ll :
 forall a b c : Z, Zdivides b c -> Zgcd (c + a) b = Zgcd a b.
Proof.
 intros a b c.
 rewrite Zplus_comm.
 apply Zgcd_plus_elim_lr.
Qed.

Lemma Zgcd_minus_elim_rr :
 forall a b c : Z, Zdivides a c -> Zgcd a (b - c) = Zgcd a b.
Proof.
 intros a b c Hdiv.
 unfold Zminus in |- *.
 apply Zgcd_plus_elim_rr.
 auto with zarith.
Qed.

Lemma Zgcd_minus_elim_rl :
 forall a b c : Z, Zdivides a c -> Zgcd a (c - b) = Zgcd a b.
Proof.
 intros a b c Hdiv.
 replace (c - b)%Z with (- (b - c))%Z.
  rewrite Zgcd_Zopp_r.
  apply Zgcd_minus_elim_rr.
  assumption.
 lia.
Qed.

Lemma Zgcd_minus_elim_lr :
 forall a b c : Z, Zdivides b c -> Zgcd (a - c) b = Zgcd a b.
Proof.
 intros a b c.
 rewrite (Zgcd_symm a b).
 rewrite (Zgcd_symm (a - c) b).
 apply Zgcd_minus_elim_rr.
Qed.

Lemma Zgcd_minus_elim_ll :
 forall a b c : Z, Zdivides b c -> Zgcd (c - a) b = Zgcd a b.
Proof.
 intros a b c.
 rewrite (Zgcd_symm a b).
 rewrite (Zgcd_symm (c - a) b).
 apply Zgcd_minus_elim_rl.
Qed.

Lemma Zgcd_mod_lft : forall a b : Z, (b > 0)%Z -> Zgcd (a mod b) b = Zgcd a b.
Proof.
 intros a b Hb.
 replace (a mod b)%Z with (a - b * (a / b))%Z.
  apply Zgcd_minus_elim_lr.
  apply Zdivides_mult_elim_rht.
  apply Zdivides_ref.
 generalize (Z_div_mod_eq_full a b).
 auto with zarith.
Qed.

Lemma Zgcd_mod_rht : forall a b : Z, (a > 0)%Z -> Zgcd a (b mod a) = Zgcd a b.
Proof.
 intros a b Ha.
 repeat rewrite (Zgcd_symm a); apply Zgcd_mod_lft; exact Ha.
Qed.


Lemma Zgcd_div_gcd_1 :
 forall a b : Z, Zgcd a b <> 0%Z -> Zgcd (a / Zgcd a b) (b / Zgcd a b) = 1%Z.
Proof.
 intros a b Hab.
 apply Zdivides_antisymm; auto with zarith.
  apply Z.lt_gt.
  apply Zgcd_pos.
  generalize (Zgcd_nonzero a b); intro Hnz; elim Hnz; auto.
   intro Ha; left; intro Hfalse; generalize (Zgcd_div_mult_lft a b);
     rewrite Hfalse; simpl in |- *; tauto.
  intro Hb; right; intro Hfalse; generalize (Zgcd_div_mult_rht a b);
    rewrite Hfalse; simpl in |- *; tauto.
 cut (1%Z = (Zgcd_coeff_a a b * (a / Zgcd a b) + Zgcd_coeff_b a b * (b / Zgcd a b))%Z).
  intro H1; rewrite H1.
  apply Zdivides_plus_elim.
   apply Zdivides_mult_elim_lft.
   apply Zgcd_is_divisor_lft.
  apply Zdivides_mult_elim_lft.
  apply Zgcd_is_divisor_rht.
 generalize (Zgcd_lin_comb a b); intro Hlincomb; generalize (Zgcd_is_divisor_lft a b); intro Hdivb;
   elim Hdivb; intros y Hy; generalize (Zgcd_is_divisor_rht a b);
     intro Hdiva; elim Hdiva; intros x Hx; set (d := Zgcd a b).
 move d after Hy.
 fold d in Hx; fold d in Hy.
 replace 1%Z with (Zgcd a b / d)%Z; auto with zarith.
 rewrite Hlincomb.
 set (u := Zgcd_coeff_a a b); set (v := Zgcd_coeff_b a b).
 rewrite Zdiv_plus_elim; auto with zarith.
 rewrite <- Hx; rewrite <- Hy.
 repeat rewrite Zmult_assoc.
 repeat rewrite Zdiv_mult_cancel_rht; auto.
Qed.


End zgcd.


#[global]
Hint Resolve Zgcd_duv_zero_rht: zarith.
#[global]
Hint Resolve Zgcd_zero_rht: zarith.
#[global]
Hint Resolve Zgcd_coeff_a_zero_rht: zarith.
#[global]
Hint Resolve Zgcd_coeff_b_zero_rht: zarith.
#[global]
Hint Resolve Zgcd_duv_Zopp_l: zarith.
#[global]
Hint Resolve Zgcd_Zopp_l: zarith.
#[global]
Hint Resolve Zgcd_coeff_a_Zopp_l: zarith.
#[global]
Hint Resolve Zgcd_coeff_b_Zopp_l: zarith.
#[global]
Hint Resolve Zgcd_duv_Zopp_r: zarith.
#[global]
Hint Resolve Zgcd_Zopp_r: zarith.
#[global]
Hint Resolve Zgcd_coeff_a_Zopp_r: zarith.
#[global]
Hint Resolve Zgcd_coeff_b_Zopp_r: zarith.
#[global]
Hint Resolve Zgcd_duv_abs: zarith.
#[global]
Hint Resolve Zgcd_abs: zarith.
#[global]
Hint Resolve Zgcd_coeff_a_abs: zarith.
#[global]
Hint Resolve Zgcd_coeff_b_abs: zarith.
#[global]
Hint Resolve Zgcd_duv_rec: zarith.
#[global]
Hint Resolve Zgcd_rec: zarith.
#[global]
Hint Resolve Zgcd_coeff_a_rec: zarith.
#[global]
Hint Resolve Zgcd_coeff_b_rec: zarith.
#[global]
Hint Resolve Zgcd_duv_divisor: zarith.
#[global]
Hint Resolve Zgcd_divisor: zarith.
#[global]
Hint Resolve Zgcd_coeff_a_divisor: zarith.
#[global]
Hint Resolve Zgcd_coeff_b_divisor: zarith.
#[global]
Hint Resolve Zgcd_duv_symm: zarith.
#[global]
Hint Resolve Zgcd_symm: zarith.
#[global]
Hint Resolve Zgcd_coeff_a_symm: zarith.
#[global]
Hint Resolve Zgcd_coeff_b_symm: zarith.
#[global]
Hint Resolve Zgcd_is_divisor_lft: zarith.
#[global]
Hint Resolve Zgcd_is_divisor_rht: zarith.
#[global]
Hint Resolve Zgcd_lin_comb: zarith.
#[global]
Hint Resolve Zgcd_zero: zarith.
#[global]
Hint Resolve Zgcd_nonneg: zarith.
#[global]
Hint Resolve Zgcd_nonzero: zarith.
#[global]
Hint Resolve Zgcd_pos: zarith.
#[global]
Hint Resolve Zgcd_is_gcd: zarith.
#[global]
Hint Resolve Zgcd_intro: zarith.
#[global]
Hint Resolve Zgcd_intro_unfolded: zarith.
#[global]
Hint Resolve Zdiv_gcd_elim_lft: zarith.
#[global]
Hint Resolve Zdiv_gcd_elim_rht: zarith.
#[global]
Hint Resolve Zdiv_gcd_elim: zarith.
#[global]
Hint Resolve Zgcd_mod0_lft: zarith.
#[global]
Hint Resolve Zgcd_mod0_rht: zarith.
#[global]
Hint Resolve Zgcd_div_mult_lft: zarith.
#[global]
Hint Resolve Zgcd_div_mult_rht: zarith.
#[global]
Hint Resolve Zgcd_idemp: zarith.
#[global]
Hint Resolve Zgcd_zero_lft: zarith.
#[global]
Hint Resolve Zgcd_zero_rht: zarith.
#[global]
Hint Resolve Zgcd_one_lft: zarith.
#[global]
Hint Resolve Zgcd_one_rht: zarith.
#[global]
Hint Resolve Zgcd_le_lft: zarith.
#[global]
Hint Resolve Zgcd_le_rht: zarith.
#[global]
Hint Resolve Zgcd_gcd_ll: zarith.
#[global]
Hint Resolve Zgcd_gcd_lr: zarith.
#[global]
Hint Resolve Zgcd_gcd_rl: zarith.
#[global]
Hint Resolve Zgcd_gcd_rr: zarith.
#[global]
Hint Resolve Zgcd_mult_elim_ll: zarith.
#[global]
Hint Resolve Zgcd_mult_elim_lr: zarith.
#[global]
Hint Resolve Zgcd_mult_elim_rl: zarith.
#[global]
Hint Resolve Zgcd_mult_elim_rr: zarith.
#[global]
Hint Resolve Zgcd_plus_elim_ll: zarith.
#[global]
Hint Resolve Zgcd_plus_elim_lr: zarith.
#[global]
Hint Resolve Zgcd_plus_elim_rl: zarith.
#[global]
Hint Resolve Zgcd_plus_elim_rr: zarith.
#[global]
Hint Resolve Zgcd_minus_elim_ll: zarith.
#[global]
Hint Resolve Zgcd_minus_elim_lr: zarith.
#[global]
Hint Resolve Zgcd_minus_elim_rl: zarith.
#[global]
Hint Resolve Zgcd_minus_elim_rr: zarith.
#[global]
Hint Resolve Zgcd_mod_lft: zarith.
#[global]
Hint Resolve Zgcd_mod_rht: zarith.
#[global]
Hint Resolve Zgcd_div_gcd_1: zarith.


(**
** Relative primality
*)


Section zrelprime.

Definition Zrelprime (a b : Z) := Zgcd a b = 1%Z.

Lemma Zrelprime_dec : forall a b : Z, {Zrelprime a b} + {~ Zrelprime a b}.
Proof.
 intros a b.
 unfold Zrelprime in |- *.
 case (Zdec (Zgcd a b - 1)).
  intro H1.
  left.
  auto with zarith.
 intro Hn1.
 right.
 auto with zarith.
Qed.

Lemma Zrelprime_irref : forall a : Z, (a > 1)%Z -> ~ Zrelprime a a.
Proof.
 intros a Ha.
 unfold Zrelprime in |- *.
 rewrite Zgcd_idemp.
  auto with zarith.
 auto with zarith.
Qed.

Lemma Zrelprime_symm : forall a b : Z, Zrelprime a b -> Zrelprime b a.
Proof.
 unfold Zrelprime in |- *.
 intros.
 rewrite Zgcd_symm.
 assumption.
Qed.

Lemma Zrelprime_one_lft : forall a : Z, Zrelprime 1 a.
Proof.
 intro a.
 unfold Zrelprime in |- *.
 apply Zgcd_one_lft.
Qed.

Lemma Zrelprime_one_rht : forall a : Z, Zrelprime a 1.
Proof.
 intro a.
 unfold Zrelprime in |- *.
 apply Zgcd_one_rht.
Qed.

Lemma Zrelprime_nonzero_rht :
 forall a b : Z, Zrelprime a b -> Z.abs a <> 1%Z -> b <> 0%Z.
Proof.
 intros a b H Ha.
 intro Hfalse.
 rewrite Hfalse in H.
 unfold Zrelprime in H.
 rewrite Zgcd_zero_rht in H.
 tauto.
Qed.

Lemma Zrelprime_nonzero_lft :
 forall a b : Z, Zrelprime a b -> Z.abs b <> 1%Z -> a <> 0%Z.
Proof.
 intros.
 apply (Zrelprime_nonzero_rht b a).
  apply Zrelprime_symm.
  assumption.
 assumption.
Qed.

Lemma Zrelprime_mult_intro :
 forall a b x y : Z, Zrelprime (a * x) (b * y) -> Zrelprime a b.
Proof.
 intros a b x y.
 unfold Zrelprime in |- *.
 intro H1.
 apply Zgcd_intro_unfolded; auto with zarith.
  generalize (Zgcd_nonzero (a * x) (b * y)); rewrite H1; intro H0; elim H0; auto with zarith.
 intros q Hq.
 rewrite <- H1.
 apply Zdiv_gcd_elim; apply Zdivides_mult_elim_rht; tauto.
Qed.

Lemma Zrelprime_divides_intro :
 forall a b p q : Z,
 Zdivides a p -> Zdivides b q -> Zrelprime p q -> Zrelprime a b.
Proof.
 intros a b p q Ha Hb; elim Ha; intros x Hx; rewrite <- Hx; elim Hb;
   intros y Hy; rewrite <- Hy; rewrite (Zmult_comm x a);
     rewrite (Zmult_comm y b); apply Zrelprime_mult_intro.
Qed.

Lemma Zrelprime_div_mult_intro :
 forall a b c : Z, Zrelprime a b -> Zdivides a (b * c) -> Zdivides a c.
Proof.
 intros a b c Hab Hdiv.
 case (Zdec (Z.abs a - 1)).
  intro H1.
  exists (c * Z.sgn a)%Z.
  rewrite <- Zmult_assoc.
  replace (Z.sgn a * a)%Z with (Z.abs a) by auto with zarith.
  replace (Z.abs a) with 1%Z; auto with zarith.
 intro Hn1.
 unfold Zrelprime in Hab.
 generalize (Zgcd_lin_comb a b).
 rewrite Hab.
 set (u := Zgcd_coeff_a a b); set (v := Zgcd_coeff_b a b).
 intro H1.
 replace c with (u * a * c + v * b * c)%Z.
  apply Zdivides_plus_elim.
   auto with zarith.
  rewrite <- Zmult_assoc.
  auto with zarith.
 symmetry  in |- *.
 rewrite <- (Zmult_1_l c).
 replace (u * a * (1 * c))%Z with (u * a * c)%Z.
  replace (v * b * (1 * c))%Z with (v * b * c)%Z.
   rewrite H1.
   auto with zarith.
  rewrite Zmult_1_l; auto.
 rewrite Zmult_1_l; auto.
Qed.

Lemma Zrelprime_mult_div_simpl :
 forall a b x y : Z, Zrelprime a b -> (x * a)%Z = (y * b)%Z -> Zdivides b x.
Proof.
 intros a b x y Hab Heq.
 case (Zdec a).
  intro Ha; rewrite Ha in Hab; unfold Zrelprime in Hab; rewrite Zgcd_zero_lft in Hab.
  exists (Z.sgn b * x)%Z; rewrite Zmult_comm; rewrite Zmult_assoc;
    rewrite (Zmult_comm b (Z.sgn b)); rewrite <- Zmult_sgn_eq_abs; rewrite Hab; apply Zmult_1_l.
 intro Ha.
 apply (Zmult_div_simpl_3 a x y b Heq Ha).
 apply (Zrelprime_div_mult_intro a b y Hab).
 exists x.
 rewrite Heq; apply Zmult_comm.
Qed.

Lemma Zrelprime_div_mult_elim :
 forall a b c : Z,
 Zrelprime a b -> Zdivides a c -> Zdivides b c -> Zdivides (a * b) c.
Proof.
 intros a b c Hab Ha Hb.
 elim Ha; intros x Hx.
 elim Hb; intros y Hy.
 rewrite <- Hx.
 rewrite (Zmult_comm x a).
 cut (Zdivides b x); auto with zarith.
 apply (Zrelprime_mult_div_simpl a b x y Hab).
 rewrite Hx; rewrite Hy; auto.
Qed.

Lemma Zrelprime_gcd_mult_elim_lft :
 forall a b c : Z, Zrelprime a b -> Zgcd (a * b) c = (Zgcd a c * Zgcd b c)%Z.
Proof.
 intros a b c.
 unfold Zrelprime in |- *.
 case (Zdec (a * b)).
  intro Hab0.
  generalize (Zmult_zero_div a b Hab0); intro Hab.
  elim Hab; intro H1; rewrite Hab0; rewrite H1; repeat rewrite Zgcd_zero_lft;
    repeat rewrite Zgcd_zero_rht; intro H2; rewrite Zgcd_abs;
      rewrite H2; rewrite Zgcd_one_lft; auto with zarith.
 intros Hab0 Hrelprime.
 apply Zdivides_antisymm.
    apply Z.lt_gt; apply Zgcd_pos; auto.
   rewrite <- (Zmult_0_r (Zgcd a c)).
   apply Zmult_pos_mon_lt_lft.
    apply Z.lt_gt; apply Zgcd_pos; left; rewrite Zmult_comm in Hab0; auto with zarith.
   apply Z.lt_gt; apply Zgcd_pos; left; auto with zarith.
  rewrite (Zgcd_lin_comb a c); rewrite (Zgcd_lin_comb b c).
  repeat rewrite Zmult_plus_distr_r; repeat rewrite Zmult_plus_distr_l.
  apply Zdivides_plus_elim; apply Zdivides_plus_elim; auto with zarith.
 apply Zdiv_gcd_elim.
  apply Zdivides_mult_elim; auto with zarith.
 apply Zrelprime_div_mult_elim; auto with zarith.
 apply (Zrelprime_divides_intro (Zgcd a c) (Zgcd b c) a b); auto with zarith.
Qed.

Lemma Zrelprime_gcd_mult_elim_rht :
 forall a b c : Z, Zrelprime a b -> Zgcd c (a * b) = (Zgcd c a * Zgcd c b)%Z.
Proof.
 intros a b c; rewrite (Zgcd_symm c (a * b)); rewrite (Zgcd_symm c a);
   rewrite (Zgcd_symm c b); apply Zrelprime_gcd_mult_elim_lft.
Qed.

Lemma Zrelprime_mult_elim_lft :
 forall a b c : Z, Zrelprime a c -> Zrelprime b c -> Zrelprime (a * b) c.
Proof.
 intros a b c.
 unfold Zrelprime in |- *.
 intros Ha Hb.
 generalize (Zgcd_lin_comb a c); rewrite Ha; set (p := Zgcd_coeff_a a c) in *;
   set (q := Zgcd_coeff_b a c) in *.
 generalize (Zgcd_lin_comb b c); rewrite Hb; set (r := Zgcd_coeff_a b c) in *;
   set (s := Zgcd_coeff_b b c) in *.
 intros Hla Hlb.
 apply Zdivides_antisymm.
    apply Z.lt_gt; apply Zgcd_pos.
    case (Zdec c); auto.
    intro Hc0.
    left.
    rewrite Hc0 in Ha; rewrite Zgcd_zero_rht in Ha; rewrite Hc0 in Hb;
      rewrite Zgcd_zero_rht in Hb; intro Hfalse.
    generalize (Zmult_zero_div _ _ Hfalse); intro H0; elim H0.
     intro Ha0; rewrite Ha0 in Ha; discriminate.
    intro Hb0; rewrite Hb0 in Hb; discriminate.
   auto with zarith.
  replace 1%Z with ((r * b + s * c) * (p * a + q * c))%Z.
   repeat rewrite Zmult_plus_distr_r; repeat rewrite Zmult_plus_distr_l;
     rewrite (Zmult_comm p a); rewrite (Zmult_comm a b);
       apply Zdivides_plus_elim; apply Zdivides_plus_elim; auto with zarith.
  rewrite <- Hla; rewrite <- Hlb; auto with zarith.
 auto with zarith.
Qed.


End zrelprime.

#[global]
Hint Resolve Zrelprime_dec: zarith.
#[global]
Hint Resolve Zrelprime_irref: zarith.
#[global]
Hint Resolve Zrelprime_symm: zarith.
#[global]
Hint Resolve Zrelprime_one_lft: zarith.
#[global]
Hint Resolve Zrelprime_one_rht: zarith.
#[global]
Hint Resolve Zrelprime_nonzero_rht: zarith.
#[global]
Hint Resolve Zrelprime_nonzero_lft: zarith.
#[global]
Hint Resolve Zrelprime_mult_intro: zarith.
#[global]
Hint Resolve Zrelprime_divides_intro: zarith.
#[global]
Hint Resolve Zrelprime_div_mult_intro: zarith.
#[global]
Hint Resolve Zrelprime_mult_div_simpl: zarith.
#[global]
Hint Resolve Zrelprime_div_mult_elim: zarith.
#[global]
Hint Resolve Zrelprime_gcd_mult_elim_lft: zarith.
#[global]
Hint Resolve Zrelprime_gcd_mult_elim_rht: zarith.
#[global]
Hint Resolve Zrelprime_mult_elim_lft: zarith.


(**
** Primes
Let p be a positive number.
*)


Section prime.

Variable p : positive.

Definition Prime :=
  p <> 1%positive /\
  (forall x : positive, Zdivides (Zpos x) (Zpos p) -> x = 1%positive \/ x = p).

Lemma prime_rel_prime :
 Prime ->
 forall x : positive, (Zpos x < Zpos p)%Z -> Zrelprime (Zpos p) (Zpos x).
Proof.
 intros Hprime x Hx.
 unfold Prime in Hprime.
 elim Hprime.
 intros H1 Hdiv.
 unfold Zrelprime in |- *.
 set (d := Zgcd (Zpos p) (Zpos x)).
 cut (0 < d)%Z.
  cut (d < Zpos p)%Z.
   cut (Zdivides d (Zpos p)).
    cut (d = Zgcd (Zpos p) (Zpos x)); auto.
    case d.
      auto with zarith.
     intros D HD HDiv HDlt HDpos.
     generalize (Hdiv D HDiv); intro H0; elim H0.
      intro HD1; rewrite HD1; auto.
     intro HDp; rewrite HDp in HDlt; elim (Zlt_irref _ HDlt).
    auto with zarith.
   unfold d in |- *; auto with zarith.
  apply (Z.le_lt_trans d (Zpos x) (Zpos p)); unfold d in |- *; auto with zarith.
 unfold d in |- *; apply Zgcd_pos; auto with zarith.
Qed.


(* Lemma Zprime_dec: (p:Z) {(Zprime p)} + {~(Zprime p)}. *)


End prime.
