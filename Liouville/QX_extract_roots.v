(*
Copyright © 2009 Valentin Blot

Permission is hereby granted, free of charge, to any person obtaining a copy of
this proof and associated documentation files (the "Proof"), to deal in
the Proof without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Proof, and to permit persons to whom the Proof is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Proof.

THE PROOF IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE PROOF OR THE USE OR OTHER DEALINGS IN THE PROOF.
*)
Require Import CPoly_Degree.
Require Import CRing_Homomorphisms.
Require Import ordfields.Qordfield.
Require Import CauchySeq.
Require Import Q_in_CReals.

Require Import CPoly_Euclid RingClass CRingClass.
Require Import Q_can nat_Q_lists RX_deg RX_div QX_root_loc.

Section Z_Q.

Let QX := cpoly_cring Q_as_CRing.
Add Ring q_r : (r_rt (Ring:=CRing_is_Ring Q_as_CRing)).
Add Ring qx_r : (r_rt (Ring:=CRing_is_Ring (cpoly_cring Q_as_CRing))).

Let QX_dec := RX_dec Q_as_CRing Q_dec.
Let QX_deg := RX_deg Q_as_CRing Q_dec.

Fixpoint QX_test_list (P : QX) (l : list Q_as_CRing) : option Q_as_CRing :=
  match l with
    | nil => None
    | cons q l => if (Q_dec (P ! q) Zero) then Some q else QX_test_list P l
  end.

Lemma QX_test_list_spec_none : forall P l, QX_test_list P l = None ->
        forall q : Q_as_CRing, In q l -> P ! q [#] Zero.
Proof.
induction l.
  intros; contradiction.
unfold QX_test_list.
case (Q_dec P ! a Zero).
  intros; discriminate.
fold (QX_test_list P l).
intros Hap Hnone q.
simpl (In q (a::l)).
case (Q_dec a q).
  intros Haq Hin Hval.
  destruct Hap.
  rewrite Haq; assumption.
intros.
apply IHl.
  assumption.
destruct H.
  destruct c; rewrite H; reflexivity.
assumption.
Qed.

Lemma QX_test_list_spec_some : forall P l x, QX_test_list P l = Some x ->
        P ! x [=] Zero.
Proof.
induction l.
  intros; discriminate.
unfold QX_test_list.
fold (QX_test_list P l).
case (Q_dec P ! a Zero); [|intro; assumption].
intros.
injection H; intro.
rewrite <- H0; assumption.
Qed.

Let P0 (P : QX) := nth_coeff 0 (QX_ZX.qx2zx P).
Let Pn (P : QX) := nth_coeff (QX_deg P) (QX_ZX.qx2zx P).

Definition QX_find_root (P : QX) : option Q_as_CRing :=
    if (Q_dec (P ! Zero) Zero) then Some Zero else QX_test_list P (list_Q (P0 P) (Pn P)).

Lemma QX_find_root_spec_none : forall P, QX_find_root P = None -> forall q : Q_as_CRing, P ! q [#] Zero.
Proof.
intro P; unfold QX_find_root.
case (Q_dec P ! Zero Zero).
  intros; discriminate.
intros Hap Hnone q.
assert (forall x y : Q_as_CRing, {x = y} + {x <> y}).
  clear; intros x y.
  destruct x; destruct y; simpl.
  case (Z_eq_dec Qnum Qnum0); case (Z_eq_dec Qden Qden0); intros H1 H2.
        left; f_equal; [assumption|injection H1; tauto].
      right; intro H3; injection H3; intros; destruct H1; f_equal; assumption.
    right; intro H3; injection H3; intros; destruct H2; assumption.
  right; intro H3; injection H3; intros; destruct H2; assumption.
destruct (In_dec X (Q_can q) (list_Q (P0 P) (Pn P))).
  intro H; rewrite -> (Q_can_spec q) in H; revert H.
  apply (QX_test_list_spec_none _ _ Hnone _ i).
intro Hval; apply n.
apply QX_root_loc; assumption.
Qed.

Lemma QX_find_root_spec_some : forall P x, QX_find_root P = Some x -> P ! x [=] Zero.
Proof.
intros P x; unfold QX_find_root.
case (Q_dec P ! Zero Zero).
  intros H1 H2; injection H2; intro H3; rewrite <- H3; assumption.
intro Hap; apply QX_test_list_spec_some.
Qed.

Lemma QX_integral : forall p q : QX, p [#] Zero -> q [#] Zero -> p[*]q [#] Zero.
Proof.
intros p q Hp Hq.
apply (nth_coeff_strext _ (QX_deg p + QX_deg q)).
simpl (nth_coeff (QX_deg p + QX_deg q) (Zero:QX)).
cut (degree (QX_deg p + QX_deg q) (p[*]q)).
  intro H; apply H.
apply (degree_mult Q_as_CField).
  apply RX_deg_spec; assumption.
apply RX_deg_spec; assumption.
Qed.

Lemma QX_deg_mult : forall p q, p [#] Zero -> q [#] Zero ->
           QX_deg (p[*]q) = QX_deg p + QX_deg q.
Proof.
intros p q Hp Hq.
set (RX_deg_spec _ Q_dec _ Hp).
set (RX_deg_spec _ Q_dec _ Hq).
set (degree_mult Q_as_CField _ _ _ _ d d0).
fold QX_deg in d1.
apply (degree_inj _ (p[*]q)); [|assumption].
apply RX_deg_spec.
apply QX_integral; assumption.
Qed.

Lemma QX_div_deg0 : forall (p : QX) (a : Q_as_CRing),
              QX_deg p <> 0 -> RX_div _ p a [#] Zero.
Proof.
intros p a Hdeg.
case (QX_dec (RX_div _ p a) Zero); [|tauto].
intro Heq; destruct Hdeg; revert Heq.
unfold RX_div.
destruct (cpoly_div p (_X_monic _ a)).
destruct x as [q r].
unfold fst, snd in *.
clear s.
destruct c.
destruct d.
intro Hq.
rewrite -> Hq in s.
assert (H : p [=] r); [rewrite s; unfold cg_minus; unfold QX; ring|].
unfold QX_deg; rewrite (RX_deg_wd _ Q_dec _ _ H); fold QX_deg.
destruct (_X_monic _ a).
destruct (degree_le_zero _ _ (d _ H1)).
unfold QX_deg; rewrite (RX_deg_wd _ Q_dec _ _ s1).
rewrite RX_deg_c_; reflexivity.
Qed.

Lemma QX_div_deg : forall (p : QX) (a : Q_as_CRing),
          QX_deg p <> 0 -> QX_deg p = S (QX_deg (RX_div _ p a)).
Proof.
intros p a Hdeg.
case_eq (QX_deg p).
  intro; destruct Hdeg; assumption.
intros n Heq.
f_equal.
revert Heq.
unfold QX_deg; rewrite (RX_deg_wd _ Q_dec _ _ (RX_div_spec _ p a)).
rewrite RX_deg_sum.
  rewrite RX_deg_c_.
  rewrite max_comm; unfold max.
  rewrite -> QX_deg_mult.
      unfold QX_deg; rewrite RX_deg_minus.
        rewrite RX_deg_c_ RX_deg_x_; fold QX_deg.
        simpl; rewrite plus_comm; simpl.
        intro H; injection H; symmetry; assumption.
      rewrite RX_deg_x_ RX_deg_c_; discriminate.
    apply QX_div_deg0; assumption.
  right; left; discriminate.
rewrite -> QX_deg_mult.
    unfold QX_deg; rewrite RX_deg_minus.
      rewrite RX_deg_x_ RX_deg_c_ RX_deg_c_.
      rewrite plus_comm; discriminate.
    rewrite RX_deg_x_ RX_deg_c_; discriminate.
  apply QX_div_deg0; assumption.
right; left; discriminate.
Qed.

Fixpoint QX_extract_roots_rec (n : nat) (P : QX) :=
  match n with
    | O => P
    | S n =>
      match QX_find_root P with
        | None => P
        | Some x => QX_extract_roots_rec n (RX_div _ P x)
      end
  end.

Definition QX_extract_roots (P : QX) := QX_extract_roots_rec (QX_deg P) P.

Lemma QX_extract_roots_spec_rat : forall P a,
       P [#] Zero -> (QX_extract_roots P) ! a [#] Zero.
Proof.
unfold QX_extract_roots.
intros P a; remember (QX_deg P) as n; revert P Heqn.
induction n.
  intros P Hdeg Hap; unfold QX_extract_roots_rec.
  destruct (RX_deg_spec _ Q_dec _ Hap).
  fold QX_deg in d; rewrite <- Hdeg in d.
  destruct (degree_le_zero _ _ d).
  case (Q_dec P ! a Zero); [|tauto].
  intro Heq; destruct (ap_imp_neq _ _ _ Hap); clear Hap; revert Heq.
  rewrite s c_apply; intro H; rewrite H; split; [reflexivity|apply I].
unfold QX_extract_roots_rec.
intros P Hdeg Hap.
case_eq (QX_find_root P).
  intros x Hsome; fold (QX_extract_roots_rec n (RX_div _ P x)).
  apply IHn.
    apply eq_add_S.
    rewrite <- QX_div_deg; [assumption|].
  rewrite <- Hdeg; discriminate.
  case (QX_dec (RX_div _ P x) Zero); [|tauto].
  intro Heq; apply QX_div_deg0.
  rewrite <- Hdeg; discriminate.
intro; apply QX_find_root_spec_none; assumption.
Qed.

Definition inj_Q_fun := Build_CSetoid_fun _ _ _ (inj_Q_strext IR).
Lemma inj_Q_pres_plus : fun_pres_plus _ _ inj_Q_fun.
Proof. intros x y; apply inj_Q_plus. Qed.
Lemma inj_Q_pres_unit : fun_pres_unit _ _ inj_Q_fun.
Proof. apply inj_Q_One. Qed.
Lemma inj_Q_pres_mult : fun_pres_mult _ _ inj_Q_fun.
Proof. intros x y; apply inj_Q_mult. Qed.
Definition inj_Q_rh := Build_RingHom _ _ inj_Q_fun inj_Q_pres_plus inj_Q_pres_mult inj_Q_pres_unit.
Definition inj_QX_rh := cpoly_map inj_Q_rh.

Lemma QX_extract_roots_spec_nrat : forall (P : QX) (x : IR),
      (forall y : Q_as_CRing, x [~=] (inj_Q_rh y)) ->
         (inj_QX_rh P) ! x [=] Zero -> (inj_QX_rh (QX_extract_roots P)) ! x [=] Zero.
Proof.
intros P x Hx; unfold QX_extract_roots.
remember (QX_deg P) as n; revert P Heqn; induction n.
  intros; unfold QX_extract_roots_rec; assumption.
intros P Hdeg Hval; unfold QX_extract_roots_rec; fold (QX_extract_roots_rec).
case_eq (QX_find_root P); [|intro; assumption].
intros y Hsome.
apply IHn.
  apply eq_add_S.
  rewrite Hdeg; apply QX_div_deg.
  rewrite <- Hdeg; discriminate.
clear IHn; revert Hval.
rewrite {1} (RX_div_spec _ P y).
rewrite rh_pres_plus.
rewrite rh_pres_mult.
rewrite rh_pres_minus.
rewrite (cpoly_map_X _ _ inj_Q_rh).
rewrite (cpoly_map_C _ _ inj_Q_rh).
rewrite (cpoly_map_C _ _ inj_Q_rh).
rewrite plus_apply.
rewrite mult_apply.
rewrite minus_apply.
rewrite x_apply.
rewrite c_apply.
rewrite c_apply.
rewrite (QX_find_root_spec_some _ _ Hsome).
rewrite rh_pres_zero.
rewrite cm_rht_unit.
rewrite mult_commutes.
set (H := Hx y); revert H; generalize (RX_div Q_as_CRing P y).
clear; intros P Hap Heq.
apply (mult_eq_zero IR (x[-]inj_Q_rh y)); [|assumption].
intro; apply Hap.
apply cg_inv_unique_2; assumption.
Qed.

End Z_Q.
