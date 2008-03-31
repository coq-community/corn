(*
Copyright © 2006-2008 Russell O’Connor

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

Require Import Ndigits.
Require Import ZArith.
Require Import Basics.
Require Import Qordfield.
Require Import COrdFields2.
Require Import Qpower.
Require Import CornTac.

Open Local Scope Q_scope.

(** These functions effiecently find bounds on rational numbers of the
form 3^z or 4^z. *)

Lemma power3bound : forall (q:Q), (q <= (3^(Z_of_nat (let (n,_):= q in match n with Zpos p => Psize p | _ => O end)))%Z).
intros [[|n|n] d]; try discriminate.
unfold Qle.
simpl.
Open Scope Z_scope.
rewrite Zpos_mult_morphism.
apply Zmult_le_compat; auto with *.
clear - n.
apply Zle_trans with (two_p (Zsucc (log_inf n))-1)%Z.
 rewrite <- Zle_plus_swap.
 apply Zlt_succ_le.
 change (' n+1) with (Zsucc ('n)).
 apply Zsucc_lt_compat.
 destruct (log_inf_correct2 n).
 assumption.
replace (Zsucc (log_inf n)) with (Z_of_nat (Psize n)).
 apply Zle_trans with (two_p (Z_of_nat (Psize n))).
  auto with *.
 induction (Psize n); auto with *.
 rewrite inj_S.
 simpl.
 unfold Zsucc.
 rewrite two_p_is_exp; auto with *.
 change (two_p 1) with 2.
 rewrite Zpower_exp; auto with *.
 change (3^1) with 3.
 apply Zmult_le_compat; auto with *.
 induction (Z_of_nat n0); auto with *.
induction n; auto with *; simpl; rewrite <- IHn;
 rewrite <- POS_anti_convert; rewrite inj_S; reflexivity.
Close Scope Z_scope.
Qed.

Lemma power4bound : forall (q:Q), (q <= (4^(Z_of_nat (let (n,_):= q in match n with Zpos p => Psize p | _ => O end)))%Z).
Proof.
intros q.
eapply Qle_trans.
 apply power3bound.
generalize (let (n, _) := q in
    match n with
    | 0 => 0%nat
    | ' p => Psize p
    | Zneg _ => 0%nat
    end)%Z.
intros n.
unfold Qle.
simpl.
ring_simplify.
induction n.
 apply Zle_refl.
rewrite inj_S.
unfold Zsucc.
do 2 (rewrite Zpower_exp;try auto with *).
ring_simplify.
apply Zmult_le_compat; try discriminate.
 assumption.
clear -n.
induction n.
 discriminate.
rewrite inj_S.
unfold Zsucc.
rewrite Zpower_exp;try auto with *.
Qed.

Lemma power4bound' : forall (q:Q), (0 < q) -> ((/(4^(Z_of_nat (let (_,d):= q in Psize d)))%Z) <= q).
Proof.
intros [[|n|n] d] H.
  elim (Qlt_not_eq _ _ H).
  constructor.
 assert (X:=power4bound (d#n)).
 simpl in X.
 rewrite Zpower_Qpower; try auto with *.
 apply Qle_shift_inv_r.
  clear - d.
  induction (Psize d).
   constructor.
  rewrite inj_S.
  unfold Zsucc.
  rewrite Qpower_plus.
   discriminate.
  rsapply mult_resp_pos;[assumption|constructor].
 rewrite <- Zpower_Qpower; try auto with *.
 destruct (inject_Z (4%positive ^ Psize d)%Z).
 change ((1 * (d * Qden)%positive <= n * Qnum * 1)%Z).
 ring_simplify.
 unfold Qle in *.
 simpl in X.
 rewrite Zmult_comm.
 assumption.
elim (Qlt_not_le _ _ H).
discriminate.
Qed.
