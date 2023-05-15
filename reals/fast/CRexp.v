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

Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import CoRN.model.totalorder.QMinMax.
Require Import CoRN.reals.fast.CRAlternatingSum.
Require Import CoRN.reals.fast.CRAlternatingSum_alg.
Require Import CoRN.reals.fast.CRstreams.
Require Export CoRN.reals.fast.CRArith.
Require Import CoRN.reals.fast.CRIR.
Require Import CoRN.reals.iso_CReals.
Require Import Coq.QArith.Qpower.
Require Import CoRN.algebra.COrdFields2.
Require Import CoRN.model.ordfields.Qordfield.
Require Import CoRN.transc.PowerSeries.
Require Import CoRN.reals.fast.CRpower.
Require Import CoRN.transc.Exponential.
Require Import CoRN.transc.RealPowers.
Require Import CoRN.reals.fast.Compress.
Require Import Coq.NArith.Ndigits.
Require Import CoRN.reals.fast.ModulusDerivative.
Require Import CoRN.reals.fast.ContinuousCorrect.
Require Import CoRN.reals.fast.CRsign.
Require Import CoRN.reals.Q_in_CReals.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qround.
Require Import CoRN.tactics.CornTac.
Require Import MathClasses.theory.int_pow.
Require Import MathClasses.interfaces.abstract_algebra.

(* Backwards compatibility for Hint Rewrite locality attributes *)
Set Warnings "-unsupported-attributes".

Set Implicit Arguments.

Opaque CR.
Opaque Exp.

Local Open Scope Q_scope.
Local Open Scope uc_scope.

Lemma Qpower_le_1 : forall (a : Q) (p : positive),
    0 <= a <= 1 -> 0 <= a ^ p <= 1.
Proof.
  split.
  - apply Qpower_pos, H.
  - revert p. apply Pos.peano_ind. apply H.
    intros p Hp. unfold Qpower.
    rewrite <- Pos.add_1_l, Qpower_plus_positive.
    apply (Qle_trans _ (1*Qpower_positive a p)).
    apply Qmult_le_compat_r. apply H.
    apply (Qpower_pos a p), H.
    rewrite Qmult_1_l. apply Hp.
Qed.

Lemma Qabs_Qpower : forall (a:Q) (p:positive),
    Qabs (a ^ p) == (Qabs a) ^ p.
Proof.
  intro a. apply Pos.peano_ind.
  - reflexivity.
  - intros p Hp. 
    simpl. rewrite <- Pos.add_1_l.
    rewrite Qpower_plus_positive.
    rewrite Qabs_Qmult, Hp. clear Hp.
    rewrite Qpower_plus_positive. reflexivity.
Qed.

Lemma Qinv_le_compat : forall (a b : Q),
    0 < a -> a <= b -> /b <= /a.
Proof.
  intros. apply Qle_shift_inv_l. exact H.
  apply (Qmult_le_l _ _ b).
  exact (Qlt_le_trans _ a _ H H0).
  rewrite Qmult_1_r, Qmult_assoc.
  rewrite Qmult_inv_r.
  rewrite Qmult_1_l. exact H0.
  intro abs. rewrite abs in H0.
  apply (Qlt_irrefl 0).
  exact (Qlt_le_trans _ _ _ H H0).
Qed.

Lemma fact_power_2 : forall n:nat, (2^pred n <= fact n)%nat.
Proof.
  induction n.
  - apply Nat.le_refl.
  - apply (Nat.le_trans _ ((S n) * 2^pred n)).
    2: apply Nat.mul_le_mono_nonneg_l; [apply le_0_n | exact IHn].
    clear IHn. destruct n. simpl. apply Nat.le_refl.
    simpl.
    apply Nat.add_le_mono_l, Nat.add_le_mono_l, le_0_n.
Qed.
  
Lemma Qceiling_fact_le : forall q:Q,
    0 < q -> 
    q <=
    Pos.of_nat (fact (Pos.to_nat (Pos.succ (Z.to_pos (Z.log2_up (Qceiling q))))))
               # 1.
Proof.
  intros q H. 
  apply (Qle_trans _ _ _ (Qle_ceiling q)).
  assert (0 < Qceiling q)%Z.
  { rewrite Zlt_Qlt. apply (Qlt_le_trans _ _ _ H). apply Qle_ceiling. }
  revert H0. generalize (Qceiling q). intros p ppos. clear H q.
  unfold Qle; simpl.
  rewrite Z.mul_1_r, Pos.mul_1_r.
  destruct p as [|p|p].
  exfalso; inversion ppos.
  2: exfalso; inversion ppos. clear ppos.
  apply (Z.le_trans _ (2 ^ Z.log2_up p)).
  apply Z.log2_up_le_pow2. reflexivity.
  apply Z.le_refl.
  revert p. apply Pos.peano_case. discriminate.
  intro p.
  generalize (Z.log2_up (Pos.succ p))
             (Z.log2_up_pos (Pos.succ p) (Pos.lt_1_succ p)).
  clear p. intros p ppos.
  destruct p. inversion ppos.
  2: inversion ppos. clear ppos.
  unfold Z.to_pos.
  pose proof (fact_power_2 (Pos.to_nat (Pos.succ p))).
  rewrite Pos2Nat.inj_succ in H.
  unfold pred in H.
  rewrite Pos2Nat.inj_succ.
  simpl (2^p)%Z.
  rewrite <- Pos2Z.inj_pow_pos.
  apply Pos2Nat.inj_le.
  rewrite Nat2Pos.id.
  2: apply fact_neq_0.
  refine (Nat.le_trans _ _ _ _ H).
  clear H. generalize p.
  apply Pos.peano_ind.
  + apply Nat.le_refl.
  + intros. rewrite Pos2Nat.inj_succ, Pos.pow_succ_r. 
    rewrite Pos2Nat.inj_mul.
    apply Nat.mul_le_mono_nonneg_l. apply le_0_n.
    exact H.
Qed.

(**
** Exponential
[exp] is implement by its alternating Taylor's series.
*)

Section ExpSeries.
Variable a:Q.

Definition expStream (px : positive*Q) : positive*Q
  := (Pos.succ (fst px), snd px * a * (1#fst px)).

Lemma expStream_fst : forall p, fst (iterate _ expStream p (1%positive, 1)) ≡ Pos.succ p.
Proof.
  apply Pos.peano_ind.
  - reflexivity.
  - intros. rewrite iterate_succ. simpl.
    rewrite H. reflexivity.
Qed.

Lemma Str_pth_expStream : forall p,
    Str_pth _ expStream p (xH,1) == (1#Pos.of_nat (fact (Pos.to_nat p)))*a^p.
Proof.
  apply Pos.peano_ind.
  - unfold Str_pth. simpl. apply Qmult_1_r.
  - intros. unfold Str_pth.
    rewrite iterate_succ. simpl.
    unfold Str_pth in H. rewrite H. clear H.
    rewrite expStream_fst. simpl.
    rewrite <- (Qmult_comm (1#Pos.succ p)), Qmult_assoc, Qmult_assoc.
    rewrite <- (Qmult_assoc ((1 # Pos.succ p) * (1 # Pos.of_nat (fact (Pos.to_nat p))))).
    apply Qmult_comp.
    + unfold Qmult, Qeq, Qnum, Qden. rewrite Z.mul_1_l.
      rewrite Z.mul_1_l.
      rewrite Pos2Nat.inj_succ.
      change (fact (S (Pos.to_nat p)))%nat
        with (S (Pos.to_nat p) * fact (Pos.to_nat p))%nat.
      rewrite Nat2Pos.inj_mul. 2: discriminate.
      2: apply fact_neq_0.
      rewrite Nat2Pos.inj_succ, Pos2Nat.id.
      reflexivity. pose proof (Pos2Nat.is_pos p).
      intro abs. rewrite abs in H. inversion H.
    + rewrite <- Pos.add_1_r.
      rewrite Qpower_plus_positive. reflexivity.
Qed.

Lemma expStream_alt : -1 <= a <= 0 -> Str_alt_decr _ expStream (xH,1).
Proof.
  intros aneg p.
  unfold Str_pth. rewrite iterate_succ.
  generalize (iterate (positive and Q) expStream p (1%positive, 1)).
  intros [n q]. unfold expStream, snd, fst. split.
  - rewrite <- Qmult_assoc.
    rewrite <- (Qmult_1_l (Qabs q)).
    rewrite Qabs_Qmult, Qmult_comm.
    apply Qmult_le_compat_r. 2: apply Qabs_nonneg.
    rewrite Qabs_Qmult.
    apply (Qle_trans _ (1 * Qabs (1#n))).
    apply Qmult_le_compat_r. 2: apply Qabs_nonneg.
    apply Qabs_Qle_condition. split.
    apply aneg. apply (Qle_trans _ 0). apply aneg. discriminate.
    rewrite Qmult_1_l. apply Pos.le_1_l.
  - destruct aneg as [_ aneg].
    rewrite <- (Qmult_comm a).
    rewrite <- Qmult_assoc, <- Qmult_assoc.
    rewrite <- (Qmult_0_l (q * ((1 # n) * q))).
    apply Qmult_le_compat_r. exact aneg.
    rewrite Qmult_comm.
    destruct q, Qnum; unfold Qle; discriminate.
Qed.

Lemma expStream_zl
  : -1 <= a <= 0
    -> Limit_zero _ expStream (xH,1)
                 (fun e:Qpos => Pos.succ (Z.to_pos (Z.log2_up (Qceiling (/ (proj1_sig e)))))).
Proof.
  (* 1/e <= Qceiling (1/e) <= 2 ^ (Z.log2_up (Qceiling (1/e)))
     and we add 1 more to get <= fact. *)
  intros aneg [e epos]; unfold proj1_sig.
  (* Replace a^k by 1 *)
  rewrite Str_pth_expStream.
  rewrite Qabs_Qmult, Qmult_comm.
  apply (Qle_trans
           _ (1 * Qabs (1 # Pos.of_nat (fact (Pos.to_nat (Pos.succ (Z.to_pos (Z.log2_up (Qceiling (/ e)))))))))).
  apply Qmult_le_compat_r. 2: apply Qabs_nonneg.
  - generalize (Pos.succ (Z.to_pos (Z.log2_up (Qceiling (/ e))))).
    intro p. rewrite Qabs_Qpower.
    apply Qpower_le_1. split. apply Qabs_nonneg.
    apply Qabs_Qle_condition. split. apply aneg.
    apply (Qle_trans _ 0). apply aneg. discriminate.
  - rewrite Qmult_1_l. clear aneg a.
    (* Replace fact k by 2^k. *)
    simpl.
    rewrite <- (Qinv_involutive e) at 2.
    assert (0 < /e) as H.
    { apply Qinv_lt_0_compat, epos. }
    apply (@Qinv_le_compat
             (/e) ((Pos.of_nat (fact (Pos.to_nat (Pos.succ (Z.to_pos (Z.log2_up (Qceiling (/ e)))))))) # 1)).
    exact H.
    apply Qceiling_fact_le, H.
Qed.

End ExpSeries.

Lemma exp_ps_correct : forall (a:Q) (p:positive) H,
    inj_Q IR (Str_pth _ (expStream a) p (xH,1))%Q
    = Exp_ps (Pos.to_nat p) (inj_Q IR a) H.
Proof.
 intros a p H.
 rewrite (inj_Q_wd _ _ _ (Str_pth_expStream a p)).
 revert p H.
 apply (Pos.peano_ind (fun p =>  ∀ (H : Dom (Exp_ps (Pos.to_nat p)) (inj_Q IR a)),
    inj_Q IR ((1 # Pos.of_nat (fact (Pos.to_nat p))) * a ^ p) =
    Exp_ps (Pos.to_nat p) (inj_Q IR a) H)).
 - intros H.
   simpl ((1 # Pos.of_nat (fact (Pos.to_nat 1))) * a ^ 1).
   rewrite (inj_Q_wd _ _ _ (one_mult _ a)).
   unfold Pos.to_nat. simpl.
   rewrite one_mult.
   setoid_replace ([1] [/] [0] [+] [1] [//] nring_fac_ap_zero IR 1) with (cr_one IR).
   rewrite one_mult.
   rewrite cg_inv_zero.
   reflexivity.
   unfold cf_div.
   rewrite one_mult.
   rewrite <- inv_one at 2.
   apply f_rcpcl_wd.
   rewrite cm_lft_unit.
   reflexivity.
 - intros p IHp H.
   rewrite Pos2Nat.inj_succ.
   stepl (([1][/](nring (S (Pos.to_nat p)))[//]nringS_ap_zero IR (Pos.to_nat p))
            [*](inj_Q IR a)[*]Exp_ps (Pos.to_nat p) (inj_Q IR a) H).
   + simpl.
     rewrite (mult_commutes IR (nexp IR (Pos.to_nat p) (inj_Q IR a [-] [0]))).
     rewrite (ax_mult_assoc IR _ _ (cr_proof IR)).
     rewrite (ax_mult_assoc IR _ _ (cr_proof IR)).
     apply mult_wd. 2: reflexivity.
     rewrite cg_inv_zero.
     rewrite <- (mult_commutes IR (inj_Q IR a)).
     rewrite <- (mult_commutes IR (inj_Q IR a)).
     rewrite <- (ax_mult_assoc IR _ _ (cr_proof IR)).
     apply mult_wd. reflexivity.
     pose proof (mult_resp_ap_zero _ _ _ (nringS_ap_zero IR (Pos.to_nat p)) (nring_fac_ap_zero IR (Pos.to_nat p)))
       as X.
     rewrite <- (mult_of_divs _ _ _ _ _ _ _ X).
     apply div_wd. apply mult_one.
     apply eq_symmetric.
     change (fact (Pos.to_nat p) + (Pos.to_nat p) * fact (Pos.to_nat p))%nat
       with (S (Pos.to_nat p)*(fact (Pos.to_nat p)))%nat.
     apply nring_comm_mult.
   + stepl (inj_Q IR ((1#(Pos.succ p))
                      *a*((1 # Pos.of_nat (fact (Pos.to_nat p))) * a ^ Pos.to_nat p))%Q).
     * apply inj_Q_wd.
       rewrite <- Pos.add_1_l at 2.
       rewrite (Qpower_plus' a 1 p).
       2: discriminate.
       simpl (a ^ 1).
       rewrite Qmult_assoc, Qmult_assoc.
       apply Qmult_comp.
       rewrite <- (Qmult_comm a), <- Qmult_assoc, Qmult_comm.
       apply Qmult_comp. 2: reflexivity.
       change (fact (S (Pos.to_nat p)))%nat
         with ((S (Pos.to_nat p)) * fact (Pos.to_nat p))%nat.
       rewrite Nat2Pos.inj_mul.
       2: discriminate. 2: apply fact_neq_0.
       replace (Pos.of_nat (S (Pos.to_nat p))) with (Pos.succ p).
       reflexivity.
       rewrite Nat2Pos.inj_succ.
       rewrite Pos2Nat.id. reflexivity.
       pose proof (Pos2Nat.is_pos p).
       intro abs. rewrite abs in H0. inversion H0.
       rewrite positive_nat_Z. reflexivity.
     * stepl (([1][/]nring (R:=IR) (S (Pos.to_nat p))[//]nringS_ap_zero IR (Pos.to_nat p))[*]inj_Q IR a[*]
            inj_Q IR ((1 # Pos.of_nat (fact (Pos.to_nat p))) * a ^ p)%Q)
       ; [apply mult_wdr; apply IHp|].
       clear IHp H.
       apply eq_symmetric.
       eapply eq_transitive;[apply inj_Q_mult|].
       eapply eq_transitive;[apply mult_wdl;apply inj_Q_mult|].
       rewrite positive_nat_Z. 
       apply mult_wdl.
       apply mult_wdl.
       change (1 # Pos.succ p)%Q with (1/Pos.succ p)%Q.
       assert (A:inj_Q IR ((Pos.succ p):Q)[=]nring (S (Pos.to_nat p))).
       { stepl (inj_Q IR (nring (S (Pos.to_nat p)))).
         apply inj_Q_nring.
         apply inj_Q_wd.
         simpl.
         rewrite <- Pos.add_1_r.
         rewrite Pos2Z.inj_add, inject_Z_plus.
         apply Qplus_comp. 2: reflexivity.
         revert p. apply Pos.peano_ind.
         reflexivity. intros p IHp.
         rewrite Pos2Nat.inj_succ. simpl.
         rewrite -> IHp.
         rewrite <- Pos.add_1_r.
         rewrite Pos2Z.inj_add, inject_Z_plus.
         reflexivity. }
       assert (B:inj_Q IR (Pos.succ p:Q)[#][0]).
       { stepl (nring (R:=IR) (S (Pos.to_nat p))).
         apply nringS_ap_zero.
         apply eq_symmetric;assumption. }
       eapply eq_transitive;[apply inj_Q_div|].
       instantiate (1:=B).
       apply div_wd.
       apply inj_Q_One.
       exact A.
Qed.

Definition rational_exp_small_neg (a:Q) (p:-(1) <= a <= 0) : CR
  := translate 1 (AltSeries _ (expStream a) (xH,1%Q) _
                            (expStream_alt p) (expStream_zl p)).

Lemma rational_exp_small_neg_wd (a1 a2 : Q) (p1 : -(1) <= a1 <= 0) (p2 : -(1) <= a2 <= 0) :
  a1 == a2 → rational_exp_small_neg p1 = rational_exp_small_neg p2.
Proof. 
  intros E. unfold rational_exp_small_neg. 
  rewrite <- CRplus_translate.
  rewrite <- CRplus_translate.
  apply CRplus_eq_r.
  apply AltSeries_wd.
  apply Pos.peano_ind.
  - unfold Str_pth; simpl.
    rewrite E. reflexivity.
  - intros. unfold Str_pth.
    rewrite iterate_succ, iterate_succ.
    simpl.
    unfold Str_pth in H. rewrite H. clear H.
    apply Qmult_comp. 
    apply Qmult_comp. reflexivity.
    exact E. 
    rewrite expStream_fst, expStream_fst.
    reflexivity.
  - reflexivity.
Qed.

Lemma rational_exp_small_neg_correct : forall (a:Q) Ha,
    (@rational_exp_small_neg a Ha == IRasCR (Exp (inj_Q IR a)))%CR.
Proof.
  intros a Ha.
  unfold rational_exp_small_neg.
  rewrite <- CRplus_translate.
  setoid_replace 1%CR with
      (IRasCR
         ((λ n : nat,
                 Exp_ps n (inj_Q IR a)
                        (fun_series_inc_IR realline Exp_ps Exp_conv (inj_Q IR a) I n)) 0%nat)).
  apply: AltSeries_correct.
  intro p.
  apply exp_ps_correct.
  simpl.
  rewrite <- IR_One_as_CR.
  apply IRasCR_wd.
  rewrite mult_one.
  unfold cf_div.
  rewrite one_mult.
  rewrite <- inv_one at 1.
  apply f_rcpcl_wd.
  rewrite cm_lft_unit.
  reflexivity.
Qed.

Program Definition CRe_inv := @rational_exp_small_neg (-1) _.
Next Obligation. constructor; discriminate. Qed.

(** exp is extended to work on [[-2^n, 0]] for all n. *)

(* Faster to compress between the powers of 2, than take a big power 2^n. *)
Fixpoint CRpower_2_iter (n : nat) (x : CR) : CR :=
  match n with
  | O => x
  | S p => CRpower_N_bounded 2 (1#1) (compress (CRpower_2_iter p x))
  end.

Lemma CRpower_2_iter_wd : forall (n : nat) (x y : CR),
    (x == y)%CR -> (CRpower_2_iter n x == CRpower_2_iter n y)%CR.
Proof.
  induction n.
  - intros. exact H.
  - intros. simpl. apply Cmap_wd. reflexivity.
    rewrite compress_fun_correct, compress_fun_correct.
    apply IHn, H.
Qed.

Local Opaque compress CRpower_N_bounded.
Lemma rational_exp_neg_bounded_correct_aux (a : Q) :
  a ≤ 0 → (CRpower_N_bounded 2 (1 # 1)) (IRasCR (Exp (inj_Q IR (a / 2))))
          = IRasCR (Exp (inj_Q IR a)).
Proof.
 intros Ea.
 rewrite <- CRpower_N_bounded_correct.
 - change (CRpower_slow (IRasCR (Exp (inj_Q IR (a / 2)))) (N.to_nat 2))%CR
     with (IRasCR (Exp (inj_Q IR (a / 2)))
           * (IRasCR (Exp (inj_Q IR (a / 2))) * 1))%CR. 
   rewrite CRmult_1_r.
   rewrite <- IR_mult_as_CR.
   apply IRasCR_wd.
  set (a':=inj_Q IR (a/2)).
  simpl.
  stepl (Exp (a'[+]a')); [| now apply Exp_plus].
  apply Exp_wd.
  unfold a'.
  eapply eq_transitive.
   apply eq_symmetric; apply (inj_Q_plus IR).
  apply inj_Q_wd.
  change (a / (2#1) + a / (2#1) == a). field.
 - apply leEq_imp_AbsSmall.
   + rewrite <- IR_Zero_as_CR.
     apply IR_leEq_as_CR.
     apply less_leEq; apply Exp_pos.
   + apply (@CRle_trans _ (IRasCR [1])).
     apply IR_leEq_as_CR. apply Exp_leEq_One.
     stepr (inj_Q IR 0); [| now apply (inj_Q_nring IR 0)].
     apply inj_Q_leEq.
     apply mult_cancel_leEq with (2:Q).
     constructor.
     change (a/2*2<=0).
     now replace LHS with a by (simpl; field; discriminate). 
     simpl. rewrite IR_One_as_CR. apply CRle_refl.
Qed.

(** [exp] works on all nonpositive numbers. *)

(* Do not do 2^n in nat, it could make a very large unary nat. *)
Lemma rational_exp_neg_bounded_correct : forall (n:nat) (a:Q) (Ha : -1 <= a*(1#2)^n <= 0),
    (CRpower_2_iter n (rational_exp_small_neg Ha) == IRasCR (Exp (inj_Q IR a)))%CR.
Proof.
 induction n.
 - intros. simpl.
   assert (-1 <= a <= 0) as Ha_simpl.
   { simpl in Ha. rewrite Qmult_1_r in Ha. exact Ha. }
   rewrite <- (rational_exp_small_neg_correct Ha_simpl).
   apply rational_exp_small_neg_wd.
   apply Qmult_1_r.
 - intros a Ha.
   simpl.
   rewrite -> compress_correct.
   rewrite <- rational_exp_neg_bounded_correct_aux.
   apply Cmap_wd. reflexivity.
   assert (-1 <= (a/2)*(1#2)^n <= 0) as Ha_div.
   { change (S n) with (1+n)%nat in Ha.
     rewrite Nat2Z.inj_add, Qpower_plus in Ha.
     simpl in Ha. rewrite Qmult_assoc in Ha.
     exact Ha. discriminate. }
   rewrite <- (IHn _ Ha_div).
   apply CRpower_2_iter_wd, rational_exp_small_neg_wd.
   unfold Qdiv. rewrite <- Qmult_assoc.
   apply Qmult_comp. reflexivity.
   change (/2) with ((1#2)^1).
   rewrite <- Qpower_plus.
   clear IHn.
   change 1%Z with (Z.of_nat 1).
   rewrite <- (Nat2Z.inj_add 1 n).
   reflexivity. discriminate.
   destruct Ha as [_ Ha].
   apply (Qmult_le_r _ _ ((1#2)^S n)).
   apply Q.Qpower_0_lt. reflexivity.
   rewrite Qmult_0_l. exact Ha.
Qed.

(* Improve n such as -2^n <= a.
   -a <= 2^n is equivalent to Qceiling(-a) <= 2^n and then
   we can use the integer log2. *)
Lemma rational_exp_bound_power_2 : forall (a:Q), 
    a <= 0 -> - inject_Z (2^Z.to_nat (Z.log2_up (Qceiling(-a)))) <= a.
Proof.
 intros [[|n|n] d] Ha; simpl.
   discriminate.
  elim Ha.
  reflexivity.
  rewrite Z2Nat.id.
  clear Ha.
  rewrite <- (Qopp_involutive (Z.neg n # d)) at 2.
  apply Qopp_le_compat.
  change (-(Z.neg n#d)) with (Zpos n # d).
  apply Q.Zle_Qle_Qceiling.
  apply Z.log2_up_le_pow2.
  2: apply Z.le_refl.
  apply Z2Nat.inj_lt. apply Z.le_refl.
  apply (Qceiling_resp_le 0). discriminate.
  apply Q.Qlt_lt_of_nat_inject_Z.
  reflexivity.
  apply Z.log2_up_nonneg.
Qed.

Lemma power_2_improve_bound_correct : forall (n:nat) (a:Q),
    a <= 0 ->
    -inject_Z (2^n) <= a ->
    -1 <= a*(1#2)^n <= 0.
Proof.
  split.
  - apply (Qmult_le_r _ _ ((2#1)^n)).
    apply Q.Qpower_0_lt. reflexivity.
    apply (Qle_trans _ a).
    rewrite Zpower_Qpower in H0.
    exact H0. apply Nat2Z.is_nonneg.
    rewrite <- Qmult_assoc, <- Qmult_power.
    setoid_replace ((1 # 2) * 2)%Q with 1%Q by reflexivity.
    rewrite Qpower_1, Qmult_1_r. apply Qle_refl.
  - rewrite <- (Qmult_0_l ((1#2)^n)).
    apply Qmult_le_compat_r. exact H.
    apply Qpower_pos. discriminate.
Qed.

Definition rational_exp_neg (a:Q) (Ha : a <= 0) : CR
  := CRpower_2_iter
       (Z.to_nat (Z.log2_up (Qceiling(-a))))
       (rational_exp_small_neg
          (power_2_improve_bound_correct _ Ha (rational_exp_bound_power_2 Ha))).

(* Some time measures on a 5000 bogomips CPU
Lemma Zneg_neg : forall p:positive, Z.neg p # 1 <= 0.
Proof. intros. discriminate. Qed.
Time Eval vm_compute in (approximate (rational_exp_neg (@Zneg_neg 100%positive))
                                     (Qpos2QposInf (1#(10 ^ 100)%positive))).
(* 1.3 secs *)
Time Eval vm_compute in (approximate (rational_exp_neg (@Zneg_neg 200%positive))
                                     (Qpos2QposInf (1#(10 ^ 200)%positive))).
(* 8 secs *)
Time Eval vm_compute in (approximate (rational_exp_neg (@Zneg_neg 300%positive))
                                     (Qpos2QposInf (1#(10 ^ 300)%positive))).
(* 23.6 secs *)
*)

Lemma rational_exp_neg_correct : forall (a:Q) Ha,
 (@rational_exp_neg a Ha == IRasCR (Exp (inj_Q IR a)))%CR.
Proof.
 intros a Ha.
 apply rational_exp_neg_bounded_correct.
Qed.

(** exp(x) is bounded below by (3^x) for x nonpositive, and hence
exp(x) is positive. *)
Lemma CRe_inv_posH : ('(1#3) <= CRe_inv)%CR.
Proof.
 unfold CRle.
 apply CRpos_nonNeg.
 CR_solve_pos (1#1)%Qpos.
Qed.

(* We parametrize the following lemmas by a lowerbound of [CRe_inv] so that
    we can easily swap lowerbounds. *)
Lemma rational_exp_neg_posH (q : Qpos) (n:nat) (a:Q) :
  -n ≤ a → a ≤ 0 → '(proj1_sig q) ≤ CRe_inv
  → '(proj1_sig q^n) ≤ IRasCR (Exp (inj_Q IR a)).
Proof.
 intros Hn Ha small.
 rewrite <- IR_inj_Q_as_CR.
 rewrite <- IR_leEq_as_CR.
 stepl (inj_Q IR (proj1_sig q) [^]n)
   by (now (apply eq_symmetric; apply inj_Q_power)).
 assert (X:[0][<]inj_Q IR (`q)).
  stepl (inj_Q IR 0); [| now apply (inj_Q_nring IR 0)].
  apply inj_Q_less.
  now destruct q.
 astepl (inj_Q IR (`q)[!](nring n)[//]X).
 unfold power.
 apply Exp_resp_leEq.
 destruct n.
 simpl (nring 0).
 rewrite cring_mult_zero_op.
  stepl (inj_Q IR 0); [| now apply (inj_Q_nring IR 0)].
  apply inj_Q_leEq.
  assumption.
 apply (fun a b => (shift_mult_leEq' _ a b _ (nringS_ap_zero IR n))).
  apply nring_pos; auto with *.
 stepr (inj_Q IR (a/(S n))).
  apply Exp_cancel_leEq.
  astepl (inj_Q IR (`q)).
  rewrite -> IR_leEq_as_CR.
  rewrite -> IR_inj_Q_as_CR.
  assert (Ha0 : -(1)<=(a/S n)<=0).
   split.
    rewrite -> Qle_minus_iff.
    replace RHS with ((a + S n)*(1/(S n))) by (simpl; field;discriminate).
    replace LHS with (0*(1/(S n))) by simpl; ring.
    apply: mult_resp_leEq_rht;simpl.
     replace RHS with (a + - (- (P_of_succ_nat n))) by simpl; ring.
     rewrite <- Qle_minus_iff.
     assumption.
    rewrite <- (Qmake_Qdiv 1 (P_of_succ_nat n)).
    discriminate.
   replace RHS with (0*(1/(S n))) by simpl; ring.
   apply: mult_resp_leEq_rht;simpl.
    assumption.
   rewrite <- (Qmake_Qdiv 1 (P_of_succ_nat n)).
   discriminate.
  rewrite <- (rational_exp_small_neg_correct Ha0).
  apply CRle_trans with CRe_inv.
   apply small.
  unfold CRe_inv.
  do 2 rewrite -> (rational_exp_small_neg_correct).
  rewrite <- IR_leEq_as_CR.
  apply Exp_resp_leEq.
  apply inj_Q_leEq.
  tauto.
 assert (X0:inj_Q IR (inject_Z (S n))[#][0]).
  stepl (inj_Q IR (nring (S n))).
   stepl (@nring IR (S n)); [| now (apply eq_symmetric; apply (inj_Q_nring IR (S n)))].
   apply (nringS_ap_zero).
  apply inj_Q_wd.
  apply nring_Q.
 stepl (inj_Q IR a[/]_[//]X0).
  apply div_wd.
   apply eq_reflexive.
  stepl (inj_Q IR (nring (S n))).
   apply inj_Q_nring.
  apply inj_Q_wd.
  apply nring_Q.
 apply eq_symmetric.
 apply inj_Q_div.
Qed.

Lemma rational_exp_neg_posH' (c : Qpos) (a : Q) : 
  a ≤ 0 → '(proj1_sig c) ≤ CRe_inv
  → '(proj1_sig (Qpos_power c (-Qfloor a))) ≤ IRasCR (Exp (inj_Q IR a)).
Proof.
 intros Ha small.
 assert (X0:(0 <= -Qfloor a)%Z).
  apply Z.opp_nonneg_nonpos.
  rewrite Q.Zle_Qle.
  apply Qle_trans with a; [| assumption].
  now apply Qfloor_le.
  setoid_replace (proj1_sig (Qpos_power c (-Qfloor a)))
    with (proj1_sig c ^ Z_to_nat X0).
  apply rational_exp_neg_posH; trivial.
  rewrite <- (Z_to_nat_correct X0).
  rewrite inject_Z_opp, Qopp_involutive.
  now apply Qfloor_le.
 now rewrite <- Z_to_nat_correct.
Qed.

(* Need transparent and fast positivity to define
   exponential on positive rationals by division. *)
Lemma rational_exp_neg_pos : forall (a:Q) Ha,
 CRpos (@rational_exp_neg a Ha).
Proof.
 intros a Ha.
 exists (Qpos_power (1#3) (-Qfloor a))%Qpos. simpl.
 rewrite rational_exp_neg_correct.
 apply (rational_exp_neg_posH' (1#3)); trivial.
 apply CRe_inv_posH.
Defined.

(** exp is extended to all numbers by saying exp(x) = 1/exp(-x) when x
is positive. *)
Definition rational_exp (a:Q) : CR.
Proof.
  destruct a as [[|n|n] d].
  - exact 1%CR.
  - refine (CRinv_pos (Qpos_power (1#3) (Qceiling (n#d)))%Qpos
                      (@rational_exp_neg (Zneg n#d) _)).
    discriminate.
  - apply (@rational_exp_neg (Zneg n#d)).
    discriminate.
Defined.

(* Some time measures on a 5000 bogomips CPU
Time Eval vm_compute in (approximate (rational_exp (100#1)) (Qpos2QposInf (1#1))).
(* 1.2 secs *)

Time Eval vm_compute in (approximate (rational_exp (200#1)) (Qpos2QposInf (1#1))).
(* 7.1 secs *)

Time Eval vm_compute in (approximate (rational_exp (300#1)) (Qpos2QposInf (1#1))).
(* 21 secs *)
*)

Lemma rational_exp_pos_correct (a : Q) (Pa : 0 ≤ a) (c : Qpos) :
  ('proj1_sig c <= IRasCR (Exp (inj_Q IR (-a)%Q)))%CR → 
  CRinv_pos c (IRasCR (Exp (inj_Q IR (-a)))) = IRasCR (Exp (inj_Q IR a)).
Proof.
 intros Ec.
 assert (X: (IRasCR (Exp (inj_Q IR (-a)%Q)) >< 0)%CR).
  right. exists c.
  now ring_simplify.
 rewrite (CRinvT_pos_inv c X); trivial.
 rewrite <- IR_recip_as_CR_2.
 apply IRasCR_wd.
 apply eq_symmetric.
 eapply eq_transitive;[|apply div_wd; apply eq_reflexive].
 apply Exp_inv'.
 rewrite (inj_Q_inv IR a), cg_inv_inv.
 reflexivity.
Qed.

Lemma rational_exp_correct (a : Q) :
 (rational_exp a = IRasCR (Exp (inj_Q IR a)))%CR.
Proof.
 unfold rational_exp.
 destruct a as [[|n|n] d].
 - rewrite <- IR_One_as_CR.
   apply IRasCR_wd.
   setoid_replace (inj_Q IR (0 # d)) with (cm_unit IR).
   symmetry. apply Exp_zero.
   rewrite <- inj_Q_Zero.
   apply inj_Q_wd. reflexivity.
 - rewrite rational_exp_neg_correct.
   apply (@rational_exp_pos_correct (Zpos n#d)).
   discriminate.
   apply (rational_exp_neg_posH' (1#3)).
   discriminate.
   now apply CRe_inv_posH.
 - apply rational_exp_neg_correct.
Qed.

Lemma rational_exp_square (a : Q) :
  a ≤ 0 → CRpower_N_bounded 2 (1 # 1) (rational_exp (a / 2)) = rational_exp a.
Proof.
 intros.
 rewrite 2!rational_exp_correct.
 now apply rational_exp_neg_bounded_correct_aux.
Qed.

Lemma rational_exp_opp (c : Qpos) (a : Q) :
  0 ≤ a → '(proj1_sig c) ≤ rational_exp (-a) → CRinv_pos c (rational_exp (-a)) = rational_exp a.
Proof.
  rewrite ?rational_exp_correct.
  intros. now apply rational_exp_pos_correct.
Qed.

Lemma rational_exp_lower_bound (c : Qpos) (a : Q) : 
  a ≤ 0 → '(proj1_sig c) ≤ CRe_inv
  → '(proj1_sig (Qpos_power c (-Qfloor a))) ≤ rational_exp a.
Proof.
 rewrite rational_exp_correct.
 now apply rational_exp_neg_posH'.
Qed.

(**
*** e
*)
Definition CRe : CR := rational_exp 1.

Lemma CRe_correct : (CRe = IRasCR E)%CR.
Proof.
 unfold CRe.
 rewrite -> rational_exp_correct.
 apply IRasCR_wd.
 rewrite inj_Q_One.
 algebra.
Qed.

#[global]
Hint Rewrite <- CRe_correct : IRtoCR.

Opaque inj_Q.

(** [exp] is uniformly continuous below any given integer. *)
Definition exp_bound (z:Z) : Qpos :=
(match z with
 |Z0 => 1#1
 |Zpos p => Qpos_power (3#1) p
 |Zneg p => Qpos_power (1#2) p
 end)%Qpos.

Lemma exp_bound_bound : forall (z:Z) x, closer (inj_Q IR (z:Q)) x -> AbsIR (Exp x)[<=]inj_Q IR (proj1_sig (exp_bound z)).
Proof.
 intros [|z|z]; simpl; intros x Hx; apply AbsSmall_imp_AbsIR;
   (apply leEq_imp_AbsSmall;[apply less_leEq; apply Exp_pos|]).
 rewrite inj_Q_One.
 apply Exp_leEq_One.
 rewrite inj_Q_Zero in Hx.
 exact Hx.
  apply leEq_transitive with (Exp (Max x [0])).
   apply Exp_resp_leEq.
   apply lft_leEq_Max.
  stepr (Three[!](inj_Q IR (inject_Z z))[//](pos_three IR)).
   astepl (E[!](Max x [0])[//]pos_E).
   apply real_power_resp_leEq_both; try solve [IR_solve_ineq (1#1)%Qpos].
    apply rht_leEq_Max.
   apply Max_leEq; auto.
   stepl (inj_Q IR 0).
    apply inj_Q_leEq.
    simpl; auto with *.
   apply (inj_Q_nring IR 0).
  stepl (Three[!]nring (nat_of_P z)[//]pos_three IR).
   astepl (@nring IR 3 [^](nat_of_P z)).
   stepl ((inj_Q IR (3%mc:Q))[^](nat_of_P z)).
    stepl (inj_Q IR (3%mc^z)).
     apply inj_Q_wd.
     apply eq_symmetric.
     reflexivity.
    rewrite <- convert_is_POS.
    apply inj_Q_power.
   apply nexp_wd.
   apply (inj_Q_nring IR 3).
  apply power_wd.
   apply eq_reflexive.
  apply eq_symmetric.
  rewrite <- convert_is_POS.
  stepl (inj_Q IR (nring (nat_of_P z))).
   apply (inj_Q_nring).
  apply inj_Q_wd; apply nring_Q.
 stepr (Half[!](inj_Q IR (inject_Z z))[//](pos_half IR)).
  astepl (Exp [--][--]x).
  astepl ([1][/]_[//](Exp_ap_zero [--]x)).
  unfold Half.
  astepr (([1][!]inj_Q IR (z:Q)[//]pos_one _)[/]((Two[!]inj_Q IR (z:Q)[//]pos_two _))[//]power_ap_zero _ _ _).
  astepr ([1][/]((Two[!]inj_Q IR (z:Q)[//]pos_two _))[//]power_ap_zero _ _ _).
  apply recip_resp_leEq.
   apply power_pos.
  astepr (E[!][--]x[//]pos_E).
  apply real_power_resp_leEq_both; try solve [IR_solve_ineq (1#1)%Qpos].
   stepl (inj_Q IR 0).
    apply inj_Q_leEq.
    simpl; auto with *.
   apply (inj_Q_nring IR 0).
   rewrite <- cg_inv_inv.
  apply inv_resp_leEq.
  stepr (inj_Q IR ((Zneg z):Q)).
   assumption.
  astepr (inj_Q IR (-(z:Q))).
  apply inj_Q_wd.
  simpl; reflexivity.
 stepl (Half[!]nring (nat_of_P z)[//]pos_half IR).
  astepl (@Half IR [^](nat_of_P z)).
  stepl ((inj_Q IR ((1#2):Q))[^](nat_of_P z)).
   stepl (inj_Q IR ((1#2)^z)).
    apply inj_Q_wd.
    apply eq_symmetric.
    reflexivity.
   rewrite <- (convert_is_POS z).
   apply inj_Q_power.
  apply nexp_wd.
  assert (X:(inj_Q IR (2:Q))[#][0]).
   stepr (inj_Q IR 0).
    apply inj_Q_ap; discriminate.
   apply (inj_Q_nring IR 0).
  stepr ((inj_Q IR 1)[/]_[//]X).
   stepl (inj_Q IR (1/2)).
    apply inj_Q_div.
   apply inj_Q_wd.
   apply eq_symmetric; apply Qmake_Qdiv.
  apply div_wd.
  apply inj_Q_One.
  apply (inj_Q_nring IR 2).
 apply power_wd.
  apply eq_reflexive.
 apply eq_symmetric.
 rewrite <- convert_is_POS.
 stepl (inj_Q IR (nring (nat_of_P z))).
  apply (inj_Q_nring).
 apply inj_Q_wd; apply nring_Q.
Qed.

Lemma exp_bound_uc_prf : forall z:Z, is_UniformlyContinuousFunction (fun a => rational_exp (Qmin z a)) (Qscale_modulus (proj1_sig (exp_bound z))).
Proof.
 intros z.
 assert (Z:Derivative (closer (inj_Q IR (z:Q))) I Expon Expon).
  apply (Included_imp_Derivative realline I).
   Deriv.
  Included.
 apply (is_UniformlyContinuousD None (Some (z:Q)) I _ _ Z).
  intros q [] H.
  apply rational_exp_correct.
 intros x [] H.
 apply: exp_bound_bound.
 assumption.
Qed.

Definition exp_bound_uc (z:Z) :  Q_as_MetricSpace --> CR :=
Build_UniformlyContinuousFunction (@exp_bound_uc_prf z).

(** [exp] for any real number upto a given integer. *)
Definition exp_bounded (z:Z) : CR --> CR := (Cbind QPrelengthSpace (exp_bound_uc z)).

Lemma exp_bounded_correct : forall (z:Z) x, closer (inj_Q _ (z:Q)) x -> (IRasCR (Exp x)==exp_bounded z (IRasCR x))%CR.
Proof.
 intros z x Hx.
 assert (Z:Continuous (closer (inj_Q IR (z:Q))) Expon).
  apply (Included_imp_Continuous realline).
   Contin.
  Included.
 apply (fun a b c => @ContinuousCorrect _ a Expon Z b c x I); auto with *.
  constructor.
 intros q [] H.
 transitivity (exp_bound_uc z q);[|].
  change (' q)%CR with (Cunit_fun _ q).
  unfold exp_bounded.
  pose proof (Cbind_correct QPrelengthSpace (exp_bound_uc z)).
  apply ucEq_equiv in H0.
  rewrite (H0 (Cunit_fun Q_as_MetricSpace q)). clear H0.
  apply BindLaw1.
 change (rational_exp (Qmin z q) == IRasCR (Exp (inj_Q IR q)))%CR.
 rewrite -> rational_exp_correct.
 apply IRasCR_wd.
 apply Exp_wd.
 apply inj_Q_wd.
 simpl.
 rewrite <- Qle_min_r.
 apply leEq_inj_Q with IR.
 assumption.
Qed.

(** exp on all real numbers.  [exp_bounded] should be used instead when [x]
is known to be bounded by some intenger. *)
Definition exp (x:CR) : CR
  := exp_bounded (Qceiling (approximate x (Qpos2QposInf (1#1)) + (1#1))) x.
(* begin hide *)
Arguments exp : clear implicits.
(* end hide *)
Lemma exp_bound_lemma : forall x : CR, (x <= ' (approximate x (Qpos2QposInf (1 # 1)) + 1)%Q)%CR.
Proof.
 intros x.
 assert (X:=ball_approx_l x (1#1)).
 rewrite <- CRAbsSmall_ball in X.
 destruct X as [X _].
 simpl in X.
 rewrite <- CRplus_Qplus.
 apply CRle_trans with (doubleSpeed x).
  rewrite -> (doubleSpeed_Eq x); apply CRle_refl.
 intros e.
 assert (Y:=X e).
 simpl in *.
 do 2 (unfold Cap_raw in *; simpl in * ).
 apply (Qle_trans _ _ _ Y).
 ring_simplify. apply Qle_refl.
Qed.

Lemma exp_correct : forall x, (IRasCR (Exp x) = exp (IRasCR x))%CR.
Proof.
 intros x.
 unfold exp.
 apply exp_bounded_correct.
 simpl.
 apply leEq_transitive with (inj_Q IR ((approximate (IRasCR x) (Qpos2QposInf (1 # 1)) + 1)));
   [|apply inj_Q_leEq; simpl;auto with *].
 rewrite -> IR_leEq_as_CR.
 rewrite -> IR_inj_Q_as_CR.
 apply exp_bound_lemma.
Qed.
(* begin hide *)
#[global]
Hint Rewrite exp_correct : IRtoCR.
(* end hide *)
Lemma exp_bound_exp : forall (z:Z) (x:CR),
 (x <= 'z ->
  exp_bounded z x == exp x)%CR.
Proof.
 intros z x H.
 unfold exp.
 set (a:=(approximate x (Qpos2QposInf (1 # 1)) + 1)).
 rewrite <- (CRasIRasCR_id x).
 rewrite <- exp_bounded_correct.
  rewrite <- exp_bounded_correct.
   reflexivity.
  change (CRasIR x [<=] inj_Q IR (Qceiling a:Q)).
  rewrite -> IR_leEq_as_CR.
  autorewrite with IRtoCR.
  rewrite -> CRasIRasCR_id.
  apply CRle_trans with ('a)%CR.
   apply exp_bound_lemma.
  rewrite -> CRle_Qle.
  auto with *.
 change (CRasIR x [<=] inj_Q IR (z:Q)).
 rewrite -> IR_leEq_as_CR.
 autorewrite with IRtoCR.
 rewrite -> CRasIRasCR_id.
 assumption.
Qed.
(* begin hide *)
Add Morphism exp with signature (@msp_eq _) ==> (@msp_eq _) as exp_wd.
Proof.
 intros x y Hxy.
 unfold exp at 1.
 set (a :=  (approximate x (Qpos2QposInf (1 # 1)) + 1)).
 rewrite -> Hxy.
 apply exp_bound_exp.
 rewrite <- Hxy.
 apply CRle_trans with ('a)%CR.
  apply exp_bound_lemma.
 rewrite -> CRle_Qle.
 auto with *.
Qed.
(* end hide *)
Lemma exp_Qexp : forall x : Q, (exp (' x) = rational_exp x)%CR.
Proof.
 intros x.
 rewrite <- IR_inj_Q_as_CR.
 rewrite <- exp_correct.
 rewrite <- rational_exp_correct.
 reflexivity.
Qed.

#[global]
Instance: Proper ((=) ==> (=)) rational_exp.
Proof.
  intros x1 x2 E.
  rewrite <-2!exp_Qexp.
  now rewrite E.
Qed.

(* begin hide *)
#[global]
Hint Rewrite exp_Qexp : CRfast_compute.
(* end hide *)
