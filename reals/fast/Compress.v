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

Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import CoRN.model.totalorder.QposMinMax.
Require Export CoRN.model.metric2.CRmetric.
Require Import CoRN.model.metric2.Qmetric.
Require Import Coq.ZArith.Zdiv.

Opaque CR.

Local Open Scope Q_scope.
Local Open Scope uc_scope.

(**
** Compression
Compress improves the computation by reducing the size of the numerator
and denominator of rational numbers. It works by increasing the
requested precession, but then rounding the result to a value with a
small numerator and denominator.

The full euclidean algortihm would find the optimial rational approximation.
But for speed we simply do division to quickly find a good rational
approximation.
*)
Definition approximateQ (x:Q) (p:positive) :=
let (n,d) := x in (Z.div (n*Zpos p) (Zpos d)#p).

Lemma approximateQ_correct : forall x p,
    ball (1#p) x (approximateQ x p).
Proof.
 intros [n d] p.
 split; simpl; unfold Qle; simpl.
 - apply Z.le_trans with 0%Z.
   discriminate.
  apply Zmult_le_0_compat; auto with *.
  replace (n * Zpos p + - (n * Zpos p / Zpos d) * Zpos d)%Z
    with (n * Zpos p - ((n * Zpos p / Zpos d) * Zpos d))%Z by ring.
  apply Zle_minus_le_0.
  rewrite Zmult_comm.
  apply Z_mult_div_ge; auto with *.
 - rewrite Zpos_mult_morphism.
 apply Zmult_le_compat_r; auto with *.
 replace (n * Zpos p + - (n * Zpos p / Zpos d) * Zpos d)%Z
   with ((n*Zpos p) mod (Zpos d))%Z.
  destruct (Z_mod_lt (n*Zpos p) (Zpos d)); auto with *.
 symmetry. transitivity (n * Zpos p - (Zpos d*(n * Zpos p / Zpos d)))%Z;[ring|].
 symmetry.
 apply -> Zeq_plus_swap.
 rewrite Zplus_comm.
 symmetry.
 apply Z_div_mod_eq.
 auto with *.
Qed.

Lemma approximateQ_big : forall (z:Z) a p, ((z#1) <= a) -> (z#1) <= approximateQ a p.
Proof.
 intros z [n d] p Ha.
 unfold approximateQ.
 unfold Qle in *.
 simpl in *.
 apply Zlt_succ_le.
 unfold Z.succ.
 apply Zmult_gt_0_lt_reg_r with (Zpos d).
 reflexivity.
 replace ((n * Zpos p / Zpos d * 1 + 1) * Zpos d)%Z
   with (Zpos d* (n*Zpos p/ Zpos d) + (Zmod (n*Zpos p) (Zpos d)) - (Zmod (n*Zpos p) (Zpos d)) + Zpos d)%Z
   by ring.
 rewrite <- (Z_div_mod_eq (n*Zpos p) (Zpos d)) by auto with zarith.
 apply Z.le_lt_trans with (n*1*Zpos p)%Z.
  replace (z*Zpos p*Zpos d)%Z with (z*Zpos d*Zpos p)%Z by ring.
  apply Zmult_lt_0_le_compat_r; auto with *.
 apply Zlt_0_minus_lt.
 replace (n * Zpos p - (n * Zpos p) mod (Zpos d) + Zpos d - n * 1 * Zpos p)%Z
   with (Zpos d - (Zmod (n*Zpos p) (Zpos d)))%Z by ring.
 rewrite <- Zlt_plus_swap.
 ring_simplify.
 assert (X:(Zpos d >0)%Z) by auto with *.
 destruct (Z_mod_lt (n*Zpos p) _ X).
 assumption.
Qed.

(** Compress doubles the requried precision and uses the extra leway to
round the rational number. *)
Definition compress_raw (x:CR) (e:QposInf) : Q :=
match e with
| QposInfinity => approximate x e
| Qpos2QposInf e =>
 let (n,d) := proj1_sig e in
 match (Z.succ (Z.div (2*Zpos d) n)) with
  Zpos p => approximateQ (approximate x (Qpos2QposInf (exist (Qlt 0) (1#p) eq_refl))) p
 |_ => approximate x e
 end
end.

Lemma compress_raw_prop : forall x (e:Qpos),
    ball (proj1_sig e) x (Cunit (compress_raw x e)).
Proof.
 intros x. intros [[n d] dpos].
 destruct n as [|n|n]. inversion dpos. 2: inversion dpos.
 simpl.
 assert (0 < Z.succ (Zpos (d~0)%positive / Zpos n))%Z as zpos.
 { unfold Z.succ. 
   apply (Z.lt_le_trans _ (0+1)). reflexivity.
   apply Z.add_le_mono_r. apply Z_div_pos.
   reflexivity. discriminate. }
 destruct (Z.succ (Zpos (xO d) / Zpos n)) eqn:Hp.
 - exfalso. discriminate.
 - apply ball_weak_le with (2#p).
  unfold Qle.
  simpl.
  rewrite Zpos_mult_morphism.
  rewrite <- Hp.
  unfold Z.succ.
  rewrite Zmult_plus_distr_r.
  apply Zle_0_minus_le.
  replace (Zpos n * (Zpos (d~0)%positive / Zpos n) + Zpos n * 1 - Zpos (d~0)%positive)%Z
    with (Zpos n - (Zpos (xO d) - Zpos n * (Zpos (xO d) / Zpos n)))%Z by ring.
  apply Zle_minus_le_0.
  replace (Zpos (d~0)%positive - Zpos n * (Zpos (d~0)%positive / Zpos n))%Z
    with (Zpos (xO d) mod (Zpos n))%Z.
   destruct (Z_mod_lt (Zpos (xO d)) (Zpos n)); auto with *.
  symmetry. transitivity (Zpos (xO d) - (Zpos n*(Zpos (xO d) / Zpos n)))%Z;[ring|].
  symmetry; apply -> Zeq_plus_swap.
  rewrite Zplus_comm.
  symmetry.
  apply Z_div_mod_eq.
  auto with *.
  assert (QposEq (2#p) ((1#p)+(1#p))).
  { unfold QposEq. simpl. 
    repeat rewrite -> Qmake_Qdiv.
    unfold Qdiv.
    ring. }
 apply (ball_wd _ H _ _ (reflexivity _) _ _ (reflexivity _)). clear H. 
  eapply ball_triangle with (Cunit (approximate x (Qpos2QposInf (1#p)))).
   apply ball_approx_r.
  Transparent CR.
  change (ball (m:=Complete Q_as_MetricSpace)
               (1 # p) (Cunit (approximate x (Qpos2QposInf (1 # p))))
               (Cunit (approximateQ (approximate x (Qpos2QposInf (1 # p))) p))).
  rewrite -> ball_Cunit.
  apply approximateQ_correct.
 - exfalso. discriminate.
Qed.

Lemma compress_raw_prf : forall x,
    is_RegularFunction (@ball Q_as_MetricSpace) (compress_raw x).
Proof.
 intros x e1 e2.
 rewrite <- ball_Cunit.
 eapply ball_triangle;[|apply compress_raw_prop].
 apply ball_sym.
 apply compress_raw_prop.
Qed.

Definition compress_fun (x:CR) : CR :=
Build_RegularFunction (compress_raw_prf x).

(** Compress is equivalent to the identity function. *)
Lemma compress_fun_correct : forall x, (compress_fun x==x)%CR.
Proof.
 intros x.
 apply regFunEq_e.
 intros e.
 unfold compress_fun.
 unfold approximate at 1.
 rewrite <- ball_Cunit.
 eapply ball_triangle;[|apply ball_approx_r].
 apply ball_sym.
 apply compress_raw_prop.
Qed.

Lemma compress_uc : is_UniformlyContinuousFunction compress_fun Qpos2QposInf.
Proof.
 intros e x y H.
 do 2 rewrite -> compress_fun_correct.
 assumption.
Qed.

Definition compress : CR --> CR :=
Build_UniformlyContinuousFunction compress_uc.

Lemma compress_correct : forall x, (compress x==x)%CR.
Proof.
 intros x.
 apply compress_fun_correct.
Qed.
