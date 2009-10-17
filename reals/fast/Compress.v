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

Require Export CRmetric.
Require Import Qmetric.
Require Import COrdAbs.
Require Import Qordfield.
Require Import CornTac.

Opaque CR.

Open Local Scope Q_scope.
Open Local Scope uc_scope.

(**
** Compression
Compress improves the compuation by reducing the size of the numerator
and denominator of rational numbers.  It works by increasing the
requested precession, but then rounding the result to a value with a
small numerator and denominator.

The full euclidean algortihm would find the optimial rational approximation.
But for speed we simply do division to quickly find a good rational
approximation.
*)
Definition approximateQ (x:Q) (p:positive) :=
let (n,d) := x in (Zdiv (n*p) d#p).

Lemma approximateQ_correct : forall x p, ball (1#p) x (approximateQ x p).
Proof.
 intros [n d] p.
 split; simpl; unfold Qle; simpl.
  apply Zle_trans with 0%Z.
   discriminate.
  apply Zmult_le_0_compat; auto with *.
  replace RHS with (n * p - ((n * p / d) * d))%Z by ring.
  apply Zle_minus_le_0.
  rewrite Zmult_comm.
  apply Z_mult_div_ge; auto with *.
 rewrite Zpos_mult_morphism.
 apply Zmult_le_compat_r; auto with *.
 replace LHS with ((n*p) mod d)%Z.
  destruct (Z_mod_lt (n*p) d); auto with *.
 transitivity (n * p - (d*(n * p / d)))%Z;[ring|].
 symmetry.
 apply -> Zeq_plus_swap.
 rewrite Zplus_comm.
 symmetry.
 apply Z_div_mod_eq.
 auto with *.
Qed.

Lemma approximateQ_big : forall (z:Z) a p, (z <= a) -> z <= approximateQ a p.
Proof.
 intros z [n d] p Ha.
 unfold approximateQ.
 unfold Qle in *.
 simpl in *.
 apply Zlt_succ_le.
 unfold Zsucc.
 apply Zmult_gt_0_lt_reg_r with d.
  auto with *.
 replace RHS with (d* (n*p/d) + (Zmod (n*p) d) - (Zmod (n*p) d) + d)%Z by ring.
 rewrite <- (Z_div_mod_eq (n*p) d); try auto with *.
 apply Zle_lt_trans with (n*1*p)%Z.
  replace LHS with (z*d*p)%Z by ring.
  apply Zmult_lt_0_le_compat_r; auto with *.
 apply Zlt_0_minus_lt.
 replace RHS with (d - (Zmod (n*p) d))%Z by ring.
 rewrite <- Zlt_plus_swap.
 ring_simplify.
 assert (X:(d >0)%Z) by auto with *.
 destruct (Z_mod_lt (n*p) _ X).
 assumption.
Qed.

(** Compress doubles the requried precision and uses the extra leway to
round the rational number. *)
Definition compress_raw (x:CR) (e:QposInf) : Q :=
match e with
| QposInfinity => approximate x e
| Qpos2QposInf e =>
 let (n,d) := e in
 match (Zsucc (Zdiv (2*d) n)) with
  Zpos p => approximateQ (approximate x (Qpos2QposInf (1#p))) p
 |_ => approximate x e
 end
end.

Lemma compress_raw_prop : forall x e, ball e x (Cunit (compress_raw x e)).
Proof.
 intros x [n d].
 simpl.
 case_eq (Zsucc (xO d / n));try (intros; apply: ball_approx_r).
 intros p Hp.
 apply ball_weak_le with (2#p)%Qpos.
  unfold Qle.
  simpl.
  rewrite Zpos_mult_morphism.
  rewrite <- Hp.
  unfold Zsucc.
  rewrite Zmult_plus_distr_r.
  apply Zle_0_minus_le.
  replace RHS with (n - (xO d - n * (xO d / n)))%Z by ring.
  apply Zle_minus_le_0.
  replace LHS with ((xO d) mod n)%Z.
   destruct (Z_mod_lt (xO d) n); auto with *.
  transitivity (xO d - (n*(xO d / n)))%Z;[ring|].
  symmetry; apply -> Zeq_plus_swap.
  rewrite Zplus_comm.
  symmetry.
  apply Z_div_mod_eq.
  auto with *.
 setoid_replace (2#p)%Qpos with ((1#p)+(1#p))%Qpos.
  eapply ball_triangle with (Cunit (approximate x (1#p)%Qpos)).
   apply: ball_approx_r.
  Transparent CR.
  change (ball (m:=Complete Q_as_MetricSpace) (1 # p) (Cunit (approximate x (1 # p)%Qpos))
    (Cunit (approximateQ (approximate x (1 # p)%Qpos) p))).
  rewrite -> ball_Cunit.
  apply approximateQ_correct.
 unfold QposEq.
 autorewrite with QposElim.
 repeat rewrite -> Qmake_Qdiv.
 unfold Qdiv.
 ring.
Qed.

Lemma compress_raw_prf : forall x, is_RegularFunction (compress_raw x).
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
 apply: regFunEq_e.
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
