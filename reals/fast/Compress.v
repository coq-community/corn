(*
Copyright © 2006 Russell O’Connor

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
transitivity (n * p - (d*(n * p / d)))%Z;[|ring].
rewrite <- Zeq_plus_swap.
rewrite Zplus_comm.
symmetry.
apply Z_div_mod_eq.
auto with *.
Qed.

Definition compress_fun (x:CR) (e:QposInf) : Q :=
match e with
| QposInfinity => approximate x e
| Qpos2QposInf e =>
 let (n,d) := e in 
 match (Zsucc (Zdiv (2*d) n)) with 
  Zpos p => approximateQ (approximate x (Qpos2QposInf (1#p))) p
 |_ => approximate x e 
 end
end.

Lemma compress_fun_prop : forall x e, ball e x (Cunit (compress_fun x e)).
Proof.
intros x [n d].
simpl.
case_eq (Zsucc (xO d / n));try (intros; rapply ball_approx_r).
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
 transitivity (xO d - (n*(xO d / n)))%Z;[|ring].
 rewrite <- Zeq_plus_swap.
 rewrite Zplus_comm.
 symmetry.
 apply Z_div_mod_eq.
 auto with *.
setoid_replace (2#p)%Qpos with ((1#p)+(1#p))%Qpos.
 eapply ball_triangle with (Cunit (approximate x (1#p)%Qpos)).
  rapply ball_approx_r.
 Transparent CR.
 change (ball (m:=Complete Q_as_MetricSpace) (1 # p) (Cunit (approximate x (1 # p)%Qpos))
  (Cunit (approximateQ (approximate x (1 # p)%Qpos) p))).
 rewrite ball_Cunit.
 apply approximateQ_correct.
unfold QposEq.
autorewrite with QposElim.
repeat rewrite Qmake_Qdiv.
unfold Qdiv.
ring.
Qed.

Lemma compress_fun_prf : forall x, is_RegularFunction (compress_fun x).
Proof.
intros x e1 e2.
rewrite <- ball_Cunit.
eapply ball_triangle;[|apply compress_fun_prop].
apply ball_sym.
apply compress_fun_prop.
Qed.

Definition compress (x:CR) : CR :=
Build_RegularFunction (compress_fun_prf x).

Lemma compress_correct : forall x, (compress x==x)%CR.
Proof.
intros x.
rapply regFunEq_e.
intros e.
unfold compress.
unfold approximate at 1.
rewrite <- ball_Cunit.
eapply ball_triangle;[|apply ball_approx_r].
apply ball_sym.
apply compress_fun_prop.
Qed.
