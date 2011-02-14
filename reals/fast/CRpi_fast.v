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

Require Export CRArith.
Require Import CRIR.
Require Import Q_in_CReals.
Require Import QMinMax.
Require Import CRarctan_small.
Require Import MoreArcTan.
Require Import CornTac.
Require Import abstract_algebra.

Set Implicit Arguments.

Open Local Scope Q_scope.
Open Local Scope uc_scope.

Opaque inj_Q CR.
(**
** Pi
(Please import CRpi instead)

This version is faster to compute than CRpi_slow; however it is slower to
compile.

Pi is defined as

176*arctan(1/57) + 28*arctan(1/239) - 48*arctan(1/682) + 96*arctan(1/12943).
*)
Section Pi.

Lemma small_per_57 : (0 <= (1#(57%positive)) <= 1)%Q.
Proof.
 split; discriminate.
Qed.

Lemma small_per_239 : (0 <= (1#(239%positive)) <= 1)%Q.
Proof.
 split; discriminate.
Qed.

Lemma small_per_682 : (0 <= (1#(682%positive)) <= 1)%Q.
Proof.
 split; discriminate.
Qed.

Lemma small_per_12943 : (0 <= (1#(12943%positive)) <= 1)%Q.
Proof.
 split; discriminate.
Qed.

Definition r_pi (r:Q) : CR :=
((scale (176%Z*r) (rational_arctan_small_pos small_per_57) +
  scale (28%Z*r) (rational_arctan_small_pos small_per_239)) +
 (scale (-(48%Z)*r) (rational_arctan_small_pos small_per_682) +
  scale (96%Z*r) (rational_arctan_small_pos small_per_12943)))%CR.

(** To prove that pi is is correct we repeatedly use the arctan sum law.
The problem is that the arctan sum law only works for input between -1
and 1.  We use reflect to show that our use of arctan sum law always
satifies this restriction. *)

Let f (a b:Q) : Q :=
 let (x,y) := a in
 let (z,w) := b in
 Qred ((x*w + y*z)%Z/(y*w-x*z)%Z).

Lemma f_char : forall a b, f a b == (a+b)/(1-a*b).
Proof.
 intros [x y] [w z].
 unfold f.
 rewrite -> Qred_correct.
 destruct (Z_eq_dec (y*z) (x*w)) as [H|H].
  unfold Qmult.
  simpl ((Qnum (x # y) * Qnum (w # z) # Qden (x # y) * Qden (w # z))).
  repeat rewrite <- H.
  replace (y * z - y * z)%Z with 0%Z by ring.
  setoid_replace (1-(y * z # y * z)) with 0.
   change ((x * z + y * w)%Z * 0 == ((x # y) + (w # z)) * 0).
   ring.
  rewrite -> (Qmake_Qdiv (y*z)).
  change (1 - (y * z)%positive / (y * z)%positive == 0).
  field; discriminate.
 unfold Zminus.
 repeat rewrite -> injz_plus.
 change (((x * z) + (y * w)) / (y * z - x * w) == ((x # y) + (w # z)) / (1 - (x #y)*(w # z))).
 repeat rewrite -> Qmake_Qdiv.
 field.
 repeat split; try discriminate.
 cut (~(y * z)%Z == (x * w)%Z).
  intros X Y.
  apply X.
  replace RHS with ((x * w)%Z + 0) by simpl; ring.
  rewrite <- Y.
  change ((y * z) == (x * w) + (y * z - x * w)).
  ring.
 intros X; apply H.
 unfold Qeq in X.
 simpl in X.
 rewrite Pmult_1_r in X.
 change  ((y * z)%Z = (x * w * 1)%Z) in X.
 rewrite X.
 ring.
Qed.

Lemma ArcTan_plus_ArcTan_Q : forall x y, -(1) <= x <= 1 -> -(1) <= y <= 1 -> ~1-x*y==0 ->
 (ArcTan (inj_Q _ x)[+]ArcTan (inj_Q _ y)[=]ArcTan (inj_Q _ (f x y))).
Proof.
 intros x y [Hx0 Hx1] [Hy0 Hy1] H.
 assert (X:forall z, -(1) <= z -> [--]One[<=]inj_Q IR z).
  intros z Hz.
  stepl ((inj_Q IR (-(1)))).
   apply inj_Q_leEq; assumption.
  eapply eq_transitive.
   apply (inj_Q_inv IR (1)).
  apply un_op_wd_unfolded.
  rstepr (nring 1:IR).
  apply (inj_Q_nring IR 1).
 assert (X0:forall z, z <= 1 -> inj_Q IR z[<=]One).
  intros z Hz.
  stepr ((inj_Q IR ((1)))).
   apply inj_Q_leEq; assumption.
  rstepr (nring 1:IR).
  apply (inj_Q_nring IR 1).
 assert (One[-](inj_Q IR x)[*](inj_Q IR y)[#]Zero).
  stepl (inj_Q IR (1[-]x[*]y)).
   (stepr (inj_Q IR Zero); [| now apply (inj_Q_nring IR 0)]).
   apply inj_Q_ap; assumption.
  eapply eq_transitive.
   apply inj_Q_minus.
  apply bin_op_wd_unfolded.
   rstepr (nring 1:IR); apply (inj_Q_nring IR 1).
  apply un_op_wd_unfolded.
  apply inj_Q_mult.
 apply eq_transitive with (ArcTan (inj_Q IR x[+]inj_Q IR y[/](One[-]inj_Q IR x[*]inj_Q IR y)[//]X1)).
  apply ArcTan_plus_ArcTan; first [apply X; assumption |apply X0; assumption].
 apply ArcTan_wd.
 stepl (inj_Q IR ((x[+]y)/(One[-]x*y))).
  apply inj_Q_wd.
  simpl.
  symmetry.
  apply f_char.
 assert (H0:(inj_Q IR (One[-]x * y))[#]Zero).
  (stepr (inj_Q IR 0); [| now apply (inj_Q_nring IR 0)]).
  apply inj_Q_ap; assumption.
 apply eq_transitive with (inj_Q IR (x[+]y)[/]inj_Q IR (One[-]x * y)[//]H0).
  apply (inj_Q_div).
 apply div_wd.
  apply inj_Q_plus.
 eapply eq_transitive.
  apply inj_Q_minus.
 apply bin_op_wd_unfolded.
  rstepr (nring 1:IR).
  apply (inj_Q_nring IR 1).
 apply un_op_wd_unfolded.
 apply inj_Q_mult.
Qed.

Definition ArcTan_multiple : forall x, -(1) <= x <= 1 -> forall n, {True} + {(nring n)[*]ArcTan (inj_Q _ x)[=]ArcTan (inj_Q _ (iter_nat n _ (f x) 0))}.
Proof.
 intros x Hx.
 induction n.
  right.
  abstract ( rstepl (Zero:IR); (stepl (ArcTan Zero); [| now apply ArcTan_zero]); apply ArcTan_wd;
    apply eq_symmetric; apply (inj_Q_nring IR 0)).
 simpl.
 destruct (IHn) as [H|H].
  left; constructor.
 set (y:=(iter_nat n Q (f x) 0)) in *.
 destruct (Qlt_le_dec_fast 1 y) as [_|Y0].
  left; constructor.
 destruct (Qlt_le_dec_fast y (-(1))) as [_|Y1].
  left; constructor.
 destruct (Qeq_dec (1-x*y) 0) as [_|Y2].
  left; constructor.
 right.
 abstract ( rstepl (ArcTan (inj_Q IR x)[+](nring n[*]ArcTan (inj_Q IR x))); csetoid_rewrite H;
   apply ArcTan_plus_ArcTan_Q; try assumption; split; assumption).
Defined.

Lemma reflect_right : forall A B (x:{A}+{B}), (match x with left _ => False | right _ => True end) -> B.
Proof.
 intros A B x.
 elim x.
  contradiction.
 trivial.
Qed.

Lemma Pi_Formula :
(((nring 44)[*]ArcTan (inj_Q IR (1 /  57%Z))[-]
  (nring 12)[*]ArcTan (inj_Q IR (1 / 682%Z))[+]
  (nring  7)[*]ArcTan (inj_Q IR (1 / 239%Z))[+]
  (nring 24)[*]ArcTan (inj_Q IR (1 / 12943%Z)))[=]
 Pi[/]FourNZ).
Proof.
 assert (H0:-(1) <= (1/(57%Z)) <= 1).
  split; discriminate.
 assert (H1:-(1) <= (1/(239%Z)) <= 1).
  split; discriminate.
 assert (H2:-(1) <= (1/(682%Z)) <= 1).
  split; discriminate.
 assert (H3:-(1) <= (1/(12943%Z)) <= 1).
  split; discriminate.
 set (y0:=(iter_nat 44 _ (f (1/57%Z)) 0)).
 set (y1:=(iter_nat 7 _ (f (1/239%Z)) 0)).
 set (y2:=(iter_nat 12 _ (f (1/682%Z)) 0)).
 set (y3:=(iter_nat 24 _ (f (1/12943%Z)) 0)).
 rstepl (nring 44[*]ArcTan (inj_Q IR (1 / 57%positive))[+]
   [--](nring 12[*]ArcTan (inj_Q IR (1 / 682%positive)))[+]
     (nring 7[*]ArcTan (inj_Q IR (1 / 239%positive))[+]
       nring 24[*]ArcTan (inj_Q IR (1 / 12943%positive)))).
 csetoid_replace ((nring 44)[*]ArcTan (inj_Q IR (1 / 57%positive)))
   (ArcTan (inj_Q IR y0)); [|apply: (reflect_right (ArcTan_multiple H0 44)); now vm_compute].
 csetoid_replace ((nring 7)[*]ArcTan (inj_Q IR (1 / 239%positive))) (ArcTan (inj_Q IR y1));
   [|apply: (reflect_right (ArcTan_multiple H1 7)); now vm_compute].
 csetoid_replace ((nring 12)[*]ArcTan (inj_Q IR (1 / 682%positive))) (ArcTan (inj_Q IR y2));
   [|apply: (reflect_right (ArcTan_multiple H2 12)); now vm_compute].
 csetoid_replace ((nring 24)[*]ArcTan (inj_Q IR (1 / 12943%positive))) (ArcTan (inj_Q IR y3));
   [|apply: (reflect_right (ArcTan_multiple H3 24)); now vm_compute].
 vm_compute in y0.
 vm_compute in y1.
 vm_compute in y2.
 vm_compute in y3.
 csetoid_replace ([--](ArcTan (inj_Q IR y2))) (ArcTan (inj_Q IR (-y2)));
   [|csetoid_rewrite_rev (ArcTan_inv (inj_Q IR y2));
     apply ArcTan_wd; apply eq_symmetric; apply (inj_Q_inv IR y2)].
 csetoid_replace (ArcTan (inj_Q IR y0)[+]ArcTan (inj_Q IR (-y2))) (ArcTan (inj_Q IR (f y0 (-y2))));
   [|apply ArcTan_plus_ArcTan_Q; try split; now vm_compute].
 csetoid_replace (ArcTan (inj_Q IR y1)[+]ArcTan (inj_Q IR y3)) (ArcTan (inj_Q IR (f y1 y3)));
   [|apply ArcTan_plus_ArcTan_Q; try split; now vm_compute].
 set (z0 := (f y0 (-y2))).
 set (z1 := (f y1 y3)).
 vm_compute in z0.
 vm_compute in z1.
 csetoid_replace (ArcTan (inj_Q IR z0)[+]ArcTan (inj_Q IR z1)) (ArcTan (inj_Q IR (f z0 z1)));
   [|apply ArcTan_plus_ArcTan_Q; try split; now vm_compute].
 set (z3:= (f z0 z1)).
 vm_compute in z3.
 eapply eq_transitive;[|apply ArcTan_one].
 apply ArcTan_wd.
 rstepr (nring 1:IR).
 apply (inj_Q_nring IR 1).
Qed.

Lemma r_pi_correct : forall r, (r_pi r == IRasCR ((inj_Q IR r)[*]Pi))%CR.
Proof.
 intros r.
 unfold r_pi.
 repeat rewrite <- (CRmult_scale).
 setoid_replace ((176*r)) with ((4*r*44)) by (simpl; ring).
 setoid_replace (28*r) with (4*r*7) by (simpl; ring).
 setoid_replace (-(48)*r) with (4*r*-(12)) by (simpl; ring).
 setoid_replace (96*r) with (4*r*24) by (simpl; ring).
 repeat rewrite <- CRmult_Qmult.
 transitivity ('4 * 'r *(' 44 * rational_arctan_small_pos small_per_57 +
   ' 7 * rational_arctan_small_pos small_per_239 +
     (' (-(12)) * rational_arctan_small_pos small_per_682 +
       ' 24 * rational_arctan_small_pos small_per_12943)))%CR.
  ring.
 repeat (rewrite -> (rational_arctan_small_pos_correct); [|constructor]).
 repeat rewrite <- IR_inj_Q_as_CR.
 repeat (rewrite <- IR_mult_as_CR || rewrite <- IR_plus_as_CR).
 apply IRasCR_wd.
 rstepr (Four[*]inj_Q IR r[*]Pi[/]FourNZ).
 apply mult_wd.
  apply mult_wdl.
  apply (inj_Q_nring IR 4).
 eapply eq_transitive;[|apply Pi_Formula].
 rstepr (nring 44[*]ArcTan (inj_Q IR (1 / 57%positive))[+]
   nring 7[*]ArcTan (inj_Q IR (1 / 239%positive))[+]
     (([--](nring 12))[*]ArcTan (inj_Q IR (1 / 682%positive))[+]
       nring 24[*]ArcTan (inj_Q IR (1 / 12943%positive)))).
 repeat apply bin_op_wd_unfolded; try apply eq_reflexive.
    apply (inj_Q_nring IR 44).
   apply (inj_Q_nring IR 7).
  eapply eq_transitive.
   apply (inj_Q_inv IR (nring 12)).
  csetoid_rewrite (inj_Q_nring IR 12).
  apply eq_reflexive.
 apply (inj_Q_nring IR 24).
Qed.

Global Instance: Proper ((=) ==> (=)) r_pi.
Proof.
  intros ? ? E. unfold r_pi.
  now rewrite E.
Qed.

Definition CRpi : CR := (r_pi 1).

Lemma CRpi_correct : (IRasCR Pi == CRpi)%CR.
Proof.
 unfold CRpi.
 rewrite -> r_pi_correct.
 apply IRasCR_wd.
 rstepl ((nring 1)[*]Pi).
 apply mult_wdl.
 apply eq_symmetric.
 apply (inj_Q_nring IR 1).
Qed.

End Pi.
(* begin hide *)
Hint Rewrite CRpi_correct : IRtoCR.
(* end hide *)
