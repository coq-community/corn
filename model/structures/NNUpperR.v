(* This module is designed to *not* be Import'ed, only Require'd. *)

Require Import
  Qabs Qordfield Qpossec Qminmax Ring Program.

Require QnonNeg.
Import QnonNeg.notations.

Local Hint Resolve Qle_refl.

Open Local Scope Q_scope.

(* Some generic utilities: *)

Definition pred_eq {X} (p q: X -> Prop): Prop := forall x, p x <-> q x.

Instance: forall X, Equivalence (@pred_eq X) := {}.

(* Some facts about Q: *)

Lemma Qplus_wiggle (x y z : Q):
  0 <= x -> 0 <= y -> x + y < z -> exists e: Qpos, x + e + y < z.
Proof with auto.
 intros ?? E.
 destruct (Qpos_lt_plus E) as [e F].
 exists ((1#2) * e)%Qpos.
 rewrite F.
 simpl. ring_simplify.
 apply Qplus_lt_l.
 do 2 rewrite (Qplus_comm x).
 apply Qplus_lt_l.
 rewrite <- (Qmult_1_l e) at 2.
 apply Qmult_lt_compat_r...
 reflexivity.
Qed.

Lemma Qmult_wiggle (x y z : Q):
  0 <= x -> 0 <= y -> x * y < z -> exists e : Qpos, (x + e) * y < z.
Proof with auto with *.
 intros xnn ynn xyz.
 destruct (Qdec_sign y) as [[A|B]|C].
   exfalso. apply Qle_not_lt with 0 y...
  destruct (Qpos_lt_plus xyz) as [e E].
  exists (e / ((2#1) * exist (Qlt 0) y B))%Qpos.
  rewrite E.
  rewrite Qmult_plus_distr_l.
  do 2 rewrite (Qplus_comm (x * y)).
  apply Qplus_lt_l.
  simpl.
  setoid_replace (e * / ((2 # 1) * y) * y) with (/ (2 # 1) * e) by (simpl; field)...
  rewrite <- (Qmult_1_l e) at 2.
  apply Qmult_lt_compat_r...
 exists (1#1)%Qpos. revert xyz.
 rewrite C, Qmult_0_r, Qmult_0_r...
Qed.

Lemma Qmid (x y: Q): x < y ->
 let mid := (1#2)%Qpos*(x+y) in
  x < mid /\ mid < y.
Proof with auto; try reflexivity.
 intros. subst mid.
 split.
  setoid_replace x with (x * (1#2) + x * (1#2)) at 1 by (simpl; ring).
  setoid_replace ((1 # 2) * (x + y)) with (y * (1 # 2) + x * (1 # 2)) by (simpl; ring).
  apply Qplus_lt_l.
  apply Qmult_lt_compat_r...
 setoid_replace y with (y * (1#2) + y * (1#2)) at 2 by (simpl; ring).
 setoid_replace ((1 # 2) * (x + y)) with (x * (1 # 2) + y * (1 # 2)) by (simpl; ring).
 apply Qplus_lt_l.
 apply Qmult_lt_compat_r...
Qed.

Lemma QnonNeg_mid (x y: QnonNeg): ` x < ` y ->
 let mid := ((1#2) * (x + y))%Qnn in
  ` x < ` mid /\ ` mid < ` y.
Proof.
 intros. subst mid. simpl.
 apply Qmid. assumption.
Qed.

Lemma Qmult_le_compat: forall x y x' y' : Q, 0 <= x <= x' -> 0 <= y <= y' -> x * y <= x' * y'.
Proof.
 intros.
 apply Qle_trans with (x * y').
  do 2 rewrite (Qmult_comm x).
  apply Qmult_le_compat_r; intuition.
 apply Qmult_le_compat_r. intuition.
 apply Qle_trans with y; intuition.
Qed.

Local Hint Resolve Qlt_le_weak.

(* Next up, the actual data type for non-negative upper cuts: *)

Record T := make
  { is_bound: QnonNeg -> Prop
  ; bound: QnonNeg
  ; closed_le: forall q q', `q <= `q' -> is_bound q -> is_bound q'
  ; bound_is_bound: is_bound bound }.

(* Note that we don't enforce closedness or openness of the cut in this definition.
Instead, we write le and eq so that they only depend on non-lowest upper bounds. *)

(* The bound and bound_is_bound fields are just there to rule out an empty cut. A
weaker way to accomplish this is by replacing the two with a field of type

   ~ forall q, ~ is_bound q

Maybe this is better. A preliminary experiment did reveal a complication in the proof
of mult_0_l, because it uses the bound. Possible solutions there include (1) requiring
is_bound stability so that the negated forall above can be classically flipped to
an exists, or (2) using a separate inductively defined cut predicate for multiplication
which has an additional constructor for the multiplication-by-0 case. *)

Hint Immediate bound_is_bound.

Instance is_bound_Proper: forall (x: T), Proper (QnonNeg.eq ==> iff) (is_bound x).
Proof with auto.
 unfold QnonNeg.eq. intros x y z E.
 split; intro.
  apply closed_le with y... rewrite E...
 apply closed_le with z... rewrite E...
Qed.

Definition le (x y: T): Prop := forall q, is_bound y q -> forall r, `q < `r -> is_bound x r.

Local Infix "<=" := le.

Lemma le_refl (x: T): x <= x.
Proof. repeat intro. apply closed_le with q; auto. Qed.

Lemma le_trans (x y z: T): x <= y -> y <= z -> x <= z.
Proof with auto.
 intros xley ylez q zq r qr.
 destruct (QnonNeg_mid q r qr).
 apply (xley ((1#2)*(q+r))%Qnn)...
 apply (ylez q)...
Qed.

Definition eq (x y: T): Prop := x <= y /\ y <= x.

Local Infix "==" := eq.

Global Instance: Proper (eq ==> eq ==> iff) le.
Proof with intuition.
 unfold eq. intros x y ? a b ?.
 split; intro.
  apply le_trans with x...
  apply le_trans with a...
 apply le_trans with y...
 apply le_trans with b...
Qed.

Global Instance: Equivalence eq.
Proof with intuition.
 unfold eq.
 split; repeat intro...
    apply le_refl.
   apply le_refl.
  apply le_trans with y...
 apply le_trans with y...
Qed.

Global Program Coercion inject_Qnn (q: QnonNeg): T := make (Qle q) q _ _.

Next Obligation. apply Qle_trans with (q0); assumption. Qed.

Global Instance: Proper (QnonNeg.eq ==> eq) inject_Qnn.
Proof with auto.
 unfold eq, le.
 intros ?? H.
 split; simpl; intros.
  rewrite H. apply Qle_trans with (`q)...
 rewrite <- H. apply Qle_trans with (`q)...
Qed.

Definition bound_doesnt_matter (q: QnonNeg) b H H' U U':
  make (Qle q) b H U == make (Qlt q) b H' U'.
Proof with auto.
 unfold eq, le in *. simpl.
 split; intros e ???.
  apply Qle_trans with (`e)...
 apply Qle_lt_trans with (`e)...
Qed.

Section binop. (* used for addition and multiplication *)

  Variables
    (o: Q -> Q -> Q) (u: Q) (u_ok: (0 <= u)%Q)
    (o_ok: (forall x y, 0 <= x -> 0 <= y -> 0 <= o x y)%Q)
    (o_comm: (forall x y, o x y == o y x)%Q)
    (o_assoc: (forall x y z, o x (o y z) == o (o x y) z)%Q)
    (o_le_compat: (forall x y x' y', 0 <= x <= x' -> 0 <= y <= y' -> o x y <= o x' y')%Q)
    (o_u_left: (forall x, o u x == x)%Q)
    (o_sneaky: (forall (x y z: Q), 0 <= x -> 0 <= y -> o x y < z -> exists e: Qpos, o (x + e) y < z)%Q).
      (* todo: use monoid or something *)

  Definition u_nn: QnonNeg := exist _ _ u_ok.

  Definition o_nn := QnonNeg.binop o o_ok.

  Inductive BinopBound (x y: QnonNeg -> Prop): (QnonNeg -> Prop) :=
    is_binop_bound (q q': QnonNeg): x q -> y q' ->
      forall (r: QnonNeg), (o (` q) (` q') <= ` r)%Q -> BinopBound x y r.
        (* using <= instead of == makes closed_le automatic. using ==/<= at all makes wd automatic. *)

  Lemma BinopBound_le x y a b: (`a <= `b)%Q -> BinopBound x y a -> BinopBound x y b.
  Proof with auto.
   intros E B. revert B E.
   intros [v w xv yw r F] E.
   apply (is_binop_bound x y v w)...
   apply Qle_trans with (`r)...
  Qed.

  Instance BinopBound_Proper: Proper (pred_eq ==> pred_eq ==> QnonNeg.eq ==> iff) BinopBound.
  Proof with auto.
   unfold Proper, respectful.
   cut (forall x y x0 y0 x1 y1, pred_eq x y -> pred_eq x0 y0 ->
     (`x1 == `y1)%Q -> BinopBound x x0 x1 -> BinopBound y y0 y1).
    split; apply H; auto; symmetry...
   intros ?????? U V A B. revert B A.
   intros [v w xv yw r F] E.
   apply (is_binop_bound _ _ v w).
     apply U...
    apply V...
   apply Qle_trans with (`r)...
   rewrite E...
  Qed.

  Lemma BinopBound_sym x y: pred_eq (BinopBound x y) (BinopBound y x).
  Proof with auto.
   split; intros [a b xa yb r E].
    apply (is_binop_bound y x b a yb xa). rewrite o_comm...
   apply (is_binop_bound x y b a yb xa). rewrite o_comm...
  Qed.

  Lemma BinopBound_assoc (n m p: T) (q: QnonNeg):
    BinopBound (is_bound n) (BinopBound (is_bound m) (is_bound p)) q ->
    BinopBound (BinopBound (is_bound n) (is_bound m)) (is_bound p) q.
  Proof with auto.
   intros [a b na [v w z x y E] c F].
   apply BinopBound_le with (o_nn (o_nn a v) w).
    simpl.
    apply Qle_trans with (o (`a) (`y))...
    rewrite <- o_assoc.
    apply o_le_compat; split...
   apply is_binop_bound with (o_nn a v) w...
   apply is_binop_bound with a v...
  Qed.

  Program Definition binop (x y: T): T :=
    make (BinopBound (is_bound x) (is_bound y)) (o_nn (bound x) (bound y)) _ _.

  Next Obligation. (* closed_le *)
   apply BinopBound_le with (exist _ q H2); auto.
  Qed.

  Next Obligation. (* bound_is_bound *)
   apply (is_binop_bound (is_bound x) (is_bound y) (bound x) (bound y)); auto.
  Qed.

  Lemma binop_comm (x y: T): binop x y == binop y x.
  Proof with auto.
   cut (forall a b, binop a b <= binop b a).
    intro H. split; apply H.
   unfold eq, le.  simpl. intros.
   inversion H. subst. clear H.
   apply BinopBound_sym.
   apply is_binop_bound with q0 q'...
   apply Qle_trans with (`q)...
  Qed.

  Lemma binop_le_compat_l (x y z: T): x <= y -> binop x z <= binop y z.
  Proof with auto.
   unfold le. simpl. intros H q [v w yv zw r E s rs].
   specialize (H _ yv).
   assert (o (`v) (`w) < `s) as os. apply Qle_lt_trans with (`r)...
   destruct (o_sneaky _ _ _ (proj2_sig _) (proj2_sig _) os).
   apply (is_binop_bound (is_bound x) (is_bound z)) with (v + x0)%Qnn w...
   apply H. simpl.
   rewrite Qplus_comm. rewrite <- Qplus_0_l at 1. apply Qplus_lt_l...
  Qed.

  Lemma binop_le_compat (x y: T) (v w: T): x <= y -> v <= w -> binop x v <= binop y w.
  Proof.
   intros. apply le_trans with (binop x w);
    [do 2 rewrite (binop_comm x) |]; apply binop_le_compat_l; auto.
  Qed.

  Global Instance binop_Proper: Proper (eq ==> eq ==> eq) binop.
  Proof. unfold eq. repeat intro. split; apply binop_le_compat; intuition. Qed.

  Lemma binop_assoc (n m p: T): binop n (binop m p) == binop (binop n m) p.
  Proof with auto.
   unfold eq, le. simpl.
   split; intros.
    apply BinopBound_sym.
    apply BinopBound_assoc.
    apply BinopBound_sym.
    apply BinopBound_assoc.
    apply BinopBound_sym...
    apply BinopBound_le with q...
   apply BinopBound_assoc.
   apply BinopBound_le with q...
  Qed. 

  Lemma binop_unit_left (x: T): binop u_nn x == x.
  Proof with auto.
   unfold eq, le. simpl.
   split.
    intros.
    apply (is_binop_bound) with u_nn q...
    simpl. rewrite o_u_left...
   intros q [q0 q' H1 H2 v H3] r vr.
   apply closed_le with q'...
   apply Qle_trans with (`v)...
   rewrite <- (o_u_left (`q')).
   apply Qle_trans with (o (`q0) (`q'))...
  Qed.

End binop.

Definition plus := binop Qplus QnonNeg.Qplus_nonneg.
Definition mult := binop Qmult Qmult_le_0_compat.

Local Infix "+" := plus.
Local Infix "*" := mult.

Instance: Proper (eq ==> eq ==> eq) plus.
Proof binop_Proper Qplus QnonNeg.Qplus_nonneg Qplus_comm Qplus_wiggle.

Instance: Proper (eq ==> eq ==> eq) mult.
Proof binop_Proper Qmult Qmult_le_0_compat Qmult_comm Qmult_wiggle.

Lemma plus_0_l: forall x, 0%Qnn + x == x.
Proof.
 refine (binop_unit_left Qplus 0 (Qle_refl _) QnonNeg.Qplus_nonneg _ Qplus_0_l).
 intros. apply Qplus_le_compat; intuition. 
Qed.

Lemma plus_comm: forall x y, x + y == y + x.
Proof binop_comm Qplus QnonNeg.Qplus_nonneg Qplus_comm.

Lemma plus_assoc: forall n m p, n + (m + p) == (n + m) + p.
Proof.
 apply (binop_assoc Qplus QnonNeg.Qplus_nonneg Qplus_comm Qplus_assoc).
 intros. apply Qplus_le_compat; intuition. 
Qed.

Lemma plus_le_compat: forall x y a b, x <= y -> a <= b -> x + a <= y + b.
Proof binop_le_compat Qplus QnonNeg.Qplus_nonneg Qplus_comm Qplus_wiggle.

Lemma Qle_0_1: (0 <= 1)%Q.
Proof. discriminate. Qed.

Lemma mult_1_l: forall x, 1%Qnn * x == x.
Proof binop_unit_left Qmult 1 Qle_0_1 Qmult_le_0_compat Qmult_le_compat Qmult_1_l.

Lemma mult_comm: forall x y, x * y == y * x.
Proof binop_comm Qmult Qmult_le_0_compat Qmult_comm.

Lemma mult_assoc: forall n m p, n * (m * p) == (n * m) * p.
Proof binop_assoc Qmult Qmult_le_0_compat Qmult_comm Qmult_assoc Qmult_le_compat.

Lemma mult_plus_distr n m p: (n + m) * p == n * p + m * p.
Proof with auto; simpl.
 unfold eq. split.
  intros _ [_ _ [e d ?? b ?][g f ?? c ?]a ?] r H0...
  apply BinopBound_le with (e * d + g * f)%Qnn...
   apply Qle_trans with (`b + `c)%Q...
    apply Qplus_le_compat...
   apply Qle_trans with (`a)...
  apply is_binop_bound with (e + g)%Qnn (QnonNeg.min d f)...
    apply is_binop_bound with e g... 
   apply QnonNeg.min_case...
   apply (is_bound_Proper p)...
  rewrite Qmult_plus_distr_l.
  apply Qplus_le_compat...
   do 2 rewrite (Qmult_comm (`e)).
   apply Qmult_le_compat_r...
   apply Q.le_min_l.
  do 2 rewrite (Qmult_comm (`g)).
  apply Qmult_le_compat_r...
  apply Q.le_min_r.
 intros q [a b [c d ?? e ?] ? r1 ?] r E...
 apply BinopBound_le with ((c + d) * b)%Qnn...
  apply Qle_trans with (`e * `b)%Q...
   apply Qmult_le_compat_r...
  apply Qle_trans with (`r1)...
 apply is_binop_bound with (c * b)%Qnn (d * b)%Qnn.
   apply is_binop_bound with c b...
  apply is_binop_bound with d b...
 simpl. ring_simplify...
Qed.

Lemma le_closed (e x: T): (forall d: Qpos, x <= e + d) -> x <= e.
Proof with auto.
 unfold le. simpl. intros H q H0 r qr.
 destruct (Qpos_lt_plus qr) as [d E].
 apply (H ((1#2)*d)%Qpos (q + (2#3)*d)%Qnn).
  apply (is_binop_bound Qplus) with q ((1#2)*d)%Qnn...
  simpl.
  apply Qplus_le_compat...
  apply Qmult_le_compat_r...
  discriminate.
 simpl.
 rewrite E.
 do 2 rewrite (Qplus_comm (`q)).
 apply Qplus_lt_l.
 simpl.
 rewrite <- (Qmult_1_l d).
 apply Qmult_lt_compat_r...
 reflexivity.
Qed.

Lemma le_0 x: 0%Qnn <= x.
Proof. unfold le. simpl. auto. Qed.

Hint Immediate le_0.

Lemma le_0_eq x: x <= 0%Qnn -> x == 0%Qnn.
Proof. split. assumption. apply le_0. Qed.

Lemma mult_0_l (x: T): 0%Qnn * x == 0%Qnn.
Proof with auto.
 split... unfold le. simpl. intros.
 apply (is_binop_bound) with 0%Qnn (bound x)...
 simpl. rewrite Qmult_0_l...
Qed.

Lemma plus_homo (x y: QnonNeg): (x + y)%Qnn == x + y.
Proof with auto.
 unfold eq, le. simpl.
 split; intros.
  inversion H. subst. clear H.
  apply Qle_trans with (`q)...
  apply Qle_trans with (`q0 + `q')%Q...
  apply Qplus_le_compat...
 apply (is_binop_bound Qplus) with x y...
 apply Qle_trans with (`q)...
Qed.

Lemma semi_ring: semi_ring_theory (R:=T) 0%Qnn 1%Qnn plus mult eq.
Proof.
 constructor.
        apply plus_0_l.
       apply plus_comm.
      apply plus_assoc.
     apply mult_1_l.
    apply mult_0_l.
   apply mult_comm.
  apply mult_assoc.
 apply mult_plus_distr.
Qed.

Add Ring cut_ring: semi_ring.

Module notations.

  Delimit Scope NNUpperR_scope with Rnnu. 

  Global Infix "<=" := le: NNUpperR_scope.
  Global Infix "==" := eq: NNUpperR_scope.
  Global Infix "+" := plus: NNUpperR_scope.
  Global Infix "*" := mult: NNUpperR_scope.

  Global Notation NNUpperR := T.

End notations.

(* To show concretely that we've actually gotten beyond mere rationals, here's the square of two: *)

Program Definition sqrt2: T :=
  make (fun x => (2#1) <= x*x)%Q (2#1)%Qnn _ _.

Next Obligation. Proof with auto.
 simpl in *.
 apply Qle_trans with (q * q)%Q...
 apply Qmult_le_compat...
Qed.

(* For its correctness, I assume (because I'm lazy and couldn't find this in the stdlib) that square roots
 can be over-approximated to arbitrary precision: *)

Lemma sqrt2_correct
  (Qsqrt_overapprox: forall (x: QnonNeg) (e: Qpos), { r: QnonNeg | ` x <= ` r * ` r /\ ` r * ` r < ` x + e }%Q):
    sqrt2 * sqrt2 == (2#1)%Qnn.
Proof with auto.
 unfold eq, le. simpl.
 split; intros.
  destruct (Qpos_lt_plus H0).
  destruct (Qsqrt_overapprox (2#1)%Qnn x).
  destruct a.
  apply (is_binop_bound Qmult) with x0 x0...
  rewrite q0.
  apply Qle_trans with ((2 # 1)%Q + x)%Q...
  apply Qplus_le_compat...
 inversion_clear H.
 destruct (Qlt_le_dec (`q0) (`q')).
  apply Qle_trans with (`q0*`q0)%Q...
  apply Qle_trans with (`q0*`q')%Q...
   apply Qmult_le_compat...
  apply Qle_trans with (`q)...
 apply Qle_trans with (`q'*`q')%Q...
 apply Qle_trans with (`q0*`q')%Q...
  apply Qmult_le_compat...
 apply Qle_trans with (`q)...
Qed.
