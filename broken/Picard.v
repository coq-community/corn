Require Import
 Unicode.Utf8 Program
 CRArith CRabs
 Qauto Qround Qmetric
 (*stdlib_omissions.P
 stdlib_omissions.Z
 stdlib_omissions.Q
 stdlib_omissions.N*).

Require Qinf QnonNeg QnnInf CRball.
Import
  QnonNeg Qinf.notations QnonNeg.notations QnnInf.notations CRball.notations
  Qabs propholds.

Require Import metric FromMetric2 AbstractIntegration SimpleIntegration.
Require Import canonical_names decision setoid_tactics.

Close Scope uc_scope. (* There is a leak in some module *)
Open Scope signature_scope. (* To interpret "==>" *)

(* The following instances are needed to show that Lipschitz functions are
uniformly continuous: metric.lip_uc *)
Global Instance Qmsd : MetricSpaceDistance Q := λ x y, abs (x - y).

Global Instance Qmsc : MetricSpaceClass Q.
Proof. intros x1 x2; apply gball_Qabs; reflexivity. Qed.

(* Should be generalized from Q *)
Lemma mspc_ball_abs (r x y : Q) : mspc_ball r x y ↔ abs (x - y) ≤ r.
Proof. apply gball_Qabs. Qed.

Lemma mspc_ball_abs_flip (r x y : Q) : mspc_ball r x y ↔ abs (y - x) ≤ r.
Proof.
rewrite <- abs.abs_negate, <- rings.negate_swap_r. apply gball_Qabs.
Qed.

Lemma nested_balls {x1 x2 y1 y2 e : Q} :
  mspc_ball e x1 x2 -> x1 ≤ y1 -> y1 ≤ y2 -> y2 ≤ x2 -> mspc_ball e y1 y2.
Proof.
intros B A1 A2 A3. apply mspc_ball_abs_flip in B. apply mspc_ball_abs_flip.
assert (x1 ≤ x2) by (transitivity y1; [| transitivity y2]; trivial).
rewrite abs.abs_nonneg by now apply rings.flip_nonneg_minus.
rewrite abs.abs_nonneg in B by now apply rings.flip_nonneg_minus.
apply rings.flip_le_minus_l. apply rings.flip_le_minus_l in B.
transitivity x2; [easy |]. transitivity (e + x1); [easy |].
apply (orders.order_preserving (e +)); easy.
Qed. (* Too long? *)

SearchAbout abs Q.

Section Extend.

Context `{ExtMetricSpaceClass Y} (a : Q) (r : QnonNeg).

(* Sould [r] be [Q] or [QnonNeg]? If [r : Q], then [extend] below is not
necessarily continuous. This may be OK because we could add the premise [0
≤ r] to the lemma that says that [extend] is Lipschitz. However, the
definition below is not well-typed because if [r < 0], then [ball r a (a -
r)] is false, so we can't apply [f] to [a - r]. So we assume [r : QnonNeg]. *)

Lemma mspc_ball_edge_l : mspc_ball r a (a - `r).
Proof.
destruct r as [e ?]; simpl.
apply gball_Qabs. mc_setoid_replace (a - (a - e)) with e by ring.
change (abs e ≤ e). rewrite abs.abs_nonneg; [reflexivity | trivial].
Qed.

Lemma mspc_ball_edge_r : mspc_ball r a (a + `r).
Proof.
destruct r as [e ?]; simpl.
apply Qmetric.gball_Qabs. mc_setoid_replace (a - (a + e)) with (-e) by ring.
change (abs (-e) ≤ e). rewrite abs.abs_negate, abs.abs_nonneg; [reflexivity | trivial].
Qed.

Context (f : sig (mspc_ball r a) -> Y).

(* Since the following is a Program Definition, we could write [f (a - r)]
and prove the obligation [mspc_ball r a (a - r)]. However, this obligation
would depend on x and [H1 : x ≤ a - r] even though they are not used in the
proof. So, if [x1 ≤ a - r] and [x2 ≤ a - r], then [extend x1] would reduce
to [f ((a - r) ↾ extend_obligation_1 x1 H1)] and [extend x2] would reduce
to [f ((a - r) ↾ extend_obligation_1 x2 H2)]. To apply mspc_refl, we would
need to prove that these applications of f are equal, i.e., f is a morphism
that does not depend on the second component of the pair. So instead we
prove mspc_ball_edge_l and mspc_ball_edge_r, which don't depend on x. *)

Program Definition extend : Q -> Y :=
  λ x, if (decide (x ≤ a - r))
       then f ((a - r) ↾ mspc_ball_edge_l)
       else if (decide (a + r ≤ x))
            then f ((a + r) ↾ mspc_ball_edge_r)
            else f (x ↾ _).
Next Obligation.
apply Qmetric.gball_Qabs, Q.Qabs_diff_Qle.
apply orders.le_flip in H1; apply orders.le_flip in H2.
split; trivial.
Qed.

Global Instance extend_lip `{!IsLipschitz f L} : IsLipschitz extend L.
Proof with (assumption || (apply orders.le_flip; assumption) || reflexivity).
constructor; [apply (lip_nonneg f L) |].
intros x1 x2 e A.
assert (0 ≤ e) by now apply (radius_nonneg x1 x2).
assert (0 ≤ L) by apply (lip_nonneg f L).
assert (a - to_Q r ≤ a + to_Q r) by
  (destruct r; simpl; transitivity a;
    [apply rings.nonneg_minus_compat | apply semirings.plus_le_compat_r]; (easy || reflexivity)).
unfold extend.
destruct (decide (x1 ≤ a - to_Q r)); destruct (decide (x2 ≤ a - to_Q r)).
* apply mspc_refl; solve_propholds.
* destruct (decide (a + to_Q r ≤ x2));  apply (lip_prf f L).
  + apply (nested_balls A)...
  + apply (nested_balls A)...
* destruct (decide (a + to_Q r ≤ x1)); apply (lip_prf f L).
  + apply mspc_symm; apply mspc_symm in A. apply (nested_balls A)...
  + apply mspc_symm; apply mspc_symm in A. apply (nested_balls A)...
* destruct (decide (a + to_Q r ≤ x1)); destruct (decide (a + to_Q r ≤ x2));
  apply (lip_prf f L).
  + apply mspc_refl; solve_propholds.
  + apply mspc_symm; apply mspc_symm in A. apply (nested_balls A)...
  + apply (nested_balls A)...
  + apply A.
Qed.

Lemma extend_inside (x : Q) (A : mspc_ball r a x) : extend x = f (x ↾ A).
Admitted.

End Extend.

Global Instance : Proper (equiv ==> equiv) (abs (A := CR)).
Proof. change abs with (@ucFun CR CR CRabs); apply _. Qed.

Section Picard.

Context (x0 : Q) (y0 : CR) (rx ry : QnonNeg).

Notation sx := (sig (mspc_ball rx x0)).
Notation sy := (sig (mspc_ball ry y0)).

Context (v : sx * sy -> CR) `{!IsLipschitz v Lv}.

(*Context (f : sx -> sy) `{!IsLipschitz f Lf}.

Check _ : IsLocallyUniformlyContinuous (extend x0 rx (v ∘ (together Datatypes.id f) ∘ diag)) _.*)

Definition picard' (f : sx -> sy) `{!IsLipschitz f Lf} : Q -> CR :=
  λ x, y0 + int (extend x0 rx (v ∘ (together Datatypes.id f) ∘ diag)) x0 x.

(*
Variable f : Lipschitz sx sy.
(*Check _ : IsLipschitz f _.*)
Check _ : IsLocallyLipschitz (extend x0 rx (v ∘ (together Datatypes.id f) ∘ diag)) _.
Check _ : Integral (extend x0 rx (v ∘ (together Datatypes.id f) ∘ diag)).
Check _ : Integrable (extend x0 rx (v ∘ (together Datatypes.id f) ∘ diag)).
Check _ : IsLocallyLipschitz (λ x : Q, int (extend x0 rx (v ∘ (together Datatypes.id f) ∘ diag)) x0 x) _.
Check _ : IsLocallyLipschitz (picard' f) _. Goal True.
assert (0 ≤ to_Q rx). apply (proj2_sig rx).
Check _ : PropHolds (0 ≤ to_Q rx).
Check _ : IsLipschitz (restrict (picard' f) x0 rx) _.
*)

Definition picard'' (f : Lipschitz sx sy) : Lipschitz sx CR.
assert (0 ≤ to_Q rx) by apply (proj2_sig rx). (* Add this to typeclass_instances? *)
refine (Build_Lipschitz (restrict (picard' f) x0 rx) _ _).
Defined.

Variable M : Q.

Hypothesis v_bounded : forall z : sx * sy, abs (v z) ≤ 'M.

Hypothesis rx_ry : `rx * M ≤ ry.

Instance M_nonneg : PropHolds (0 ≤ M).
Proof.
assert (Ax : mspc_ball rx x0 x0) by apply mspc_refl, (proj2_sig rx).
assert (Ay : mspc_ball ry y0 y0) by apply mspc_refl, (proj2_sig ry).
apply CRle_Qle. transitivity (abs (v (x0 ↾ Ax , y0 ↾ Ay))); [apply CRabs_nonneg | apply v_bounded].
Qed.

Lemma picard_sy (f : Lipschitz sx sy) (x : sx) : mspc_ball ry y0 (restrict (picard' f) x0 rx x).
Proof.
destruct x as [x x_sx]. change (restrict (picard' f) x0 rx (x ↾ x_sx)) with (picard' f x).
unfold picard'. apply CRball.gball_CRabs.
match goal with
| |- context [int ?g ?x1 ?x2] => change (abs (y0 - (y0 + int g x1 x2)) ≤ '`ry)
end.
rewrite rings.negate_plus_distr, plus_assoc, rings.plus_negate_r, rings.plus_0_l, CRabs_negate.
transitivity ('(abs (x - x0) * M)).
+ apply int_abs_bound. apply _. (* Should not be required *)
  intros t A.
  assert (A1 : mspc_ball rx x0 t) by
    (apply (mspc_ball_convex x0 x); [apply mspc_refl, (proj2_sig rx) | |]; trivial).
  (* [(extend_inside (A:= A1))]: "Wrong argument name: A" *)
  rewrite (extend_inside _ _ _ _ A1). apply v_bounded.
+ apply CRle_Qle. change (abs (x - x0) * M ≤ ry). transitivity (`rx * M).
  - now apply (orders.order_preserving (.* M)), mspc_ball_abs_flip.
  - apply rx_ry.
Qed.


End Picard.


(*
Require Import CRArith CRtrans CRconst Qmetric Utf8.
Require Import ProductMetric CompleteProduct (*CPoly_Newton*).
Require Import (*metric2.*)Classified.

Notation "X × Y" := (ProductMS X Y) (at level 40).
Notation "f >> g" := (Cbind_slow f ∘ g) (at level 50).
Notation "x >>= f" := (Cbind_slow f x) (at level 50).
Notation "( f , g )" := (together f g).

Section ODE.
 Open Scope uc_scope.

 Variable v: (Q_as_MetricSpace × Q_as_MetricSpace) --> CR.
 Variable f: Q_as_MetricSpace --> CR.

 Definition vxfx := (v >> Couple ∘ (Cunit, f) ∘ diag _).
End ODE.

Section Picard_op.
 Definition k := (1#2).
 Variable f: Q_as_MetricSpace --> CR.
 Require SimpsonIntegration Qpossec.

 (* Picard operator, ∫ f, from 0 to t *)
 Definition Picard_raw (t:Q_as_MetricSpace) : CR :=
   let f' := uc_compose (scale k) f in
   (1 + (SimpsonIntegration.simpson_integral f' 1 0 (QabsQpos t)))%CR.

 Lemma Picard_uc: (is_UniformlyContinuousFunction Picard_raw (λ (ε:Qpos), ε)).
 admit.
 Qed.

 (* locally lipschitz *)
 Definition Picard := (Cbind QPrelengthSpace (Build_UniformlyContinuousFunction Picard_uc)).

End Picard_op.

Section Banach_iter.
 (* Iterate operator L, n times *)
 Variable L:CR-->CR.
 Fixpoint Picard_seq (n : nat) : Q_as_MetricSpace --> CR :=
   match n with
   | O => L ∘ Cunit
   | S m => (Picard (Picard_seq m) ) ∘ Cunit
   end.
End Banach_iter.

Section example.

Definition g : CR --> CR := Cbind QPrelengthSpace (const_uc (1:Q_as_MetricSpace)).

Definition picard (n:nat) := (Picard_seq g n).

Definition eval (n:positive) (r:CR) : Z :=
 let m := (iter_pos n _ (Pmult 10) 1%positive) in
 let (a,b) := (approximate r (1#m)%Qpos)*m in
 Zdiv a b.

Definition h := const_uc (5#7:Q_as_MetricSpace).
Definition h' := uc_compose (scale (11#13)) h.

Require Import Integration.
Require Import SimpsonIntegration.

Time Eval vm_compute in (eval 3 (1 + (Integrate h' 0 (1#2)))%CR).
Time Eval vm_compute in (eval 3 (1 + (simpson_integral h' 1 0 (1#2)))%CR).

Time Eval vm_compute in (eval 3 (Picard_raw (@const_uc Q_as_MetricSpace (1#1)) 1)).
Time Eval vm_compute in (eval 3 (picard 1 1)).
Time Eval vm_compute in (eval 2 (picard 2 1)).

End example.
*)