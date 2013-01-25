Require Import
 Unicode.Utf8 Program
 CRArith CRabs
 Qauto Qround Qmetric
 (*stdlib_omissions.P
 stdlib_omissions.Z
 stdlib_omissions.Q
 stdlib_omissions.N*).

Require Qinf QnonNeg QnnInf CRball.
Import Qinf.notations QnonNeg.notations QnnInf.notations CRball.notations Qabs.

Require Import metric FromMetric2 AbstractIntegration SimpleIntegration.
Require Import canonical_names decision setoid_tactics.

Close Scope uc_scope. (* There is a leak in some module *)

Global Instance Qmsd : MetricSpaceDistance Q := λ x y, abs (x - y).

Global Instance Qmsc : MetricSpaceClass Q.
Proof. intros x1 x2; apply gball_Qabs; reflexivity. Qed.

Section Extend.

Context `{ExtMetricSpaceClass Y} (a : Q) (r : QnonNeg) (f : sig (mspc_ball r a) -> Y).

Program Definition extend : Q -> Y :=
  λ x, if (decide (x ≤ a - r))
       then f (a - r)
       else if (decide (a + r ≤ x))
            then f (a + r)
            else f x.
Next Obligation.
destruct r as [e ?]; simpl.
apply Qmetric.gball_Qabs. mc_setoid_replace (a - (a - e)) with e by ring.
change (abs e ≤ e). rewrite abs.abs_nonneg; [reflexivity | trivial].
Qed.

Next Obligation.
destruct r as [e ?]; simpl.
apply Qmetric.gball_Qabs. mc_setoid_replace (a - (a + e)) with (-e) by ring.
change (abs (-e) ≤ e). rewrite abs.abs_negate, abs.abs_nonneg; [reflexivity | trivial].
Qed.

Next Obligation.
apply Qmetric.gball_Qabs, Q.Qabs_diff_Qle. apply orders.le_flip in H1; apply orders.le_flip in H2.
split; trivial.
Qed.

Global Instance extend_lip `{!IsLipschitz f L} : IsLipschitz extend L.
Admitted.

End Extend.

Section Picard.

Context (x0 : Q) (y0 : CR) (rx ry : QnonNeg).

Notation sx := (sig (mspc_ball rx x0)).
Notation sy := (sig (mspc_ball ry y0)).

Context (v : sx * sy -> CR) `{!IsLipschitz v Lv}.

Definition picard' (f : sx -> sy) `{!IsLipschitz f Lf} : sx -> CR :=
  λ x, y0 + int (extend x0 rx (v ∘ (together Datatypes.id f) ∘ diag)) x0 (`x).



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