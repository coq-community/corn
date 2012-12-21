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