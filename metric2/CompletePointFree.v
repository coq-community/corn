(* This is a test of how to combine type classes with the old records.
Specifically, how to use the pointfree machinery with the [Complete] monad *)
Require Import CRtrans.
Require Import Qmetric.

Section ODE.
Open Scope uc_scope.
Require Import ProductMetric CompleteProduct.
Require Import Unicode.Utf8.
Require Import metric2.Classified.
Require Import Circle.
Notation "X * Y":=(ProductMS X Y).
Notation " f >> g ":= (Cbind_slow f ∘ g) (at level 50).
Notation " x >>= f ":= (Cbind_slow f x) (at level 50).
Notation "( f , g )":= (together f g).

(*
Context (v: (Q*Q) → CR)
        `{!UniformlyContinuous_mu v}
        `{!UniformlyContinuous v}.

Context (f:Q→CR)
        `{!UniformlyContinuous_mu f}
        `{!UniformlyContinuous f}.

We would like to define fun x => v (x, f x), more precisely:
Definition vxfx : UCFunction Q CR := 
  ucFunction (fun x => (Couple (Cunit x, f x) >>= v)).

Better:
Definition vxfx : UCFunction Q CR := 
  ucFunction (fun x => (Couple (x, f x) >>= v)).

Where Cunit is derived from the Coercion inject_Q.
Coercion inject_Q: QArith_base.Q>-> CR.
But this cannot be a Coercion(?)
*)

Section bind_uc.
  Context (X Y:MetricSpace)
   (f: X → Complete Y) `{!UniformlyContinuous_mu f} `{!UniformlyContinuous f}.

(* Definition bindf : Complete X -> Complete Y := 
  Cbind_slow  (wrap_uc_fun' f).

Definition test: UCFunction (Complete X) (Complete Y):= 
  ucFunction (fun x => bindf x). *)

(* The classified version *)
Definition bindf: UCFunction (Complete X) (Complete Y):= 
   ucFunction (Cbind_slow  (wrap_uc_fun' f)).

Variable g:X --> Complete Y.
Definition test': UCFunction (Complete X) (Complete Y):= 
  ucFunction (fun x => (Cbind_slow g) x).

(* Note that: unwrap_uc_fun automatically unwraps g *)
End bind_uc.