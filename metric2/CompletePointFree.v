(* This is a test of how to combine type classes with the old records.
Specifically, how to use the pointfree machinery with the [Complete] monad *)
Require Import CRtrans.
Require Import Qmetric.

Section ODE.
Open Scope uc_scope.
Require Import ProductMetric CompleteProduct.
Require Import Unicode.Utf8.
Require Import metric2.Classified.
Require Import stdlib_rationals.

(*
Check (_:MetricSpaceClass (Q*Q)).
Check (_:MetricSpaceClass (CR*Q)).
*)

Section bind_uc.
(* We use the packed MetricSpace because we do not (yet) want to redefine Complete.
However, here is a first attempt:
Definition CompleteC Y `{MetricSpaceClass Y}:=(Complete (bundle_MetricSpace Y)).
  Context `{MetricSpaceClass X} `{MetricSpaceClass Y}
   {f: X → CompleteC Y} `{!UniformlyContinuous_mu f} `{!UniformlyContinuous f}.
*)

Context {X Y : MetricSpace} (f: X → Complete Y) `{!UniformlyContinuous_mu f} `{!UniformlyContinuous f}.

(* Definition bindf : Complete X -> Complete Y := 
  Cbind_slow  (wrap_uc_fun' f).

Definition test: UCFunction (Complete X) (Complete Y):= 
  ucFunction (fun x => bindf x). *)

(* The classified version *)
Definition Cbind_slowC: UCFunction (Complete X) (Complete Y):= 
   ucFunction (Cbind_slow  (wrap_uc_fun' f)).

Variable g:X --> Complete Y.
Definition test': UCFunction (Complete X) (Complete Y):= 
  ucFunction (fun x => (Cbind_slow g) x).

(* Note that: unwrap_uc_fun automatically unwraps g *)
End bind_uc.
Notation " f >> g ":= (Cbind_slowC f ∘ g) (at level 50).
Notation " x >>= f ":= (Cbind_slowC f x) (at level 50).

Section test.
(* Should Q*Q be bundled ? *)
Context (v: (Q*Q) → CR)
        `{!UniformlyContinuous_mu v}
        `{!UniformlyContinuous v}.

Context (f:Q→CR)
        `{!UniformlyContinuous_mu f}
        `{!UniformlyContinuous f}.

(*
Can be replace by the default (,) ?
Notation "( f , g )":= (together f g).
We would like to define fun x => v (x, f x), more precisely:
*)

(* Check (Cbind_slowC v).
Definition vxfx : UCFunction Q CR := 
  ucFunction (fun x => (Couple (Cunit x, f x) >>= v)).

Better:
Definition vxfx : UCFunction Q CR := 
  ucFunction (fun x => (Couple (x, f x) >>= v)).

Where Cunit is derived from the Coercion inject_Q.
Coercion inject_Q: QArith_base.Q>-> CR.
But this cannot be a Coercion(?)
*)

End test.
End ODE.
