Require Import Program QArith ZArith Bignums.BigZ.BigZ.
From CoRN Require Import Qpossec MetricMorphisms Qmetric Qdlog ARArith.
From MathClasses.implementations Require Import stdlib_rationals stdlib_binary_integers fast_integers dyadics.

Add Field Q : (dec_fields.stdlib_field_theory Q).

Notation bigD := (Dyadic bigZ).

Print Dyadic.

(* We want to avoid timing the printing mechanism *)

Definition test:bigD->True.
intro x;auto.
Defined.

Definition x:bigD:= (dyadic (10000000%bigZ) (100000%bigZ)).
Definition square:bigD-> bigD:=fun x:bigD => (dy_mult x x) .
Check dy_pow.

Check (Z⁺).
Check NonNeg.
Search NonNeg.
Check ((1 _):(Z⁺)).

(* Time Eval vm_compute in (test (dy_pow x (((40%Z) _)))).*)

Time Eval native_compute in (test (square x)). 

From CoRN Require Import ARbigD.
Time Eval vm_compute in (test (bigD_div (square x) x (10000%Z))).
From CoRN Require Import ApproximateRationals.
