Require Import QArith.
Require Import abstract_algebra.
Require Import Qmetric Qring Setoid.

Section Qvectorspace.
(** Vector spaces
     We restrict to vector spaces over Q since the general constructive theory of fields is not well understood.
     Note that an R-vector space is a Q-vector space *)
Class Scalar_mult `{Abgroup X}:=scal_mult: Q->X->X.
Notation "'.'":=scal_mult (at level 50).
Infix "(.)" := scal_mult (only parsing, at level 50).
(*Context X {e:Equiv X} (op:X->X->X).*)
(*
Class VectorSpace `{Abgroup X} `{sm:Scalar_mult}:Prop:={
vs_distr: forall q:Q, forall x y:X, (sm q (x+ y)=(q(.)x)+(q(.)y))
}.
*)
