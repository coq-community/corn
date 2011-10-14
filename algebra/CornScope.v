Require Export CSetoids.
Delimit Scope corn_scope with corn.
(* Open Scope corn_scope.*)

Arguments Scope cs_ap [ _ corn_scope corn_scope].
Arguments Scope cs_eq [ _ corn_scope corn_scope].

(* Infix "#" := cs_ap (at level 70, no associativity) : corn_scope. *)
Infix "==" := cs_eq (at level 70, no associativity) : corn_scope.

Require Import CSemiGroups.
Arguments Scope csg_op [ _ corn_scope corn_scope ].
Infix "+" := csg_op (at level 50, left associativity) : corn_scope.


Require Import CMonoids.
Notation "0" := (cm_unit _) : corn_scope.
Notation "(+)" := csg_op (only parsing) : corn_scope.

Require Import CGroups.
Notation "- x" := (cg_inv x) (at level 35, right associativity) : corn_scope.
Infix "-" := cg_minus (at level 50, left associativity) : corn_scope.

Require Import CRings.
Arguments Scope cr_mult [ _ corn_scope corn_scope ].
Infix "*" := cr_mult (at level 40, left associativity) : corn_scope.
Notation "x ^ n" := (nexp_op _ n x) : corn_scope.
Notation "1" := [1] : corn_scope.
