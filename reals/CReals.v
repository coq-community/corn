(* $Id$ *)

(** printing Lim %\ensuremath{\lim}% *)

Require Export COrdCauchy.

(** * Definition of the notion of reals
The reals are defined as a Cauchy-closed Archimedean constructive 
ordered field in which we have a maximum function. The maximum
function is definable, using countable choice, but in a rather tricky
way. Cauchy completeness is stated by assuming a function [lim]
that returns a real number for every Cauchy sequence together with a
proof that this number is the limit.  
*)

(* Begin_SpecReals *)

Record is_CReals (R : COrdField) (lim : CauchySeq R -> R) : CProp := 
  {ax_Lim : forall s : CauchySeq R, SeqLimit s (lim s);
   ax_Arch : forall x : R, {n : nat | x[<=]nring n}}.

Record CReals : Type := 
  {crl_crr :> COrdField;
   crl_lim : CauchySeq crl_crr -> crl_crr;
   crl_proof : is_CReals crl_crr crl_lim}.

(* End_SpecReals *)

Definition Lim : forall IR : CReals, CauchySeq IR -> IR := crl_lim.

Implicit Arguments Lim [IR].