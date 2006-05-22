(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


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
  {ax_Lim  : forall s : CauchySeq R, SeqLimit s (lim s);
   ax_Arch : forall x : R, {n : nat | x [<=] nring n}}.

Record CReals : Type := 
  {crl_crr   :> COrdField;
   crl_lim   :  CauchySeq crl_crr -> crl_crr;
   crl_proof :  is_CReals crl_crr crl_lim}.

(* End_SpecReals *)

Definition Lim : forall IR : CReals, CauchySeq IR -> IR := crl_lim.

Implicit Arguments Lim [IR].
