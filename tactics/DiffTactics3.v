(* Copyright © 1998-2006
 * Henk Barendregt
 * Luís Cruz-Filipe
 * Herman Geuvers
 * Mariusz Giero
 * Rik van Ginneken
 * Dimitri Hendriks
 * Sébastien Hinderer
 * Bart Kirkels
 * Pierre Letouzey
 * Iris Loeb
 * Lionel Mamane
 * Milad Niqui
 * Russell O’Connor
 * Randy Pollack
 * Nickolay V. Shmyrev
 * Bas Spitters
 * Dan Synek
 * Freek Wiedijk
 * Jan Zwanenburg
 *
 * This work is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; either version 2.1 of the License, or
 * (at your option) any later version.
 *
 * This work is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along
 * with this work; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 *)

(* begin hide *)
Require Export CoRN.ftc.MoreFunSeries.
Require Export CoRN.ftc.Composition.
Require Export CoRN.tactics.DiffTactics2.

Ltac Deriv_substR :=
  match goal with
  |  |- (Derivative ?X1 _) =>
      let t := derivative_of X1 in
      apply Derivative_wdr with t
  end.

Inductive symbPF : Type :=
  | shyp :
      forall (I : interval) (pI : proper I) (F F' : PartIR),
      Derivative I pI F F' -> symbPF
  | shyp' :
      forall (I : interval) (pI : proper I) (F : PartIR),
      Diffble I pI F -> symbPF
  | sconst : forall c : IR, symbPF
  | sid : symbPF
  | splus : symbPF -> symbPF -> symbPF
  | sinv : symbPF -> symbPF
  | sminus : symbPF -> symbPF -> symbPF
  | smult : symbPF -> symbPF -> symbPF
  | sscalmult : IR -> symbPF -> symbPF
  | snth : symbPF -> nat -> symbPF
  | srecip : symbPF -> symbPF
  | sdiv : symbPF -> symbPF -> symbPF
  | scomp : symbPF -> symbPF -> symbPF.
(*
  | ssum0     : nat->(nat->symbPF)->symbPF
  | ssumx     : (n:nat)((i:nat)(lt i n)->symbPF)->symbPF
  | ssum      : nat->nat->(nat->symbPF)->symbPF
*)

Fixpoint symb_to_PartIR (r : symbPF) : PartIR :=
  match r with
  | shyp _ _ f _ _ => f
  | shyp' _ _ f _ => f
  | sconst c => [-C-]c
  | sid => FId
  | splus f g => symb_to_PartIR f{+}symb_to_PartIR g
  | sinv f => {--}(symb_to_PartIR f)
  | sminus f g => symb_to_PartIR f{-}symb_to_PartIR g
  | smult f g => symb_to_PartIR f{*}symb_to_PartIR g
  | sscalmult c f => c{**}symb_to_PartIR f
  | snth f n => symb_to_PartIR f{^}n
  | srecip f => {1/}(symb_to_PartIR f)
  | sdiv f g => symb_to_PartIR f{/}symb_to_PartIR g
  | scomp f g =>
      symb_to_PartIR f[o]
      symb_to_PartIR g
      (*
        | (ssum0 n f)      => (FSum0 n [i:nat](symb_to_PartIR (f i)))
        | (ssumx n f)      => (FSumx n [i:nat][Hi:(lt i n)](symb_to_PartIR (f i Hi)))
        | (ssum m n f)     => (FSum m n [i:nat](symb_to_PartIR (f i)))
      *)
  end.

Fixpoint symbPF_deriv (r : symbPF) : PartIR :=
  match r with
  | shyp _ _ _ f' _ => f'
  | shyp' J pJ F H => Deriv J pJ F H
  | sconst c => [-C-][0]
  | sid => [-C-][1]
  | splus f g => symbPF_deriv f{+}symbPF_deriv g
  | sinv f => {--}(symbPF_deriv f)
  | sminus f g => symbPF_deriv f{-}symbPF_deriv g
  | smult f g =>
      symb_to_PartIR f{*}symbPF_deriv g{+}symbPF_deriv f{*}symb_to_PartIR g
  | sscalmult c f => c{**}symbPF_deriv f
  | snth f n =>
      match n with
      | O => [-C-][0]
      | S p => nring (S p){**}(symbPF_deriv f{*}symb_to_PartIR (snth f p))
      end
  | srecip f => {--}(symbPF_deriv f{/}symb_to_PartIR f{*}symb_to_PartIR f)
  | sdiv f g =>
      (symbPF_deriv f{*}symb_to_PartIR g{-}symb_to_PartIR f{*}symbPF_deriv g){/}
      symb_to_PartIR g{*}symb_to_PartIR g
  | scomp g f =>
      (symbPF_deriv g[o]symb_to_PartIR f){*}
      symbPF_deriv f
      (*
        | (ssum0 n f)       => (FSum0 n [i:nat](symbPF_deriv (f i)))
        | (ssumx n f)       => (FSumx n [i:nat][Hi:(lt i n)](symbPF_deriv (f i Hi)))
        | (ssum m n f)      => (FSum m n [i:nat](symbPF_deriv (f i)))
      *)
  end.

Ltac PartIR_to_symbPF f :=
  match constr:(f) with
  | ([-C-]?X3) => constr:(sconst X3)
  | FId => constr:(sid)
  | (?X3{+}?X4) =>
      let t1 := PartIR_to_symbPF X3 with t2 := PartIR_to_symbPF X4 in
      constr:(splus t1 t2)
  | ({--}?X3) =>
      let t1 := PartIR_to_symbPF X3 in
      constr:(sinv t1)
  | (?X3{-}?X4) =>
      let t1 := PartIR_to_symbPF X3 with t2 := PartIR_to_symbPF X4 in
      constr:(sminus t1 t2)
  | (?X3{*}?X4) =>
      let t1 := PartIR_to_symbPF X3 with t2 := PartIR_to_symbPF X4 in
      constr:(smult t1 t2)
  | (?X3{**}?X4) =>
      let t := PartIR_to_symbPF X4 in
      constr:(sscalmult X3 t)
  | (?X3{^}?X4) =>
      let t1 := PartIR_to_symbPF X3 in
      constr:(snth t1 X4)
  | ({1/}?X3) =>
      let t1 := PartIR_to_symbPF X3 in
      constr:(srecip t1)
  | (?X3{/}?X4) =>
      let t1 := PartIR_to_symbPF X3 with t2 := PartIR_to_symbPF X4 in
      constr:(sdiv t1 t2)
  | (?X3[o]?X4) =>
      let t1 := PartIR_to_symbPF X3 with t2 := PartIR_to_symbPF X4 in
      constr:(scomp t1 t2)
  | ?X3 =>
      let t := constr:(X3) in
      match goal with
      | H:(Derivative ?X1 ?X2 t ?X4) |- _ =>
          constr:(shyp X1 X2 t X4 H)
      | H:(Diffble ?X1 ?X2 t) |- _ => constr:(shyp' X1 X2 t H)
      end
  end.

Ltac Derivative_Help :=
  match goal with
  |  |- (Derivative ?X1 ?X2 ?X3 ?X4) =>
      let r := PartIR_to_symbPF X3 in
      (apply Derivative_wdr with (symbPF_deriv r);
        [ unfold symbPF_deriv, symb_to_PartIR in |- *
        | simpl in |- *; Deriv ])
  end.
(* end hide *)
