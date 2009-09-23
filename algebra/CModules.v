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
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This work is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this work; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 *)
(* CModules.v, v1.0, 28april2004, Bart Kirkels *)

(** printing [+] %\ensuremath+% #+# *)
(** printing [*] %\ensuremath\times% #&times;# *)
(** printing ['] %\ensuremath.% #.# *)
(** printing [-] %\ensuremath{-}% #&minus;# *)
(** printing [--] %\ensuremath-% #&minus;# *)
(** printing [=] %\ensuremath=% #&equiv;# *)
(** printing [#] %\ensuremath\#% *)
(** printing Zero %\ensuremath{\mathbf0}% #0# *)
(** printing One %\ensuremath{\mathbf1}% #1# *)

Require Export CRings.

(**
* Modules
** Definition of the notion of an R-Module
Let [R] be a ring.
*)

Section Module_Definition.

Variable R : CRing.

Record is_RModule (A : CAbGroup) (mu : CSetoid_bin_fun R A A) : Prop :=
  {rm_pl1 : forall (a:R)(x y:A), (mu a (x[+]y))[=]
            ((mu a x)[+](mu a y));
   rm_pl2 : forall (a b:R)(x:A), (mu (a[+]b) x)[=]
            ((mu a x)[+](mu b x));
   rm_mult: forall (a b:R)(x:A), (mu (a[*]b) x)[=]
            (mu a (mu b x));
   rm_one : forall x:A, (mu One x)[=]x}.

Record RModule : Type :=
  {rm_crr :> CAbGroup;
   rm_mu  : CSetoid_bin_fun R rm_crr rm_crr;
   rm_proof: is_RModule rm_crr rm_mu}.

End Module_Definition.

Implicit Arguments is_RModule [R].
Implicit Arguments rm_crr [R].
Implicit Arguments rm_mu  [R].
Implicit Arguments rm_pl1 [R].
Implicit Arguments rm_pl2 [R].
Implicit Arguments rm_mult[R].
Implicit Arguments rm_one [R].
Implicit Arguments rm_proof[R].

Notation "a ['] x" := (rm_mu _ a x) (at level 20, right associativity).

(**
Let [R] be a ring, let [A] be an [R]-Module.
** Lemmas on Modules
*)

Section Module.

Variable R : CRing.


(**
*** Axioms on Modules
*)

Section Module_Axioms.

Variable A : RModule R.

Lemma RModule_is_RModule : is_RModule (rm_crr A) (rm_mu A).
Proof.
 elim A; intuition.
Qed.

Lemma mu_plus1 :
 forall (a : R) (x y : A), a['](x[+]y) [=] a[']x [+] a[']y.
Proof.
 elim RModule_is_RModule; intuition.
Qed.

Lemma mu_plus2 :
 forall (a b : R) (x : A), (a[+]b) ['] x [=] a[']x [+] b[']x.
Proof.
 elim RModule_is_RModule; intuition.
Qed.

Lemma mu_mult :
 forall (a b : R) (x : A), (a[*]b)['] x [=] a[']b[']x.
Proof.
 elim RModule_is_RModule; intuition.
Qed.

Lemma mu_one : forall x : A, One[']x [=] x.
Proof.
 elim RModule_is_RModule; intuition.
Qed.

End Module_Axioms.

Hint Resolve mu_plus1 mu_plus2 mu_mult mu_one : algebra.

(**
*** Facts on Modules
*)

Section Module_Basics.

Variable A : RModule R.

(* begin hide *)

Lemma mu0help : forall (a:R) (x:A), Zero[']x [=] a[']Zero[']x.
Proof.
 intros a x; astepl ((a[*]Zero)[']x); algebra.
Qed.

Hint Resolve mu0help : algebra.

Lemma mu0help2 : forall x:A, Zero[']x [=] Zero[']x [+] Zero[']x.
Proof.
 intro x; astepl ((One[+]One)[']Zero[']x); algebra.
 astepl (One[']Zero[']x [+] One['](Zero[']x)).
 algebra.
Qed.

Hint Resolve mu0help2 : algebra.

(* end hide *)

Lemma mu_zerox : forall x : A, Zero[']x [=] Zero.
Proof.
 intro x; apply eq_symmetric.
 apply (cg_cancel_lft _ (Zero[']x)); algebra.
 astepl (Zero[']x); algebra.
Qed.

Hint Resolve mu_zerox : algebra.

Lemma mu_minusonex : forall x:A, [--]One[']x [=] [--]x.
Proof.
 intro x; apply (cg_cancel_rht A x ([--]One[']x) [--]x).
 astepr (Zero:A).
 astepl ([--]One[']x [+] One[']x).
 astepl (([--]One[+]One)['] x).
 astepl (Zero[']x); algebra.
Qed.

Hint Resolve mu_minusonex : algebra.

Lemma mu_azero : forall a:R, a['](Zero:A) [=] Zero.
Proof.
 intro a; apply (cg_cancel_rht A (a['](Zero:A))).
 astepr (a['](Zero:A)).
 astepl (a[']((Zero:A)[+](Zero:A))).
 Step_final (a['](Zero:A)).
Qed.

Lemma mu_aminusx : forall (a:R)(x:A), a['][--]x [=] [--] (a[']x).
Proof.
 intros a x; apply (cg_cancel_rht A (a[']x)).
 astepr (Zero:A).
 astepl (a[']([--]x[+]x)).
 astepl (a['](Zero:A)).
 apply mu_azero.
Qed.

Lemma mu_minusax : forall (a:R)(x:A), [--]a[']x [=] [--] (a[']x).
Proof.
 intros a x; apply (cg_cancel_rht A (a[']x)).
 astepr (Zero:A).
 astepl (([--]a[+]a)[']x).
 astepl ((Zero:R)[']x).
 apply mu_zerox.
Qed.

Hint Resolve mu_azero mu_aminusx mu_minusax: algebra.

(* begin hide *)

Lemma mu_strext : forall (a1 a2:R)(x1 x2:A), a1[']x1[#]a2[']x2 ->
                  a1[#]a2 or x1[#]x2.
Proof.
 elim (rm_mu A); intuition.
Qed.

(* end hide *)

Lemma mu_axap0_aap0 : forall (a:R)(x:A), a[']x [#] (Zero:A) -> a [#] (Zero:R).
Proof.
 intros a x X; apply (cg_ap_cancel_rht R a (Zero:R) a).
 astepr a.
 cut (a[+]a[#]a or x[#]x); intuition.
  assert False; try apply (ap_irreflexive_unfolded A x); try assumption.
  elim H.
 apply mu_strext.
 astepl ((a[']x)[+](a[']x)).
 astepr ((Zero:A)[+](a[']x)).
 apply op_rht_resp_ap; assumption.
Qed.

Lemma mu_axap0_xap0 : forall (a:R)(x:A), a[']x [#] (Zero:A) -> x [#] (Zero:A).
Proof.
 intros a x X; apply (cg_ap_cancel_rht A x (Zero:A) x).
 astepr x.
 cut (a[#]a or x[+]x[#]x); intuition.
  assert False; try apply (ap_irreflexive_unfolded R a); try assumption.
  elim H.
 apply mu_strext.
 astepl ((a[']x)[+](a[']x)).
 astepr ((Zero:A)[+](a[']x)).
 apply op_rht_resp_ap; assumption.
Qed.

Hint Resolve mu_strext mu_axap0_aap0 mu_axap0_xap0 : algebra.

End Module_Basics.

(**
** Rings are Modules
*)

Section Rings.

Lemma R_is_RModule : is_RModule R cr_mult.
Proof.
 apply Build_is_RModule; intuition.
Qed.

Definition R_as_RModule := Build_RModule R R cr_mult R_is_RModule.

End Rings.

(**
% \newpage %
** Definition of sub- and comodules
*)

Section CoSubModules.

Variable A : RModule R.

Record is_submod (subP : wd_pred A) : CProp :=
  {smzero : subP Zero;
   smplus : forall x y:A, subP x and subP y -> subP (x[+]y);
   smmult : forall (x:A)(a:R), subP x -> subP(a[']x)}.

Record submod : Type :=
  {smpred :> wd_pred A;
   smproof:  is_submod smpred}.

(* begin hide *)
Variable sm : submod.
Definition submod_as_CSetoid := Build_SubCSetoid A sm.
(* end hide *)

Record is_comod (coP : wd_pred A) : CProp :=
  {cmapzero : forall x:A, coP x -> x[#]Zero;
   cmplus : forall x y:A, coP (x[+]y) -> coP x or coP y;
   cmmult : forall (x:A)(a:R), coP (a[']x) -> coP x}.

Record comod : Type :=
  {cmpred :> wd_pred A;
   cmproof:  is_comod cmpred}.

(* begin hide *)
Variable cm : comod.
Definition comod_as_CSetoid := Build_SubCSetoid A cm.
(* end hide *)

End CoSubModules.

Implicit Arguments is_submod [A].
Implicit Arguments is_comod [A].


(**
** Axioms on sub- and comodules
Let [sm] be a submodule, let [cm] be a comodule.
*)

Section CoSubModule_Axioms.

Variable A : RModule R.
Variable sm : submod A.
Variable cm : comod A.

Lemma submod_is_submod : is_submod sm.
Proof.
 elim sm; auto.
Qed.

Lemma comod_is_comod : is_comod cm.
Proof.
 elim cm; auto.
Qed.

Lemma comod_apzero : forall x:A, cm x -> x[#]Zero.
Proof.
 elim cm. intuition elim cmproof0.
Qed.

Lemma comod_nonzero : Not (cm Zero).
Proof.
 intro.
 cut ((Zero:A)[#](Zero:A)); try apply comod_apzero; try assumption.
 apply ap_irreflexive.
Qed.

Lemma comod_plus : forall x y:A, cm (x[+]y) -> cm x or cm y.
Proof.
 elim cm. intuition elim cmproof0.
Qed.

Lemma comod_mult : forall (x:A)(a:R), cm (a[']x) -> cm x.
Proof.
 elim cm. intuition elim cmproof0.
Qed.

Lemma comod_wd : forall x y:A, x[=]y -> cm x -> cm y.
Proof.
 elim cm.
 simpl in |-*.
 intro.
 elim cmpred0.
 intros.
 apply (wdp_well_def x y); auto.
Qed.

End CoSubModule_Axioms.



End Module.

Implicit Arguments comod_plus [R].
Implicit Arguments comod_mult [R].
Implicit Arguments comod_wd [R].
Implicit Arguments comod_apzero [R].
Implicit Arguments comod_nonzero [R].
Implicit Arguments is_submod [R].
Implicit Arguments submod [R].
Implicit Arguments is_comod [R].
Implicit Arguments comod [R].
Implicit Arguments cmpred [R].
Implicit Arguments cmproof [R].

Hint Resolve mu_plus1 mu_plus2 mu_mult mu_one : algebra.
Hint Resolve mu0help mu0help2 mu_zerox mu_minusonex: algebra.
Hint Resolve mu_azero mu_aminusx mu_minusax: algebra.
Hint Resolve mu_strext mu_axap0_aap0 mu_axap0_xap0 : algebra.
Hint Resolve comod_apzero comod_nonzero : algebra.
Hint Resolve comod_plus comod_mult comod_wd : algebra.
