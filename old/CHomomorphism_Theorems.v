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
(* Homomorphism_Theorems.v, v1.0, 28april2004, Bart Kirkels *)

(** printing [+] %\ensuremath+% #+# *)
(** printing [*] %\ensuremath\times% #&times;# *)
(** printing ['] %\ensuremath.% #.# *)
(** printing [-] %\ensuremath{-}% #&minus;# *)
(** printing [--] %\ensuremath-% #&minus;# *)
(** printing [=] %\ensuremath=% #&equiv;# *)
(** printing [#] %\ensuremath\#% *)
(** printing Zero %\ensuremath{\mathbf0}% #0# *)
(** printing One %\ensuremath{\mathbf1}% #1# *)
(** printing sigma %\ensuremath{\sigma}%  *)
(** printing sigst %\ensuremath{\sigma^{*}}%  *)
(** printing tau %\ensuremath{\tau}%  *)
(** printing Rsigma %\ensuremath{\sigma}%  *)
(** printing Rsigst %\ensuremath{\sigma^{*}}%  *)
(** printing Rtau %\ensuremath{\tau}%  *)
(** printing Cs %\ensuremath{C_{\sigma}}%  *)
(** printing CsR %\ensuremath{C_{\sigma}}%  *)

Require Export CQuotient_Modules.
Require Export CModule_Homomorphisms.
Require Export CQuotient_Rings.
Require Export CRing_Homomorphisms.

(**
* Homomorphism Theorems
** The homomorphism theorem for modules
Let [R] be a ring, [A] and [B] [R]-Modules, and [sigma] a module homomorphism
from [A] to [B].
*** [Cs] is a comodule
We define [Cs], a comodule and prove that it really is a comodule.
*)

Section Theorem_on_Modules.

Variable R : CRing.


Section Cs_CoModule.

Variables A B : RModule R.
Variable sigma : ModHom A B.

Definition cspred (x:A) : CProp := (sigma x) [#] Zero.

Definition cswdpred : (wd_pred A).
Proof.
 apply (Build_wd_pred A cspred).
 unfold pred_wd; intros x y.
 unfold cspred; auto.
 intros H0 H1.
 assert ((hommap A B sigma) x [=] (hommap A B sigma) y).
  apply (csf_wd A B (hommap A B sigma) x y H1).
 astepl ((hommap A B sigma) x).
 assumption.
Defined.

Lemma cs_is_comod : is_comod A cswdpred.
Proof.
 unfold cswdpred.
 apply Build_is_comod; simpl in |-*; unfold cspred.
   (* cm_apzero *)
   apply mh_apzero.
  (* cm_plus *)
  intros x y X.
  cut ((sigma x)[+](sigma y)[#]Zero).
   intro X0.
   apply cg_add_ap_zero; auto.
  astepl (sigma (x[+]y)); algebra.
 (* cm_mult *)
 intros x a X.
 cut ((rm_mu B)a (sigma x)[#]Zero).
  intro X0.
  apply (mu_axap0_xap0 R B a (sigma x)); assumption.
 astepl ((hommap A B sigma) ((rm_mu A) a x)); assumption.
Qed.

Definition cs_as_comod := Build_comod R A cswdpred cs_is_comod.

End Cs_CoModule.


Variables A B : RModule R.
Variable sigma : ModHom A B.

(**
Now we can `divide' [A] by $\lnot$#~#[Cs].
*)

Definition Cs := cs_as_comod A B sigma.
Definition AdivCs := quotmod_as_RModule A Cs.

(**
We now define the functions of which we want to prove the existence.
*)

Definition tau (x:A) := (x:AdivCs).

(* begin hide *)
Lemma tau_strext : fun_strext tau.
Proof.
 red in |-*; intros x y; unfold tau; simpl in |-*.
 unfold ap_quotmod; simpl in |-*; unfold cspred.
 intro X; cut ((x[-]y)[#]Zero); algebra.
 apply (mh_apzero A B sigma (x[-]y)); assumption.
Qed.
(* end hide *)

Definition tau_is_fun := Build_CSetoid_fun A AdivCs tau tau_strext.

Lemma tau_surj : surjective tau_is_fun.
Proof.
 red in |-*; intro b.
 exists b.
 simpl in |-*.
 apply eq_quotmod_wd.
 unfold tau; intuition.
Qed.

Definition sigst (x:AdivCs) := (sigma x).

(* begin hide *)
Lemma sigst_strext : fun_strext sigst.
Proof.
 red in |-*; intros x y; unfold sigst; simpl in |-*.
 unfold ap_quotmod; simpl in |-*; unfold cspred.
 intro X.
 astepl (sigma (x[+]([--]y))); simpl in |-*.
 astepl ((sigma x)[+](sigma ([--]y))); simpl in |-*.
 astepl ((sigma x)[+][--](sigma y)).
 astepl ((sigma x)[-](sigma y)).
 apply minus_ap_zero; assumption.
Qed.
(* end hide *)

Definition sigst_is_fun := Build_CSetoid_fun AdivCs B sigst sigst_strext.

Lemma sigst_inj : injective sigst_is_fun.
Proof.
 red in |-*; intros x y.
 simpl in |-*.
 unfold ap_quotmod.
 simpl in |-*.
 unfold cspred.
 intro X.
 unfold sigst.
 apply (cg_ap_cancel_rht B (sigma x) (sigma y) [--](sigma y)).
 astepr (Zero:B).
 astepl ((sigma x)[+](sigma [--]y)); simpl.
  astepl (sigma (x[+][--]y)); simpl.
   assumption.
  apply mh_pres_plus.
 apply plus_resp_eq; apply mh_pres_minus.
Qed.

(**
And now we have reached a goal: we can easily formulate and prove
the homomorphism theorem for modules.
*)

Lemma ModHomTheorem : {tau : CSetoid_fun A AdivCs | surjective tau}
                  and {sigst : CSetoid_fun AdivCs B | injective sigst}.
Proof.
 split.
  exists tau_is_fun; apply tau_surj.
 exists sigst_is_fun; apply sigst_inj.
Qed.

End Theorem_on_Modules.

(**
** The homomorphism theorem for rings
Let [R] and [S] be rings and [sigma] a ring homomorphism from [R] to [S].
*** [CsR] is a coideal
We define [CsR], a coideal and prove that it really is a coideal.
*)

Section Theorem_on_Rings.

Section Cs_CoIdeal.

Variables R S : CRing.
Variable sigma : RingHom R S.

Definition cspredR (x:R) : CProp := (sigma x) [#] Zero.

Definition cswdpredR : (wd_pred R).
Proof.
 apply (Build_wd_pred R cspredR).
 unfold pred_wd; intros x y.
 unfold cspredR; auto.
 intros H0 H1.
 assert ((rhmap R S sigma) x [=] (rhmap R S sigma) y).
  apply (csf_wd R S (rhmap R S sigma) x y H1).
 astepl ((rhmap R S sigma) x).
 assumption.
Defined.

Lemma cs_is_coideal : is_coideal cswdpredR.
Proof.
 unfold cswdpredR.
 apply Build_is_coideal; simpl in |-*; unfold cspredR.
    (* C_apzero *)
    apply rh_apzero.
   (* C_plus *)
   intros x y X.
   cut ((sigma x)[+](sigma y)[#]Zero).
    intro X0.
    apply cg_add_ap_zero; auto.
   astepl (sigma (x[+]y)); algebra.
  (* C_mult *)
  intros x y X.
  cut ((sigma x)[*](sigma y)[#]Zero).
   intro X0; split; algebra.
    apply (cring_mult_ap_zero S (sigma x) (sigma y)); auto.
   apply (cring_mult_ap_zero_op S (sigma x) (sigma y)); auto.
  astepl (sigma (x[*]y)); assumption.
 (* C_non_triv *)
 astepl (One:S); algebra.
Qed.

Definition cs_as_coideal := Build_coideal R cswdpredR cs_is_coideal.

End Cs_CoIdeal.


Variables R S : CRing.
Variable sigma : RingHom R S.

(**
Now we can `divide' [R] by $\lnot$#~#[CsR].
*)

Definition CsR := cs_as_coideal R S sigma.
Definition RdivCsR := quotring_as_CRing R CsR.

(**
We now define the functions of which we want to prove the existence.
*)

Definition Rtau (x:R) := (x:RdivCsR).

Lemma Rtau_strext : fun_strext Rtau.
Proof.
 red in |-*; intros x y; unfold Rtau; simpl in |-*.
 unfold ap_quotring; simpl in |-*; unfold cspred.
 intro X; cut ((x[-]y)[#]Zero); algebra.
 apply (rh_apzero R S sigma (x[-]y)); assumption.
Qed.

Definition Rtau_is_fun := Build_CSetoid_fun R RdivCsR Rtau Rtau_strext.

Lemma Rtau_surj : surjective Rtau_is_fun.
Proof.
 red in |-*; intro b.
 exists b.
 simpl in |-*.
 apply eq_quotring_wd.
 unfold Rtau; intuition.
Qed.

Definition Rsigst (x:RdivCsR) := (sigma x).

Lemma Rsigst_strext : fun_strext Rsigst.
Proof.
 red in |-*; intros x y; unfold Rsigst; simpl in |-*.
 unfold ap_quotring; simpl in |-*; unfold cspredR.
 intro X.
 astepl (sigma (x[+]([--]y))); simpl in |-*.
 astepl ((sigma x)[+](sigma ([--]y))); simpl in |-*.
 astepl ((sigma x)[+][--](sigma y)).
 astepl ((sigma x)[-](sigma y)).
 apply minus_ap_zero; assumption.
Qed.

Definition Rsigst_is_fun := Build_CSetoid_fun RdivCsR S Rsigst Rsigst_strext.

Lemma Rsigst_inj : injective Rsigst_is_fun.
Proof.
 red in |-*; intros x y.
 simpl in |-*.
 unfold ap_quotring.
 simpl in |-*.
 unfold cspred.
 intro X.
 unfold Rsigst.
 apply (cg_ap_cancel_rht S (sigma x) (sigma y) [--](sigma y)).
 astepr (Zero:S).
 astepl ((sigma x)[+](sigma [--]y)); simpl.
  astepl (sigma (x[+][--]y)); simpl.
   assumption.
  apply rh_pres_plus.
 autorewrite with ringHomPush.
 reflexivity.
Qed.

(**
And now we have reached a goal: we can easily formulate and prove
the homomorphism theorem for rings.
*)

Lemma RingHomTheorem : {Rtau : CSetoid_fun R RdivCsR | surjective Rtau}
                  and {Rsigst : CSetoid_fun RdivCsR S | injective Rsigst}.
Proof.
 split.
  exists Rtau_is_fun; apply Rtau_surj.
 exists Rsigst_is_fun; apply Rsigst_inj.
Qed.

End Theorem_on_Rings.
