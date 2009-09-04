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

(** printing [/] %\ensuremath{/}% #/# *)
(** printing [//] %\ensuremath\ddagger% #&Dagger;# *)
(** printing {/} %\ensuremath{/}% #/# *)
(** printing {1/} %\ensuremath{\frac1\cdot}% #1/# *)
(** printing [/]?[//] %\ensuremath{/?\ddagger}% #/?&Dagger;# *)

Require Export CRings.

Transparent sym_eq.
Transparent f_equal.


Transparent cs_crr.
Transparent csg_crr.
Transparent cm_crr.
Transparent cg_crr.
Transparent cr_crr.

Transparent csf_fun.
Transparent csbf_fun.
Transparent csr_rel.

Transparent cs_eq.
Transparent cs_neq.
Transparent cs_ap.
Transparent cm_unit.
Transparent csg_op.
Transparent cg_inv.
Transparent cg_minus.
Transparent cr_one.
Transparent cr_mult.

Transparent nexp_op.

(* Begin_SpecReals *)

(* FIELDS *)
(**
* Fields %\label{section:fields}%
** Definition of the notion Field
*)

Definition is_CField (R : CRing) (cf_rcpcl : forall x : R, x [#] Zero -> R) : Prop :=
  forall x Hx, is_inverse cr_mult One x (cf_rcpcl x Hx).

Record CField : Type := 
  {cf_crr   :> CRing;
   cf_rcpcl :  forall x : cf_crr, x [#] Zero -> cf_crr;
   cf_proof :  is_CField cf_crr cf_rcpcl;
   cf_rcpsx :  forall x y x_ y_, cf_rcpcl x x_ [#] cf_rcpcl y y_ -> x [#] y}.
(* End_SpecReals *)

Definition f_rcpcl' (F : CField) : PartFunct F.
intro F.
apply Build_PartFunct with (fun x : F => x [#] Zero) (cf_rcpcl F).
 red in |- *; intros; astepl x. auto.
exact (cf_rcpsx F).
Defined.

Definition f_rcpcl F x x_ := f_rcpcl' F x x_.

Implicit Arguments f_rcpcl [F].

(**
[cf_div] is the division in a field. It is defined in terms of
multiplication and the reciprocal. [x[/]y] is only defined if
we have a proof of [y [#] Zero].
*)

Definition cf_div (F : CField) (x y : F) y_ : F := x[*]f_rcpcl y y_.

Implicit Arguments cf_div [F].
Notation "x [/] y [//] Hy" := (cf_div x y Hy) (at level 80).

(**
%\begin{convention}\label{convention:div-form}%
- Division in fields is a (type dependent) ternary function: [(cf_div x y Hy)] is denoted infix by [x [/] y [//] Hy].
- In lemmas, a hypothesis that [t [#] Zero] will be named [t_].
- We do not use [NonZeros], but write the condition [ [#] Zero] separately.
- In each lemma, we use only variables for proof objects, and these variables
 are universally quantified.
For example, the informal lemma
$\frac{1}{x}\cdot\frac{1}{y} = \frac{1}{x\cdot y}$
#(1/x).(1/y) = 1/(x.y)# for all [x] and [y]is formalized as
[[
forall (x y : F) x_ y_ xy_, (1[/]x[//]x_) [*] (1[/]y[//]y_) [=] 1[/] (x[*]y)[//]xy_
]]
and not as
[[
forall (x y : F) x_ y_, (1[/]x[//]x_) [*] (1[/]y[//]y_) [=] 1[/] (x[*]y)[//](prod_nz x y x_ y_)
]]
We have made this choice to make it easier to apply lemmas; this can
be quite awkward if we would use the last formulation.
- So every division occurring in the formulation of a lemma is of the
form [e[/]e'[//]H] where [H] is a variable.  Only exceptions: we may
write [e[/] (Snring n)] and [e[/]TwoNZ], [e[/]ThreeNZ] and so on.
(Constants like [TwoNZ] will be defined later on.)

%\end{convention}%

** Field axioms
%\begin{convention}% Let [F] be a field.
%\end{convention}%
*)
Section Field_axioms.
Variable F : CField.

Lemma CField_is_CField : is_CField F (cf_rcpcl F).
elim F; auto.
Qed.

Lemma rcpcl_is_inverse : forall x x_, is_inverse cr_mult One x (cf_rcpcl F x x_).
apply CField_is_CField.
Qed.

End Field_axioms.

Section Field_basics.
(**
** Field basics
%\begin{convention}% Let [F] be a field.
%\end{convention}%
*)

Variable F : CField.

Lemma rcpcl_is_inverse_unfolded : forall x x_, x[*]cf_rcpcl F x x_ [=] One.
intros x x_.
elim (rcpcl_is_inverse F x x_); auto.
Qed.

Lemma field_mult_inv : forall (x : F) x_, x[*]f_rcpcl x x_ [=] One.
Proof rcpcl_is_inverse_unfolded.
Hint Resolve field_mult_inv: algebra.

Lemma field_mult_inv_op : forall (x : F) x_, f_rcpcl x x_[*]x [=] One.
intros x x_.
elim (rcpcl_is_inverse F x x_); auto.
Qed.

End Field_basics.

Hint Resolve field_mult_inv field_mult_inv_op: algebra.

Section Field_multiplication.
(**
** Properties of multiplication
%\begin{convention}% Let [F] be a field.
%\end{convention}%
*)

Variable F : CField.

Lemma mult_resp_ap_zero : forall x y : F, x [#] Zero -> y [#] Zero -> x[*]y [#] Zero.
intros x y Hx Hy.
apply cring_mult_ap_zero with (f_rcpcl y Hy).
astepl x.
auto.
astepl (x[*]One).
eapply eq_transitive_unfolded.
2: apply CRings.mult_assoc.
algebra.
Qed.

Lemma mult_lft_resp_ap : forall x y z : F, x [#] y -> z [#] Zero -> z[*]x [#] z[*]y.
intros x y z H Hz.
apply zero_minus_apart.
unfold cg_minus in |- *.
astepl (z[*]x[+]z[*][--]y).
astepl (z[*] (x[+][--]y)).
astepl (z[*] (x[-]y)).
apply mult_resp_ap_zero; algebra.
Qed.

Lemma mult_rht_resp_ap : forall x y z : F, x [#] y -> z [#] Zero -> x[*]z [#] y[*]z.
intros x y z H Hz.
astepl (z[*]x).
astepr (z[*]y).
apply mult_lft_resp_ap; assumption.
Qed.

Lemma mult_resp_neq_zero : forall x y : F, x[~=]Zero -> y[~=]Zero -> x[*]y[~=]Zero.
intros x y Hx Hy.
cut (~ Not (x [#] Zero)).
intro H.
cut (~ Not (y [#] Zero)).
intro H0.
apply notnot_ap_imp_neq.
cut (x [#] Zero -> y [#] Zero -> x[*]y [#] Zero).
intro H1.
intro.
apply H0; intro H3.
apply H; intro H4.
apply H2; auto.

intros; apply mult_resp_ap_zero; auto.

apply neq_imp_notnot_ap; auto.

apply neq_imp_notnot_ap; auto.
Qed.

Lemma mult_resp_neq : forall x y z : F, x[~=]y -> z[~=]Zero -> x[*]z[~=]y[*]z.
intros x y z H Hz.
generalize (neq_imp_notnot_ap _ _ _ H).
generalize (neq_imp_notnot_ap _ _ _ Hz).
generalize (mult_rht_resp_ap x y z).
intros H1 H2 H3.
apply notnot_ap_imp_neq.
intro H4.
apply H2; intro.
apply H3; intro.
apply H4.
auto.
Qed.

Lemma mult_eq_zero : forall x y : F, x[~=]Zero -> x[*]y [=] Zero -> y [=] Zero.
intros x y Hx Hxy.
apply not_ap_imp_eq.

intro H.
elim (eq_imp_not_neq _ _ _ Hxy).
apply mult_resp_neq_zero.
 assumption.
apply ap_imp_neq.
assumption.
Qed.

Lemma mult_cancel_lft : forall x y z : F, z [#] Zero -> z[*]x [=] z[*]y -> x [=] y.
intros x y z Hz H.
apply not_ap_imp_eq.
intro H2.
elim (eq_imp_not_ap _ _ _ H).
apply mult_lft_resp_ap; assumption.
Qed.

Lemma mult_cancel_rht : forall x y z : F, z [#] Zero -> x[*]z [=] y[*]z -> x [=] y.
intros x y z Hz H.
apply (mult_cancel_lft x y z).
 assumption.
astepr (y[*]z).
Step_final (x[*]z).
Qed.

Lemma square_eq_aux : forall x a : F, x[^]2 [=] a[^]2 -> (x[+]a) [*] (x[-]a) [=] Zero.
intros x a H.
astepl (x[^]2[-]a[^]2).
Step_final (a[^]2[-]a[^]2).
Qed.

Lemma square_eq_weak : forall x a : F, x[^]2 [=] a[^]2 -> Not (x [#] a and x [#] [--]a).
intros x a H.
intro H0.
elim H0; intros H1 H2.
generalize (square_eq_aux _ _ H); intro H3.
generalize (eq_imp_not_ap _ _ _ H3); intro H4.
apply H4.
apply mult_resp_ap_zero.
 astepr ([--]a[+]a). apply op_rht_resp_ap. auto.
astepr (a[-]a).
apply minus_resp_ap_rht.
assumption.
Qed.

Lemma cond_square_eq : forall x a : F,
 (Two:F) [#] Zero -> a [#] Zero -> x[^]2 [=] a[^]2 -> x [=] a or x [=] [--]a.
intros x a H Ha H0.
cut (a [#] [--]a).
intro H1.
elim (ap_cotransitive_unfolded _ _ _ H1 x); intro H2.
 right.
 apply not_ap_imp_eq.
 intro H3.
 elim (square_eq_weak _ _ H0).
 split; auto.
 apply ap_symmetric_unfolded; auto.
left.
apply not_ap_imp_eq.
intro H3.
elim (square_eq_weak _ _ H0); auto.

apply plus_cancel_ap_lft with a.
astepr (Zero:F).
astepl (Two[*]a).
apply mult_resp_ap_zero; auto.
Qed.
End Field_multiplication.

Section x_square.
Lemma x_xminone : forall (F : CField) (x : F), x[^]2 [=] x -> x[*] (x[-]One) [=] Zero.
intros H x h.
astepl (x[*]x[-]x[*]One).
astepl (x[*]x[-]x).
apply cg_cancel_rht with x.
astepl (x[*]x[+][--]x[+]x).
astepl (x[*]x[+]([--]x[+]x)).
astepl (x[*]x[+]Zero).
astepl (x[*]x).
astepr x.
astepl (x[^]2).
exact h.
Qed.

Lemma square_id : forall (F : CField) (x : F), x[^]2 [=] x -> {x [=] Zero} + {x [=] One}.
intros F x H.
cut ((Zero:F) [#] (One:F)).
intro H0.
elim (ap_cotransitive_unfolded _ _ _ H0 x).
intro H1.
right.
apply not_ap_imp_eq.
red in |- *.
intro H2.
set (H3 := minus_resp_ap_rht F x One One H2) in *.
set
 (H4 :=
  ap_wdr_unfolded F (x[-]One) (One[-]One) Zero H3
    (cg_minus_correct F One)) in *.
set (H5 := ap_symmetric_unfolded F Zero x H1) in *.
set (H6 := mult_resp_ap_zero F x (x[-]One) H5 H4) in *.
simpl in |- *.

set (H7 := x_xminone F x H) in *.
set (H8 := eq_imp_not_ap F (x[*] (x[-]One)) Zero H7) in *.
intuition.

left.
apply not_ap_imp_eq.
red in |- *.
intro H2.
set (H3 := minus_resp_ap_rht F x One One b) in *.
set
 (H4 :=
  ap_wdr_unfolded F (x[-]One) (One[-]One) Zero H3
    (cg_minus_correct F One)) in *.
set (H6 := mult_resp_ap_zero F x (x[-]One) H2 H4) in *.
set (H7 := x_xminone F x H) in *.
set (H8 := eq_imp_not_ap F (x[*] (x[-]One)) Zero H7) in *.
intuition.

apply ap_symmetric_unfolded.
apply ring_non_triv.
Qed.
End x_square.


Hint Resolve mult_resp_ap_zero: algebra.


Section Rcpcl_properties.
(**
** Properties of reciprocal
%\begin{convention}% Let [F] be a field.
%\end{convention}%
*)

Variable F : CField.

Lemma inv_one : f_rcpcl One (ring_non_triv F) [=] One.
astepl (One[*]f_rcpcl One (ring_non_triv F)).
apply field_mult_inv.
Qed.

Lemma f_rcpcl_wd : forall (x y : F) x_ y_, x [=] y -> f_rcpcl x x_ [=] f_rcpcl y y_.
intros x y H.
unfold f_rcpcl in |- *; algebra.
Qed.

Lemma f_rcpcl_mult : forall (y z : F) y_ z_ yz_,
 f_rcpcl (y[*]z) yz_ [=] f_rcpcl y y_[*]f_rcpcl z z_.
intros y z nzy nzz nzyz.
apply mult_cancel_lft with (y[*]z).
 assumption.
astepl (One:F).
astepr (y[*]z[*] (f_rcpcl z nzz[*]f_rcpcl y nzy)).
astepr (y[*] (z[*] (f_rcpcl z nzz[*]f_rcpcl y nzy))).
astepr (y[*] (z[*]f_rcpcl z nzz[*]f_rcpcl y nzy)).
astepr (y[*] (One[*]f_rcpcl y nzy)).
astepr (y[*]f_rcpcl y nzy).
Step_final (One:F).
Qed.

Lemma f_rcpcl_resp_ap_zero : forall (y : F) y_, f_rcpcl y y_ [#] Zero.
intros y nzy.
apply cring_mult_ap_zero_op with y.
astepl (One:F). apply one_ap_zero.
Qed.

Lemma f_rcpcl_f_rcpcl : forall (x : F) x_ r_, f_rcpcl (f_rcpcl x x_) r_ [=] x.
intros x nzx nzr.
apply mult_cancel_rht with (f_rcpcl x nzx).
 assumption.
astepr (One:F).
Step_final (f_rcpcl x nzx[*]f_rcpcl (f_rcpcl x nzx) nzr).
Qed.

End Rcpcl_properties.

Section MultipGroup.
(**
** The multiplicative group of nonzeros of a field.
%\begin{convention}% Let [F] be a field
%\end{convention}%
*)

Variable F : CField.

(**
The multiplicative monoid of NonZeros.
*)

Definition NonZeroMonoid : CMonoid := Build_SubCMonoid
 (Build_multCMonoid F) (nonZeroP (M:=F)) (one_ap_zero F) (mult_resp_ap_zero F).

Definition fmg_cs_inv : CSetoid_un_op NonZeroMonoid.
red in |- *.
cut
 (forall x : NonZeroMonoid,
  nonZeroP (cf_rcpcl F (scs_elem _ _ x) (scs_prf _ _ x))).
intro H.
apply
 Build_CSetoid_fun
  with
    (fun x : NonZeroMonoid =>
     Build_subcsetoid_crr _ _ (cf_rcpcl F (scs_elem _ _ x) (scs_prf _ _ x))
       (H x)).
red in |- *.
simpl in |- *.
simple destruct x; simple destruct y. intros scs_elem0 scs_prf0 H0.
apply (cf_rcpsx _ _ _ _ _ H0).
intro; simpl in |- *.
red in |- *.
astepl (f_rcpcl (scs_elem _ _ x) (scs_prf _ _ x)).
apply f_rcpcl_resp_ap_zero.
Defined.

Lemma plus_nonzeros_eq_mult_dom : forall x y : NonZeroMonoid,
 scs_elem _ _ (x[+]y) [=] scs_elem _ _ x[*]scs_elem _ _ y.
simple destruct x; simple destruct y; algebra.
Qed.

Lemma cfield_to_mult_cgroup : CGroup.
apply (Build_CGroup NonZeroMonoid fmg_cs_inv).
intro x.
red in |- *.
elim x; intros x_ Hx.
simpl in |- *; apply cf_proof.
Qed.

End MultipGroup.

Section Div_properties.
(**
** Properties of division
%\begin{convention}% Let [F] be a field.
%\end{convention}%

%\begin{nameconvention}%
In the names of lemmas, we denote [[/]] by [div], and
[One[/]] by [recip].
%\end{nameconvention}%
*)

Variable F : CField.

Lemma div_prop : forall (x : F) x_, (Zero[/] x[//]x_) [=] Zero.
unfold cf_div in |- *; algebra.
Qed.

Lemma div_1 : forall (x y : F) y_, (x[/] y[//]y_) [*]y [=] x.
intros x y y_.
astepl (x[*]f_rcpcl y y_[*]y).
astepl (x[*] (f_rcpcl y y_[*]y)).
Step_final (x[*]One).
Qed.

Lemma div_1' : forall (x y : F) y_, y[*] (x[/] y[//]y_) [=] x.
intros x y y_.
astepl ((x[/] y[//]y_) [*]y).
apply div_1.
Qed.

Lemma div_1'' : forall (x y : F) y_, (x[*]y[/] y[//]y_) [=] x.
intros x y y_.
unfold cf_div in |- *.
astepl (y[*]x[*]f_rcpcl y y_).
astepl (y[*] (x[*]f_rcpcl y y_)).
change (y[*] (x[/] y[//]y_) [=] x) in |- *.
apply div_1'.
Qed.

Hint Resolve div_1: algebra.

Lemma x_div_x : forall (x : F) x_, (x[/] x[//]x_) [=] One.
intros x x_.
unfold cf_div in |- *.
apply field_mult_inv.
Qed.

Hint Resolve x_div_x: algebra.

Lemma x_div_one : forall x : F, (x[/] One[//]ring_non_triv F) [=] x.
intro x.
unfold cf_div in |- *.
generalize inv_one; intro H.
astepl (x[*]One).
apply mult_one.
Qed.

(**
The next lemma says $x\cdot\frac{y}{z} = \frac{x\cdot y}{z}$
#x.(y/z) = (x.y)/z#.
*)

Lemma x_mult_y_div_z : forall (x y z : F) z_, x[*] (y[/] z[//]z_) [=] (x[*]y[/] z[//]z_).
unfold cf_div in |- *; algebra.
Qed.

Hint Resolve x_mult_y_div_z: algebra.


Lemma div_wd : forall (x x' y y' : F) y_ y'_, x [=] x' -> y [=] y' -> (x[/] y[//]y_) [=] (x'[/] y'[//]y'_).
intros x x' y y' nzy nzy' H H0.
unfold cf_div in |- *.
cut (f_rcpcl y nzy [=] f_rcpcl y' nzy').
intro H1.
algebra.

apply f_rcpcl_wd.
assumption.
Qed.

Hint Resolve div_wd: algebra_c.

(**
The next lemma says $\frac{\frac{x}{y}}{z} = \frac{x}{y\cdot z}$
#[(x/y)/z = x/(y.z)]#
*)

Lemma div_div : forall (x y z : F) y_ z_ yz_, ((x[/] y[//]y_) [/] z[//]z_) [=] (x[/] y[*]z[//]yz_).
intros x y z nzy nzz nzyz.
unfold cf_div in |- *.
astepl (x[*] (f_rcpcl y nzy[*]f_rcpcl z nzz)).
apply mult_wdr.
apply eq_symmetric_unfolded.
apply f_rcpcl_mult.
Qed.


Lemma div_resp_ap_zero_rev : forall (x y : F) y_, x [#] Zero -> (x[/] y[//]y_) [#] Zero.
intros x y nzy Hx.
unfold cf_div in |- *.
apply mult_resp_ap_zero.
 assumption.
apply f_rcpcl_resp_ap_zero.
Qed.


Lemma div_resp_ap_zero : forall (x y : F) y_, (x[/] y[//]y_) [#] Zero -> x [#] Zero.
intros x y nzy Hxy.
astepl ((x[/] y[//]nzy) [*]y). algebra.
Qed.

(**
The next lemma says $\frac{x}{\frac{y}{z}} = \frac{x\cdot z}{y}$
#[x/(y/z) = (x.z)/y]#
*)

Lemma div_div2 : forall (x y z : F) y_ z_ yz_, (x[/] y[/] z[//]z_[//]yz_) [=] (x[*]z[/] y[//]y_).
intros x y z nzy nzz nzyz.
unfold cf_div in |- *.
astepr (x[*] (z[*]f_rcpcl y nzy)).
apply mult_wdr.
cut (f_rcpcl z nzz [#] Zero).
intro nzrz.
apply
 eq_transitive_unfolded with (f_rcpcl y nzy[*]f_rcpcl (f_rcpcl z nzz) nzrz).
 apply f_rcpcl_mult.
astepr (f_rcpcl y nzy[*]z).
apply mult_wdr.
apply f_rcpcl_f_rcpcl.

apply f_rcpcl_resp_ap_zero.
Qed.

(**
The next lemma says $\frac{x\cdot p}{y\cdot q} = \frac{x}{y}\cdot \frac{p}{q}$
#[(x.p)/(y.q) = (x/y).(p/q)]#
*)

Lemma mult_of_divs : forall (x y p q : F) y_ q_ yq_,
 (x[*]p[/] y[*]q[//]yq_) [=] (x[/] y[//]y_) [*] (p[/] q[//]q_).
intros x y p q nzy nzq nzyq.
unfold cf_div in |- *.
astepl (x[*] (p[*]f_rcpcl (y[*]q) nzyq)).
astepr (x[*] (f_rcpcl y nzy[*] (p[*]f_rcpcl q nzq))).
apply mult_wdr.
astepr (f_rcpcl y nzy[*]p[*]f_rcpcl q nzq).
astepr (p[*]f_rcpcl y nzy[*]f_rcpcl q nzq).
astepr (p[*] (f_rcpcl y nzy[*]f_rcpcl q nzq)).
apply mult_wdr.
apply f_rcpcl_mult.
Qed.

Lemma div_dist : forall (x y z : F) z_, (x[+]y[/] z[//]z_) [=] (x[/] z[//]z_) [+] (y[/] z[//]z_).
unfold cf_div in |- *; algebra.
Qed.

Lemma div_dist' : forall (x y z : F) z_, (x[-]y[/] z[//]z_) [=] (x[/] z[//]z_) [-] (y[/] z[//]z_).
unfold cf_div in |- *; algebra.
Qed.

Lemma div_semi_sym : forall (x y z : F) y_ z_, ((x[/] y[//]y_) [/] z[//]z_) [=] ((x[/] z[//]z_) [/] y[//]y_).
intros.
unfold cf_div in |- *.
astepl (x[*] ((f_rcpcl y y_) [*] (f_rcpcl z z_))).
Step_final (x[*] ((f_rcpcl z z_) [*] (f_rcpcl y y_))).
Qed.

Hint Resolve div_semi_sym: algebra.

Lemma eq_div : forall (x y u v : F) y_ v_, x[*]v [=] u[*]y -> (x[/] y[//]y_) [=] (u[/] v[//]v_).
intros x y u v Hy Hv H.
astepl (x[*]One[/] y[//]Hy).
astepl (x[*] (v[/] v[//]Hv) [/] y[//]Hy).
astepl ((x[*]v[/] v[//]Hv) [/] y[//]Hy).
astepl ((u[*]y[/] v[//]Hv) [/] y[//]Hy).
astepl ((u[*]y[/] y[//]Hy) [/] v[//]Hv).
astepl (u[*] (y[/] y[//]Hy) [/] v[//]Hv).
Step_final (u[*]One[/] v[//]Hv).
Qed.

Lemma div_strext : forall (x x' y y' : F) y_ y'_, (x[/] y[//]y_) [#] (x'[/] y'[//]y'_) -> x [#] x' or y [#] y'.
intros x x' y y' Hy Hy' H.
unfold cf_div in H.
elim (cs_bin_op_strext F cr_mult _ _ _ _ H).
 auto.
intro H1.
right.
unfold f_rcpcl in H1.
exact (pfstrx _ _ _ _ _ _ H1).
Qed.

End Div_properties.

Hint Resolve div_1 div_1' div_1'' div_wd x_div_x x_div_one div_div div_div2
  mult_of_divs x_mult_y_div_z mult_of_divs div_dist div_dist' div_semi_sym
  div_prop: algebra.

(**
** Cancellation laws for apartness and multiplication
%\begin{convention}% Let [F] be a field
%\end{convention}%
*)

Section Mult_Cancel_Ap_Zero.

Variable F : CField.

Lemma mult_cancel_ap_zero_lft : forall x y : F, x[*]y [#] Zero -> x [#] Zero.
intros x y H.
cut (x[*]y [#] Zero[*]Zero).
intro H0.
elim (bin_op_strext_unfolded _ _ _ _ _ _ H0); intro H1.
 3: astepr (Zero:F); auto.
assumption.

astepl (x[*]y[/] y[//]H1).
apply div_resp_ap_zero_rev.
assumption.
Qed.

Lemma mult_cancel_ap_zero_rht : forall x y : F, x[*]y [#] Zero -> y [#] Zero.
intros x y H.
apply mult_cancel_ap_zero_lft with x.
astepl (x[*]y). auto.
Qed.

Lemma recip_ap_zero : forall (x : F) x_, (One[/] x[//]x_) [#] Zero.
intros; apply cring_mult_ap_zero with x.
astepl (One:F). algebra.
Qed.

Lemma recip_resp_ap : forall (x y : F) x_ y_, x [#] y -> (One[/] x[//]x_) [#] (One[/] y[//]y_).
intros x y x_ y_ H.
apply zero_minus_apart.
apply mult_cancel_ap_zero_lft with (x[*]y).
apply ap_wdl with (y[-]x).
 apply minus_ap_zero.
 apply ap_symmetric_unfolded; assumption.
eapply eq_transitive_unfolded.
 2: apply eq_symmetric_unfolded; apply dist_2b.
apply cg_minus_wd.
 astepr (x[*]y[*] (One[/] x[//]x_)).
 astepr (x[*]y[*]One[/] x[//]x_).
 astepr (x[*]y[/] x[//]x_).
 astepr (y[*]x[/] x[//]x_).
 astepr (y[*] (x[/] x[//]x_)).
 Step_final (y[*]One).
astepr (x[*]y[*] (One[/] y[//]y_)).
astepr (x[*]y[*]One[/] y[//]y_).
astepr (x[*]y[/] y[//]y_).
astepr (x[*] (y[/] y[//]y_)).
Step_final (x[*]One).
Qed.

End Mult_Cancel_Ap_Zero.

Section CField_Ops.

(**
** Functional Operations

We now move on to lifting these operations to functions.  As we are
dealing with %\emph{partial}% #<i>partial</i># functions, we don't
have to worry explicitly about the function by which we are dividing
being non-zero everywhere; this will simply be encoded in its domain.

%\begin{convention}%
Let [X] be a Field and [F,G:(PartFunct X)] have domains respectively
[P] and [Q].
%\end{convention}%
*)

Variable X : CField.

Variables F G : PartFunct X.

(* begin hide *)
Let P := Dom F.
Let Q := Dom G.
(* end hide *)

Section Part_Function_Recip.

(**
Some auxiliary notions are helpful in defining the domain.
*)

Let R := extend Q (fun x Hx => G x Hx [#] Zero).

Let Ext2R := ext2 (S:=X) (P:=Q) (R:=fun x Hx => G x Hx [#] Zero).

Lemma part_function_recip_strext : forall x y Hx Hy,
 (One[/] _[//]Ext2R x Hx) [#] (One[/] _[//]Ext2R y Hy) -> x [#] y.
intros x y Hx Hy H.
elim (div_strext _ _ _ _ _ _ _ H); intro H1.
 elimtype False; apply ap_irreflexive_unfolded with (x := One:X); auto.
exact (pfstrx _ _ _ _ _ _ H1).
Qed.

Lemma part_function_recip_pred_wd : pred_wd X R.
red in |- *; intros x y H H0.
elim H; intros H1 H2; split.
 apply (dom_wd X G x y H1 H0).
intro H3; astepl (G x H1). auto.
Qed.

Definition Frecip := Build_PartFunct X _ part_function_recip_pred_wd
 (fun x Hx => One[/] _[//]Ext2R x Hx) part_function_recip_strext.

End Part_Function_Recip.

Section Part_Function_Div.

(**
For division things work out almost in the same way.
*)

Let R := Conj P (extend Q (fun x Hx => G x Hx [#] Zero)).

Let Ext2R := ext2 (S:=X) (P:=Q) (R:=fun x Hx => G x Hx [#] Zero).

Lemma part_function_div_strext : forall x y Hx Hy,
 (F x (prj1 X _ _ _ Hx) [/] _[//]Ext2R x (prj2 X _ _ _ Hx)) [#]
  (F y (prj1 X _ _ _ Hy) [/] _[//]Ext2R y (prj2 X _ _ _ Hy)) -> 
 x [#] y.
intros x y Hx Hy H.
elim (div_strext _ _ _ _ _ _ _ H); intro H1;
 exact (pfstrx _ _ _ _ _ _ H1).
Qed.

Lemma part_function_div_pred_wd : pred_wd X R.
red in |- *; intros x y H H0.
elim H; intros H1 H2; split.
 apply (dom_wd X F x y H1 H0).
clear H1.
elim H2; intros H1 H3; split.
 apply (dom_wd X G x y H1 H0).
intro H4; astepl (G x H1). auto.
Qed.

Definition Fdiv := Build_PartFunct X _ part_function_div_pred_wd
 (fun x Hx => F x (Prj1 Hx) [/] _[//]Ext2R x (Prj2 Hx)) part_function_div_strext.

End Part_Function_Div.

(**
%\begin{convention}% Let [R:X->CProp].
%\end{convention}%
*)

Variable R:X -> CProp.

Lemma included_FRecip : included R Q ->
 (forall x, R x -> forall Hx, G x Hx [#] Zero) -> included R (Dom Frecip).
intros H H0.
simpl in |- *.
unfold extend in |- *.
split.
apply H; assumption.
intros; apply H0; assumption.
Qed.

Lemma included_FRecip' : included R (Dom Frecip) -> included R Q.
intro H; simpl in H; eapply included_extend; apply H.
Qed.

Lemma included_FDiv : included R P -> included R Q ->
 (forall x, R x -> forall Hx, G x Hx [#] Zero) -> included R (Dom Fdiv).
intros HP HQ Hx.
simpl in |- *.
apply included_conj.
assumption.
unfold extend in |- *.
split.
apply HQ; assumption.
intros; apply Hx; assumption.
Qed.

Lemma included_FDiv' : included R (Dom Fdiv) -> included R P.
intro H; simpl in H; eapply included_conj_lft; apply H.
Qed.

Lemma included_FDiv'' : included R (Dom Fdiv) -> included R Q.
intro H; simpl in H; eapply included_extend; eapply included_conj_rht;
 apply H.
Qed.

End CField_Ops.

Implicit Arguments Frecip [X].
Notation "{1/} x" := (Frecip x) (at level 4, right associativity).

Implicit Arguments Fdiv [X].
Infix "{/}" := Fdiv (at level 41, no associativity).

Hint Resolve included_FRecip included_FDiv : included.

Hint Immediate included_FRecip' included_FDiv' included_FDiv'' : included.
