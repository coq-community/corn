(* $Id$ *)

(** printing ['] %{'}% #'# *)

Require Export CFields.

(**
* Vector Spaces

Obsolete but maintained.
*)
Set Implicit Arguments.
Unset Strict Implicit.
Record VSpace (F : CField) : Type := 
  {vs_vs :> CGroup;
   vs_op : CSetoid_outer_op F vs_vs;
   vs_assoc :
    forall (a b : F) (v : vs_vs), vs_op (a[*]b) v[=]vs_op a (vs_op b v);
   vs_unit : forall v : vs_vs, vs_op One v[=]v;
   vs_distl :
    forall (a b : F) (v : vs_vs), vs_op (a[+]b) v[=]vs_op a v[+]vs_op b v;
   vs_distr :
    forall (a : F) (v u : vs_vs), vs_op a (v[+]u)[=]vs_op a v[+]vs_op a u}.
Set Strict Implicit.
Unset Implicit Arguments.

Hint Resolve vs_assoc vs_unit vs_distl vs_distr: algebra.

Implicit Arguments vs_op [F v].
Infix "[']" := vs_op (at level 30, no associativity).

(**
%\begin{convention}%
Let [F] be a fiels and let [V] be a vector space over [F]
%\end{convention}%
*)

Section VS_basics.
Variable F : CField.
Variable V : VSpace F.

Lemma vs_op_zero : forall a : F, a['](Zero:V)[=]Zero.
intros.
apply cg_cancel_lft with (a['](Zero:V)).
AStepl (a[']((Zero:V)[+]Zero)).
Step_final (a['](Zero:V)).
Qed.

Lemma zero_vs_op : forall v : V, Zero[']v[=]Zero.
intros.
apply cg_cancel_lft with (Zero[']v).
AStepl ((Zero[+]Zero)[']v).
Step_final (Zero[']v).
Qed.

Hint Resolve vs_op_zero zero_vs_op: algebra.

Lemma vs_op_inv_V : forall (x : F) (y : V), x['][--]y[=][--](x[']y).
intros.
apply cg_inv_unique.
AStepl (x['](y[+][--]y)).
Step_final (x['](Zero:V)).
Qed.

Lemma vs_op_inv_S : forall (x : F) (y : V), [--]x[']y[=][--](x[']y).
intros.
apply cg_inv_unique.
AStepl ((x[+][--]x)[']y).
Step_final (Zero[']y).
Qed.

Hint Resolve vs_op_inv_V vs_op_inv_S: algebra.

Lemma vs_inv_assoc :
 forall (a : F) (nz : a[#]Zero) (v : V), v[=]f_rcpcl a nz['](a[']v).
intros.
AStepl (One[']v).
Step_final ((f_rcpcl a nz[*]a)[']v).
Qed.
Hint Resolve vs_inv_assoc: algebra.


Lemma ap_zero_vs_op_l : forall (a : F) (v : V), a[']v[#]Zero -> a[#]Zero.
intros.
elim (csoo_strext _ _ (vs_op (F:=F) (v:=V)) a Zero v v).
auto.
intro contra; elim (ap_irreflexive _ _ contra).
AStepr (Zero:V). auto.
Qed.

Lemma ap_zero_vs_op_r : forall (a : F) (v : V), a[']v[#]Zero -> v[#]Zero.
intros.
elim (csoo_strext _ _ (vs_op (F:=F) (v:=V)) a a v Zero).
intro contra; elim (ap_irreflexive _ _ contra).
auto.
AStepr (Zero:V). auto.
Qed.

(* note this is the same proof as mult_resp_ap_zero *)
Lemma vs_op_resp_ap_rht :
 forall (a : F) (v u : V), a[#]Zero -> v[#]u -> a[']v[#]a[']u.
intros.
cut (f_rcpcl a X['](a[']v)[#]f_rcpcl a X['](a[']u)).
intros H1.
case (csoo_strext _ _ _ _ _ _ _ H1).
intro contra; elim (ap_irreflexive _ _ contra).
auto.
AStepr u.
AStepl v. auto.
Qed.

Lemma vs_op_resp_ap_zero :
 forall (a : F) (v : V), a[#]Zero -> v[#]Zero -> a[']v[#]Zero.
intros.
AStepr (a['](Zero:V)).
apply vs_op_resp_ap_rht; assumption.
Qed.

Lemma vs_op_resp_ap_lft :
 forall (a b : F) (v : V), a[#]b -> v[#]Zero -> a[']v[#]b[']v.
intros.
apply zero_minus_apart.
AStepl ((a[-]b)[']v).
apply vs_op_resp_ap_zero; [ idtac | assumption ].
apply minus_ap_zero; assumption.
unfold cg_minus in |- *. Step_final (a[']v[+][--]b[']v).
Qed.

End VS_basics.
Hint Resolve vs_op_zero zero_vs_op: algebra.