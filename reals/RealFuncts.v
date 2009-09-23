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

Require Export CReals1.

(**
* Continuity of Functions on Reals
*)

(* begin hide *)
Set Implicit Arguments.
Unset Strict Implicit.
(* end hide *)

Section Continuity.
Variable f : CSetoid_un_op IR.
Variable f2 : CSetoid_bin_op IR.

(**
Let [f] be a unary setoid operation on [IR] and
let [f2] be a binary setoid operation on [IR].

We use the following notations for intervals. [Intclr a b] for the
closed interval [[a,b]], [Intolr a b] for the
open interval [(a,b)], [Intcl a] for the
left-closed interval $[a,\infty)$#[a,&infin;)#, [Intol a] for the
left-open interval $(a,\infty)$#(a,&infin;)#, [Intcr b] for the
right-closed interval $(-\infty,b]$#(-&infin;,b]#.

Intervals like $[a,b]$#[a,b]# are defined for arbitrary reals [a,b] (being
$\emptyset$#&empty;# for [a [>] b]).
*)

Definition Intclr (a b x : IR) : Prop := a [<=] x /\ x [<=] b.

Definition Intolr (a b x : IR) : CProp := a [<] x and x [<] b.

Definition Intol (a x : IR) : CProp := a [<] x.

Definition Intcl (a x : IR) : Prop := a [<=] x.

Definition Intcr (b x : IR) : Prop := x [<=] b.

(** The limit of [f(x)] as [x] goes to [p = l], for both unary and binary
functions:

The limit of [f] in [p] is [l] if
[[
forall e [>] Zero, exists d [>] Zero, forall (x : IR)
( [--]d [<] p[-]x [<] d) -> ( [--]e [<] [--]f(x) [<] e)
]]
*)

Definition funLim (p l : IR) : CProp := forall e, Zero [<] e ->
  {d : IR | Zero [<] d | forall x, AbsSmall d (p[-]x) -> AbsSmall e (l[-]f x)}.

(** The definition of limit of [f] in [p] using Cauchy sequences. *)

Definition funLim_Cauchy (p l : IR) : CProp := forall s : CauchySeqR, Lim s [=] p ->
 forall e, Zero [<] e -> {N : nat | forall m, N <= m -> AbsSmall e (f (s m) [-]l)}.

(** The first definition implies the second one. *)

(*
 Ax_iom funLim_prop1 :(p,l:IR)(funLim p l)->(funLim_Cauchy p l).
Intros. Unfold funLim_Cauchy. Unfold funLim in H. Intros.
Elim (H e H1). Intros.
Elim s. Intros s_seq s_proof.
Decompose [and] H2.
Cut (Zero  [<]   x[/]TwoNZ).
Intro Hx2.
Elim (s_proof (x[/]TwoNZ) Hx2).
Intros N HN.
Exists N.
Intros.
Apply AbsSmall_minus.
Apply H5.
Generalize (HN m H3).
Intro HmN.
*)

(** The limit of [f] in [(p,p')] is [l] if
[[
forall e [>] Zero, exists d [>] Zero, forall (x : IR)
( [--]d [<] p[-]x [<] d) -> ( [--]d' [<] p'[-]y [<] d') -> ( [--]e [<] l[-]f(x,y) [<] e
]]
*)

Definition funLim2 (p p' l : IR) : CProp := forall e : IR, Zero [<] e -> {d : IR | Zero [<] d | forall x y,
  AbsSmall d (p[-]x) -> AbsSmall d (p'[-]y) -> AbsSmall e (l[-]f2 x y)}.

(** The function [f] is continuous at [p] if the limit of [f(x)] as
[x] goes to [p] is [f(p)].  This is the [eps [/] delta] definition.
We also give the definition with limits of Cauchy sequences.
*)

Definition continAt (p : IR) : CProp := funLim p (f p).

Definition continAtCauchy (p : IR) : CProp := funLim_Cauchy p (f p).

Definition continAt2 (p q : IR) : CProp := funLim2 p q (f2 p q).

(*
Ax_iom continAt_prop1 :(p:IR)(continAt p)->(continAtCauchy p).
*)

Definition contin : CProp := forall x : IR, continAt x.

Definition continCauchy : CProp := forall x : IR, continAtCauchy x.

Definition contin2 : CProp := forall x y : IR, continAt2 x y.

(**
Continuous on a closed, resp.%\% open, resp.%\% left open, resp.%\% left closed
interval *)

Definition continOnc a b : CProp := forall x, Intclr a b x -> continAt x.

Definition continOno a b : CProp := forall x, Intolr a b x -> continAt x.

Definition continOnol a : CProp := forall x, Intol a x -> continAt x.

Definition continOncl a : CProp := forall x, Intcl a x -> continAt x.

(*
Section Sequence_and_function_limits.

_**
If $\lim_{x->p} (f x) = l$, then for every sequence $p_n$ whose
limit is $p$, $\lim_{n->\infty} f (p_n) =l$.
 *_

Lemma funLim_SeqLimit:
  (p,l:IR)(fl:(funLim p l))
    (pn:nat->IR)(sl:(SeqLimit pn p)) (SeqLimit ( [n:nat] (f (pn n))) l).
Proof.
Intros; Unfold seqLimit.
Intros eps epos.
Elim (fl ? epos); Intros del dh; Elim dh; Intros H0 H1.
Elim (sl ? H0); Intros N Nh.
Exists N. Intros m leNm.
Apply AbsSmall_minus.
Apply H1.
Apply AbsSmall_minus.
Apply (Nh ? leNm).
Qed.

_**** Is the converse constructively provable? **
Lemma SeqLimit_funLim:
  (p,l:IR)((pn:nat->IR)(sl:(SeqLimit pn p)) (SeqLimit ( [n:nat] (f (pn n))) l))->
    (funLim p l).
****_

_**
Now the same Lemma in terms of Cauchy sequences: if $\lim_{x->p} (f x) = l$,
then for every Cauchy sequence $s_n$ whose
limit is $p$, $\lim_{n->\infty} f (s_n) =l$.
 *_

Ax_iom funLim_isCauchy:
  (p,l:IR)(funLim p l)->(s:CauchySeqR)((Lim s)  [=]   p)->
	(e:IR)(Zero  [<]  e)->(Ex [N:nat] (m:nat)(le N m)
			 ->(AbsSmall e ((s m) [-] (s N)))).

End Sequence_and_function_limits.

Section Monotonic_functions.

Definition str_monot  := (x,y:IR)(x  [<]  y)->((f x)  [<]  (f y)).

Definition str_monotOnc  := [a,b:IR]
         (x,y:IR)(Intclr a b x)->(Intclr a b y)
                ->(x  [<]  y)->((f x)  [<]  (f y)).

Definition str_monotOncl  := [a:IR]
         (x,y:IR)(Intcl a x)->(Intcl a y)
                ->(x  [<]  y)->((f x)  [<]  (f y)).

Definition str_monotOnol  := [a:IR]
         (x,y:IR)(Intol a x)->(Intol a y)
                ->(x  [<]  y)->((f x)  [<]  (f y)).

_** Following probably not needed for the FTA proof;
it stated that strong monotonicity on a closed interval implies that the
intermediate value theorem holds on this interval. For FTA we need IVT on
$[0,\infty>$.
*_

Ax_iom strmonc_imp_ivt :(a,b:IR)(str_monotOnc a b)
           ->(x,y:IR)(x  [<]  y)->(Intclr a b x)->(Intclr a b y)
               ->((f x)  [<]  Zero)->(Zero  [<]  (f y))
                   ->(EX z:IR | (Intclr x y z)/\((f z)  [=]  Zero)).
_**
$\forall c\in\RR (f\mbox{ strongly monotonic on }[c,\infty>)
\rightarrow \forall a,b\in\RR(c <a)\rightarrow( c< b)\rightarrow\ (f (a)<0)
\rightarrow\ (0:<f(b))
         \rightarrow \forall x,y\in\RR (a\leq x\leq b)\rightarrow
	(a\leq y\leq b)\rightarrow (x<y)
                \rightarrow \exists z\in\RR(x\leq z\leq y)\wedge(f(z)\noto 0))$
*_

Ax_iom strmon_ivt_prem : (c:IR)(str_monotOncl c)->
  (a,b:IR)(Intcl c a)->(Intcl c b)->((f a)  [<]   Zero)->(Zero   [<]  (f b))
       ->(x,y:IR)(Intclr a b x)->(Intclr a b y)->(x  [<]  y)
              ->(EX z:IR | (Intclr x y z)/\((f z)  [#]  Zero)).

_** The following is lemma 5.8 from the skeleton

$\forall c\in\RR (f\mbox{ strongly monotonic on }[c,\infty>)
\rightarrow \forall a,b\in\RR(a<b) \rightarrow(c <a)\rightarrow( c< b)
\rightarrow(f (a)<0)\rightarrow (0:<f(b))
         \rightarrow \exists z\in\RR(a\leq z\leq b)\wedge(f(z)= 0))$
*_

Ax_iom strmoncl_imp_ivt : (c:IR)(str_monotOncl c)
           ->(a,b:IR)(a  [<]  b)->(Intcl c a)->(Intcl c b)
               ->((f a)  [<]  Zero)->(Zero  [<]  (f b))
                   ->(EX z:IR | (Intclr a b z)/\ ((f z)  [=]  Zero)).
End Monotonic_functions.

*)
End Continuity.

(* begin hide *)
Set Strict Implicit.
Unset Implicit Arguments.
(* end hide *)
