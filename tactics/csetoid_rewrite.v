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

(** 200904: first experimental version submitted to corn;
things need to be improved and cleaned up!; hendriks@cs.ru.nl *)
(*
110204: renamed setoid_rewrite into csetoid_rewrite
in order to avoid name clashes with setoid_rewrite
in Coq's initial environment.
*)

Ltac typeof x := type of x.
  (* Quickly secure "type of" before the following Require brings in ssreflect which destroys it. *)

Require Export CSetoidFun.

Section move_us.

Lemma csr_wd :
 forall (S:CSetoid) (R:CSetoid_relation S) (x1 x2 y1 y2:S),
   R x1 x2 -> (x1[=]y1) -> (x2[=]y2) -> R y1 y2.
Proof
 fun S R x1 x2 y1 y2 h h0 h1 => csr_wdl S R x1 y2 y1 (csr_wdr S R x1 x2 y2 h h1) h0.

Lemma Ccsr_wd :
 forall (S:CSetoid) (R:CCSetoid_relation S) (x1 x2 y1 y2:S),
   R x1 x2 -> (x1[=]y1) -> (x2[=]y2) -> R y1 y2.
Proof
 fun S R x1 x2 y1 y2 h h0 h1 => Ccsr_wdl S R x1 y2 y1 (Ccsr_wdr S R x1 x2 y2 h h1) h0.

Lemma eq_wd :
 forall (S:CSetoid) (x1 x2 y1 y2:S),
   (x1[=]x2) -> (x1[=]y1) -> (x2[=]y2) -> y1[=]y2.
Proof
 fun S x1 x2 y1 y2 h h0 h1 => eq_transitive S y1 x1 y2 (eq_symmetric S x1 y1 h0)
   (eq_transitive S x1 x2 y2 h h1).

Lemma ap_wd :
 forall (S:CSetoid) (x1 x2 y1 y2:S),
   (x1[#]x2) -> (x1[=]y1) -> (x2[=]y2) -> y1[#]y2.
Proof
 fun S x1 x2 y1 y2 h h0 h1 => ap_wdl S x1 y2 y1 (ap_wdr S x1 x2 y2 h h1) h0.

Lemma CAnd_proj1 : forall A B:CProp, A and B -> A.
Proof.
 intros A B h; elim h; exact (fun a _ => a).
Qed.

Lemma CAnd_proj2 : forall A B:CProp, A and B -> B.
Proof.
 intros A B h; elim h; exact (fun _ b => b).
Qed.

Lemma COr_elim : forall A B C:CProp, (A -> C) -> (B -> C) -> A or B -> C.
Proof.
 intros A B C H H0 H1.
 elim H1; intro H2; [ exact (H H2) | exact (H0 H2) ].
Qed.

End move_us.

(** Definition of [csetoid_rewrite]: a rewrite tactic for setoid equality;
it rewrites within formulae of type [Prop] and [CProp], built up from
connectives [->], [and], [CAnd], [or], [COr], [iff], [Iff], [not], [Not],
[CNot], and atomic formulae [(P t)], [(R t s)], [t[=]s], [t[#]s] for
[T:CSetoid], [t,s:T], [P:(CSetoid_predicate T)], [R:(CSetoid_relation T)],
[R:(CCSetoid_relation T)]. Note that atoms are built up from predicates and
relations that are well-defined with respect to setoid equality.

Setoid terms of type [T] are terms constructed by [(f s)], [(g s s')],
[(h s s_)], where [f:(CSetoid_fun S T)], [g:(CSetoid_bin_fun S S' T)],
[h:(CSetoid_part_fun S T)], [s:S], [s':S'], [s_:(cspf_dom S T f s)];
needless to say, those setoid functions respect setoid equality.

Tactic [csetoid_rewrite] is composed of tactics [total_csetoid_rewrite] and
[partial_csetoid_rewrite]. The former is applied in case there are no partial
setoid functions present in the goal. The latter if there are. We further
explain this separation.

To define the rewrite tactic we use the method of reflection, see [1].
Because we have to deal with partial functions (see the definition of
[CSetoid_part_fun] in file [CSetoids.v]), we use %\emph{partial}%
#<em>partial</em># reflection, see [2]. Partial reflection means to have an
interpretation %\emph{relation}%#<em>relation</em># instead of an
interpretation function.

Unfortunately, we were unable to define our tactic for the most general case,
that is, for terms that contain both partial functions as well as setoid
functions whose domain(s) and co-domain are not necessarily the same.
When proving lemmas involving statements [e II^r t] (saying [t] is an
interpretation of syntactic expression [e] under the variable assigment [r],
one often needs to reason by induction over [e] and then inverting the so
obtained instances of the inductively defined [e II^rho t]. However, in the
general case where we have to deal with functions whose domain and co-domain
differ, inversion doesn't yield the desired result. Consider, for instance,
[var II^r t]. Here, we want to perform inversion and obtain [t=r], for
[var II^r r] is a defining clause of [II] and moreover the only one mentioning
[var]. However, inversion returns somthing like [<p,t> = <p,r>].
This has got to do with the so-called elimination predicate which predicts
the type of the outcome of a case analysis dependent on the destructed
variable. For more info ask the author and see his related
#<a href="http://pauillac.inria.fr/pipermail/coq-club/2003/001127.html">
mail</a># to the coq-club.

We opted for the next best option of using two tactics, one using total
reflection, its application being restricted to terms constructed
from total functions (domain(s) and co-domain are allowed to be distinct).
The other using partial reflection, its application being restricted to
terms built up from (partial as well as total) %\emph{operations}%
#<em>operations</em># (i.e.%\% functions whose domain(s) and co-domain are
equal).

References:

[1] Boutin, "Using Reflection to Build Efficient and Certified Decision
Procedures", TACS, LNCS 1281, pp.%\% 515--529, 1997.

[2] Geuvers, Wiedijk and Zwanenburg, "Equational Reasoning via Partial
Reflection", TPHOLs, LNCS 1896, pp.%\% 162--178, 2000.
*)

(*Section total_csetoid_rewrite.*)

Section syntactic_total_setoid_expressions.

(** Syntactic setoid expressions reflecting setoid terms built from total
setoid functions. [S] is the setoid of the subterm to be replaced. *)

Inductive tot_set_exp (S:CSetoid) : CSetoid -> Type :=
  | tse_var : tot_set_exp S S
  | tse_fun :
      forall T1 T2:CSetoid,
        CSetoid_fun T1 T2 -> tot_set_exp S T1 -> tot_set_exp S T2
  | tse_bfun :
      forall T1 T2 T3:CSetoid,
        CSetoid_bin_fun T1 T2 T3 ->
        tot_set_exp S T1 -> tot_set_exp S T2 -> tot_set_exp S T3
  | tse_con : forall T:CSetoid, T -> tot_set_exp S T.

(** Interpretation of `total' setoid expressions. *)

Fixpoint tse_int (S T:CSetoid) (r:S) (e:tot_set_exp S T) {struct e} : T :=
  match e with
  | tse_var => r
  | tse_fun T1 T2 f e0 => f (tse_int S T1 r e0)
  | tse_bfun T1 T2 T3 f e1 e2 => f (tse_int S T1 r e1) (tse_int S T2 r e2)
  | tse_con T t => t
  end.

(** [tse_int] is well-defined. *)

Lemma tse_int_wd :
 forall (S T:CSetoid) (r1 r2:S),
   (r1[=]r2) -> forall e:tot_set_exp S T, tse_int S T r1 e[=]tse_int S T r2 e.
Proof.
 intros S T r1 r2 h.
 induction e; simpl in |- *.
    exact h.
   apply csf_wd; assumption.
  apply csbf_wd; assumption.
 apply eq_reflexive.
Qed.

End syntactic_total_setoid_expressions.

(** The `quote function' maps setoid terms [t:T] to syntactic expressions
[(tot_set_exp S T)]; term [r:S] (supposed to be a subterm of [t:T] to be
replaced later on) is mapped to [(tse_var r)]. Other `leafs' [t0:T'] of [t]
are mapped to [(tse_con S T' t0)]. *)

Ltac tse_quote S T r t :=
  match constr:t with
  | r => constr:(tse_var S)
  | (csf_fun ?X1 ?X2 ?X3 ?X4) =>
      let T1 := constr:X1
      with T2 := constr:X2
      with f := constr:X3
      with t0 := constr:X4 in
      let e := tse_quote S T1 r t0 in
      constr:(tse_fun S T1 T2 f e)
  | (csbf_fun ?X1 ?X2 ?X3 ?X4 ?X5 ?X6) =>
      let T1 := constr:X1
      with T2 := constr:X2
      with T3 := constr:X3
      with f := constr:X4
      with t1 := constr:X5
      with t2 := constr:X6 in
      let e1 := tse_quote S T1 r t1 with e2 := tse_quote S T2 r t2 in
      constr:(tse_bfun S T1 T2 T3 f e1 e2)
  | ?X1 => let t0 := constr:X1 in
           constr:(tse_con S T t0)
  end.

(** Given [S:CSetoid;r1,r2:S] and [A:Prop] or [A:CProp],
[(replace_in_formula1 S r1 r2 A)]
replaces all occurrences of subterm [r1] in [A] by [r2]. *)

Ltac tot_repl_in_form S r1 r2 A :=
  match constr:A with
  | (csp_pred ?X1 ?X2 ?X3) =>
      let T := constr:X1 with P := constr:X2 with t := constr:X3 in
      let e := tse_quote S T r1 t in
      let r := constr:(tse_int S T r2 e) in
      constr:(P r)
  | (csr_rel ?X1 ?X2 ?X3 ?X4) =>
      let T := constr:X1
      with R := constr:X2
      with t1 := constr:X3
      with t2 := constr:X4 in
      let e1 := tse_quote S T r1 t1 with e2 := tse_quote S T r1 t2 in
      let r1 := constr:(tse_int S T r2 e1)
      with r2 := constr:(tse_int S T r2 e2) in
      constr:(R r1 r2)
  | (Ccsr_rel ?X1 ?X2 ?X3 ?X4) =>
      let T := constr:X1
      with R := constr:X2
      with t1 := constr:X3
      with t2 := constr:X4 in
      let e1 := tse_quote S T r1 t1 with e2 := tse_quote S T r1 t2 in
      let r1 := constr:(tse_int S T r2 e1)
      with r2 := constr:(tse_int S T r2 e2) in
      constr:(R r1 r2)
  | (cs_eq (r:=(cs_crr ?X1)) ?X2 ?X3) =>
      let T := constr:X1 with t1 := constr:X2 with t2 := constr:X3 in
      let e1 := tse_quote S T r1 t1 with e2 := tse_quote S T r1 t2 in
      let r1 := constr:(tse_int S T r2 e1)
      with r2 := constr:(tse_int S T r2 e2) in
      constr:(cs_eq (r:=T) r1 r2)
  | (cs_ap (c:=?X1) ?X2 ?X3) =>
      let T := constr:X1 with t1 := constr:X2 with t2 := constr:X3 in
      let e1 := tse_quote S T r1 t1 with e2 := tse_quote S T r1 t2 in
      let r1 := constr:(tse_int S T r2 e1)
      with r2 := constr:(tse_int S T r2 e2) in
      constr:(cs_ap (c:=T) r1 r2)
  | (?X1 -> ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let B1 := tot_repl_in_form S r1 r2 A1
      with B2 := tot_repl_in_form S r1 r2 A2 in
      constr:(B1 -> B2)
  | (?X1 /\ ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let B1 := tot_repl_in_form S r1 r2 A1
      with B2 := tot_repl_in_form S r1 r2 A2 in
      constr:(B1 /\ B2)
  | (?X1 and ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let B1 := tot_repl_in_form S r1 r2 A1
      with B2 := tot_repl_in_form S r1 r2 A2 in
      constr:(B1 and B2)
  | (?X1 \/ ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let B1 := tot_repl_in_form S r1 r2 A1
      with B2 := tot_repl_in_form S r1 r2 A2 in
      constr:(B1 \/ B2)
  | (?X1 or ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let B1 := tot_repl_in_form S r1 r2 A1
      with B2 := tot_repl_in_form S r1 r2 A2 in
      constr:(B1 or B2)
  | (?X1 <-> ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let B1 := tot_repl_in_form S r1 r2 A1
      with B2 := tot_repl_in_form S r1 r2 A2 in
      constr:(B1 <-> B2)
  | (Iff ?X1 ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let B1 := tot_repl_in_form S r1 r2 A1
      with B2 := tot_repl_in_form S r1 r2 A2 in
      constr:(Iff B1 B2)
  | (~ ?X1) =>
      let A0 := constr:X1 in
      let B0 := tot_repl_in_form S r1 r2 A0 in
      constr:(~ B0)
  | (Not ?X1) =>
      let A0 := constr:X1 in
      let B0 := tot_repl_in_form S r1 r2 A0 in
      constr:(Not B0)
(*  | (CNot ?X1) =>
      let A0 := constr:X1 in
      let B0 := tot_repl_in_form S r1 r2 A0 in
      constr:(CNot B0)*)
  | ?X1 => let A0 := constr:X1 in
           constr:A0
  end.

(**
Given [S:CSetoid;r1,r2:S;h:r1[=]r2;h0:r2[=]r1] and [A:CProp] or [A:Prop],
we get [(tot_set_rewr_prf1 S r1 r2 h h0 A) : A->A[r1:=r2]] and
[(tot_set_rewr_prf2 S r1 r2 h h0 A) : A[r1:=r2]->A] where [A[r1:=r2]] denotes
[(tot_repl_in_form S r1 r2 A)]. The argument [h0:r2[=]r1] is present to avoid
iterated application of [eq_symmetric].
*)

Ltac tot_set_rewr_prf1 S r1 r2 h h0 A :=
  match constr:A with
  | (csp_pred ?X1 ?X2 ?X3) =>
      let T := constr:X1 with P := constr:X2 with t := constr:X3 in
      let e := tse_quote S T r1 t in
      let s := constr:(tse_int S T r1 e)
      with r := constr:(tse_int S T r2 e)
      with d := constr:(tse_int_wd S T r1 r2 h e) in
      constr:(fun a:P s => csp_wd T P s r a d)
  | (csr_rel ?X1 ?X2 ?X3 ?X4) =>
      let T := constr:X1
      with R := constr:X2
      with t1 := constr:X3
      with t2 := constr:X4 in
      let e1 := tse_quote S T r1 t1 with e2 := tse_quote S T r1 t2 in
      let s1 := constr:(tse_int S T r1 e1)
      with s2 := constr:(tse_int S T r1 e2)
      with r1 := constr:(tse_int S T r2 e1)
      with r2 := constr:(tse_int S T r2 e2)
      with d1 := constr:(tse_int_wd S T r1 r2 h e1)
      with d2 := constr:(tse_int_wd S T r1 r2 h e2) in
      constr:(fun a:R s1 s2 => csr_wd T R s1 s2 r1 r2 a d1 d2)
  | (Ccsr_rel ?X1 ?X2 ?X3 ?X4) =>
      let T := constr:X1
      with R := constr:X2
      with t1 := constr:X3
      with t2 := constr:X4 in
      let e1 := tse_quote S T r1 t1 with e2 := tse_quote S T r1 t2 in
      let s1 := constr:(tse_int S T r1 e1)
      with s2 := constr:(tse_int S T r1 e2)
      with r1 := constr:(tse_int S T r2 e1)
      with r2 := constr:(tse_int S T r2 e2)
      with d1 := constr:(tse_int_wd S T r1 r2 h e1)
      with d2 := constr:(tse_int_wd S T r1 r2 h e2) in
      constr:(fun a:R s1 s2 => Ccsr_wd T R s1 s2 r1 r2 a d1 d2)
  | (cs_eq (r:=(cs_crr ?X1)) ?X2 ?X3) =>
      let T := constr:X1 with t1 := constr:X2 with t2 := constr:X3 in
      let e1 := tse_quote S T r1 t1 with e2 := tse_quote S T r1 t2 in
      let s1 := constr:(tse_int S T r1 e1)
      with s2 := constr:(tse_int S T r1 e2)
      with r1 := constr:(tse_int S T r2 e1)
      with r2 := constr:(tse_int S T r2 e2)
      with d1 := constr:(tse_int_wd S T r1 r2 h e1)
      with d2 := constr:(tse_int_wd S T r1 r2 h e2) in
      constr:(fun a:cs_eq (r:=T) s1 s2 => eq_wd T s1 s2 r1 r2 a d1 d2)
  | (cs_ap (c:=?X1) ?X2 ?X3) =>
      let T := constr:X1 with t1 := constr:X2 with t2 := constr:X3 in
      let e1 := tse_quote S T r1 t1 with e2 := tse_quote S T r1 t2 in
      let s1 := constr:(tse_int S T r1 e1)
      with s2 := constr:(tse_int S T r1 e2)
      with r1 := constr:(tse_int S T r2 e1)
      with r2 := constr:(tse_int S T r2 e2)
      with d1 := constr:(tse_int_wd S T r1 r2 h e1)
      with d2 := constr:(tse_int_wd S T r1 r2 h e2) in
      constr:(fun a:cs_ap (c:=T) s1 s2 => ap_wd T s1 s2 r1 r2 a d1 d2)
  | (?X1 -> ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let d1 := tot_set_rewr_prf1 S r1 r2 h h0 A2
      with d2 := tot_set_rewr_prf2 S r1 r2 h h0 A1 in
      constr:(fun (p:A1 -> A2) b => d1 (p (d2 b)))
  | (?X1 /\ ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let d1 := tot_set_rewr_prf1 S r1 r2 h h0 A1
      with d2 := tot_set_rewr_prf1 S r1 r2 h h0 A2 in
      constr:(fun p:A1 /\ A2 => conj (d1 (fst p)) (d2 (snd p)))
  | (?X1 and ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let d1 := tot_set_rewr_prf1 S r1 r2 h h0 A1
      with d2 := tot_set_rewr_prf1 S r1 r2 h h0 A2 in
      constr:(fun p:A1 and A2 =>
                pair _ _ (d1 (CAnd_proj1 _ _ p))
                  (d2 (CAnd_proj2 _ _ p)))
  | (?X1 \/ ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let d1 := tot_set_rewr_prf1 S r1 r2 h h0 A1
      with d2 := tot_set_rewr_prf1 S r1 r2 h h0 A2 in
      constr:(or_ind (fun a => or_introl _ (d1 a))
                (fun a => or_intror _ (d2 a)))
  | (?X1 or ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let d1 := tot_set_rewr_prf1 S r1 r2 h h0 A1
      with d2 := tot_set_rewr_prf1 S r1 r2 h h0 A2 in
      constr:(COr_elim A1 A2 _ (fun a => inl _ _ (d1 a))
                (fun a => inr _ _ (d2 a)))
  | (?X1 <-> ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let ab1 := tot_set_rewr_prf1 S r1 r2 h h0 A1
      with ab2 := tot_set_rewr_prf1 S r1 r2 h h0 A2
      with ba1 := tot_set_rewr_prf2 S r1 r2 h h0 A1
      with ba2 := tot_set_rewr_prf2 S r1 r2 h h0 A2 in
      constr:(fun p:A1 <-> A2 =>
                conj (fun b1 => ab2 (fst p (ba1 b1)))
                  (fun b2 => ab1 (snd p (ba2 b2))))
  | (Iff ?X1 ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let ab1 := tot_set_rewr_prf1 S r1 r2 h h0 A1
      with ab2 := tot_set_rewr_prf1 S r1 r2 h h0 A2
      with ba1 := tot_set_rewr_prf2 S r1 r2 h h0 A1
      with ba2 := tot_set_rewr_prf2 S r1 r2 h h0 A2 in
      constr:(fun p:Iff A1 A2 =>
                pair (fun b1 => ab2 (CAnd_proj1 _ _ p (ba1 b1)))
                  (fun b2 => ab1 (CAnd_proj2 _ _ p (ba2 b2))))
  | (~ ?X1) =>
      let A0 := constr:X1 in
      let d := tot_set_rewr_prf2 S r1 r2 h h0 A0 in
      constr:(fun (p:~ A0) b => p (d b))
  | (Not ?X1) =>
      let A0 := constr:X1 in
      let d := tot_set_rewr_prf2 S r1 r2 h h0 A0 in
      constr:(fun (p:Not A0) b => p (d b))
(*   | (CNot ?X1) =>
      let A0 := constr:X1 in
      let d := tot_set_rewr_prf2 S r1 r2 h h0 A0 in
      constr:(fun (p:CNot A0) b => p (d b)) *)
  | ?X1 => let A0 := constr:X1 in
           constr:(fun a:A0 => a)
  end
 with tot_set_rewr_prf2 S r1 r2 h h0 A :=
  match constr:A with
  | (csp_pred ?X1 ?X2 ?X3) =>
      let T := constr:X1 with P := constr:X2 with t := constr:X3 in
      let e := tse_quote S T r1 t in
      let s := constr:(tse_int S T r1 e)
      with r := constr:(tse_int S T r2 e)
      with d := constr:(tse_int_wd S T r2 r1 h0 e) in
      constr:(fun b:P r => csp_wd T P r s b d)
  | (csr_rel ?X1 ?X2 ?X3 ?X4) =>
      let T := constr:X1
      with R := constr:X2
      with t1 := constr:X3
      with t2 := constr:X4 in
      let e1 := tse_quote S T r1 t1 with e2 := tse_quote S T r1 t2 in
      let s1 := constr:(tse_int S T r1 e1)
      with s2 := constr:(tse_int S T r1 e2)
      with r1 := constr:(tse_int S T r2 e1)
      with r2 := constr:(tse_int S T r2 e2)
      with d1 := constr:(tse_int_wd S T r2 r1 h0 e1)
      with d2 := constr:(tse_int_wd S T r2 r1 h0 e2) in
      constr:(fun b:R r1 r2 => csr_wd T R r1 r2 s1 s2 b d1 d2)
  | (Ccsr_rel ?X1 ?X2 ?X3 ?X4) =>
      let T := constr:X1
      with R := constr:X2
      with t1 := constr:X3
      with t2 := constr:X4 in
      let e1 := tse_quote S T r1 t1 with e2 := tse_quote S T r1 t2 in
      let s1 := constr:(tse_int S T r1 e1)
      with s2 := constr:(tse_int S T r1 e2)
      with r1 := constr:(tse_int S T r2 e1)
      with r2 := constr:(tse_int S T r2 e2)
      with d1 := constr:(tse_int_wd S T r2 r1 h0 e1)
      with d2 := constr:(tse_int_wd S T r2 r1 h0 e2) in
      constr:(fun b:R r1 r2 => Ccsr_wd T R r1 r2 s1 s2 b d1 d2)
  | (cs_eq (r:=(cs_crr ?X1)) ?X2 ?X3) =>
      let T := constr:X1 with t1 := constr:X2 with t2 := constr:X3 in
      let e1 := tse_quote S T r1 t1 with e2 := tse_quote S T r1 t2 in
      let s1 := constr:(tse_int S T r1 e1)
      with s2 := constr:(tse_int S T r1 e2)
      with r1 := constr:(tse_int S T r2 e1)
      with r2 := constr:(tse_int S T r2 e2)
      with d1 := constr:(tse_int_wd S T r2 r1 h0 e1)
      with d2 := constr:(tse_int_wd S T r2 r1 h0 e2) in
      constr:(fun b:cs_eq (r:=T) r1 r2 => eq_wd T r1 r2 s1 s2 b d1 d2)
  | (cs_ap (c:=?X1) ?X2 ?X3) =>
      let T := constr:X1 with t1 := constr:X2 with t2 := constr:X3 in
      let e1 := tse_quote S T r1 t1 with e2 := tse_quote S T r1 t2 in
      let s1 := constr:(tse_int S T r1 e1)
      with s2 := constr:(tse_int S T r1 e2)
      with r1 := constr:(tse_int S T r2 e1)
      with r2 := constr:(tse_int S T r2 e2)
      with d1 := constr:(tse_int_wd S T r2 r1 h0 e1)
      with d2 := constr:(tse_int_wd S T r2 r1 h0 e2) in
      constr:(fun b:cs_ap (c:=T) r1 r2 => ap_wd T r1 r2 s1 s2 b d1 d2)
  | (?X1 -> ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let d1 := tot_set_rewr_prf1 S r1 r2 h h0 A1
      with d2 := tot_set_rewr_prf2 S r1 r2 h h0 A2 in
      constr:(fun q (a:A1) => d2 (q (d1 a)))
  | (?X1 /\ ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let d1 := tot_set_rewr_prf2 S r1 r2 h h0 A1
      with d2 := tot_set_rewr_prf2 S r1 r2 h h0 A2 in
      constr:(fun q:_ /\ _ => conj (d1 (fst q)) (d2 (snd q)))
  | (?X1 and ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let d1 := tot_set_rewr_prf2 S r1 r2 h h0 A1
      with d2 := tot_set_rewr_prf2 S r1 r2 h h0 A2 in
      constr:(fun q:_ and _ =>
                @pair A1 A2 (d1 (CAnd_proj1 _ _ q))
                  (d2 (CAnd_proj2 _ _ q)))
  | (?X1 \/ ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let d1 := tot_set_rewr_prf2 S r1 r2 h h0 A1
      with d2 := tot_set_rewr_prf2 S r1 r2 h h0 A2 in
      constr:(or_ind (fun b => or_introl A2 (d1 b))
                (fun b => or_intror A1 (d2 b)))
  | (?X1 or ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let d1 := tot_set_rewr_prf2 S r1 r2 h h0 A1
      with d2 := tot_set_rewr_prf2 S r1 r2 h h0 A2 in
      constr:(COr_elim _ _ (A1 or A2) (fun b => inl A1 A2 (d1 b))
                (fun b => inr A1 A2 (d2 b)))
  | (?X1 <-> ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let ab1 := tot_set_rewr_prf1 S r1 r2 h h0 A1
      with ab2 := tot_set_rewr_prf1 S r1 r2 h h0 A2
      with ba1 := tot_set_rewr_prf2 S r1 r2 h h0 A1
      with ba2 := tot_set_rewr_prf2 S r1 r2 h h0 A2 in
      constr:(fun q:_ <-> _ =>
                conj (fun a1:A1 => ba2 (fst q (ab1 a1)))
                  (fun a2:A2 => ba1 (snd q (ab2 a2))))
  | (Iff ?X1 ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let ab1 := tot_set_rewr_prf1 S r1 r2 h h0 A1
      with ab2 := tot_set_rewr_prf1 S r1 r2 h h0 A2
      with ba1 := tot_set_rewr_prf2 S r1 r2 h h0 A1
      with ba2 := tot_set_rewr_prf2 S r1 r2 h h0 A2 in
      constr:(fun q:Iff _ _ =>
                pair (fun a1:A1 => ba2 (CAnd_proj1 _ _ q (ab1 a1)))
                  (fun a2:A2 => ba1 (CAnd_proj2 _ _ q (ab2 a2))))
  | (~ ?X1) =>
      let A0 := constr:X1 in
      let d := tot_set_rewr_prf1 S r1 r2 h h0 A0 in
      constr:(fun (q:~ _) (a:A0) => q (d a))
  | (Not ?X1) =>
      let A0 := constr:X1 in
      let d := tot_set_rewr_prf1 S r1 r2 h h0 A0 in
      constr:(fun (q:Not _) (a:A0) => q (d a))
(*   | (CNot ?X1) =>
      let A0 := constr:X1 in
      let d := tot_set_rewr_prf1 S r1 r2 h h0 A0 in
      constr:(fun (q:CNot _) (a:A0) => q (d a))*)
  | ?X1 => let A0 := constr:X1 in
           constr:(fun a:A0 => a)
  end.

(* rewrite -> h *)
Ltac total_csetoid_rewrite h :=
  let type_of_h := typeof h in
  match constr:type_of_h with
  | (cs_eq (r:=(cs_crr ?X1)) ?X2 ?X3) =>
      let S := constr:X1 with r1 := constr:X2 with r2 := constr:X3 in
      let h0 := constr:(eq_symmetric S r1 r2 h) in
      match goal with
      |  |- ?X1 =>
          let A := constr:X1 in
          let B := tot_repl_in_form S r1 r2 A
          with d := tot_set_rewr_prf2 S r1 r2 h h0 A in
          ((*:B->A*) cut B; [ exact d | unfold tse_int in |- * ])
      end
  end.

(* rewrite <- h *)
Ltac total_csetoid_rewrite_rev h :=
  let type_of_h := typeof h in
  match constr:type_of_h with
  | (cs_eq (r:=(cs_crr ?X1)) ?X2 ?X3) =>
      let S := constr:X1 with r2 := constr:X2 with r1 := constr:X3 in
      let h0 := constr:(eq_symmetric S r2 r1 h) in
      match goal with
      |  |- ?X1 =>
          let A := constr:X1 in
          let B := tot_repl_in_form S r1 r2 A
          with d := tot_set_rewr_prf2 S r1 r2 h0 h A in
          ((*:B->A*) cut B; [ exact d | unfold tse_int in |- * ])
      end
  end.

(* rewrite -> h in h0 *)
Ltac total_csetoid_rewrite_cxt h h0 :=
  let type_of_h := typeof h in
  match constr:type_of_h with
  | (cs_eq (r:=(cs_crr ?X1)) ?X2 ?X3) =>
      let S := constr:X1 with r1 := constr:X2 with r2 := constr:X3 in
      let h1 := constr:(eq_symmetric S r1 r2 h) with A := typeof h0 in
      let B := tot_repl_in_form S r1 r2 A
      with d := tot_set_rewr_prf1 S r1 r2 h h1 A in
      ((*:A->B*) cut B;
        [ unfold tse_int in |- *; clear h0; intro h0 | exact (d h0) ])
  end.

(* rewrite <- h in h0 *)
Ltac total_csetoid_rewrite_cxt_rev h h0 :=
  let type_of_h := typeof h in
  match constr:type_of_h with
  | (cs_eq (r:=(cs_crr ?X1)) ?X2 ?X3) =>
      let S := constr:X1 with r2 := constr:X2 with r1 := constr:X3 in
      let h1 := constr:(eq_symmetric S r2 r1 h) with A := typeof h0 in
      let B := tot_repl_in_form S r1 r2 A
      with d := tot_set_rewr_prf1 S r1 r2 h1 h A in
      ((*:A->B*) cut B;
        [ unfold tse_int in |- *; clear h0; intro h0 | exact (d h0) ])
  end.

(* replace x with y *)
Ltac total_setoid_replace x y :=
  let h := fresh in
  (cut (x[=]y); [ intro h; total_csetoid_rewrite h; clear h | idtac ]).

(* replace x with y in h *)
Ltac total_setoid_replace_cxt x y h :=
  let h0 := fresh in
  (cut (x[=]y); [ intro h0; total_csetoid_rewrite_cxt h0 h; clear h0 | idtac ]).

(*End total_csetoid_rewrite.*)

(*Section partial_csetoid_rewrite.*)

(* tbd: new CSetoids.v: *)

Definition CSetoid_part_op := PartFunct.
Definition cspf_dom (T _:CSetoid) := pfdom T.
Definition cspf_dom_wd (T _:CSetoid) := dom_wd T.
Definition cspf_wd (T:CSetoid) := pfwdef T.

(* to avoid universe inconsistencies (tbd: explain *)

Inductive my_sigT (A:Type) (P:A -> Type) : Type :=
    my_existT : forall x:A, P x -> my_sigT A P.

Definition proj1_my_sigT (A:Type) (P:A -> Type) (e:my_sigT A P) :=
  match e with
  | my_existT a b => a
  end.

Definition proj2_my_sigT (A:Type) (P:A -> Type) (e:my_sigT A P) :=
  match e return P (proj1_my_sigT A P e) with
  | my_existT a b => b
  end.

Set Implicit Arguments.
Unset Strict Implicit.

Section syntactic_partial_setoid_expressions.

Variable T : CSetoid.

Inductive part_set_exp : Type :=
  | pse_var : part_set_exp
  | pse_uop : CSetoid_un_op T -> part_set_exp -> part_set_exp
  | pse_bop :
      CSetoid_bin_op T -> part_set_exp -> part_set_exp -> part_set_exp
  | pse_pop : CSetoid_part_op T -> part_set_exp -> part_set_exp
  | pse_con : T -> part_set_exp.

(** Interpretation as a relation between syntactic expressions and
(semantical) setoid terms; [r] is the term to be replaced (later on). *)

Variable r : T.

Inductive pse_int : part_set_exp -> T -> Type :=
  | pse_int_var : pse_int pse_var r
  | pse_int_uop :
      forall (F:CSetoid_un_op T) (e:part_set_exp) (t:T),
        pse_int e t -> pse_int (pse_uop F e) (F t)
  | pse_int_bop :
      forall (F:CSetoid_bin_op T) (e1 e2:part_set_exp)
        (t1 t2:T),
        pse_int e1 t1 -> pse_int e2 t2 -> pse_int (pse_bop F e1 e2) (F t1 t2)
  | pse_int_pop :
      forall (F:CSetoid_part_op T) (e:part_set_exp)
        (t:T),
        pse_int e t ->
        forall Ht:cspf_dom T T F t, pse_int (pse_pop F e) (F t Ht)
  | pse_int_con : forall t:T, pse_int (pse_con t) t.

(** `Heavy' syntactic expressions, carrying their own interpretation. *)

Inductive part_set_xexp : T -> Type :=
  | psxe_var : part_set_xexp r
  | psxe_uop :
      forall (F:CSetoid_un_op T) (t:T),
        part_set_xexp t -> part_set_xexp (F t)
  | psxe_bop :
      forall (F:CSetoid_bin_op T) (t1 t2:T),
        part_set_xexp t1 -> part_set_xexp t2 -> part_set_xexp (F t1 t2)
  | psxe_pop :
      forall (F:CSetoid_part_op T) (t:T) (Ht:cspf_dom T T F t),
        part_set_xexp t -> part_set_xexp (F t Ht)
  | psxe_con : forall t:T, part_set_xexp t.

(** Interpretation of proof loaded (`heavy') syntactic expressions;
extracts the semantical component from heavy expressions. *)

Definition psxe_int t (_:part_set_xexp t) := t.

(** The forgetful mapping from heavy to light syntactic expressions;
extracts the syntactical component from heavy expressions. *)

Fixpoint forget (t:T) (e:part_set_xexp t) {struct e} : part_set_exp :=
  match e with
  | psxe_var => pse_var
  | psxe_uop F t0 e0 => pse_uop F (forget e0)
  | psxe_bop F t1 t2 e1 e2 => pse_bop F (forget e1) (forget e2)
  | psxe_pop F t0 H e0 => pse_pop F (forget e0)
  | psxe_con t => pse_con t
  end.

(** The second extraction of an heavy expression is an interpretation
of its first extraction (note [(xexp_int t e)=t]). *)

Lemma extract_correct :
 forall (t:T) (e:part_set_xexp t), pse_int (forget e) t.
Proof.
 simple induction e; clear e t; simpl in |- *.
     exact pse_int_var.
    intros F t e h.
    apply pse_int_uop; exact h.
   intros F t1 t2 e1 h1 e2 h2.
   apply pse_int_bop with (1 := h1) (2 := h2).
  intros F t Ht e h.
  apply pse_int_pop; exact h.
 exact pse_int_con.
Defined.

Lemma pse_int_var_inv : forall t:T, pse_int pse_var t -> t = r.
Proof.
 intros t h; inversion h; reflexivity.
Defined.

Lemma pse_int_con_inv : forall c t:T, pse_int (pse_con c) t -> t = c.
Proof.
 intros c t h; inversion h; reflexivity.
Defined.

(** The interpretation relation [pse_int] is a partial function. *)

Lemma pse_int_ext :
 forall (e:part_set_exp) (t t':T), pse_int e t -> pse_int e t' -> t[=]t'.
Proof.
 simple induction e; clear e.
     intros t t' h h0.
     rewrite (pse_int_var_inv h).
     rewrite (pse_int_var_inv h0).
     apply eq_reflexive.
    intros F e IH t t' h h0.
    inversion_clear h; inversion_clear h0.
    apply csf_wd; apply IH; assumption.
   intros F e1 IH1 e2 IH2 t t' h h0.
   inversion_clear h; inversion_clear h0.
   apply csbf_wd; [ apply IH1 | apply IH2 ]; assumption.
  intros F e IH t t' h h0.
  inversion_clear h; inversion_clear h0.
  apply cspf_wd; apply IH; assumption.
 intros c t t' h h0.
 rewrite (pse_int_con_inv h).
 rewrite (pse_int_con_inv h0).
 apply eq_reflexive.
Qed.

End syntactic_partial_setoid_expressions.

(** [pse_int] is well-founded. *)

Lemma pse_int_wd :
 forall (T:CSetoid) (r r':T),
   (r[=]r') ->
   forall (e:part_set_exp T) (t t':T),
     pse_int r e t -> pse_int r' e t' -> t[=]t'.
Proof.
 intros T r r' h.
 simple induction e; clear e.
     intros t t' h0 h1.
     rewrite (pse_int_var_inv h0).
     rewrite (pse_int_var_inv h1).
     exact h.
    intros F e IH t t' h0 h1.
    inversion_clear h0; inversion_clear h1.
    apply csf_wd; apply IH; assumption.
   intros F e1 IH1 e2 IH2 t t' h0 h1.
   inversion_clear h0; inversion_clear h1.
   apply csbf_wd; [ apply IH1 | apply IH2 ]; assumption.
  intros F e IH t t' h0 h1.
  inversion_clear h0; inversion_clear h1.
  apply cspf_wd; apply IH; assumption.
 intros c t t' h0 h1.
 rewrite (pse_int_con_inv h0).
 rewrite (pse_int_con_inv h1).
 apply eq_reflexive.
Defined.

(** The following lemma states that if [r1[=]r2] and [t1] is an interpretation
of [e] under the variable assigment [r1], then there exists an interpretation
[t2] of [e] under the assignment [r2]. *)

Lemma replacement_lemma :
 forall (T:CSetoid) (e:part_set_exp T) (r1 r2 t1:T),
   (r1[=]r2) -> pse_int r1 e t1 -> my_sigT T (pse_int r2 e).
Proof.
 intros T e r1 r2 t1 H H0.
 elim H0; clear H0 e t1.
     exists r2.
     apply pse_int_var.
    intros F e a1 Ha1 IH.
    elim IH; intros a2 Ha2.
    exists (F a2); apply pse_int_uop with (1 := Ha2).
   intros F ea a1 eb b1 Ha1 IHa Hb1 IHb.
   elim IHa; intros a2 Ha2.
   elim IHb; intros b2 Hb2.
   exists (F a2 b2); apply pse_int_bop with (1 := Ha2) (2 := Hb2).
  intros F e a1 Ha1 IH Da1.
  elim IH; intros a2 Ha2.
  assert (Da2 := cspf_dom_wd T T F a1 a2 Da1 (pse_int_wd H Ha1 Ha2)).
  exists (F a2 Da2).
  apply pse_int_pop with (1 := Ha2).
 intro t; exists t; apply pse_int_con.
Defined.

(** Given [H:r1[=]r2] and [H0:(pse_int r1 e t1)], the first projection of
[(replacement_lemma H H0)] is the term [t2] obtained by replacing in [t1]
subterm [r1] by [r2]. The second projection is the proof of
[(pse_int r2 e t2)]. *)

Definition replace_in_term (T:CSetoid) (r1 r2 t1:T)
  (e:part_set_exp T) (H:r1[=]r2) (H0:pse_int r1 e t1) :=
  proj1_my_sigT T (pse_int r2 e) (replacement_lemma H H0).

Definition replace_in_term_proof (T:CSetoid) (r1 r2 t1:T)
  (e:part_set_exp T) (H:r1[=]r2) (H0:pse_int r1 e t1) :=
  proj2_my_sigT T (pse_int r2 e) (replacement_lemma H H0).

Set Strict Implicit.
Unset Implicit Arguments.

(** The `quote function' maps from the semantical level to heavy syntactic
expressions: given a setoid term [t:T], [psxe_quote] yields a
[(part_set_xexp T)]. Term [r:T] (supposed to be a subterm of [t:T] to be
replaced later on) is mapped to [(psxe_var r)]. Other `leafs' [t0] of [t] are
mapped to [(psxe_con r t0)]. *)

Ltac psxe_quote r t :=
  match constr:t with
  | r => constr:(psxe_var r)
  | (csf_fun ?X1 ?X1 ?X2 ?X3) =>
      let F := constr:X2 with t0 := constr:X3 in
      let e := psxe_quote r t0 in
      constr:(psxe_uop F e)
  | (csbf_fun ?X1 ?X1 ?X1 ?X2 ?X3 ?X4) =>
      let F := constr:X2 with t1 := constr:X3 with t2 := constr:X4 in
      let e1 := psxe_quote r t1 with e2 := psxe_quote r t2 in
      constr:(psxe_bop F e1 e2)
      (*
        | [(cspf_fun ?1 ?1 ?2 ?3 ?4)] ->
      *)
  | (Part ?X2 ?X3 ?X4) =>
      let F := constr: (*1*) X2 with t0 := constr:X3 with Ht0 := constr:X4 in
      let e := psxe_quote r t0 in
      constr:(psxe_pop (F:=F) Ht0 e)
  | ?X1 => let t0 := constr:X1 in
           constr:(psxe_con r t0)
  end.

(** Given [H:r1[=]r2] and [A:Prop] or [A:CProp], [(replace_in_formula2 H A)]
replaces all occurrences of subterm [r1] in [A] by [r2]. *)

Ltac part_repl_in_form H A :=
  let type_of_H := typeof H in
  match constr:type_of_H with
  | (cs_eq (r:=(cs_crr ?X1)) ?X2 ?X3) =>
      let r1 := constr:X2 with r2 := constr:X3 in
      match constr:A with
      | (csp_pred ?X1 ?X2 ?X3) =>
          let P := constr:X2 with t := constr:X3 in
          let e := psxe_quote r1 t in
          let Ht := constr:(extract_correct e) in
          let s := constr:(replace_in_term H Ht) in
          constr:(P s)
      | (csr_rel ?X1 ?X2 ?X3 ?X4) =>
          let R := constr:X2 with t1 := constr:X3 with t2 := constr:X4 in
          let e1 := psxe_quote r1 t1 with e2 := psxe_quote r1 t2 in
          let Ht1 := constr:(extract_correct e1)
          with Ht2 := constr:(extract_correct e2) in
          let s1 := constr:(replace_in_term H Ht1)
          with s2 := constr:(replace_in_term H Ht2) in
          constr:(R s1 s2)
      | (Ccsr_rel ?X1 ?X2 ?X3 ?X4) =>
          let R := constr:X2 with t1 := constr:X3 with t2 := constr:X4 in
          let e1 := psxe_quote r1 t1 with e2 := psxe_quote r1 t2 in
          let Ht1 := constr:(extract_correct e1)
          with Ht2 := constr:(extract_correct e2) in
          let s1 := constr:(replace_in_term H Ht1)
          with s2 := constr:(replace_in_term H Ht2) in
          constr:(R s1 s2)
      | (cs_eq (r:=(cs_crr ?X1)) ?X2 ?X3) =>
          let T := constr:X1 with t1 := constr:X2 with t2 := constr:X3 in
          let e1 := psxe_quote r1 t1 with e2 := psxe_quote r1 t2 in
          let Ht1 := constr:(extract_correct e1)
          with Ht2 := constr:(extract_correct e2) in
          let s1 := constr:(replace_in_term H Ht1)
          with s2 := constr:(replace_in_term H Ht2) in
          constr:(cs_eq (r:=T) s1 s2)
      | (cs_ap (c:=?X1) ?X2 ?X3) =>
          let T := constr:X1 with t1 := constr:X2 with t2 := constr:X3 in
          let e1 := psxe_quote r1 t1 with e2 := psxe_quote r1 t2 in
          let Ht1 := constr:(extract_correct e1)
          with Ht2 := constr:(extract_correct e2) in
          let s1 := constr:(replace_in_term H Ht1)
          with s2 := constr:(replace_in_term H Ht2) in
          constr:(cs_ap (c:=T) s1 s2)
      | (?X1 -> ?X2) =>
          let A1 := constr:X1 with A2 := constr:X2 in
          let B1 := part_repl_in_form H A1 with B2 := part_repl_in_form H A2 in
          constr:(B1 -> B2)
      | (?X1 /\ ?X2) =>
          let A1 := constr:X1 with A2 := constr:X2 in
          let B1 := part_repl_in_form H A1 with B2 := part_repl_in_form H A2 in
          constr:(B1 /\ B2)
      | (?X1 and ?X2) =>
          let A1 := constr:X1 with A2 := constr:X2 in
          let B1 := part_repl_in_form H A1 with B2 := part_repl_in_form H A2 in
          constr:(B1 and B2)
      | (?X1 \/ ?X2) =>
          let A1 := constr:X1 with A2 := constr:X2 in
          let B1 := part_repl_in_form H A1 with B2 := part_repl_in_form H A2 in
          constr:(B1 \/ B2)
      | (?X1 or ?X2) =>
          let A1 := constr:X1 with A2 := constr:X2 in
          let B1 := part_repl_in_form H A1 with B2 := part_repl_in_form H A2 in
          constr:(B1 or B2)
      | (?X1 <-> ?X2) =>
          let A1 := constr:X1 with A2 := constr:X2 in
          let B1 := part_repl_in_form H A1 with B2 := part_repl_in_form H A2 in
          constr:(B1 <-> B2)
      | (Iff ?X1 ?X2) =>
          let A1 := constr:X1 with A2 := constr:X2 in
          let B1 := part_repl_in_form H A1 with B2 := part_repl_in_form H A2 in
          constr:(Iff B1 B2)
      | (~ ?X1) =>
          let A0 := constr:X1 in
          let B0 := part_repl_in_form H A0 in
          constr:(~ B0)
      | (Not ?X1) =>
          let A0 := constr:X1 in
          let B0 := part_repl_in_form H A0 in
          constr:(Not B0)
(*      | (CNot ?X1) =>
          let A0 := constr:X1 in
          let B0 := part_repl_in_form H A0 in
          constr:(CNot B0)*)
      | ?X1 => let A0 := constr:X1 in
               constr:A0
      end
  end.

(**
Given [T:CSetoid;r1,r2:T;H:r1[=]r2;H0:r2[=]r1] (checked by main call)
and [A:CProp] or [A:Prop], we get [(part_set_rewr_prf1 H H0 A) : A->A[r2/r1]]
and [(part_set_rewr_prf2 r1 r2 H H0 A) : A[r2/r1]->A] where [A[r2/r1]] denotes
[(part_repl_in_form H A)]. The argument [H0:r2[=]r1] is present to avoid
iterated application of [eq_symmetric].
*)

Ltac part_set_rewr_prf1 r1 r2 H H0 A :=
  match constr:A with
  | (csp_pred ?X1 ?X2 ?X3) =>
      let T := constr:X1 with P := constr:X2 with t := constr:X3 in
      let e := psxe_quote r1 t in
      let Ht := constr:(extract_correct e) in
      let s := constr:(replace_in_term H Ht)
      with Hs := constr:(replace_in_term_proof H Ht) in
      let d := constr:(pse_int_wd H Ht Hs) in
      constr:(fun a:P t => csp_wd T P t s a d)
  | (csr_rel ?X1 ?X2 ?X3 ?X4) =>
      let T := constr:X1
      with R := constr:X2
      with t1 := constr:X3
      with t2 := constr:X4 in
      let e1 := psxe_quote r1 t1 with e2 := psxe_quote r1 t2 in
      let Ht1 := constr:(extract_correct e1)
      with Ht2 := constr:(extract_correct e2) in
      let s1 := constr:(replace_in_term H Ht1)
      with s2 := constr:(replace_in_term H Ht2)
      with Hs1 := constr:(replace_in_term_proof H Ht1)
      with Hs2 := constr:(replace_in_term_proof H Ht2) in
      let d1 := constr:(pse_int_wd H Ht1 Hs1)
      with d2 := constr:(pse_int_wd H Ht2 Hs2) in
      constr:(fun a:R t1 t2 => csr_wd T R t1 t2 s1 s2 a d1 d2)
  | (Ccsr_rel ?X1 ?X2 ?X3 ?X4) =>
      let T := constr:X1
      with R := constr:X2
      with t1 := constr:X3
      with t2 := constr:X4 in
      let e1 := psxe_quote r1 t1 with e2 := psxe_quote r1 t2 in
      let Ht1 := constr:(extract_correct e1)
      with Ht2 := constr:(extract_correct e2) in
      let s1 := constr:(replace_in_term H Ht1)
      with s2 := constr:(replace_in_term H Ht2)
      with Hs1 := constr:(replace_in_term_proof H Ht1)
      with Hs2 := constr:(replace_in_term_proof H Ht2) in
      let d1 := constr:(pse_int_wd H Ht1 Hs1)
      with d2 := constr:(pse_int_wd H Ht2 Hs2) in
      constr:(fun a:R t1 t2 => Ccsr_wd T R t1 t2 s1 s2 a d1 d2)
  | (cs_eq (r:=(cs_crr ?X1)) ?X2 ?X3) =>
      let T := constr:X1 with t1 := constr:X2 with t2 := constr:X3 in
      let e1 := psxe_quote r1 t1 with e2 := psxe_quote r1 t2 in
      let Ht1 := constr:(extract_correct e1)
      with Ht2 := constr:(extract_correct e2) in
      let s1 := constr:(replace_in_term H Ht1)
      with s2 := constr:(replace_in_term H Ht2)
      with Hs1 := constr:(replace_in_term_proof H Ht1)
      with Hs2 := constr:(replace_in_term_proof H Ht2) in
      let d1 := constr:(pse_int_wd H Ht1 Hs1)
      with d2 := constr:(pse_int_wd H Ht2 Hs2) in
      constr:(fun a:cs_eq (r:=T) t1 t2 => eq_wd T t1 t2 s1 s2 a d1 d2)
  | (cs_ap (c:=?X1) ?X2 ?X3) =>
      let T := constr:X1 with t1 := constr:X2 with t2 := constr:X3 in
      let e1 := psxe_quote r1 t1 with e2 := psxe_quote r1 t2 in
      let Ht1 := constr:(extract_correct e1)
      with Ht2 := constr:(extract_correct e2) in
      let s1 := constr:(replace_in_term H Ht1)
      with s2 := constr:(replace_in_term H Ht2)
      with Hs1 := constr:(replace_in_term_proof H Ht1)
      with Hs2 := constr:(replace_in_term_proof H Ht2) in
      let d1 := constr:(pse_int_wd H Ht1 Hs1)
      with d2 := constr:(pse_int_wd H Ht2 Hs2) in
      constr:(fun a:cs_ap (c:=T) t1 t2 => ap_wd T t1 t2 s1 s2 a d1 d2)
  | (?X1 -> ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let d1 := part_set_rewr_prf1 r1 r2 H H0 A2
      with d2 := part_set_rewr_prf2 r1 r2 H H0 A1 in
      constr:(fun (p:A1 -> A2) b => d1 (p (d2 b)))
  | (?X1 /\ ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let d1 := part_set_rewr_prf1 r1 r2 H H0 A1
      with d2 := part_set_rewr_prf1 r1 r2 H H0 A2 in
      constr:(fun p:A1 /\ A2 => conj (d1 (fst p)) (d2 (snd p)))
  | (?X1 and ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let d1 := part_set_rewr_prf1 r1 r2 H H0 A1
      with d2 := part_set_rewr_prf1 r1 r2 H H0 A2 in
      constr:(fun p:A1 and A2 =>
                pair (d1 (CAnd_proj1 _ _ p))
                  (d2 (CAnd_proj2 _ _ p)))
  | (?X1 \/ ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let d1 := part_set_rewr_prf1 r1 r2 H H0 A1
      with d2 := part_set_rewr_prf1 r1 r2 H H0 A2 in
      constr:(or_ind (fun a => or_introl _ (d1 a))
                (fun a => or_intror _ (d2 a)))
  | (?X1 or ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let d1 := part_set_rewr_prf1 r1 r2 H H0 A1
      with d2 := part_set_rewr_prf1 r1 r2 H H0 A2 in
      constr:(COr_elim A1 A2 _ (fun a => inl _ _ (d1 a))
                (fun a => inr _ _ (d2 a)))
  | (?X1 <-> ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let ab1 := part_set_rewr_prf1 r1 r2 H H0 A1
      with ab2 := part_set_rewr_prf1 r1 r2 H H0 A2
      with ba1 := part_set_rewr_prf2 r1 r2 H H0 A1
      with ba2 := part_set_rewr_prf2 r1 r2 H H0 A2 in
      constr:(fun p:A1 <-> A2 =>
                conj (fun b1 => ab2 (fst p (ba1 b1)))
                  (fun b2 => ab1 (snd p (ba2 b2))))
  | (Iff ?X1 ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let ab1 := part_set_rewr_prf1 r1 r2 H H0 A1
      with ab2 := part_set_rewr_prf1 r1 r2 H H0 A2
      with ba1 := part_set_rewr_prf2 r1 r2 H H0 A1
      with ba2 := part_set_rewr_prf2 r1 r2 H H0 A2 in
      constr:(fun p:Iff A1 A2 =>
                pair (fun b1 => ab2 (CAnd_proj1 _ _ p (ba1 b1)))
                  (fun b2 => ab1 (CAnd_proj2 _ _ p (ba2 b2))))
  | (~ ?X1) =>
      let A0 := constr:X1 in
      let d := part_set_rewr_prf2 r1 r2 H H0 A0 in
      constr:(fun (p:~ A0) b => p (d b))
  | (Not ?X1) =>
      let A0 := constr:X1 in
      let d := part_set_rewr_prf2 r1 r2 H H0 A0 in
      constr:(fun (p:Not A0) b => p (d b))
(*   | (CNot ?X1) =>
      let A0 := constr:X1 in
      let d := part_set_rewr_prf2 r1 r2 H H0 A0 in
      constr:(fun (p:CNot A0) b => p (d b))*)
  | ?X1 => let A0 := constr:X1 in
           constr:(fun a:A0 => a)
  end
 with part_set_rewr_prf2 r1 r2 H H0 A :=
  match constr:A with
  | (csp_pred ?X1 ?X2 ?X3) =>
      let T := constr:X1 with P := constr:X2 with t := constr:X3 in
      let e := psxe_quote r1 t in
      let Ht := constr:(extract_correct e) in
      let s := constr:(replace_in_term H Ht)
      with Hs := constr:(replace_in_term_proof H Ht) in
      let d := constr:(pse_int_wd H0 Hs Ht) in
      constr:(fun b:P s => csp_wd T P s t b d)
  | (csr_rel ?X1 ?X2 ?X3 ?X4) =>
      let T := constr:X1
      with R := constr:X2
      with t1 := constr:X3
      with t2 := constr:X4 in
      let e1 := psxe_quote r1 t1 with e2 := psxe_quote r1 t2 in
      let Ht1 := constr:(extract_correct e1)
      with Ht2 := constr:(extract_correct e2) in
      let s1 := constr:(replace_in_term H Ht1)
      with s2 := constr:(replace_in_term H Ht2)
      with Hs1 := constr:(replace_in_term_proof H Ht1)
      with Hs2 := constr:(replace_in_term_proof H Ht2) in
      let d1 := constr:(pse_int_wd H0 Hs1 Ht1)
      with d2 := constr:(pse_int_wd H0 Hs2 Ht2) in
      constr:(fun b:R s1 s2 => csr_wd T R s1 s2 t1 t2 b d1 d2)
  | (Ccsr_rel ?X1 ?X2 ?X3 ?X4) =>
      let T := constr:X1
      with R := constr:X2
      with t1 := constr:X3
      with t2 := constr:X4 in
      let e1 := psxe_quote r1 t1 with e2 := psxe_quote r1 t2 in
      let Ht1 := constr:(extract_correct e1)
      with Ht2 := constr:(extract_correct e2) in
      let s1 := constr:(replace_in_term H Ht1)
      with s2 := constr:(replace_in_term H Ht2)
      with Hs1 := constr:(replace_in_term_proof H Ht1)
      with Hs2 := constr:(replace_in_term_proof H Ht2) in
      let d1 := constr:(pse_int_wd H0 Hs1 Ht1)
      with d2 := constr:(pse_int_wd H0 Hs2 Ht2) in
      constr:(fun b:R s1 s2 => Ccsr_wd T R s1 s2 t1 t2 b d1 d2)
  | (cs_eq (r:=(cs_crr ?X1)) ?X2 ?X3) =>
      let T := constr:X1 with t1 := constr:X2 with t2 := constr:X3 in
      let e1 := psxe_quote r1 t1 with e2 := psxe_quote r1 t2 in
      let Ht1 := constr:(extract_correct e1)
      with Ht2 := constr:(extract_correct e2) in
      let s1 := constr:(replace_in_term H Ht1)
      with s2 := constr:(replace_in_term H Ht2)
      with Hs1 := constr:(replace_in_term_proof H Ht1)
      with Hs2 := constr:(replace_in_term_proof H Ht2) in
      let d1 := constr:(pse_int_wd H0 Hs1 Ht1)
      with d2 := constr:(pse_int_wd H0 Hs2 Ht2) in
      constr:(fun b:cs_eq (r:=T) s1 s2 => eq_wd T s1 s2 t1 t2 b d1 d2)
  | (cs_ap (c:=?X1) ?X2 ?X3) =>
      let T := constr:X1 with t1 := constr:X2 with t2 := constr:X3 in
      let e1 := psxe_quote r1 t1 with e2 := psxe_quote r1 t2 in
      let Ht1 := constr:(extract_correct e1)
      with Ht2 := constr:(extract_correct e2) in
      let s1 := constr:(replace_in_term H Ht1)
      with s2 := constr:(replace_in_term H Ht2)
      with Hs1 := constr:(replace_in_term_proof H Ht1)
      with Hs2 := constr:(replace_in_term_proof H Ht2) in
      let d1 := constr:(pse_int_wd H0 Hs1 Ht1)
      with d2 := constr:(pse_int_wd H0 Hs2 Ht2) in
      constr:(fun b:cs_ap (c:=T) s1 s2 => ap_wd T s1 s2 t1 t2 b d1 d2)
  | (?X1 -> ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let d1 := part_set_rewr_prf1 r1 r2 H H0 A1
      with d2 := part_set_rewr_prf2 r1 r2 H H0 A2 in
      constr:(fun q (a:A1) => d2 (q (d1 a)))
  | (?X1 /\ ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let d1 := part_set_rewr_prf2 r1 r2 H H0 A1
      with d2 := part_set_rewr_prf2 r1 r2 H H0 A2 in
      constr:(fun q:_ /\ _ => conj (d1 (fst q)) (d2 (snd q)))
  | (?X1 and ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let d1 := part_set_rewr_prf2 r1 r2 H H0 A1
      with d2 := part_set_rewr_prf2 r1 r2 H H0 A2 in
      constr:(fun q:_ and _ =>
                @pair A1 A2 (d1 (CAnd_proj1 _ _ q))
                  (d2 (CAnd_proj2 _ _ q)))
  | (?X1 \/ ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let d1 := part_set_rewr_prf2 r1 r2 H H0 A1
      with d2 := part_set_rewr_prf2 r1 r2 H H0 A2 in
      constr:(or_ind (fun b => or_introl A2 (d1 b))
                (fun b => or_intror A1 (d2 b)))
  | (?X1 or ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let d1 := part_set_rewr_prf2 r1 r2 H H0 A1
      with d2 := part_set_rewr_prf2 r1 r2 H H0 A2 in
      constr:(COr_elim _ _ (A1 or A2) (fun b => inl A1 A2 (d1 b))
                (fun b => inr A1 A2 (d2 b)))
  | (?X1 <-> ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let ab1 := part_set_rewr_prf1 r1 r2 H H0 A1
      with ab2 := part_set_rewr_prf1 r1 r2 H H0 A2
      with ba1 := part_set_rewr_prf2 r1 r2 H H0 A1
      with ba2 := part_set_rewr_prf2 r1 r2 H H0 A2 in
      constr:(fun q:_ <-> _ =>
                conj (fun a1:A1 => ba2 (fst q (ab1 a1)))
                  (fun a2:A2 => ba1 (snd q (ab2 a2))))
  | (Iff ?X1 ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let ab1 := part_set_rewr_prf1 r1 r2 H H0 A1
      with ab2 := part_set_rewr_prf1 r1 r2 H H0 A2
      with ba1 := part_set_rewr_prf2 r1 r2 H H0 A1
      with ba2 := part_set_rewr_prf2 r1 r2 H H0 A2 in
      constr:(fun q:Iff _ _ =>
                pair (fun a1:A1 => ba2 (CAnd_proj1 _ _ q (ab1 a1)))
                  (fun a2:A2 => ba1 (CAnd_proj2 _ _ q (ab2 a2))))
  | (~ ?X1) =>
      let A0 := constr:X1 in
      let d := part_set_rewr_prf1 r1 r2 H H0 A0 in
      constr:(fun (q:~ _) (a:A0) => q (d a))
  | (Not ?X1) =>
      let A0 := constr:X1 in
      let d := part_set_rewr_prf1 r1 r2 H H0 A0 in
      constr:(fun (q:Not _) (a:A0) => q (d a))
(*  | (CNot ?X1) =>
      let A0 := constr:X1 in
      let d := part_set_rewr_prf1 r1 r2 H H0 A0 in
      constr:(fun (q:CNot _) (a:A0) => q (d a)) *)
  | ?X1 => let A0 := constr:X1 in
           constr:(fun a:A0 => a)
  end.

Ltac Unfold_partial_csetoid_rewrite_stuff :=
  unfold replace_in_term, proj1_my_sigT, replacement_lemma, extract_correct,
   pse_int_rect, part_set_xexp_rect, my_sigT_rect in |- *.

(* rewrite -> h *)
Ltac partial_csetoid_rewrite h :=
  let type_of_h := typeof h in
  match constr:type_of_h with
  | (cs_eq (r:=(cs_crr ?X1)) ?X2 ?X3) =>
      let T := constr:X1 with r1 := constr:X2 with r2 := constr:X3 in
      let h0 := constr:(eq_symmetric T r1 r2 h) in
      match goal with
      |  |- ?X1 =>
          let A := constr:X1 in
          let B := part_repl_in_form h A
          with d := part_set_rewr_prf2 r1 r2 h h0 A in
          ((*:B->A*) cut B; [ exact d | Unfold_partial_csetoid_rewrite_stuff ])
      end
  end.

(* rewrite <- h *)
Ltac partial_csetoid_rewrite_rev h :=
  let type_of_h := typeof h in
  match constr:type_of_h with
  | (cs_eq (r:=(cs_crr ?X1)) ?X2 ?X3) =>
      let T := constr:X1 with r2 := constr:X2 with r1 := constr:X3 in
      let h0 := constr:(eq_symmetric T r2 r1 h) in
      match goal with
      |  |- ?X1 =>
          let A := constr:X1 in
          let B := part_repl_in_form h A
          with d := part_set_rewr_prf2 r1 r2 h0 h A in
          ((*:B->A*) cut B; [ exact d | Unfold_partial_csetoid_rewrite_stuff ])
      end
  end.

(* rewrite -> h in h0 *)
Ltac partial_csetoid_rewrite_cxt h h0 :=
  let type_of_h := typeof h in
  match constr:type_of_h with
  | (cs_eq (r:=(cs_crr ?X1)) ?X2 ?X3) =>
      let T := constr:X1 with r1 := constr:X2 with r2 := constr:X3 in
      let h1 := constr:(eq_symmetric T r1 r2 h) with A := typeof h0 in
      let B := part_repl_in_form h A
      with d := part_set_rewr_prf1 r1 r2 h h1 A in
      ((*:A->B*) cut B;
        [ Unfold_partial_csetoid_rewrite_stuff; clear h0; intro h0
        | exact (d h0) ])
  end.

(* rewrite <- h in h0 *)
Ltac partial_csetoid_rewrite_cxt_rev h h0 :=
  let type_of_h := typeof h in
  match constr:type_of_h with
  | (cs_eq (r:=(cs_crr ?X1)) ?X2 ?X3) =>
      let T := constr:X1 with r2 := constr:X2 with r1 := constr:X3 in
      let h1 := constr:(eq_symmetric T r2 r1 h) with A := typeof h0 in
      let B := part_repl_in_form h A
      with d := part_set_rewr_prf1 r1 r2 h1 h A in
      ((*:A->B*) cut B;
        [ Unfold_partial_csetoid_rewrite_stuff; clear h0; intro h0
        | exact (d h0) ])
  end.

(* replace x with y *)
Ltac partial_setoid_replace x y :=
  let h := fresh in
  (cut (x[=]y); [ intro h; partial_csetoid_rewrite h; clear h | idtac ]).

(* replace x with y in h *)
Ltac partial_setoid_replace_cxt x y h :=
  let h0 := fresh in
  (cut (x[=]y);
    [ intro h0; partial_csetoid_rewrite_cxt h0 h; clear h0 | idtac ]).

(*End partial_csetoid_rewrite.*)

Require Export Bool.

Ltac term_cont_part t :=
  match constr:t with
  | (Part _ _ _) => constr:true
  | (csf_fun _ _ _ ?X4) =>
      let t0 := constr:X4 in
      let b := term_cont_part t0 in
      constr:b
  | (csbf_fun _ _ _ _ ?X5 ?X6) =>
      let t1 := constr:X5 with t2 := constr:X6 in
      let b1 := term_cont_part t1 with b2 := term_cont_part t2 in
      constr:(orb b1 b2)
  | _ => constr:false
  end.

Ltac form_cont_part A :=
  match constr:A with
  | (csp_pred _ _ ?X3) =>
      let t := constr:X3 in
      let b := term_cont_part t in
      constr:b
  | (csr_rel _ _ ?X3 ?X4) =>
      let t1 := constr:X3 with t2 := constr:X4 in
      let b1 := term_cont_part t1 with b2 := term_cont_part t2 in
      constr:(orb b1 b2)
  | (Ccsr_rel _ _ ?X3 ?X4) =>
      let t1 := constr:X3 with t2 := constr:X4 in
      let b1 := term_cont_part t1 with b2 := term_cont_part t2 in
      constr:(orb b1 b2)
  | (?X2[=]?X3) =>
      let t1 := constr:X2 with t2 := constr:X3 in
      let b1 := term_cont_part t1 with b2 := term_cont_part t2 in
      constr:(orb b1 b2)
  | (?X2[#]?X3) =>
      let t1 := constr:X2 with t2 := constr:X3 in
      let b1 := term_cont_part t1 with b2 := term_cont_part t2 in
      constr:(orb b1 b2)
  | (?X1 -> ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let b1 := form_cont_part A1 with b2 := form_cont_part A2 in
      constr:(orb b1 b2)
  | (?X1 /\ ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let b1 := form_cont_part A1 with b2 := form_cont_part A2 in
      constr:(orb b1 b2)
  | (?X1 and ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let b1 := form_cont_part A1 with b2 := form_cont_part A2 in
      constr:(orb b1 b2)
  | (?X1 \/ ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let b1 := form_cont_part A1 with b2 := form_cont_part A2 in
      constr:(orb b1 b2)
  | (?X1 or ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let b1 := form_cont_part A1 with b2 := form_cont_part A2 in
      constr:(orb b1 b2)
  | (?X1 <-> ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let b1 := form_cont_part A1 with b2 := form_cont_part A2 in
      constr:(orb b1 b2)
  | (Iff ?X1 ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      let b1 := form_cont_part A1 with b2 := form_cont_part A2 in
      constr:(orb b1 b2)
  | (~ ?X1) =>
      let A0 := constr:X1 in
      let b := form_cont_part A0 in
      constr:b
  | (Not ?X1) =>
      let A0 := constr:X1 in
      let b := form_cont_part A0 in
      constr:b
(*   | (CNot ?X1) =>
      let A0 := constr:X1 in
      let b := form_cont_part A0 in
      constr:b *)
  | _ => constr:false
  end.

Ltac fold_cspf_dom_in_term t :=
  match constr:t with
  | (Part _ ?X3 ?X4) =>
      let t0 := constr:X3 with h := constr:X4 in
      let H := fresh in
      (set (H := h) in *; fold_cspf_dom_in_term t0; clearbody H)
  | (csf_fun _ _ _ ?X4) =>
      let t0 := constr:X4 in
      fold_cspf_dom_in_term t0
  | (csbf_fun _ _ _ _ ?X5 ?X6) =>
      let t1 := constr:X5 with t2 := constr:X6 in
      (fold_cspf_dom_in_term t1; fold_cspf_dom_in_term t2)
  | _ => idtac
  end.

Ltac fold_cspf_dom_in_form A :=
  match constr:A with
  | (csp_pred _ _ ?X3) =>
      let t := constr:X3 in
      fold_cspf_dom_in_term t
  | (csr_rel _ _ ?X3 ?X4) =>
      let t1 := constr:X3 with t2 := constr:X4 in
      (fold_cspf_dom_in_term t1; fold_cspf_dom_in_term t2)
  | (Ccsr_rel _ _ ?X3 ?X4) =>
      let t1 := constr:X3 with t2 := constr:X4 in
      (fold_cspf_dom_in_term t1; fold_cspf_dom_in_term t2)
  | (?X2[=]?X3) =>
      let t1 := constr:X2 with t2 := constr:X3 in
      (fold_cspf_dom_in_term t1; fold_cspf_dom_in_term t2)
  | (?X2[#]?X3) =>
      let t1 := constr:X2 with t2 := constr:X3 in
      (fold_cspf_dom_in_term t1; fold_cspf_dom_in_term t2)
  | (?X1 -> ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      (fold_cspf_dom_in_form A1; fold_cspf_dom_in_form A2)
  | (?X1 /\ ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      (fold_cspf_dom_in_form A1; fold_cspf_dom_in_form A2)
  | (?X1 and ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      (fold_cspf_dom_in_form A1; fold_cspf_dom_in_form A2)
  | (?X1 \/ ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      (fold_cspf_dom_in_form A1; fold_cspf_dom_in_form A2)
  | (?X1 or ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      (fold_cspf_dom_in_form A1; fold_cspf_dom_in_form A2)
  | (?X1 <-> ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      (fold_cspf_dom_in_form A1; fold_cspf_dom_in_form A2)
  | (Iff ?X1 ?X2) =>
      let A1 := constr:X1 with A2 := constr:X2 in
      (fold_cspf_dom_in_form A1; fold_cspf_dom_in_form A2)
  | (~ ?X1) => let A0 := constr:X1 in
               fold_cspf_dom_in_form A0
  | (Not ?X1) => let A0 := constr:X1 in
                 fold_cspf_dom_in_form A0
(*   | (CNot ?X1) => let A0 := constr:X1 in
                  fold_cspf_dom_in_form A0 *)
  | _ => idtac
  end.

Ltac fold_cspf_dom :=
  match goal with
  |  |- ?X1 => let A := constr:X1 in
               fold_cspf_dom_in_form A
  end.

Ltac csetoid_rewrite h :=
  match goal with
  |  |- ?X1 =>
      let A := constr:X1 in
      let b := form_cont_part A in
      let c := eval compute in b in
      match constr:c with
      | true => partial_csetoid_rewrite h; fold_cspf_dom
      | false => total_csetoid_rewrite h
      end
  end.

Ltac csetoid_rewrite_rev h :=
  match goal with
  |  |- ?X1 =>
      let A := constr:X1 in
      let b := form_cont_part A in
      let c := eval compute in b in
      match constr:c with
      | true => partial_csetoid_rewrite_rev h; fold_cspf_dom
      | false => total_csetoid_rewrite_rev h
      end
  end.

Ltac csetoid_rewrite_cxt h h0 :=
  let A := typeof h0 in
      let b := form_cont_part A in
      let c := eval compute in b in
      match constr:c with
      | true => partial_csetoid_rewrite_cxt h h0; fold_cspf_dom_in_form A
      | false => total_csetoid_rewrite_cxt h h0
      end.

Ltac csetoid_rewrite_cxt_rev h h0 :=
  let A := typeof h0 in
      let b := form_cont_part A in
      let c := eval compute in b in
      match constr:c with
      | true => partial_csetoid_rewrite_cxt_rev h h0; fold_cspf_dom_in_form A
      | false => total_csetoid_rewrite_cxt_rev h h0
      end.

Ltac csetoid_replace x y :=
  let h := fresh in
  (cut (x[=]y); [ intro h; csetoid_rewrite h; clear h | idtac ]).

Ltac csetoid_replace_cxt x y h0 :=
  let h := fresh in
  (cut (x[=]y); [ intro h; csetoid_rewrite_cxt h h0; clear h | idtac ]).
