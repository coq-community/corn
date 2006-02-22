(* $Id: CRings.v,v 1.13 2004/08/30 09:23:10 loeb Exp $ *)

(** printing [*] %\ensuremath\times% #&times;# *)
(** printing [^] %\ensuremath{\hat{\ }}% #^# *)
(** printing {*} %\ensuremath\times% #&times;# *)
(** printing {**} %\ensuremath\ast% #&lowast;# *)
(** printing {^} %\ensuremath{\hat{\ }}% #^# *)
(** printing One %\ensuremath{\mathbf1}% #1# *)
(** printing Two %\ensuremath{\mathbf2}% #2# *)
(** printing Three %\ensuremath{\mathbf3}% #3# *)
(** printing Four %\ensuremath{\mathbf4}% #4# *)
(** printing Six %\ensuremath{\mathbf6}% #6# *)
(** printing Eight %\ensuremath{\mathbf8}% #8# *)
(** printing Nine %\ensuremath{\mathbf9}% #9# *)
(** printing Twelve %\ensuremath{\mathbf{12}}% #12# *)
(** printing Sixteen %\ensuremath{\mathbf{16}}% #16# *)
(** printing Eighteen %\ensuremath{\mathbf{18}}% #18# *)
(** printing TwentyFour %\ensuremath{\mathbf{24}}% #24# *)
(** printing FortyEight %\ensuremath{\mathbf{48}}% #48# *)

Require Export CSums.

Transparent sym_eq.
Transparent f_equal.

(* Begin_SpecReals *)

(* Constructive RINGS *)

(** * Rings
We actually define commutative rings with identity.
** Definition of the notion of Ring
*)
Definition distributive S (mult plus : CSetoid_bin_op S) :=
  forall x y z, mult x (plus y z) [=] plus (mult x y) (mult x z).

Implicit Arguments distributive [S].

Record is_CRing (G : CAbGroup) (One : G) (mult : CSetoid_bin_op G) : CProp := 
  {ax_mult_assoc : associative mult;
   ax_mult_mon   : is_CMonoid (Build_CSemiGroup G mult ax_mult_assoc) One;
   ax_mult_com   : commutes mult;
   ax_dist       : distributive mult csg_op;
   ax_non_triv   : One [#] Zero}.

Record CRing : Type := 
  {cr_crr   :> CAbGroup;
   cr_one   :  cr_crr;
   cr_mult  :  CSetoid_bin_op cr_crr;
   cr_proof :  is_CRing cr_crr cr_one cr_mult}.

Definition cr_plus := @csg_op.
Definition cr_inv := @cg_inv.
Definition cr_minus := cg_minus.


Notation One := (cr_one _).
(* End_SpecReals *)

(* Begin_SpecReals *)

(**
%\begin{nameconvention}%
In the names of lemmas, we will denote [One] with [one],
and [[*]] with [mult].
%\end{nameconvention}%
*)

Implicit Arguments cr_mult [c].
Infix "[*]" := cr_mult (at level 40, left associativity).

Section CRing_axioms.
(**
** Ring axioms
%\begin{convention}% Let [R] be a ring.
%\end{convention}%
*)
Variable R : CRing.

Lemma CRing_is_CRing : is_CRing R One cr_mult.
elim R; auto.
Qed.

Lemma mult_assoc : associative (cr_mult (c:=R)).
elim CRing_is_CRing; auto.
Qed.

Lemma mult_commutes : commutes (cr_mult (c:=R)).
elim CRing_is_CRing; auto.
Qed.

Lemma mult_mon : is_CMonoid (Build_CSemiGroup R cr_mult mult_assoc) One.
elim (cr_proof R).
intros H1 H2 H3 H4 H5.
apply is_CMonoid_proof_irr with H1.
assumption.
Qed.

(* End_SpecReals *)

Lemma dist : distributive (S:=R) cr_mult (cr_plus R).
elim (cr_proof R); auto.
Qed.

Lemma ring_non_triv : (One:R) [#] Zero.
elim (cr_proof R); auto.
Qed.

Lemma mult_wd : forall x1 x2 y1 y2 : R, x1 [=] x2 -> y1 [=] y2 -> x1[*]y1 [=] x2[*]y2.
intros; Algebra.
Qed.

Lemma mult_wdl : forall x1 x2 y : R, x1 [=] x2 -> x1[*]y [=] x2[*]y.
intros; Algebra.
Qed.

Lemma mult_wdr : forall x y1 y2 : R, y1 [=] y2 -> x[*]y1 [=] x[*]y2.
intros; Algebra.
Qed.

(* Begin_SpecReals *)

End CRing_axioms.

Section Ring_constructions.
(**
** Ring constructions
%\begin{convention}%
Let [R] be a ring.
%\end{convention}%
*)
Variable R : CRing.

(**
The multiplicative monoid of a ring is defined as follows.
*)
Definition Build_multCMonoid : CMonoid := Build_CMonoid _ _ (mult_mon R).

End Ring_constructions.

(* End_SpecReals *)

Section Ring_unfolded.
(**
** Ring unfolded
%\begin{convention}% Let [R] be a ring.
%\end{convention}%
*)
Variable R : CRing.
(* begin hide *)
Let mmR := Build_multCMonoid R.
(* end hide *)

Lemma mult_assoc_unfolded : forall x y z : R, x[*] (y[*]z) [=] x[*]y[*]z.
Proof mult_assoc R.

Lemma mult_commut_unfolded : forall x y : R, x[*]y [=] y[*]x.
Proof mult_commutes R.
Hint Resolve mult_commut_unfolded: algebra.

Lemma mult_one : forall x : R, x[*]One [=] x.
Proof cm_rht_unit mmR.

Lemma one_mult : forall x : R, One[*]x [=] x.
Proof cm_lft_unit mmR.

Lemma ring_dist_unfolded : forall x y z : R, x[*] (y[+]z) [=] x[*]y[+]x[*]z.
Proof dist R.
Hint Resolve ring_dist_unfolded: algebra.

Lemma ring_distl_unfolded : forall x y z : R, (y[+]z) [*]x [=] y[*]x[+]z[*]x.
intros x y z.
astepl (x[*] (y[+]z)).
astepl (x[*]y[+]x[*]z).
astepl (y[*]x[+]x[*]z).
Step_final (y[*]x[+]z[*]x).
Qed.

End Ring_unfolded.
Hint Resolve mult_assoc_unfolded: algebra.
Hint Resolve ring_non_triv mult_one one_mult mult_commut_unfolded: algebra.
Hint Resolve ring_dist_unfolded ring_distl_unfolded: algebra.


Section Ring_basics.
(**
** Ring basics
%\begin{convention}% Let [R] be a ring.
%\end{convention}%
*)
Variable R : CRing.

Lemma one_ap_zero : (One:R) [#] Zero.
Proof ring_non_triv R.

Definition is_zero_rht S (op : CSetoid_bin_op S) Zero : Prop := forall x, op x Zero [=] Zero.

Definition is_zero_lft S (op : CSetoid_bin_op S) Zero : Prop := forall x, op Zero x [=] Zero.

Implicit Arguments is_zero_rht [S].
Implicit Arguments is_zero_lft [S].

Lemma cring_mult_zero : forall x : R, x[*]Zero [=] Zero.
intro x.
apply cg_cancel_lft with (x[*]Zero).
astepr (x[*]Zero).
Step_final (x[*] (Zero[+]Zero)).
Qed.
Hint Resolve cring_mult_zero: algebra.

Lemma x_mult_zero : forall x y : R, y [=] Zero -> x[*]y [=] Zero.
intros x y H; Step_final (x[*]Zero).
Qed.

Lemma cring_mult_zero_op : forall x : R, Zero[*]x [=] Zero.
intro x; Step_final (x[*]Zero).
Qed.
Hint Resolve cring_mult_zero_op: algebra.

Lemma cring_inv_mult_lft : forall x y : R, x[*] [--]y [=] [--] (x[*]y).
intros x y.
apply cg_inv_unique.
astepl (x[*] (y[+] [--]y)).
Step_final (x[*]Zero).
Qed.
Hint Resolve cring_inv_mult_lft: algebra.

Lemma cring_inv_mult_rht : forall x y : R, [--]x[*]y [=] [--] (x[*]y).
intros x y.
astepl (y[*] [--]x).
Step_final ( [--] (y[*]x)).
Qed.
Hint Resolve cring_inv_mult_rht: algebra.

Lemma cring_mult_ap_zero :(forall x y : R, x[*]y [#] Zero -> x [#] Zero):CProp.
intros x y H.
elim (cs_bin_op_strext _ cr_mult x Zero y y).
  auto.
 intro contra; elim (ap_irreflexive _ _ contra).
astepr (Zero:R). auto.
Qed.

Lemma cring_mult_ap_zero_op : (forall x y : R, x[*]y [#] Zero -> y [#] Zero)
  :CProp.
intros x y H.
apply cring_mult_ap_zero with x.
astepl (x[*]y). auto.
Qed.

Lemma inv_mult_invol : forall x y : R, [--]x[*] [--]y [=] x[*]y.
intros x y.
astepl ( [--] (x[*] [--]y)).
Step_final ( [--][--] (x[*]y)).
Qed.

Lemma ring_dist_minus : forall x y z : R, x[*] (y[-]z) [=] x[*]y[-]x[*]z.
intros x y z.
unfold cg_minus in |- *.
Step_final (x[*]y[+]x[*] [--]z).
Qed.

Hint Resolve ring_dist_minus: algebra.

Lemma ring_distl_minus : forall x y z : R, (y[-]z) [*]x [=] y[*]x[-]z[*]x.
intros x y z.
unfold cg_minus in |- *.
Step_final (y[*]x[+] [--]z[*]x).
Qed.

Hint Resolve ring_distl_minus: algebra.

Lemma mult_minus1 : forall x:R, [--]One [*] x [=] [--]x.
intro x.
apply (cg_cancel_lft R x).
astepr (Zero:R).
astepl ((One[*]x)[+]([--]One[*]x)).
astepl ((One[+][--]One)[*]x).
Step_final (Zero[*]x).
Qed.

Lemma ring_distr1 : forall a b1 b2:R,
                    a [*] (b1[-]b2) [=] a[*]b1 [-] a[*]b2.
intros a b1 b2.
astepl (a[*](b1[+][--]b2)).
astepl (a[*]b1 [+] a[*][--]b2).
Step_final (a[*]b1 [+] [--](a[*]b2)).
Qed.

Lemma ring_distr2 : forall a1 a2 b:R,
                    (a1[-]a2) [*] b [=] a1[*]b [-] a2[*]b.
intros a1 a2 b.
astepl ((a1[+][--]a2)[*]b).
astepl (a1[*]b [+] [--]a2[*]b).
Step_final (a1[*]b [+] [--](a2[*]b)).
Qed.


End Ring_basics.
Hint Resolve cring_mult_zero cring_mult_zero_op: algebra.
Hint Resolve inv_mult_invol: algebra.
Hint Resolve cring_inv_mult_lft cring_inv_mult_rht: algebra.
Hint Resolve ring_dist_minus: algebra.
Hint Resolve ring_distl_minus: algebra.
Hint Resolve mult_minus1 ring_distr1 ring_distr2: algebra.
(* Begin_SpecReals *)

(**
** Ring Definitions
Some auxiliary functions and operations over a ring;
especially geared towards CReals.
*)

Section exponentiation.
(**
*** Exponentiation
%\begin{convention}%
Let [R] be a ring.
%\end{convention}%
*)
Variable R : CRing.

(* End_SpecReals *)

Fixpoint nexp (m : nat) : R -> R :=
  match m with
  | O   => fun _ : R => One
  | S n => fun x : R => nexp n x[*]x
  end.

Lemma nexp_well_def : forall n, fun_wd (nexp n).
intro n; induction  n as [| n Hrecn]; red in |- *; intros; simpl in |- *;
 Algebra.
Qed.

Lemma nexp_strong_ext : forall n, fun_strext (nexp n).
intro n; red in |- *; induction  n as [| n Hrecn]; simpl in |- *;
 intros x y H.
 elim (ap_irreflexive _ _ H).
elim (cs_bin_op_strext _ cr_mult _ _ _ _ H); auto.
Qed.

Definition nexp_op n := Build_CSetoid_un_op R (nexp n) (nexp_strong_ext n).

(* Begin_SpecReals *)

End exponentiation.

(* End_SpecReals *)

Notation "x [^] n" := (nexp_op _ n x) (at level 20).
Implicit Arguments nexp_op [R].

(* Begin_SpecReals *)

Section nat_injection.
(**
*** The injection of natural numbers into a ring
%\begin{convention}% Let [R] be a ring.
%\end{convention}%
*)
Variable R : CRing.

(**
The injection of Coq natural numbers into a ring is called [nring].
Note that this need not really be an injection; when it is, the ring is said
to have characteristic [0].
*)

Fixpoint nring (m : nat) : R :=
  match m with
  | O   => Zero
  | S n => nring n[+]One
  end.

Definition Char0 := forall n : nat, 0 < n -> nring n [#] Zero.

(* End_SpecReals *)

Lemma nring_comm_plus : forall n m, nring (n + m) [=] nring n[+]nring m.
intros n m; induction  n as [| n Hrecn]; simpl in |- *.
 Algebra.
astepr (nring n[+] (One[+]nring m)).
astepr (nring n[+] (nring m[+]One)).
Step_final (nring n[+]nring m[+]One).
Qed.

Lemma nring_comm_mult : forall n m, nring (n * m) [=] nring n[*]nring m.
intros n m; induction  n as [| n Hrecn]; simpl in |- *.
 Algebra.
apply eq_transitive_unfolded with (nring m[+]nring (n * m)). apply (nring_comm_plus m (n * m)).
astepr (nring n[*]nring m[+]One[*]nring m).
astepr (nring n[*]nring m[+]nring m).
Step_final (nring m[+]nring n[*]nring m).
Qed.

(* Begin_SpecReals *)

End nat_injection.

(* End_SpecReals *)

Hint Resolve nring_comm_plus nring_comm_mult: algebra.

(* Begin_SpecReals *)

Implicit Arguments nring [R].

(* End_SpecReals *)

Notation Two := (nring 2).
Notation Three := (nring 3).
Notation Four := (nring 4).

Notation Six := (nring 6).
Notation Eight := (nring 8).
Notation Twelve := (nring 12).
Notation Sixteen := (nring 16).

Notation Nine := (nring 9).
Notation Eighteen := (nring 18).
Notation TwentyFour := (nring 24).
Notation FortyEight := (nring 48).

Lemma one_plus_one : forall R : CRing, One[+]One [=] (Two:R).
simpl in |- *; Algebra.
Qed.

Lemma x_plus_x : forall (R : CRing) (x : R), x[+]x [=] Two[*]x.
intros R x.
astepl (One[*]x[+]One[*]x).
astepl ((One[+]One) [*]x).
simpl in |- *; Algebra.
Qed.

Hint Resolve one_plus_one x_plus_x: algebra.

(**
In a ring of characteristic zero, [nring] is really an injection.
*)

Lemma nring_different : forall R, Char0 R -> forall i j, i <> j -> nring i [#] (nring j:R).
intros R H i j H0.
elim (Cnat_total_order i j); intros.
replace j with (i + (j - i)).
astepr (nring i[+]nring (j - i):R).
astepl (nring i[+]Zero:R).
apply op_lft_resp_ap.
apply ap_symmetric_unfolded.
apply H.
omega.
auto with arith.
replace i with (j + (i - j)).
astepl (nring j[+]nring (i - j):R).
astepr (nring j[+] (Zero:R)).
apply op_lft_resp_ap.
apply H.
omega.
auto with arith.
auto.
Qed.

Section int_injection.

(**
*** The injection of integers into a ring
%\begin{convention}%
Let [R] be a ring.
%\end{convention}%
*)

Variable R : CRing.

(**
The injection of Coq integers into a ring is called [zring]. Again,
this need not really be an injection.

The first definition is now obsolete, having been replaced by a more efficient
one. It is kept to avoid having to redo all the proofs.
*)

Definition zring_old k : R := caseZ_diff k (fun m n => nring m[-]nring n).

Lemma zring_old_zero : zring_old 0 [=] Zero.
simpl in |- *; Algebra.
Qed.
Hint Resolve zring_old_zero: algebra.

Lemma zring_old_diff : forall m n : nat, zring_old (m - n) [=] nring m[-]nring n.
unfold zring_old in |- *.
intros m n.
apply
 proper_caseZ_diff_CS
  with (f := fun m0 n0 : nat => nring (R:=R) m0[-]nring n0).
clear m n.
intros m n p q H.
apply cg_cancel_lft with (nring n:R).
unfold cg_minus in |- *.
astepl (nring (R:=R) n[+] ( [--] (nring n) [+]nring m)).
astepl (nring (R:=R) n[+] [--] (nring n) [+]nring m).
astepl (Zero[+]nring (R:=R) m).
astepl (nring (R:=R) m).
apply cg_cancel_rht with (nring q:R).
astepr (nring (R:=R) n[+] (nring p[+] [--] (nring q) [+]nring q)).
astepr (nring (R:=R) n[+] (nring p[+] ( [--] (nring q) [+]nring q))).
astepr (nring (R:=R) n[+] (nring p[+]Zero)).
astepr (nring (R:=R) n[+]nring p).
astepr (nring (R:=R) (n + p)).
astepl (nring (R:=R) (m + q)).
rewrite H.
Algebra.
Qed.

Hint Resolve zring_old_diff.

Lemma zring_old_plus_nat : forall n : nat, zring_old n [=] nring n.
intro n.
replace (n:Z) with (n - 0%nat)%Z.
 astepl (nring (R:=R) n[-]nring 0).
 simpl in |- *; Algebra.
simpl in |- *; auto with zarith.
Qed.

Hint Resolve zring_old_plus_nat: algebra.

Lemma zring_old_inv_nat : forall n : nat, zring_old (- n) [=] [--] (nring n).
intro n.
replace (- n)%Z with (0%nat - n)%Z.
 astepl (nring 0[-]nring (R:=R) n).
 simpl in |- *; Algebra.
simpl in |- *; auto.
Qed.

Hint Resolve zring_old_inv_nat: algebra.

Lemma zring_old_plus : forall i j, zring_old (i + j) [=] zring_old i[+]zring_old j.
intros i j.
pattern i in |- *.
apply diff_Z_ind.
intros m n.
pattern j in |- *.
apply diff_Z_ind.
intros m0 n0.
Hint Resolve zring_old_diff: algebra.
replace (m - n + (m0 - n0))%Z with ((m + m0)%nat - (n + n0)%nat)%Z.
astepl (nring (m + m0) [-]nring (n + n0):R).
astepl (nring m[+]nring m0[-] (nring n[+]nring n0):R).
astepr (nring m[-]nring n[+] (nring m0[-]nring n0):R).
unfold cg_minus in |- *.
astepl (nring m[+] (nring m0[+] [--] (nring n[+]nring n0)):R).
astepr (nring m[+] ( [--] (nring n) [+] (nring m0[+] [--] (nring n0))):R).
apply bin_op_wd_unfolded.
 Algebra.
astepl (nring m0[+] ( [--] (nring n) [+] [--] (nring n0)):R).
astepl (nring m0[+] [--] (nring n) [+] [--] (nring n0):R).
Step_final ( [--] (nring n) [+]nring m0[+] [--] (nring n0):R).

repeat rewrite Znat.inj_plus.
auto with zarith.
Qed.

Hint Resolve zring_old_plus: algebra.

Lemma zring_old_inv : forall i, zring_old (- i) [=] [--] (zring_old i).
intro i.
pattern i in |- *.
apply diff_Z_ind.
intros m n.
replace (- (m - n))%Z with (n - m)%Z.
astepl (nring (R:=R) n[-]nring m).
astepr ( [--] (nring (R:=R) m[-]nring n)).
unfold cg_minus in |- *.
astepr ( [--] (nring m) [+] [--][--] (nring (R:=R) n)).
Step_final ( [--] (nring (R:=R) m) [+]nring n).

auto with zarith.
Qed.

Hint Resolve zring_old_inv: algebra.

Lemma zring_old_minus : forall i j, zring_old (i - j) [=] zring_old i[-]zring_old j.
intros i j.
unfold cg_minus in |- *.
replace (i - j)%Z with (i + - j)%Z.
Step_final (zring_old i[+]zring_old (- j)).

auto.
Qed.

Hint Resolve zring_old_minus: algebra.

Lemma zring_old_mult : forall i j, zring_old (i * j) [=] zring_old i[*]zring_old j.
intros i j.
pattern i in |- *.
apply diff_Z_ind.
intros m n.
pattern j in |- *.
apply diff_Z_ind.
intros m0 n0.
astepr ((nring (R:=R) m[-]nring n) [*] (nring m0[-]nring n0)).
replace ((m - n) * (m0 - n0))%Z with
 ((m * m0 + n * n0)%nat - (n * m0 + m * n0)%nat)%Z.
 2: repeat rewrite Znat.inj_plus.
 2: repeat rewrite Znat.inj_mult.
 2: repeat rewrite BinInt.Zmult_minus_distr_r.
 2: repeat rewrite Basics.Zmult_minus_distr_r.
 2: auto with zarith.
astepl (nring (R:=R) (m * m0 + n * n0) [-]nring (n * m0 + m * n0)).
astepl
 (nring (R:=R) (m * m0) [+]nring (n * n0) [-] (nring (n * m0) [+]nring (m * n0))).
astepl
 (nring (R:=R) m[*]nring m0[+]nring n[*]nring n0[-]
  (nring n[*]nring m0[+]nring m[*]nring n0)).
astepr
 (nring (R:=R) m[*] (nring m0[-]nring n0) [-]nring n[*] (nring m0[-]nring n0)).
astepr
 (nring (R:=R) m[*]nring m0[-]nring m[*]nring n0[-]
  (nring n[*]nring m0[-]nring n[*]nring n0)).
unfold cg_minus in |- *.
astepr
 (nring (R:=R) m[*]nring m0[+]
  ( [--] (nring m[*]nring n0) [+]
   [--] (nring n[*]nring m0[+] [--] (nring n[*]nring n0)))).
astepl
 (nring (R:=R) m[*]nring m0[+]
  (nring n[*]nring n0[+] [--] (nring n[*]nring m0[+]nring m[*]nring n0))).
apply bin_op_wd_unfolded.
 Algebra.
astepl
 (nring (R:=R) n[*]nring n0[+]
  ( [--] (nring n[*]nring m0) [+] [--] (nring m[*]nring n0))).
astepr
 ( [--] (nring (R:=R) m[*]nring n0) [+]
  ( [--] (nring n[*]nring m0) [+] [--][--] (nring n[*]nring n0))).
astepr
 ( [--] (nring (R:=R) m[*]nring n0) [+]
  ( [--] (nring n[*]nring m0) [+]nring n[*]nring n0)).
astepr
 ( [--] (nring (R:=R) m[*]nring n0) [+]
  (nring n[*]nring n0[+] [--] (nring n[*]nring m0))).
astepr
 ( [--] (nring (R:=R) m[*]nring n0) [+]nring n[*]nring n0[+]
  [--] (nring n[*]nring m0)).
astepr
 (nring (R:=R) n[*]nring n0[+] [--] (nring m[*]nring n0) [+]
  [--] (nring n[*]nring m0)).
Step_final
 (nring (R:=R) n[*]nring n0[+]
  ( [--] (nring m[*]nring n0) [+] [--] (nring n[*]nring m0))).
Qed.

Hint Resolve zring_old_mult: algebra.

Lemma zring_old_one : zring_old 1 [=] One.
simpl in |- *.
Step_final (One[-]Zero:R).
Qed.

Hint Resolve zring_old_one: algebra.

Lemma zring_old_inv_one : forall x, zring_old (-1) [*]x [=] [--]x.
intro x.
simpl in |- *.
astepl ( [--] (Zero[+]One) [*]x).
astepl ( [--]One[*]x).
Step_final ( [--] (One[*]x)).
Qed.

(*************** new def of zring. ***********************)

(** The [zring] function can be defined directly.  This is done here.
*)

Fixpoint pring_aux (p : positive) (pow2 : R) {struct p} : R :=
  match p with
  | xH   => pow2
  | xO p => pring_aux p (Two[*]pow2)
  | xI p => pow2[+]pring_aux p (Two[*]pow2)
  end.

Definition pring (p : positive) : R := pring_aux p One.

Definition zring (z : Z) : R :=
  match z with
  | Z0     => Zero
  | Zpos p => pring p
  | Zneg p => [--] (pring p)
  end.

Lemma pring_aux_lemma : forall p r r', r [=] r' -> pring_aux p r [=] pring_aux p r'.
simple induction p; simpl in |- *; Algebra.
Qed.

Lemma double_nring : forall n, Two[*]nring (R:=R) n [=] nring (R:=R) (n + n).
intros.
Step_final (nring (R:=R) n[+]nring n).
Qed.

Hint Resolve pring_aux_lemma double_nring: algebra.

Lemma pring_aux_nring : forall p n, pring_aux p (nring n) [=] nring (Pmult_nat p n).
simple induction p; simpl in |- *; intros.

astepl (nring n[+]pring_aux p0 (nring (n + n))).
Step_final (nring (R:=R) n[+]nring (R:=R) (Pmult_nat p0 (n + n))).

Step_final (pring_aux p0 (nring (n + n))).

Algebra.
Qed.
Hint Resolve pring_aux_nring: algebra.

Lemma pring_convert : forall p, pring p [=] nring (nat_of_P p).
intros; unfold pring, nat_of_P in |- *; simpl in |- *.
astepr (pring_aux p (nring 1)).
simpl in |- *; Algebra.
Qed.
Hint Resolve pring_convert: algebra.

Lemma zring_zring_old : forall z : Z, zring z [=] zring_old z.
simple induction z; simpl in |- *; intros.
Algebra.
astepr (nring (R:=R) (nat_of_P p)).
Algebra.
astepr ( [--] (nring (R:=R) (nat_of_P p))).
Algebra.
Qed.

Hint Resolve zring_zring_old: algebra.

Lemma zring_zero : zring 0 [=] Zero.
simpl in |- *; Algebra.
Qed.

Lemma zring_diff : forall m n : nat, zring (m - n) [=] nring m[-]nring n.
intros; Step_final (zring_old (m - n)).
Qed.

Lemma zring_plus_nat : forall n : nat, zring n [=] nring n.
intro n; Step_final (zring_old n).
Qed.

Lemma zring_inv_nat : forall n : nat, zring (- n) [=] [--] (nring n).
intro n; Step_final (zring_old (- n)).
Qed.

Lemma zring_plus : forall i j, zring (i + j) [=] zring i[+]zring j.
intros.
astepl (zring_old (i + j)).
Step_final (zring_old i[+]zring_old j).
Qed.

Lemma zring_inv : forall i, zring (- i) [=] [--] (zring i).
intro i.
astepl (zring_old (- i)).
Step_final ( [--] (zring_old i)).
Qed.

Lemma zring_minus : forall i j, zring (i - j) [=] zring i[-]zring j.
intros i j.
astepl (zring_old (i - j)).
Step_final (zring_old i[-]zring_old j).
Qed.

Lemma zring_mult : forall i j, zring (i * j) [=] zring i[*]zring j.
intros i j.
astepl (zring_old (i * j)).
Step_final (zring_old i[*]zring_old j).
Qed.

Lemma zring_one : zring 1 [=] One.
simpl in |- *.
unfold pring in |- *.
Algebra.
Qed.

Lemma zring_inv_one : forall x, zring (-1) [*]x [=] [--]x.
intro x.
simpl in |- *.
unfold pring in |- *.
simpl in |- *.
Step_final ( [--] (One[*]x)).
Qed.

End int_injection.

Implicit Arguments zring [R].

Hint Resolve pring_convert zring_zero zring_diff zring_plus_nat zring_inv_nat
  zring_plus zring_inv zring_minus zring_mult zring_one zring_inv_one:
  algebra.


Section Ring_sums.

(**
** Ring sums
%\begin{convention}% Let [R] be a ring.
%\end{convention}%
*)
Variable R : CRing.

(**
*** Infinite Ring sums
*)
Section infinite_ring_sums.

Fixpoint Sum_upto (f : nat -> R) (n : nat) {struct n} : R :=
  match n with
  | O   => Zero
  | S x => f x[+]Sum_upto f x
  end.

Lemma sum_upto_O : forall f : nat -> R, Sum_upto f 0 [=] Zero.
Algebra.
Qed.

Definition Sum_from_upto f m n : R := Sum_upto f n[-]Sum_upto f m.

(**
Here's an alternative def of [Sum_from_upto], with a lemma that
it's equivalent to the original.
*)

Definition seq_from (f : nat -> R) (n i : nat) : R := f (n + i).

Definition Sum_from_upto_alt f m n : R := Sum_upto (seq_from f m) (n - m).

End infinite_ring_sums.

Section ring_sums_over_lists.
(** *** Ring Sums over Lists
*)

Fixpoint RList_Mem (l : list R) (n : nat) {struct n} : R :=
  match l, n with
  | nil,      _   => Zero
  | cons a _, O   => a
  | cons _ k, S y => RList_Mem k y
  end.

Fixpoint List_Sum_upto (l : list R) (n : nat) {struct n} : R :=
  match n with
  | O   => Zero
  | S x => RList_Mem l x[+]List_Sum_upto l x
  end.

Lemma list_sum_upto_O : forall l : list R, List_Sum_upto l 0 [=] Zero.
Algebra.
Qed.

Definition List_Sum_from_upto l m n := List_Sum_upto l n[-]List_Sum_upto l m.

End ring_sums_over_lists.
End Ring_sums.

(**
** Distribution properties
%\begin{convention}%
Let [R] be a ring.
%\end{convention}%
*)
Section Dist_properties.
Variable R : CRing.

Lemma dist_1b : forall x y z : R, (x[+]y) [*]z [=] x[*]z[+]y[*]z.
intros x y z.
astepl (z[*] (x[+]y)).
Step_final (z[*]x[+]z[*]y).
Qed.
Hint Resolve dist_1b: algebra.

Lemma dist_2a : forall x y z : R, z[*] (x[-]y) [=] z[*]x[-]z[*]y.
intros x y z.
astepl (z[*] (x[+] [--]y)).
astepl (z[*]x[+]z[*] [--]y).
Step_final (z[*]x[+] [--] (z[*]y)).
Qed.
Hint Resolve dist_2a: algebra.

Lemma dist_2b : forall x y z : R, (x[-]y) [*]z [=] x[*]z[-]y[*]z.
intros x y z.
astepl (z[*] (x[-]y)).
Step_final (z[*]x[-]z[*]y).
Qed.
Hint Resolve dist_2b: algebra.

Lemma mult_distr_sum0_lft :  forall (f : nat -> R) x n,
 Sum0 n (fun i => x[*]f i) [=] x[*]Sum0 n f.
intros f x n.
induction  n as [| n Hrecn].
 simpl in |- *; Algebra.
simpl in |- *.
Step_final (x[*]Sum0 n f[+]x[*]f n).
Qed.
Hint Resolve mult_distr_sum0_lft.

Lemma mult_distr_sum_lft : forall (f : nat -> R) x m n,
 Sum m n (fun i => x[*]f i) [=] x[*]Sum m n f.
intros f x m n.
unfold Sum in |- *.
unfold Sum1 in |- *.
Step_final (x[*]Sum0 (S n) f[-]x[*]Sum0 m f).
Qed.
Hint Resolve mult_distr_sum_lft: algebra.

Lemma mult_distr_sum_rht : forall (f : nat -> R) x m n,
 Sum m n (fun i => f i[*]x) [=] Sum m n f[*]x.
intros f x m n.
astepl (Sum m n (fun i : nat => x[*]f i)).
Step_final (x[*]Sum m n f).
Qed.

Lemma sumx_const : forall n (x : R), Sumx (fun i (_ : i < n) => x) [=] nring n[*]x.
intros n x; induction  n as [| n Hrecn].
 simpl in |- *; Algebra.
simpl in |- *.
astepr (nring n[*]x[+]One[*]x).
Step_final (nring n[*]x[+]x).
Qed.

End Dist_properties.

Hint Resolve dist_1b dist_2a dist_2b mult_distr_sum_lft mult_distr_sum_rht
  sumx_const: algebra.


(**
** Properties of exponentiation (with the exponent in [nat])
%\begin{convention}%
Let [R] be a ring.
%\end{convention}%
*)
Section NExp_properties.
Variable R : CRing.

Lemma nexp_wd : forall (x y : R) n, x [=] y -> x[^]n [=] y[^]n.
Algebra.
Qed.

Lemma nexp_strext : forall (x y : R) n, x[^]n [#] y[^]n -> x [#] y.
intros x y n H.
exact (un_op_strext_unfolded _ _ _ _ H).
Qed.

Lemma nexp_Sn : forall (x : R) n, x[*]x[^]n [=] x[^]S n.
intros x n.
Step_final (x[^]n[*]x).
Qed.

Hint Resolve nexp_wd nexp_Sn: algebra.

Lemma nexp_plus : forall (x : R) m n, x[^]m[*]x[^]n [=] x[^] (m + n).
intros x m n.
induction  m as [| m Hrecm].
 rewrite plus_O_n.
 Step_final (One[*]x[^]n).
rewrite plus_Sn_m.
astepl (x[^]m[*]x[*]x[^]n).
astepl (x[*]x[^]m[*]x[^]n).
astepl (x[*] (x[^]m[*]x[^]n)).
Step_final (x[*]x[^] (m + n)).
Qed.
Hint Resolve nexp_plus: algebra.

Lemma one_nexp : forall n : nat, (One:R) [^]n [=] One.
intro n.
induction  n as [| n Hrecn].
 Algebra.
astepl ((One:R) [*]One[^]n).
Step_final ((One:R) [*]One).
Qed.
Hint Resolve one_nexp: algebra.

Lemma mult_nexp : forall (x y : R) n, (x[*]y) [^]n [=] x[^]n[*]y[^]n.
intros x y n.
induction  n as [| n Hrecn].
 astepl (One:R).
 Step_final ((One:R) [*]One).
astepl (x[*]y[*] (x[*]y) [^]n).
astepl (x[*]y[*] (x[^]n[*]y[^]n)).
astepl (x[*] (y[*] (x[^]n[*]y[^]n))).
astepl (x[*] (y[*]x[^]n[*]y[^]n)).
astepl (x[*] (x[^]n[*]y[*]y[^]n)).
astepl (x[*] (x[^]n[*] (y[*]y[^]n))).
Step_final (x[*]x[^]n[*] (y[*]y[^]n)).
Qed.
Hint Resolve mult_nexp: algebra.

Lemma nexp_mult : forall (x : R) m n, (x[^]m) [^]n [=] x[^] (m * n).
intros x m n.
induction  m as [| m Hrecm].
 simpl in |- *.
 Step_final ((One:R) [^]n).
astepl ((x[*]x[^]m) [^]n).
astepl (x[^]n[*] (x[^]m) [^]n).
astepl (x[^]n[*]x[^] (m * n)).
astepl (x[^] (n + m * n)).
replace (n + m * n) with (S m * n); Algebra.
Qed.
Hint Resolve nexp_mult: algebra.

Lemma zero_nexp : forall (x : R) n, 0 < n -> (Zero:R) [^]n [=] Zero.
intros x n H.
induction  n as [| n Hrecn].
 inversion H.
Step_final ((Zero:R) [*]Zero[^]n).
Qed.
Hint Resolve zero_nexp: algebra.

Lemma inv_nexp_even : forall (x : R) n, even n -> [--]x[^]n [=] x[^]n.
intros x n H.
elim (even_2n n); try assumption.
intros m H0.
rewrite H0. unfold double in |- *.
astepl ( [--]x[^]m[*] [--]x[^]m).
astepl (( [--]x[*] [--]x) [^]m).
astepl ((x[*]x) [^]m).
Step_final (x[^]m[*]x[^]m).
Qed.
Hint Resolve inv_nexp_even: algebra.

Lemma inv_nexp_two : forall x : R, [--]x[^]2 [=] x[^]2.
intro x.
apply inv_nexp_even.
auto with arith.
Qed.
Hint Resolve inv_nexp_two: algebra.

Lemma inv_nexp_odd : forall (x : R) n, odd n -> [--]x[^]n [=] [--] (x[^]n).
intros x n H.
inversion H; clear H1 H n.
astepl ( [--]x[*] [--]x[^]n0).
astepl ( [--]x[*]x[^]n0).
Step_final ( [--] (x[*]x[^]n0)).
Qed.
Hint Resolve inv_nexp_odd: algebra.

Lemma nexp_one : forall x : R, x[^]1 [=] x.
intro x.
Step_final (One[*]x).
Qed.
Hint Resolve nexp_one: algebra.

Lemma nexp_two : forall x : R, x[^]2 [=] x[*]x.
intro x.
replace 2 with (1 + 1).
 Step_final (x[^]1[*]x[^]1).
auto with arith.
Qed.
Hint Resolve nexp_two: algebra.

Lemma inv_one_even_nexp : forall n : nat, even n -> [--]One[^]n [=] (One:R).
intros n H.
Step_final ((One:R) [^]n).
Qed.
Hint Resolve inv_one_even_nexp: algebra.

Lemma inv_one_odd_nexp : forall n : nat, odd n -> [--]One[^]n [=] [--] (One:R).
intros n H.
Step_final ( [--] ((One:R) [^]n)).
Qed.
Hint Resolve inv_one_odd_nexp: algebra.

Lemma square_plus : forall x y : R, (x[+]y) [^]2 [=] x[^]2[+]y[^]2[+]Two[*]x[*]y.
intros x y.
astepl ((x[+]y) [*] (x[+]y)).
astepl (x[*] (x[+]y) [+]y[*] (x[+]y)).
astepl (x[*]x[+]x[*]y[+] (y[*]x[+]y[*]y)).
astepl (x[^]2[+]x[*]y[+] (x[*]y[+]y[^]2)).
astepl (x[^]2[+]x[*]y[+]x[*]y[+]y[^]2).
astepl (x[^]2[+] (x[*]y[+]x[*]y) [+]y[^]2).
astepl (x[^]2[+]Two[*] (x[*]y) [+]y[^]2).
astepl (x[^]2[+]Two[*]x[*]y[+]y[^]2).
astepl (x[^]2[+] (Two[*]x[*]y[+]y[^]2)).
Step_final (x[^]2[+] (y[^]2[+]Two[*]x[*]y)).
Qed.

Lemma square_minus : forall x y : R, (x[-]y) [^]2 [=] x[^]2[+]y[^]2[-]Two[*]x[*]y.
intros x y.
unfold cg_minus in |- *.
eapply eq_transitive_unfolded.
 apply square_plus.
Algebra.
Qed.

Lemma nexp_funny : forall x y : R, (x[+]y) [*] (x[-]y) [=] x[^]2[-]y[^]2.
intros x y.
astepl (x[*] (x[-]y) [+]y[*] (x[-]y)).
astepl (x[*]x[-]x[*]y[+] (y[*]x[-]y[*]y)).
astepl (x[*]x[+] [--] (x[*]y) [+] (y[*]x[+] [--] (y[*]y))).
astepl (x[*]x[+] [--] (x[*]y) [+]y[*]x[+] [--] (y[*]y)).
astepl (x[*]x[+] ( [--] (x[*]y) [+]y[*]x) [+] [--] (y[*]y)).
astepl (x[*]x[+] ( [--] (x[*]y) [+]x[*]y) [+] [--] (y[*]y)).
astepl (x[*]x[+]Zero[+] [--] (y[*]y)).
astepl (x[*]x[+] [--] (y[*]y)).
Step_final (x[*]x[-]y[*]y).
Qed.
Hint Resolve nexp_funny: algebra.

Lemma nexp_funny' : forall x y : R, (x[-]y) [*] (x[+]y) [=] x[^]2[-]y[^]2.
intros x y.
Step_final ((x[+]y) [*] (x[-]y)).
Qed.
Hint Resolve nexp_funny': algebra.

End NExp_properties.

Hint Resolve nexp_wd nexp_Sn nexp_plus one_nexp mult_nexp nexp_mult zero_nexp
  inv_nexp_even inv_nexp_two inv_nexp_odd nexp_one nexp_two nexp_funny
  inv_one_even_nexp inv_one_odd_nexp nexp_funny' one_nexp square_plus
  square_minus: algebra.

Section CRing_Ops.

(**
** Functional Operations

Now for partial functions.

%\begin{convention}%
Let [R] be a ring and let [F,G:(PartFunct R)] with predicates
respectively [P] and [Q].
%\end{convention}%
*)

Variable R : CRing.

Variables F G : PartFunct R.

(* begin hide *)
Let P := Dom F.
Let Q := Dom G.
(* end hide *)

Section Part_Function_Mult.

Lemma part_function_mult_strext : forall x y (Hx : Conj P Q x) (Hy : Conj P Q y),
 F x (Prj1 Hx) [*]G x (Prj2 Hx) [#] F y (Prj1 Hy) [*]G y (Prj2 Hy) -> x [#] y.
intros x y Hx Hy H.
elim (bin_op_strext_unfolded _ _ _ _ _ _ H); intro H1;
 exact (pfstrx _ _ _ _ _ _ H1).
Qed.

Definition Fmult := Build_PartFunct R _ (conj_wd (dom_wd _ F) (dom_wd _ G))
 (fun x Hx => F x (Prj1 Hx) [*]G x (Prj2 Hx)) part_function_mult_strext.

End Part_Function_Mult.

Section Part_Function_Nth_Power.

Variable n : nat.

Lemma part_function_nth_strext : forall x y Hx Hy, F x Hx[^]n [#] F y Hy[^]n -> x [#] y.
intros x y Hx Hy H.
apply pfstrx with F Hx Hy.
apply nexp_strext with n; assumption.
Qed.

Definition Fnth := Build_PartFunct R _ (dom_wd R F)
 (fun x Hx => F x Hx[^]n) part_function_nth_strext.

End Part_Function_Nth_Power.

(**
%\begin{convention}% Let [R':R->CProp].
%\end{convention}%
*)

Variable R':R -> CProp.

Lemma included_FMult : included R' P -> included R' Q -> included R' (Dom Fmult).
intros; simpl in |- *; apply included_conj; assumption.
Qed.

Lemma included_FMult' : included R' (Dom Fmult) -> included R' P.
intro H; simpl in H; eapply included_conj_lft; apply H.
Qed.

Lemma included_FMult'' : included R' (Dom Fmult) -> included R' Q.
intro H; simpl in H; eapply included_conj_rht; apply H.
Qed.

Variable n:nat.

Lemma included_FNth : included R' P -> forall n, included R' (Dom (Fnth n)).
auto.
Qed.

Lemma included_FNth' : forall n, included R' (Dom (Fnth n)) -> included R' (Dom F).
auto.
Qed.

End CRing_Ops.

Definition Fscalmult (R:CRing) alpha F := Fmult R [-C-]alpha F.

Implicit Arguments Fmult [R].
Infix "{*}" := Fmult (at level 40, left associativity).

Implicit Arguments Fscalmult [R].
Infix "{**}" := Fscalmult (at level 40, left associativity).

Implicit Arguments Fnth [R].
Infix "{^}" := Fnth (at level 30, right associativity).

Section ScalarMultiplication.

Variable R : CRing.

Variable F : PartFunct R.

(* begin hide *)
Let P := Dom F.
(* end hide *)

Variable R':R -> CProp.

Lemma included_FScalMult : included R' P -> forall c, included R' (Dom (c{**}F)).
intros; simpl in |- *; apply included_conj.
red in |- *; intros; auto.
assumption.
Qed.

Lemma included_FScalMult' : forall c, included R' (Dom (c{**}F)) -> included R' P.
intros c H; simpl in H; eapply included_conj_rht; apply H.
Qed.

End ScalarMultiplication.

Hint Resolve included_FMult included_FScalMult included_FNth : included.

Hint Immediate included_FMult' included_FMult'' included_FScalMult'
    included_FNth' : included.
