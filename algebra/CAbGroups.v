Require Export CGroups.

Section Abelian_Groups.

(**
* Abelian Groups
Now we introduce commutativity and add some results.
*)

Definition is_CAbGroup (G : CGroup) := commutes (csg_op (c:=G)).

Record CAbGroup : Type := 
  {cag_crr :> CGroup; cag_proof : is_CAbGroup cag_crr}.

Section AbGroup_Axioms.

Variable G : CAbGroup.
(**
%\begin{convention}%
Let [G] be an Abelian Group.
%\end{convention}%
*)

Lemma CAbGroup_is_CAbGroup : is_CAbGroup G.
elim G; auto.
Qed.

Lemma cag_commutes : commutes (csg_op (c:=G)).
exact CAbGroup_is_CAbGroup.
Qed.

Lemma cag_commutes_unfolded : forall x y : G, x[+]y[=]y[+]x.
Proof cag_commutes.

End AbGroup_Axioms.

Section SubCAbGroups.

(**
** Subgroups of an Abelian Group
*)
Variable G : CAbGroup.
Variable P : G -> CProp.
Variable Punit : P Zero.
Variable op_pres_P : bin_op_pres_pred _ P csg_op.
Variable inv_pres_P : un_op_pres_pred _ P cg_inv.

(**
%\begin{convention}%
Let [G] be an Abelian Group and [P] be a ([CProp]-valued) predicate on [G]
that contains [Zero] and is closed under [[+]] and [[--]].
%\end{convention}%
*)

Let subcrr : CGroup := Build_SubCGroup _ _ Punit op_pres_P inv_pres_P.

Lemma isabgrp_scrr : is_CAbGroup subcrr.
red in |- *. intros x y. case x. case y. intros. simpl in |- *. apply cag_commutes_unfolded.
Qed.

Definition Build_SubCAbGroup : CAbGroup := Build_CAbGroup subcrr isabgrp_scrr.

End SubCAbGroups.

Section Various.
(**
** Basic properties of Abelian groups
*)	
Hint Resolve cag_commutes_unfolded: algebra.

Variable G : CAbGroup.
(**
%\begin{convention}%
Let [G] be an Abelian Group.
%\end{convention}%
*)

Lemma cag_op_inv : forall x y : G, [--](x[+]y)[=][--]x[+][--]y.
intros x y.
AStepr ([--]y[+][--]x).
apply cg_inv_op.
Qed.

Hint Resolve cag_op_inv: algebra.

Lemma assoc_1 : forall x y z : G, x[-](y[-]z)[=]x[-]y[+]z.
intros x y z; unfold cg_minus in |- *.
AStepr (x[+]([--]y[+]z)).
Step_final (x[+]([--]y[+][--][--]z)).
Qed.

Lemma minus_plus : forall x y z : G, x[-](y[+]z)[=]x[-]y[-]z.
intros x y z.
unfold cg_minus in |- *.
Step_final (x[+]([--]y[+][--]z)).
Qed.

Lemma op_lft_resp_ap : forall x y z : G, y[#]z -> x[+]y[#]x[+]z.
Proof.
intros x y z H.
AStepl (y[+]x).
AStepr (z[+]x).
apply op_rht_resp_ap; assumption.
Qed.

Lemma cag_ap_cancel_lft : forall x y z : G, x[+]y[#]x[+]z -> y[#]z.
intros x y z H.
apply ap_symmetric_unfolded.
apply cg_ap_cancel_rht with x.
apply ap_symmetric_unfolded.
AStepl (x[+]y).
AStepr (x[+]z).
auto.
Qed.

Lemma plus_cancel_ap_lft : forall x y z : G, z[+]x[#]z[+]y -> x[#]y.
intros x y z H.
apply cag_ap_cancel_lft with z.
assumption.
Qed.

End Various.

End Abelian_Groups.

Hint Resolve cag_commutes_unfolded: algebra.
Hint Resolve cag_op_inv assoc_1 zero_minus minus_plus op_lft_resp_ap: algebra.

Section Nice_Char.

(**
** Building an abelian group

In order to actually define concrete abelian groups,
it is not in general practical to construct first a semigroup,
then a monoid, then a group and finally an abelian group.  The
presence of commutativity, for example, makes many of the monoid
proofs trivial.  In this section, we provide a constructor that
will allow us to go directly from a setoid to an abelian group.

We start from a setoid S with an element [unit], a
commutative and associative binary operation [plus] which
is strongly extensional in its first argument and admits [unit]
as a left unit, and a unary setoid
function [inv] which inverts elements respective to [plus].
*)

Variable S : CSetoid.
Variable unit : S.
Variable plus : S -> S -> S.
(**
%\begin{convention}%
Let [S] be a Setoid and [unit:S], [plus:S->S->S] and [inv] a unary
setoid operation on [S].
Assume that [plus] is commutative, associative and `left-strongly-extensional
([(plus x z) [#] (plus y z)->x [#] y]), that [unit] is a left-unit
for [plus] and [(inv x)] is a right-inverse of [x] w.r.t.%\% [plus].
%\end{convention}%
*)

Hypothesis plus_lext : forall x y z : S, plus x z[#]plus y z -> x[#]y.
Hypothesis plus_lunit : forall x : S, plus unit x[=]x.
Hypothesis plus_comm : forall x y : S, plus x y[=]plus y x.
Hypothesis plus_assoc : associative plus.

Variable inv : CSetoid_un_op S.

Hypothesis inv_inv : forall x : S, plus x (inv x)[=]unit.

Lemma plus_rext : forall x y z : S, plus x y[#]plus x z -> y[#]z.
intros x y z H.
apply plus_lext with x.
AStepl (plus x y).
AStepr (plus x z).
auto.
Qed.

Lemma plus_runit : forall x : S, plus x unit[=]x.
intro x.
Step_final (plus unit x).
Qed.

Lemma plus_is_fun : bin_fun_strong_ext _ _ _ plus.
intros x x' y y' H.
elim (ap_cotransitive_unfolded _ _ _ H (plus x y')); intro H'.
 right; apply plus_lext with x.
 AStepl (plus x y); AStepr (plus x y'); auto.
left; eauto.
Qed.

Lemma inv_inv' : forall x : S, plus (inv x) x[=]unit.
intro.
Step_final (plus x (inv x)).
Qed.

Definition plus_fun : CSetoid_bin_op S :=
  Build_CSetoid_bin_fun _ _ _ plus plus_is_fun.

Definition Build_CSemiGroup' : CSemiGroup.
apply Build_CSemiGroup with S plus_fun.
exact plus_assoc.
Defined.

Definition Build_CMonoid' : CMonoid.
apply Build_CMonoid with Build_CSemiGroup' unit.
apply Build_is_CMonoid.
exact plus_runit.
exact plus_lunit.
Defined.

Definition Build_CGroup' : CGroup.
apply Build_CGroup with Build_CMonoid' inv.
split.
auto.
apply inv_inv'.
Defined.

Definition Build_CAbGroup' : CAbGroup.
apply Build_CAbGroup with Build_CGroup'.
exact plus_comm.
Defined.

End Nice_Char.

(** ** Iteration

For reflection the following is needed; hopefully it is also useful.
*)

Section Group_Extras.

Variable G : CAbGroup.

Fixpoint nmult (a:G) (n:nat) {struct n} : G :=
  match n with
  | O => Zero
  | S p => a[+]nmult a p
  end.

Lemma nmult_wd :
 forall (x y:G) (n m:nat), (x[=]y) -> n = m -> nmult x n[=]nmult y m.
simple induction n; intros.
rewrite <- H0; Algebra.
rewrite <- H1; simpl in |- *; Algebra.
Qed.

Lemma nmult_one : forall x:G, nmult x 1[=]x.
simpl in |- *; Algebra.
Qed.

Lemma nmult_Zero : forall n:nat, nmult Zero n[=]Zero.
intro n.
induction n.
 Algebra.
simpl in |- *; Step_final ((Zero:G)[+]Zero).
Qed.

Lemma nmult_plus :
 forall (m n:nat) (x:G), nmult x m[+]nmult x n[=]nmult x (m + n).
simple induction m.
 simpl in |- *; Algebra.
clear m; intro m.
intros.
simpl in |- *. Step_final (x[+](nmult x m[+]nmult x n)).
Qed.

Lemma nmult_mult :
 forall (n m:nat) (x:G), nmult (nmult x m) n[=]nmult x (m * n).
simple induction n.
 intro. rewrite mult_0_r. Algebra.
clear n; intros.
simpl in |- *.
rewrite mult_comm. simpl in |- *.
eapply eq_transitive_unfolded.
 2: apply nmult_plus.
rewrite mult_comm. Algebra.
Qed.

Lemma nmult_inv : forall (n:nat) (x:G), nmult [--]x n[=][--](nmult x n).
intro; induction n; simpl in |- *.
 Algebra.
intros.
Step_final ([--]x[+][--](nmult x n)).
Qed.

Lemma nmult_plus' :
 forall (n:nat) (x y:G), nmult x n[+]nmult y n[=]nmult (x[+]y) n.
intro; induction n; simpl in |- *; intros.
 Algebra.
AStepr (x[+]y[+](nmult x n[+]nmult y n)).
AStepr (x[+](y[+](nmult x n[+]nmult y n))).
AStepr (x[+](y[+]nmult x n[+]nmult y n)).
AStepr (x[+](nmult x n[+]y[+]nmult y n)).
Step_final (x[+](nmult x n[+](y[+]nmult y n))).
Qed.

Hint Resolve nmult_wd nmult_Zero nmult_inv nmult_plus nmult_plus': algebra.

Definition zmult (a:G) (z:Z) : G :=
  caseZ_diff z (fun n m:nat => nmult a n[-]nmult a m).

Lemma Zeq_imp_nat_eq : forall m n:nat, m = n -> m = n.
intro m; induction m.
intro n; induction n; auto.

intro; induction n.
intro. inversion H.
intros.
rewrite (IHm n).
auto.
repeat rewrite inj_S in H.
auto with zarith.
Qed.

Lemma zmult_char :
 forall (m n:nat) (z:Z),
   z = (m - n)%Z -> forall x:G, zmult x z[=]nmult x m[-]nmult x n.
simple induction z; intros.

simpl in |- *.
replace m with n. Step_final (Zero:G). auto with zarith.

simpl in |- *.
AStepl (nmult x (nat_of_P p)).
apply cg_cancel_rht with (nmult x n).
AStepr (nmult x m).
AStepl (nmult x (nat_of_P p + n)).
apply nmult_wd; Algebra.
apply Zeq_imp_nat_eq.
rewrite <- convert_is_POS in H.
auto with zarith.

simpl in |- *.
AStepl [--](nmult x (nat_of_P p)).
unfold cg_minus in |- *.
AStepr ([--][--](nmult x m)[+][--](nmult x n)).
AStepr [--]([--](nmult x m)[+]nmult x n).
apply un_op_wd_unfolded.
apply cg_cancel_lft with (nmult x m).
AStepr (nmult x m[+][--](nmult x m)[+]nmult x n).
AStepr (Zero[+]nmult x n).
AStepr (nmult x n).
AStepl (nmult x (m + nat_of_P p)).
apply nmult_wd; Algebra.
apply Zeq_imp_nat_eq.
rewrite <- min_convert_is_NEG in H.
auto with zarith.
Qed.

Lemma zmult_wd :
 forall (x y:G) (n m:Z), (x[=]y) -> n = m -> zmult x n[=]zmult y m.
do 3 intro.
case n; intros; inversion H0.
Algebra.
unfold zmult in |- *.
simpl in |- *.
AStepl (nmult x (nat_of_P p)); Step_final (nmult y (nat_of_P p)).
simpl in |- *.
AStepl [--](nmult x (nat_of_P p)).
Step_final [--](nmult y (nat_of_P p)).
Qed.

Lemma zmult_one : forall x:G, zmult x 1[=]x.
simpl in |- *; Algebra.
Qed.

Lemma zmult_min_one : forall x:G, zmult x (-1)[=][--]x.
intros; simpl in |- *; Step_final (Zero[-]x).
Qed.

Lemma zmult_zero : forall x:G, zmult x 0[=]Zero.
simpl in |- *; Algebra.
Qed.

Lemma zmult_Zero : forall k:Z, zmult Zero k[=]Zero.
intro; induction k; simpl in |- *.
  Algebra.
 Step_final ((Zero:G)[-]Zero).
Step_final ((Zero:G)[-]Zero).
Qed.

Hint Resolve zmult_zero: algebra.

Lemma zmult_plus :
 forall (m n:Z) (x:G), zmult x m[+]zmult x n[=]zmult x (m + n).
intros; case m; case n; intros.

simpl in |- *; Step_final (Zero[+](Zero[-]Zero):G).

simpl in |- *; Step_final (Zero[+](nmult x (nat_of_P p)[-]Zero)).

simpl in |- *; Step_final (Zero[+](Zero[-]nmult x (nat_of_P p))).

simpl in |- *; Step_final (nmult x (nat_of_P p)[-]Zero[+]Zero).

simpl in |- *.
AStepl (nmult x (nat_of_P p0)[+]nmult x (nat_of_P p)).
AStepr (nmult x (nat_of_P (p0 + p))).
rewrite nat_of_P_plus_morphism. apply nmult_plus.

simpl (zmult x (Zpos p0)[+]zmult x (Zneg p)) in |- *.
AStepl (nmult x (nat_of_P p0)[+][--](nmult x (nat_of_P p))).
AStepl (nmult x (nat_of_P p0)[-]nmult x (nat_of_P p)).
apply eq_symmetric_unfolded;
 apply zmult_char with (z := (Zpos p0 + Zneg p)%Z).
rewrite convert_is_POS. unfold Zminus in |- *. rewrite min_convert_is_NEG; auto.

rewrite <- Zplus_0_r_reverse. Step_final (zmult x (Zneg p)[+]Zero).

simpl (zmult x (Zneg p0)[+]zmult x (Zpos p)) in |- *.
AStepl ([--](nmult x (nat_of_P p0))[+]nmult x (nat_of_P p)).
AStepl (nmult x (nat_of_P p)[+][--](nmult x (nat_of_P p0))).
AStepl (nmult x (nat_of_P p)[-]nmult x (nat_of_P p0)).
rewrite Zplus_comm.
apply eq_symmetric_unfolded;
 apply zmult_char with (z := (Zpos p + Zneg p0)%Z).
rewrite convert_is_POS. unfold Zminus in |- *. rewrite min_convert_is_NEG; auto.

simpl in |- *.
AStepl ([--](nmult x (nat_of_P p0))[+][--](nmult x (nat_of_P p))).
AStepl [--](nmult x (nat_of_P p0)[+]nmult x (nat_of_P p)).
AStepr [--](nmult x (nat_of_P (p0 + p))).
apply un_op_wd_unfolded.
rewrite nat_of_P_plus_morphism. apply nmult_plus.
Qed.

Lemma zmult_mult :
 forall (m n:Z) (x:G), zmult (zmult x m) n[=]zmult x (m * n).
simple induction m; simple induction n; simpl in |- *; intros.

Step_final (Zero[-]Zero[+](Zero:G)).

AStepr (Zero:G). AStepl (nmult (Zero[-]Zero) (nat_of_P p)).
Step_final (nmult Zero (nat_of_P p)).

AStepr [--](Zero:G). AStepl [--](nmult (Zero[-]Zero) (nat_of_P p)).
Step_final [--](nmult Zero (nat_of_P p)).

Algebra.

AStepr (nmult x (nat_of_P (p * p0))).
AStepl (nmult (nmult x (nat_of_P p)) (nat_of_P p0)[-]Zero).
AStepl (nmult (nmult x (nat_of_P p)) (nat_of_P p0)).
rewrite nat_of_P_mult_morphism. apply nmult_mult.

AStepr [--](nmult x (nat_of_P (p * p0))).
AStepl (Zero[-]nmult (nmult x (nat_of_P p)) (nat_of_P p0)).
AStepl [--](nmult (nmult x (nat_of_P p)) (nat_of_P p0)).
rewrite nat_of_P_mult_morphism. apply un_op_wd_unfolded. apply nmult_mult.

Algebra.

AStepr [--](nmult x (nat_of_P (p * p0))).
AStepl (nmult [--](nmult x (nat_of_P p)) (nat_of_P p0)[-]Zero).
AStepl (nmult [--](nmult x (nat_of_P p)) (nat_of_P p0)).
rewrite nat_of_P_mult_morphism. eapply eq_transitive_unfolded.
apply nmult_inv. apply un_op_wd_unfolded. apply nmult_mult.

AStepr (nmult x (nat_of_P (p * p0))).
AStepr [--][--](nmult x (nat_of_P (p * p0))).
AStepl (Zero[-]nmult [--](nmult x (nat_of_P p)) (nat_of_P p0)).
AStepl [--](nmult [--](nmult x (nat_of_P p)) (nat_of_P p0)).
rewrite nat_of_P_mult_morphism. apply un_op_wd_unfolded. eapply eq_transitive_unfolded.
apply nmult_inv. apply un_op_wd_unfolded. apply nmult_mult.
Qed.

Lemma zmult_plus' :
 forall (z:Z) (x y:G), zmult x z[+]zmult y z[=]zmult (x[+]y) z.
intro z; pattern z in |- *.
apply nats_Z_ind.
 intro n; case n.
  intros; simpl in |- *. Step_final ((Zero:G)[+](Zero[-]Zero)).
 clear n; intros.
 rewrite POS_anti_convert; simpl in |- *. set (p := nat_of_P (P_of_succ_nat n)) in *.
 AStepl (nmult x p[+]nmult y p). Step_final (nmult (x[+]y) p).
intro n; case n.
 intros; simpl in |- *. Step_final ((Zero:G)[+](Zero[-]Zero)).
clear n; intros.
rewrite NEG_anti_convert; simpl in |- *. set (p := nat_of_P (P_of_succ_nat n)) in *.
AStepl ([--](nmult x p)[+][--](nmult y p)). AStepr [--](nmult (x[+]y) p).
Step_final [--](nmult x p[+]nmult y p).
Qed.

End Group_Extras.

Hint Resolve nmult_wd nmult_one nmult_Zero nmult_plus nmult_inv nmult_mult
  nmult_plus' zmult_wd zmult_one zmult_min_one zmult_zero zmult_Zero
  zmult_plus zmult_mult zmult_plus': algebra.

Implicit Arguments nmult [G].
Implicit Arguments zmult [G].
