(* $Id: FunctSums.v,v 1.5 2004/04/23 10:00:59 lcf Exp $ *)

(** printing FSum0 %\ensuremath{\sum_0}% #&sum;<sub>0</sub># *)
(** printing FSum %\ensuremath{\sum}% #&sum;# *)
(** printing FSumx %\ensuremath{\sum'}% #&sum;'&*)

Require Export CSumsReals.
Require Export PartFunEquality.

(** *Sums of Functions

In this file we define sums are defined of arbitrary families of
partial functions.

Given a countable family of functions, their sum is defined on the
intersection of all the domains.  As is the case for groups, we will
define three different kinds of sums.

We will first consider the case of a family
$\{f_i\}_{i\in\NN}$#{f<sub>i</sub>}# of functions; we can both define
$\sum_{i=0}^{n-1}f_i$#the sum of the first n functions# ( [FSum0]) or
$\sum_{i=m}^nf_i$#the sum of f<sub>m</sub> through f<sub>n</sub>#
( [FSum]).
*)

Definition FSum0 (n : nat) (f : nat -> PartIR) : PartIR.
intros.
apply
 Build_PartFunct
  with
    (fun x : IR => forall n : nat, Dom (f n) x)
    (fun (x : IR) (Hx : forall n : nat, Dom (f n) x) =>
     Sum0 n (fun n : nat => Part (f n) x (Hx n))).
intros x y H H0 n0.
apply (dom_wd _ (f n0) x).
apply H.
assumption.
intros x y Hx Hy H.
elim (Sum0_strext' _ _ _ _ H); intros i Hi.
apply pfstrx with (f i) (Hx i) (Hy i); assumption.
Defined.

Definition FSum (m n : nat) (f : nat -> PartIR) : PartIR.
intros.
apply
 Build_PartFunct
  with
    (fun x : IR => forall n : nat, Dom (f n) x)
    (fun (x : IR) (Hx : forall n : nat, Dom (f n) x) =>
     Sum m n (fun n : nat => Part (f n) x (Hx n))).
intros x y H H0 n0.
apply (dom_wd _ (f n0) x).
apply H.
assumption.
intros x y Hx Hy H.
elim (Sum_strext' _ _ _ _ _ H); intros i Hi.
apply pfstrx with (f i) (Hx i) (Hy i); assumption.
Defined.

(**
Although [FSum] is here defined directly, it has the same relationship
to the [FSum0] operator as [Sum] has to [Sum0].  Also, all the results
for [Sum] and [Sum0] hold when these operators are replaced by their
functional equivalents.  This is an immediate consequence of the fact
that the partial functions form a group; however, as we already
mentioned, their forming too big a type makes it impossible to use
those results.
*)

Lemma FSum_FSum0 : forall m n (f : nat -> PartIR) x Hx Hx' Hx'',
 FSum m n f x Hx [=] FSum0 (S n) f x Hx'[-]FSum0 m f x Hx''.
intros.
simpl in |- *; unfold Sum, Sum1 in |- *; simpl in |- *.
apply cg_minus_wd; try apply bin_op_wd_unfolded; try apply Sum0_wd; intros;
 Algebra.
Qed.

Lemma FSum0_wd : forall m (f g : nat -> PartIR),
 (forall x HxF HxG i, f i x (HxF i) [=] g i x (HxG i)) ->
 forall x HxF HxG, FSum0 m f x HxF [=] FSum0 m g x HxG.
intros.
simpl in |- *.
apply Sum0_wd.
intros; simpl in |- *; Algebra.
Qed.

Lemma FSum_one : forall n (f : nat -> PartIR) x Hx Hx',
 FSum n n f x Hx' [=] f n x (Hx n).
intros.
simpl in |- *.
eapply eq_transitive_unfolded.
apply Sum_one.
simpl in |- *; rational.
Qed.

Lemma FSum_FSum : forall l m n (f : nat -> PartIR) x Hx Hx' Hx'',
 FSum l m f x Hx[+]FSum (S m) n f x Hx' [=] FSum l n f x Hx''.
intros.
simpl in |- *.
eapply eq_transitive_unfolded.
2: apply Sum_Sum with (l := l) (m := m).
apply bin_op_wd_unfolded; apply Sum_wd; intros; rational.
Qed.

Lemma FSum_first : forall m n (f : nat -> PartIR) x Hx Hx' Hx'',
 FSum m n f x Hx [=] f m x Hx'[+]FSum (S m) n f x Hx''.
intros.
simpl in |- *.
eapply eq_transitive_unfolded.
apply Sum_first.
apply bin_op_wd_unfolded; try apply Sum_wd; intros; rational.
Qed.

Lemma FSum_last : forall m n (f : nat -> PartIR) x Hx Hx' Hx'',
 FSum m (S n) f x Hx [=] FSum m n f x Hx'[+]f (S n) x Hx''.
intros.
simpl in |- *.
eapply eq_transitive_unfolded.
apply Sum_last.
apply bin_op_wd_unfolded; try apply Sum_wd; intros; rational.
Qed.

Lemma FSum_last' : forall m n (f : nat -> PartIR) x Hx Hx' Hx'',
 0 < n -> FSum m n f x Hx [=] FSum m (pred n) f x Hx'[+]f n x Hx''.
intros.
simpl in |- *.
eapply eq_transitive_unfolded.
apply Sum_last'.
assumption.
apply bin_op_wd_unfolded; try apply Sum_wd; intros; rational.
Qed.

Lemma FSum_wd : forall m n (f g : nat -> PartIR),
 (forall x HxF HxG i, f i x (HxF i) [=] g i x (HxG i)) ->
 forall x HxF HxG, FSum m n f x HxF [=] FSum m n g x HxG.
intros.
simpl in |- *.
apply Sum_wd.
Algebra.
Qed.

Lemma FSum_plus_FSum : forall (f g : nat -> PartIR) m n x Hx HxF HxG,
 FSum m n (fun i => f i{+}g i) x Hx [=] FSum m n f x HxF[+]FSum m n g x HxG.
intros.
simpl in |- *.
eapply eq_transitive_unfolded.
2: apply Sum_plus_Sum.
apply Sum_wd; intros; rational.
Qed.

Lemma inv_FSum : forall (f : nat -> PartIR) m n x Hx Hx',
 FSum m n (fun i => {--} (f i)) x Hx [=] [--] (FSum m n f x Hx').
intros.
simpl in |- *.
eapply eq_transitive_unfolded.
2: apply inv_Sum.
apply Sum_wd; intros; rational.
Qed.

Lemma FSum_minus_FSum : forall (f g : nat -> PartIR) m n x Hx HxF HxG,
 FSum m n (fun i => f i{-}g i) x Hx [=] FSum m n f x HxF[-]FSum m n g x HxG.
intros.
simpl in |- *.
eapply eq_transitive_unfolded.
2: apply Sum_minus_Sum.
apply Sum_wd; intros; rational.
Qed.

Lemma FSum_wd' : forall m n, m <= S n -> forall f g : nat -> PartIR,
 (forall x HxF HxG i, m <= i -> i <= n -> f i x (HxF i) [=] g i x (HxG i)) ->
 forall x HxF HxG, FSum m n f x HxF [=] FSum m n g x HxG.
intros.
simpl in |- *.
apply Sum_wd'; try assumption.
Algebra.
Qed.

Lemma FSum_resp_less : forall (f g : nat -> PartIR) m n, m <= n ->
 (forall x HxF HxG i, m <= i -> i <= n -> f i x (HxF i) [<] g i x (HxG i)) ->
 forall x HxF HxG, FSum m n f x HxF [<] FSum m n g x HxG.
intros f g m n H H0 x HxF HxG.
simpl in |- *.
apply Sum_resp_less; try assumption.
intros; apply H0; assumption.
Qed.

Lemma FSum_resp_leEq : forall (f g : nat -> PartIR) m n, m <= S n ->
 (forall x HxF HxG i, m <= i -> i <= n -> f i x (HxF i) [<=] g i x (HxG i)) ->
 forall x HxF HxG, FSum m n f x HxF [<=] FSum m n g x HxG.
intros f g m n H H0 x HxF HxG.
simpl in |- *.
apply Sum_resp_leEq; try assumption.
intros; apply H0; assumption.
Qed.

Lemma FSum_comm_scal : forall (f : nat -> PartIR) c m n x Hx Hx',
 FSum m n (fun i => f i{*} [-C-]c) x Hx [=] (FSum m n f{*} [-C-]c) x Hx'.
intros.
simpl in |- *.
eapply eq_transitive_unfolded.
2: apply (Sum_comm_scal (fun n : nat => f n x (ProjIR1 Hx' n)) c m n).
apply Sum_wd; intros; rational.
Qed.

Lemma FSum_comm_scal' : forall (f : nat -> PartIR) c m n x Hx Hx',
 FSum m n (fun i => [-C-]c{*}f i) x Hx [=] ( [-C-]c{*}FSum m n f) x Hx'.
intros.
simpl in |- *.
eapply eq_transitive_unfolded.
2: apply (Sum_comm_scal' (fun n : nat => f n x (ProjIR2 Hx' n)) c m n).
apply Sum_wd; intros; rational.
Qed.

(**
Also important is the case when we have a finite family
$\{f_i\}_{i=0}^{n-1}$ of #exactly n# functions; in this case we need
to use the [FSumx] operator.
*)

Fixpoint FSumx (n : nat) : (forall i, i < n -> PartIR) -> PartIR :=
  match n return ((forall i, i < n -> PartIR) -> PartIR) with
  | O   => fun _ => [-C-]Zero
  | S p => fun f => FSumx p (fun i l => f i (lt_S i p l)) {+} f p (lt_n_Sn p)
  end.

(**
This operator is well defined, as expected.
*)

Lemma FSumx_wd : forall n (f g : forall i, i < n -> PartIR),
 (forall i Hi x HxF HxG, f i Hi x HxF [=] g i Hi x HxG) ->
 forall x HxF HxG, FSumx n f x HxF [=] FSumx n g x HxG.
intro; case n.
intros; simpl in |- *; Algebra.
clear n.
simple induction n.
intros; simpl in |- *; Algebra.
clear n; intro.
cut {p : nat | S n = p}; [ intro H | exists (S n); auto ].
elim H; intros p Hp.
rewrite Hp; intros.
simpl in |- *.
apply bin_op_wd_unfolded.
apply H0.
intros; apply H1.
apply H1.
Qed.

Lemma FSumx_wd' : forall (P : IR -> CProp) n (f g : forall i, i < n -> PartIR),
 (forall i H H', Feq P (f i H) (g i H')) -> Feq P (FSumx n f) (FSumx n g).
intros; induction  n as [| n Hrecn].
simpl in |- *; apply Feq_reflexive; apply included_IR.
simpl in |- *; apply Feq_plus; auto.
Qed.

(**
As was already the case for [Sumx], in many cases we will need to
explicitly assume that $f_i$#f<sub>1</sub># is independent of the proof that
[i [<] n].  This holds both for the value and the domain of the partial
function $f_i$#f<sub>i</sub>#.
*)

Definition ext_fun_seq n (f : forall i, i < n -> PartIR) := forall i j, i = j ->
  forall Hi Hj x y, x [=] y -> forall Hx Hy, f i Hi x Hx [=] f j Hj y Hy.

Definition ext_fun_seq' n (f : forall i, i < n -> PartIR) := forall i j, i = j ->
  forall Hi Hj x y, x [=] y -> Dom (f i Hi) x -> Dom (f j Hj) y.

Implicit Arguments ext_fun_seq [n].
Implicit Arguments ext_fun_seq' [n].

(**
Under these assumptions, we can characterize the domain and the value of the sum function from the domains and values of the summands:
*)

Lemma FSumx_pred : forall n (f : forall i, i < n -> PartIR),
 ext_fun_seq' f -> forall x, Dom (FSumx n f) x -> forall i Hi, Dom (f i Hi) x.
intros n f H x H0 i Hi; red in H; induction  n as [| n Hrecn].
elimtype False; inversion Hi.
elim (le_lt_eq_dec _ _ Hi); intro.
cut (i < n); [ intro | auto with arith ].
set (g := fun i Hi => f i (lt_S _ _ Hi)) in *.
apply H with i (lt_S _ _ H1) x.
auto.
Algebra.
change (Dom (g i H1) x) in |- *.
apply Hrecn.
unfold g in |- *; intros.
apply H with i0 (lt_S i0 n Hi0) x0; auto.
inversion_clear H0; assumption.
elim H0; intros H1 H2; clear H0 H1.
apply H with n (lt_n_Sn n) x; auto.
symmetry  in |- *; auto.
Algebra.
Qed.

Lemma FSumx_pred' : forall n (f : forall i, i < n -> PartIR),
 ext_fun_seq' f -> forall x, (forall i Hi, Dom (f i Hi) x) -> Dom (FSumx n f) x.
intros n f H x H0; induction  n as [| n Hrecn].
simpl in |- *; auto.
split.
apply Hrecn.
red in |- *; intros.
red in H.
exact (H _ _ H1 _ _ _ _ H2 X).
intros; auto.
apply H0.
Qed.

Lemma FSumx_char : forall n f x Hx Hf,
 FSumx n f x Hx [=] Sumx (fun i Hi => f i Hi x (FSumx_pred n f Hf x Hx i Hi)).
intro; induction  n as [| n Hrecn].
Algebra.
intros; simpl in |- *.
apply bin_op_wd_unfolded; Algebra.
cut (ext_fun_seq' (fun i Hi => f i (lt_S i n Hi))).
intro H.
eapply eq_transitive_unfolded.
apply Hrecn with (Hf := H).
apply Sumx_wd; intros; simpl in |- *; Algebra.
intros i j H H0 H' x0 y H1 H2.
apply Hf with i (lt_S i n H0) x0; auto.
Qed.

(**
As we did for arbitrary groups, it is often useful to rewrite this sums as ordinary sums.
*)

Definition FSumx_to_FSum n : (forall i, i < n -> PartIR) -> nat -> PartIR.
intros n f i.
elim (le_lt_dec n i); intro.
apply ( [-C-]Zero:PartIR).
apply (f i b).
Defined.

Lemma FSumx_lt : forall n (f : forall i, i < n -> PartIR), ext_fun_seq f ->
 forall i Hi x Hx Hx', FSumx_to_FSum n f i x Hx [=] f i Hi x Hx'.
do 6 intro.
unfold FSumx_to_FSum in |- *.
elim (le_lt_dec n i); intro; simpl in |- *.
elimtype False; apply (le_not_lt n i); auto.
intros; apply H; auto.
Algebra.
Qed.

Lemma FSumx_le : forall n (f : forall i, i < n -> PartIR), ext_fun_seq f ->
 forall i x Hx, n <= i -> FSumx_to_FSum n f i x Hx [=] Zero.
do 5 intro.
unfold FSumx_to_FSum in |- *.
elim (le_lt_dec n i); intro; simpl in |- *.
intro; Algebra.
intros; elimtype False; apply (le_not_lt n i); auto.
Qed.

Lemma FSum_FSumx_to_FSum : forall n (f : forall i, i < S n -> PartIR),
 ext_fun_seq f -> ext_fun_seq' f ->
 forall x Hx Hx', FSum 0 n (FSumx_to_FSum _ f) x Hx [=] FSumx _ f x Hx'.
simple induction n.
intros; simpl in |- *.
eapply eq_transitive_unfolded.
apply Sum_one.
simpl in |- *.
cut (0 < 1); [ intro | apply lt_n_Sn ].
astepr (Part (f 0 (lt_n_Sn 0)) x (ProjIR2 Hx')).
apply FSumx_lt; assumption.
clear n; intros n H f H0 H1 x Hx Hx'.
simpl in |- *.
eapply eq_transitive_unfolded.
apply Sum_last.
apply bin_op_wd_unfolded.
set (g := fun i (l : i < S n) => f i (lt_S _ _ l)) in *.
cut (ext_fun_seq g); intros.
cut (ext_fun_seq' g).
intro H3.
astepr
 (FSumx n (fun i (l : i < n) => g i (lt_S _ _ l)) x
    (ProjIR1 (ProjIR1 Hx')) [+]g n (lt_n_Sn n) x (ProjIR2 (ProjIR1 Hx'))).
cut (Dom (FSumx _ g) x).
intro H4; cut (forall m : nat, Dom (FSumx_to_FSum (S n) g m) x).
intro Hx''.
simpl in H.
apply
 eq_transitive_unfolded
  with (Sum 0 n (fun m : nat => FSumx_to_FSum (S n) g m x (Hx'' m))).
2: apply H with (f := g); try assumption.
apply Sum_wd'.
auto with arith.
intros.
cut (i < S (S n)); [ intro | auto with arith ].
apply eq_transitive_unfolded with (f i H7 x (FSumx_pred _ _ H1 x Hx' i H7)).
apply FSumx_lt; assumption.
cut (i < S n); [ intro | auto with arith ].
apply eq_transitive_unfolded with (g i H8 x (FSumx_pred _ _ H3 x H4 i H8)).
2: apply eq_symmetric_unfolded; apply FSumx_lt; assumption.
unfold g in |- *; apply H0; auto.
Algebra.
intro.
simpl in Hx.
generalize (Hx m); clear H4 H3 H2 Hx.
unfold FSumx_to_FSum in |- *.
elim (le_lt_dec (S n) m); elim (le_lt_dec (S (S n)) m); do 2 intro;
 simpl in |- *; intro.
auto.
auto.
unfold g in |- *; apply FSumx_pred with (n := S (S n)); assumption.
unfold g in |- *; apply FSumx_pred with (n := S (S n)); assumption.
simpl in Hx'.
unfold g in |- *; inversion_clear Hx'; intros; assumption.
unfold g in |- *; red in |- *; intros.
red in H1; apply H1 with i (lt_S _ _ Hi) x0; auto.
unfold g in |- *; red in |- *; intros.
red in H0; apply H0; auto.
apply FSumx_lt; auto.
Qed.

(**
Some useful lemmas follow.
*)

Lemma FSum0_0 : forall P f, (forall n, included P (Dom (f n))) -> Feq P [-C-]Zero (FSum0 0 f).
intros P f H.
FEQ.
simpl in |- *.
red in |- *; intros; apply (H n); auto.
Qed.

Lemma FSum0_S : forall P f n, (forall m, included P (Dom (f m))) ->
 Feq P (FSum0 n f{+}f n) (FSum0 (S n) f).
intros P f n H.
FEQ.
apply included_FPlus; auto.
simpl in |- *; red in |- *; intros.
apply (H n0); auto.
simpl in |- *.
red in |- *; intros; apply (H n0); auto.
simpl in |- *; apply bin_op_wd_unfolded; Algebra.
apply Sum0_wd; Algebra.
Qed.

Lemma FSum_0 : forall P f n, (forall i, included P (Dom (f i))) -> Feq P (f n) (FSum n n f).
intros P f n H.
FEQ.
simpl in |- *.
red in |- *; intros; apply (H n0); auto.
simpl in |- *.
apply eq_symmetric_unfolded.
eapply eq_transitive_unfolded.
apply Sum_one.
Algebra.
Qed.

Lemma FSum_S : forall P f m n, (forall i, included P (Dom (f i))) ->
 Feq P (FSum m n f{+}f (S n)) (FSum m (S n) f).
intros P f m n H.
apply eq_imp_Feq.
apply included_FPlus; auto.
simpl in |- *.
red in |- *; intros; apply (H n0); auto.
simpl in |- *.
red in |- *; intros; apply (H n0); auto.
intros; simpl in |- *; apply eq_symmetric_unfolded.
eapply eq_transitive_unfolded.
apply Sum_last.
Algebra.
Qed.

Lemma FSum_FSum0' : forall P f m n, (forall i, included P (Dom (f i))) ->
 Feq P (FSum m n f) (FSum0 (S n) f{-}FSum0 m f).
intros P f m n H.
apply eq_imp_Feq.
red in |- *; intros; intro; apply (H n0); auto.
apply included_FMinus; red in |- *; intros; intro; apply (H n0); auto.
intros.
apply
 eq_transitive_unfolded
  with (Part _ _ (ProjIR1 Hx') [-]FSum0 m f _ (ProjIR2 Hx')).
apply FSum_FSum0.
simpl in |- *; rational.
Qed.
