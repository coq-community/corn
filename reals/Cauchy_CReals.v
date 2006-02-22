(* $Id: Cauchy_CReals.v,v 1.6 2004/05/26 15:58:32 letouzey Exp $ *)

Require Export Cauchy_COF.
Require Export CReals.

Section R_CReals.

(** * The Real Number Structure

We will now apply our Cauchy sequence construction to an archimedean ordered field in order to obtain a model of the real numbers.

** Injection of [Q]

We start by showing how to inject the rational numbers in the field of Cauchy sequences; this embedding preserves the algebraic operations.

%\begin{convention}% Let [F] be an ordered field.
%\end{convention}%
*)

Variable F : COrdField.

Notation "'R_COrdField''" := (R_COrdField F).

Definition inject_Q (x : F) : R_COrdField' := Build_CauchySeq _ _ (CS_seq_const _ x).

Lemma ing_eq : forall x y : F, x [=] y -> inject_Q x [=] inject_Q y.
Proof.
 intros.
 unfold inject_Q in |- *.
 simpl in |- *; intro H0.
 elim H0; intro.
 elim a; intros N HN.
 elim HN; clear H0 a HN; intros e He HN; simpl in HN.
 apply (less_irreflexive_unfolded _ e).
 apply leEq_less_trans with (Zero:F); auto.
 astepr (x[-]x); astepr (y[-]x); eauto with arith.

 elim b; intros N HN.
 elim HN; clear H0 b HN; intros e He HN; simpl in HN.
 apply (less_irreflexive_unfolded _ e).
 apply leEq_less_trans with (Zero:F); auto.
 astepr (x[-]x); astepr (x[-]y); eauto with arith.
Qed.

Lemma ing_plus : forall x y : F, inject_Q (x[+]y) [=] inject_Q x[+]inject_Q y.
Proof.
 intros.
 unfold inject_Q in |- *.
 simpl in |- *; intro H.
 elim H; intro.
 elim a; intros N HN.
 elim HN; clear H a HN; intros e He HN; simpl in HN.
 apply (less_irreflexive_unfolded _ e).
 apply leEq_less_trans with (Zero:F); auto.
 astepr (x[+]y[-] (x[+]y)); eauto with arith.

 elim b; intros N HN.
 elim HN; clear H b HN; intros e He HN; simpl in HN.
 apply (less_irreflexive_unfolded _ e).
 apply leEq_less_trans with (Zero:F); auto.
 astepr (x[+]y[-] (x[+]y)); eauto with arith.
Qed.

Lemma ing_min : forall x : F, inject_Q [--]x [=] [--] (inject_Q x).
Proof.
 intros.
 unfold inject_Q in |- *.
 simpl in |- *; intro H.
 elim H; intro.
 elim a; intros N HN.
 elim HN; clear H a HN; intros e He HN; simpl in HN.
 apply (less_irreflexive_unfolded _ e).
 apply leEq_less_trans with (Zero:F); auto.
 astepr ( [--]x[-][--]x); eauto with arith.

 elim b; intros N HN.
 elim HN; clear H b HN; intros e He HN; simpl in HN.
 apply (less_irreflexive_unfolded _ e).
 apply leEq_less_trans with (Zero:F); auto.
 astepr ( [--]x[-][--]x); eauto with arith.
Qed.

Lemma ing_lt : forall x y : F, x [<] y -> inject_Q x [<] inject_Q y.
Proof.
 intros.
 simpl in |- *.
 exists 0.
 exists ((y[-]x) [/]TwoNZ).
 apply pos_div_two.
 apply shift_zero_less_minus.
 assumption.
 intros.
 apply less_leEq; apply pos_div_two'.
 simpl in |- *.
 apply shift_zero_less_minus; auto.
Qed.

Lemma ing_ap : forall x y : F, x [#] y -> inject_Q x [#] inject_Q y.
intros x y H; elim (ap_imp_less _ _ _ H); intro Hlt; [ left | right ];
 apply ing_lt; auto.
Qed.

Lemma ing_cancel_eq : forall x y : F, inject_Q x [=] inject_Q y -> x [=] y.
intros x y Hxy.
apply not_ap_imp_eq; intro Hap.
elim (ap_irreflexive_unfolded _ (inject_Q x)).
astepr (inject_Q y).
apply ing_ap; auto.
Qed.

Lemma ing_cancel_less : forall x y : F, inject_Q x [<] inject_Q y -> x [<] y.
intros x y H.
elim H; intros N HN; elim HN; clear H HN; intros e He HN; simpl in HN.
apply less_leEq_trans with (x[+]e).
apply shift_less_plus'; astepl (Zero:F); auto.
apply shift_plus_leEq'; eauto.
Qed.

Lemma ing_le : forall x y : F, x [<=] y -> inject_Q x [<=] inject_Q y.
Proof.
 intros.
 intro.
 apply H.
 apply ing_cancel_less.
 auto.
Qed.

Lemma ing_cancel_leEq : forall x y : F, inject_Q x [<=] inject_Q y -> x [<=] y.
Proof.
 intros.
 intro.
 apply H.
 apply ing_lt.
 auto.
Qed.

Lemma ing_cancel_AbsSmall : forall e x y : F,
 AbsSmall (inject_Q e) (inject_Q x[-]inject_Q y) -> AbsSmall e (x[-]y).
Proof.
 intros.
 elim H.
 intros H0 H1.
 split.
 apply ing_cancel_leEq.
 astepl ( [--] (inject_Q e)).
 astepr (inject_Q x[-]inject_Q y).
 assumption.
 astepl (inject_Q x[+][--] (inject_Q y)).
 apply eq_transitive_unfolded with (inject_Q x[+]inject_Q [--]y).
 apply plus_resp_eq.
 apply eq_symmetric_unfolded.
 apply ing_min.
 Step_final (inject_Q (x[+][--]y)).
 apply eq_symmetric_unfolded.
 apply ing_plus.
 apply eq_symmetric_unfolded.
 apply ing_min.

 apply ing_cancel_leEq.
 astepl (inject_Q x[-]inject_Q y).
 assumption.
 astepl (inject_Q x[+][--] (inject_Q y)).
 apply eq_transitive_unfolded with (inject_Q x[+]inject_Q [--]y).
 apply plus_resp_eq.
 apply eq_symmetric_unfolded.
 apply ing_min.
 Step_final (inject_Q (x[+][--]y)).
 apply eq_symmetric_unfolded.
 apply ing_plus.
Qed.

Lemma ing_One : inject_Q (One:F) [=] One.
 apply not_ap_imp_eq; intro H.
 elim H; intro Hlt; elim Hlt; intros N HN; elim HN; clear H Hlt HN;
  intros e He HN; simpl in HN.

 apply (less_irreflexive_unfolded F Zero).
 apply less_leEq_trans with e; auto.
 astepr (One[-] (One:F)); eauto.

 apply (less_irreflexive_unfolded F Zero).
 apply less_leEq_trans with e; auto.
 astepr (One[-] (One:F)); eauto.
Qed.

Lemma ing_nring' : forall m n : nat,
 CS_seq _ (nring (R:=R_COrdField') n) m [=] CS_seq _ (inject_Q (nring n)) m.
intros.
induction  n as [| n Hrecn]; simpl in |- *; Algebra.
Qed.

Lemma ing_nring : forall n : nat, nring n [=] inject_Q (nring n).
Proof.
 intros.
 apply not_ap_imp_eq; intro Hap.
 elim Hap; intro Hlt; elim Hlt; intros N HN; elim HN; clear Hap Hlt HN;
  intros e He HN.

 apply (less_irreflexive_unfolded F Zero).
 apply less_leEq_trans with e; auto.
 eapply leEq_wdr.
 apply (HN N); auto.
 apply x_minus_x; apply eq_symmetric_unfolded; apply ing_nring'.

 apply (less_irreflexive_unfolded F Zero).
 apply less_leEq_trans with e; auto.
 eapply leEq_wdr.
 apply (HN N); auto.
 apply x_minus_x; apply ing_nring'.
Qed.

Lemma ing_mult : forall x y : F, inject_Q (x[*]y) [=] inject_Q x[*]inject_Q y.
Proof.
 intros.
 unfold inject_Q in |- *.
 simpl in |- *; intro H.
 elim H; intro.
 elim a; intros N HN.
 elim HN; clear H a HN; intros e He HN; simpl in HN.
 apply (less_irreflexive_unfolded _ e).
 apply leEq_less_trans with (Zero:F); auto.
 astepr (x[*]y[-]x[*]y); eauto with arith.

 elim b; intros N HN.
 elim HN; clear H b HN; intros e He HN; simpl in HN.
 apply (less_irreflexive_unfolded _ e).
 apply leEq_less_trans with (Zero:F); auto.
 astepr (x[*]y[-]x[*]y); eauto with arith.
Qed.

Opaque R_COrdField.

Lemma ing_div_three : forall x, inject_Q x [/]ThreeNZ [=] inject_Q (x [/]ThreeNZ).
Proof.
 intros.
 apply mult_cancel_lft with (Three:R_COrdField').
 apply pos_ap_zero.
 apply pos_three.
 (* JZ: Removed Rational. *)
 apply eq_symmetric_unfolded.
 apply
  eq_transitive_unfolded with (inject_Q (Three:F) [*]inject_Q (x [/]ThreeNZ)).
 apply mult_wdl.
 apply ing_nring.
 apply eq_transitive_unfolded with (inject_Q (Three[*]x [/]ThreeNZ)).
 apply eq_symmetric_unfolded.
 apply ing_mult.
 astepr (inject_Q x).
 apply ing_eq; Algebra.
Qed.

Transparent R_COrdField.

Lemma ing_n : forall x n H1 H2,
 (inject_Q x[/] nring n[//]H2) [=] inject_Q (x[/] nring n[//]H1).
Proof.
 intros.
 apply mult_cancel_lft with (inject_Q (nring (R:=F) n)).
 apply Greater_imp_ap.
 astepr (nring (R:=R_COrdField') n).

 apply nring_pos.
 apply neq_O_lt.
 apply nring_ap_zero_imp with F.
 assumption.

 apply ing_nring.

 apply eq_transitive_unfolded with (inject_Q x).
 rstepr (nring n[*] (inject_Q x[/] nring n[//]H2)).
 apply mult_wdl.
 apply eq_symmetric_unfolded.
 apply ing_nring.
 apply eq_symmetric_unfolded.
 apply
  eq_transitive_unfolded with (inject_Q (nring n[*] (x[/] nring n[//]H1))).
 apply eq_symmetric_unfolded.
 apply ing_mult.
 apply ing_eq.
 rational.
Qed.

Theorem expand_Q_R : forall (x : R_COrdField') e, Zero [<] e -> forall N,
 (forall m, N <= m -> AbsSmall (e [/]FourNZ) (CS_seq F x m[-]CS_seq F x N)) ->
 forall m, N <= m -> AbsSmall (inject_Q e) (inject_Q (CS_seq F x m) [-]x).
Proof.
 intros x e H N H0 m H1.

 split.
 apply less_leEq.
 simpl in |- *.
 unfold Rlt in |- *.
 exists N.
 exists (e [/]ThreeNZ).
 apply pos_div_three.
 assumption.

 intros.
 change (e [/]ThreeNZ [<=] CS_seq F (inject_Q (CS_seq F x m) [-]x) n[-][--]e)
  in |- *.
 apply plus_cancel_leEq_rht with (R := F) (z := [--]e).
 rstepl ( [--] (Two[*]e [/]ThreeNZ)).
 rstepr (CS_seq F (inject_Q (CS_seq F x m) [-]x) n).
 cut (AbsSmall (e [/]FourNZ) (CS_seq F x m[-]CS_seq F x N)).
 intro H3.
 elim H3.
 intros H4 H5.
 cut (AbsSmall (e [/]FourNZ) (CS_seq F x n[-]CS_seq F x N)).
 intro H6.
 elim H6.
 intros H7 H8.
 change ( [--] (Two[*]e [/]ThreeNZ) [<=] CS_seq F x m[-]CS_seq F x n) in |- *.
 rstepl ( [--] (e [/]ThreeNZ) [+][--] (e [/]ThreeNZ)).
 rstepr (CS_seq F x m[-]CS_seq F x N[+] (CS_seq F x N[-]CS_seq F x n)).
 apply plus_resp_leEq_both.
 apply leEq_transitive with ( [--] (e [/]FourNZ)); auto.
 apply inv_resp_leEq.
 apply mult_cancel_leEq with (nring (R:=F) 12).
 apply nring_pos.
 auto with arith.
 rstepl (Zero[+]Three[*]e); rstepr (e[+]Three[*]e).
 apply plus_resp_leEq; apply less_leEq; auto.

 apply inv_cancel_leEq.
 rstepl (CS_seq F x n[-]CS_seq F x N).
 rstepr (e [/]ThreeNZ).

 apply leEq_transitive with (e [/]FourNZ); auto.
 apply mult_cancel_leEq with (nring (R:=F) 12).
 apply nring_pos.
 auto with arith.
 rstepl (Zero[+]Three[*]e); rstepr (e[+]Three[*]e).
 apply plus_resp_leEq; apply less_leEq; auto.

 apply H0.
 assumption.
 apply H0.
 assumption.

 apply less_leEq.
 simpl in |- *.
 unfold Rlt in |- *.
 exists N.
 exists (e [/]ThreeNZ).
 apply pos_div_three.
 assumption.

 intros.
 change (e [/]ThreeNZ [<=] e[-]CS_seq F (inject_Q (CS_seq F x m) [-]x) n)
  in |- *.
 apply plus_cancel_leEq_rht with (R := F) (z := [--]e).
 rstepl ( [--] (Two[*]e [/]ThreeNZ)).
 rstepr ( [--] (CS_seq F (inject_Q (CS_seq F x m) [-]x) n)).
 apply inv_resp_leEq.
 cut (AbsSmall (e [/]FourNZ) (CS_seq F x m[-]CS_seq F x N)).
 intro.
 elim H3.
 intros H4 H5.
 cut (AbsSmall (e [/]FourNZ) (CS_seq F x n[-]CS_seq F x N)).
 intro.
 elim H6.
 intros H7 H8.
 change (CS_seq F x m[-]CS_seq F x n [<=] Two[*]e [/]ThreeNZ) in |- *.
 rstepr (e [/]ThreeNZ[+]e [/]ThreeNZ).
 rstepl (CS_seq F x m[-]CS_seq F x N[+] (CS_seq F x N[-]CS_seq F x n)).
 apply plus_resp_leEq_both.
 apply leEq_transitive with (e [/]FourNZ); auto.
 apply mult_cancel_leEq with (nring (R:=F) 12).
 apply nring_pos.
 auto with arith.
 rstepl (Zero[+]Three[*]e); rstepr (e[+]Three[*]e).
 apply plus_resp_leEq; apply less_leEq; auto.
 apply inv_cancel_leEq.
 rstepr (CS_seq F x n[-]CS_seq F x N).
 apply leEq_transitive with ( [--] (e [/]FourNZ)); auto.
 apply inv_resp_leEq.
 apply mult_cancel_leEq with (nring (R:=F) 12).
 apply nring_pos.
 auto with arith.
 rstepl (Zero[+]Three[*]e); rstepr (e[+]Three[*]e).
 apply plus_resp_leEq; apply less_leEq; auto.

 apply H0.
 assumption.
 apply H0.
 assumption.
Qed.

Lemma conv_modulus : forall (x : R_COrdField') M, {N : nat | forall m,
 N <= m -> AbsSmall (one_div_succ M) (CS_seq F x m[-]CS_seq F x N)}.
Proof.
 intros.
 case x.
 intros x_ px.
 unfold Cauchy_prop in px.
 cut
  {N : nat |
  forall m : nat, N <= m -> AbsSmall (one_div_succ M) (x_ m[-]x_ N)}.
 intro H.
 case H.
 intros N H1.
 exists N.
 intros.
 apply H1.
 assumption.
 apply px.
 apply one_div_succ_pos.
Qed.

Let T (x : R_COrdField') (m : nat) := let (N, _) := conv_modulus x m in N.

(** We now assume our original field is archimedean and prove that the
resulting one is, too.
*)


Hypothesis F_is_archemaedian : forall x : F, {n : nat | x [<] nring n}.

Theorem R_is_archemaedian : forall x : R_COrdField', {n : nat | x [<=] nring n}.
Proof.
 intros.
 case x.
 intros x_ px.
 elim (px One (pos_one _)); intros Nx HNx.
 elim (F_is_archemaedian (x_ Nx)); intros N HN.
 exists (S N).
 intro H.
 elim H; intros K HK; elim HK; clear H HK; intros e He HK; simpl in HK.
 apply (less_irreflexive_unfolded F Zero).
 apply less_leEq_trans with e; auto.
 astepr (x_ (K + Nx) [-]x_ (K + Nx)).
 eapply leEq_transitive.
 apply (HK (K + Nx)); eauto with arith.
 unfold cg_minus in |- *; apply plus_resp_leEq_lft; apply inv_resp_leEq.
 rstepl (x_ Nx[+] (x_ (K + Nx) [-]x_ Nx)).
 apply plus_resp_leEq_both.
 apply leEq_wdr with (CS_seq _ (inject_Q (nring N)) (K + Nx)).
 simpl in |- *; apply less_leEq; auto.
 apply eq_symmetric_unfolded; apply ing_nring'.

 elim (HNx (K + Nx)); auto with arith.
Qed.

(* begin hide *)
Let PT (x : R_COrdField') (M : nat) :=
  proj2_sigT nat
    (fun N : nat =>
     forall m : nat,
     N <= m -> AbsSmall (one_div_succ M) (CS_seq F x m[-]CS_seq F x N))
    (conv_modulus x M).
(* end hide *)

Lemma modulus_property : forall x M m0 m1, T x M <= m0 -> T x M <= m1 ->
 AbsSmall (Two[*]one_div_succ M) (CS_seq F x m0[-]CS_seq F x m1).
Proof.
 intros.
 rstepl (one_div_succ (R:=F) M[+]one_div_succ M).
 rstepr
  (CS_seq F x m0[-]CS_seq F x (T x M) [+] (CS_seq F x (T x M) [-]CS_seq F x m1)).
 generalize (PT x M).
 intro.
 apply AbsSmall_plus.

 apply H1.
 assumption.

 apply AbsSmall_minus.
 apply H1.
 assumption.
Qed.

Lemma modulus_property_2 : forall x M m, T x M <= m ->
 AbsSmall (one_div_succ M) (CS_seq F x m[-]CS_seq F x (T x M)).
Proof.
 intros.
 apply (PT x M).
 assumption.
Qed.

Lemma expand_Q_R_2 : forall x e N, Zero [<] e ->
 (forall m, N <= m -> AbsSmall (e [/]FourNZ) (CS_seq F x m[-]CS_seq F x N)) ->
 AbsSmall (inject_Q e) (inject_Q (CS_seq F x N) [-]x).
Proof.
 intros x e N H H0.
 apply expand_Q_R with (x := x) (e := e) (N := N).
 assumption.
 intros.
 apply H0.
 assumption.
 constructor.
Qed.

Lemma CS_seq_diagonal : forall a : CauchySeq R_COrdField',
 Cauchy_prop (fun m => let b := (CS_seq _ a m) in CS_seq F b (T b m)).
Proof.
 intros.
 unfold Cauchy_prop in |- *.
 case a.
 intros a_ pa.
 intros.
 simpl in |- *.
 unfold Cauchy_prop in pa.
 cut (e [#] Zero).
 intro H0.
 cut {n : nat | (Twelve[/] e[//]H0) [-]One [<] nring n}.
 intro H1.
 case H1.
 intros M H2.
 cut
  {N : nat |
  forall m : nat, N <= m -> AbsSmall (inject_Q e [/]SixNZ) (a_ m[-]a_ N)}.
 intro H3.
 case H3.
 intros N H4.

 exists (max N M).
 intros.

 apply ing_cancel_AbsSmall.
 rstepl
  (inject_Q e [/]ThreeNZ[+]inject_Q e [/]ThreeNZ[+]inject_Q e [/]ThreeNZ).
 rstepr
  (inject_Q (CS_seq F (a_ m) (T (a_ m) m)) [-]a_ m[+]
   (a_ (max N M) [-]
    inject_Q (CS_seq F (a_ (max N M)) (T (a_ (max N M)) (max N M)))) [+]
   (a_ m[-]a_ (max N M))).
 apply AbsSmall_plus.
 apply AbsSmall_plus.

 astepl (inject_Q (e [/]ThreeNZ)).
 apply
  AbsSmall_leEq_trans
   with (R := R_COrdField') (e1 := inject_Q (Four[*]one_div_succ m)).
 apply ing_le.
 apply leEq_transitive with (y := Four[*]one_div_succ (R:=F) M).

 apply mult_resp_leEq_lft.
 apply one_div_succ_resp_leEq.
 eauto with arith.
 apply less_leEq.
 apply pos_four.

 apply mult_cancel_leEq with (R := F) (z := (nring M[+]One) [*] (Three:F)).
 apply mult_resp_pos.
 apply less_transitive_unfolded with (F := F) (y := Twelve[/] e[//]H0).

 apply mult_cancel_less with (R := F) (z := e).
 assumption.
 rstepl (Zero:F).
 rstepr (Twelve:F).
 apply nring_pos.
 apply lt_O_Sn.
 apply plus_cancel_less with (R := F) (z := [--] (One:F)).
 rstepl ((Twelve[/] e[//]H0) [-]One).
 rstepr (nring (R:=F) M).
 exact H2.
 apply nring_pos.
 apply lt_O_Sn.

 unfold one_div_succ in |- *.
 unfold Snring in |- *.
 change
   (Four[*] (One[/] nring M[+]One[//]nringS_ap_zero F M) [*]
    ((nring M[+]One) [*]Three) [<=] e [/]ThreeNZ[*] ((nring M[+]One) [*]Three))
  in |- *.
 rstepl (Twelve:F).
 rstepr (e[*] (nring M[+]One)).
 apply mult_cancel_leEq with (R := F) (z := One[/] e[//]H0).
 apply recip_resp_pos.
 assumption.
 rstepr (nring (R:=F) M[+]One).
 apply plus_cancel_leEq_rht with (R := F) (z := [--] (One:F)).
 rstepl ((Twelve[/] e[//]H0) [-]One).
 rstepr (nring (R:=F) M).
 apply less_leEq; exact H2.

 apply
  expand_Q_R_2
   with (x := a_ m) (e := Four[*]one_div_succ (R:=F) m) (N := T (a_ m) m).

 apply mult_resp_pos.
 apply pos_four.
 apply one_div_succ_pos.

 intros.
 rstepl (one_div_succ (R:=F) m).
 apply modulus_property_2.
 assumption.

 apply eq_symmetric_unfolded.
 apply ing_div_three.

 astepl (inject_Q (e [/]ThreeNZ)).
 apply
  AbsSmall_leEq_trans
   with (R := R_COrdField') (e1 := inject_Q (Four[*]one_div_succ (R:=F) M)).
 apply less_leEq.
 apply ing_lt.

 apply mult_cancel_less with (R := F) (z := (nring M[+]One) [*] (Three:F)).
 apply mult_resp_pos.
 apply less_transitive_unfolded with (F := F) (y := Twelve[/] e[//]H0).

 apply mult_cancel_less with (R := F) (z := e).
 assumption.
 rstepl (Zero:F).
 rstepr (Twelve:F).
 apply nring_pos.
 apply lt_O_Sn.
 apply plus_cancel_less with (R := F) (z := [--] (One:F)).
 rstepl ((Twelve[/] e[//]H0) [-]One).
 rstepr (nring (R:=F) M).
 exact H2.
 apply pos_three.

 unfold one_div_succ in |- *.
 unfold Snring in |- *.
 change
   (Four[*] (One[/] nring M[+]One[//]nringS_ap_zero F M) [*]
    ((nring M[+]One) [*]Three) [<] e [/]ThreeNZ[*] ((nring M[+]One) [*]Three))
  in |- *.
 rstepl (Twelve:F).
 rstepr (e[*] (nring M[+]One)).
 apply mult_cancel_less with (R := F) (z := One[/] e[//]H0).
 apply recip_resp_pos.
 assumption.
 rstepr (nring (R:=F) M[+]One).
 apply plus_cancel_less with (R := F) (z := [--] (One:F)).
 rstepl ((Twelve[/] e[//]H0) [-]One).
 rstepr (nring (R:=F) M).
 exact H2.

 apply AbsSmall_minus.
 apply
  expand_Q_R_2
   with
     (x := a_ (max N M))
     (e := Four[*]one_div_succ (R:=F) M)
     (N := T (a_ (max N M)) (max N M)).

 apply mult_resp_pos.
 apply pos_four.
 apply one_div_succ_pos.

 intros.
 rstepl (one_div_succ (R:=F) M).
 apply
  AbsSmall_leEq_trans with (R := F) (e1 := one_div_succ (R:=F) (max N M)).
 apply one_div_succ_resp_leEq.
 auto with arith.
 apply modulus_property_2.
 assumption.

 apply eq_symmetric_unfolded.
 apply ing_div_three.

 rstepl (inject_Q e [/]SixNZ[+]inject_Q e [/]SixNZ).
 rstepr (a_ m[-]a_ N[+] (a_ N[-]a_ (max N M))).
 apply AbsSmall_plus.
 apply H4; eauto with arith.
 apply AbsSmall_minus.
 apply H4; eauto with arith.

 apply pa.

 apply mult_cancel_less with (R := R_COrdField') (z := Six:R_COrdField').
 apply pos_six.
 rstepl (Zero:R_COrdField').
 rstepr (inject_Q e).
 change (inject_Q (Zero:F) [<] inject_Q e) in |- *.
 apply ing_lt.
 assumption.

 apply F_is_archemaedian.
 apply Greater_imp_ap.
 assumption.
Qed.

(** ** Cauchy Completeness
We can also define a limit operator.
*)

Lemma Q_dense_in_R : forall x, Zero [<] x -> {q : F | Zero [<] q | inject_Q q [<] x}.
Proof.
 intros.
 cut (x [#] Zero).
 intro H0.
 cut {n : nat | (One[/] x[//]H0) [<=] nring n}.
 intro H1.
 case H1.
 intros n H2.
 cut (nring (R:=F) (S n) [#] Zero).
 intro H3.
 exists (One[/] nring (S n) [//]H3).
 apply recip_resp_pos.
 apply ing_cancel_less.
 change (Zero [<] inject_Q (nring (S n))) in |- *.
 apply less_leEq_trans with (R := R_COrdField') (y := One[/] x[//]H0).
 apply recip_resp_pos.
 assumption.
 apply leEq_transitive with (inject_Q (nring n)).
 astepr (nring (R:=R_COrdField') n).
 assumption.
 apply ing_nring.
 astepl (nring (R:=R_COrdField') n).
 astepr (nring (R:=R_COrdField') (S n)).
 apply less_leEq; astepr (nring (R:=R_COrdField') n[+]One);
  apply less_plusOne.
 apply ing_nring.
 apply ing_nring.

 cut (nring (R:=R_COrdField') (S n) [#] Zero).
 intro H4.
 astepl (inject_Q (One:F) [/] nring (S n) [//]H4).
 apply shift_div_less.
 apply nring_pos.
 auto with arith.
 astepl (One:R_COrdField').
 apply shift_less_mult' with H0.
 assumption.
 eapply leEq_less_trans.
 apply H2.
 astepr (nring (R:=R_COrdField') n[+]One); apply less_plusOne.
 apply ing_n.

 apply nringS_ap_zero.
 apply nringS_ap_zero.

 apply R_is_archemaedian.
 apply Greater_imp_ap.
 assumption.
Qed.
	
Definition LimR_CauchySeq (a : CauchySeq R_COrdField') :=
  Build_CauchySeq _ _ (CS_seq_diagonal a).

Theorem R_is_complete : forall a : CauchySeq R_COrdField',
 SeqLimit (R:=R_COrdField') a (LimR_CauchySeq a).
Proof.
 intros.
 simpl in |- *.
 red in |- *.
 case a.
 intros a_ pa.
 intros e H.
 simpl in |- *.
 set (He := pos_ap_zero _ _ H) in *.
 elim (Q_dense_in_R (e [/]ThreeNZ));
  [ intros q Hq Hinj | apply pos_div_three; auto ].
 set (Hq' := pos_ap_zero _ _ Hq) in *.
 elim (F_is_archemaedian ((Four[/] q[//]Hq') [-]One)); intros M HM.
 unfold Cauchy_prop in pa.
 elim (pa (e [/]SixNZ)); [ intros N2 HN2 | apply pos_div_six; auto ].

 elim (CS_seq_diagonal (Build_CauchySeq R_COrdField' a_ pa) (q [/]EightNZ));
  [ intros N1 HN1 | apply pos_div_eight; auto ].

 exists (max M (max N1 N2)).
 intros.

 rstepl (e [/]ThreeNZ[+]e [/]ThreeNZ[+]e [/]ThreeNZ).
 rstepr
  (a_ m[-]a_ (max M (max N1 N2)) [+]
   (a_ (max M (max N1 N2)) [-]
    inject_Q
      (CS_seq F (LimR_CauchySeq (Build_CauchySeq R_COrdField' a_ pa))
         (max M (max N1 N2)))) [+]
   (inject_Q
      (CS_seq F (LimR_CauchySeq (Build_CauchySeq R_COrdField' a_ pa))
         (max M (max N1 N2))) [-]
    LimR_CauchySeq (Build_CauchySeq R_COrdField' a_ pa))).
 apply AbsSmall_plus.
 apply AbsSmall_plus.

 rstepl (e [/]SixNZ[+]e [/]SixNZ).
 rstepr (a_ m[-]a_ N2[+] (a_ N2[-]a_ (max M (max N1 N2)))).
 apply AbsSmall_plus.
 apply HN2; eauto with arith.

 apply AbsSmall_minus; apply HN2; eauto with arith.

 apply AbsSmall_leEq_trans with (R := R_COrdField') (e1 := inject_Q q).
 apply less_leEq; assumption.
 apply AbsSmall_minus.
 simpl in |- *.

 apply
  AbsSmall_leEq_trans
   with
     (R := R_COrdField')
     (e1 := Four[*] (one_div_succ (max M (max N1 N2)):R_COrdField')).

 apply less_leEq.
 apply
  leEq_less_trans
   with (R := R_COrdField') (y := Four[*]one_div_succ (R:=R_COrdField') M).

 apply mult_resp_leEq_lft.
 apply one_div_succ_resp_leEq.
 auto with arith.

 apply less_leEq; apply pos_four.

 apply
  mult_cancel_less with (R := R_COrdField') (z := nring M[+]One:R_COrdField').

 apply
  less_transitive_unfolded
   with (F := R_COrdField') (y := inject_Q (Four[/] q[//]Hq')).
 change (inject_Q (Zero:F) [<] inject_Q (Four[/] q[//]Hq')) in |- *.
 apply ing_lt.

 apply mult_cancel_less with (R := F) (z := q).
 assumption.
 rstepl (Zero:F).
 rstepr (Four:F).
 apply pos_four.
 apply shift_less_plus.
 astepl (inject_Q ((Four[/] q[//]Hq') [+][--]One)).
 astepr (inject_Q (nring M)).
 apply ing_lt.
 rstepl ((Four[/] q[//]Hq') [-]One).
 exact HM.
 apply eq_symmetric_unfolded.
 apply ing_nring.
 unfold cg_minus in |- *.
 apply
  eq_transitive_unfolded
   with (inject_Q (Four[/] q[//]Hq') [+]inject_Q ( [--]One:F)).
 apply ing_plus.
 apply plus_resp_eq.
 apply eq_transitive_unfolded with ( [--] (inject_Q (One:F))).
 apply ing_min.
 astepl (Zero[-]inject_Q (One:F)).
 Step_final (Zero[-] (One:R_COrdField')).

 unfold one_div_succ in |- *.
 unfold Snring in |- *.
 change
   (Four[*] (One[/] nring M[+]One[//]nringS_ap_zero R_COrdField' M) [*]
    (nring M[+]One) [<] inject_Q q[*] (nring M[+]One)) 
  in |- *.

 rstepl (Four:R_COrdField').

 astepr (inject_Q q[*]inject_Q (nring M[+]One)).
 astepl (inject_Q (Four:F)).
 astepr (inject_Q (q[*] (nring M[+]One))).
 apply ing_lt.
 apply mult_cancel_less with (R := F) (z := One[/] q[//]Hq').
 apply recip_resp_pos.
 assumption.
 rstepl (Four[/] q[//]Hq').
 rstepr (nring (R:=F) M[+]One).
 apply plus_cancel_less with (R := F) (z := [--] (One:F)).
 rstepl ((Four[/] q[//]Hq') [-]One).
 rstepr (nring (R:=F) M).
 exact HM.
 apply ing_mult.
 apply eq_symmetric_unfolded.
 apply ing_nring.
 apply mult_wd.
 apply ing_eq.
 apply eq_reflexive_unfolded.
 apply eq_transitive_unfolded with (inject_Q (nring M) [+]inject_Q (One:F)).
 apply ing_plus.
 astepl (inject_Q (nring M) [+]One).
 astepl (One[+]inject_Q (nring M)).
 astepr (One[+]nring (R:=R_COrdField') M).
 apply plus_resp_eq.
 apply eq_symmetric_unfolded.
 apply ing_nring.

 astepl (inject_Q (Four[*]one_div_succ (R:=F) (max M (max N1 N2)))).
 apply
  expand_Q_R_2
   with
     (x := a_ (max M (max N1 N2)))
     (e := Four[*]one_div_succ (R:=F) (max M (max N1 N2)))
     (N := T (a_ (max M (max N1 N2))) (max M (max N1 N2))).

 apply mult_resp_pos.
 apply pos_four.
 apply one_div_succ_pos.
 intros.
 rstepl (one_div_succ (R:=F) (max M (max N1 N2))).
 apply modulus_property_2.
 assumption.
 apply
  eq_transitive_unfolded
   with (inject_Q (Four:F) [*]inject_Q (one_div_succ (max M (max N1 N2)))).
 apply ing_mult.
 apply
  eq_transitive_unfolded
   with (Four[*]inject_Q (one_div_succ (max M (max N1 N2)))).
 apply mult_wd.
 apply eq_symmetric_unfolded.
 apply ing_nring.
 apply eq_reflexive_unfolded.
 apply mult_wd.
 apply eq_reflexive_unfolded.
 unfold one_div_succ in |- *.
 unfold Snring in |- *.
 astepl (inject_Q (One[/] _[//]nringS_ap_zero _ (max M (max N1 N2)))).

 Step_final (One[/] _[//]nringS_ap_zero R_COrdField' (max M (max N1 N2))).
 apply
  eq_transitive_unfolded
   with (inject_Q (One:F) [/] _[//]nringS_ap_zero _ (max M (max N1 N2))).
 apply eq_symmetric_unfolded.
 apply ing_n.
 apply div_wd.
 exact ing_One.
 apply eq_reflexive_unfolded.

 apply AbsSmall_leEq_trans with (R := R_COrdField') (e1 := inject_Q q).
 apply less_leEq; assumption.
 apply
  expand_Q_R_2
   with
     (x := LimR_CauchySeq (Build_CauchySeq R_COrdField' a_ pa))
     (e := q)
     (N := max M (max N1 N2)).
 assumption.
 intros.
 rstepl (q [/]EightNZ[+]q [/]EightNZ).
 rstepr
  (CS_seq F (LimR_CauchySeq (Build_CauchySeq R_COrdField' a_ pa)) m0[-]
   CS_seq F (LimR_CauchySeq (Build_CauchySeq R_COrdField' a_ pa)) N1[+]
   (CS_seq F (LimR_CauchySeq (Build_CauchySeq R_COrdField' a_ pa)) N1[-]
    CS_seq F (LimR_CauchySeq (Build_CauchySeq R_COrdField' a_ pa))
      (max M (max N1 N2)))).
 apply AbsSmall_plus.
 unfold LimR_CauchySeq in |- *; simpl in |- *; apply HN1; eauto with arith.
 apply AbsSmall_minus.
 unfold LimR_CauchySeq in |- *; simpl in |- *; apply HN1; eauto with arith.
Qed.

Definition R_is_CReals := Build_is_CReals _
 LimR_CauchySeq R_is_complete R_is_archemaedian.

Definition R_as_CReals := Build_CReals _ _ R_is_CReals.

End R_CReals.
