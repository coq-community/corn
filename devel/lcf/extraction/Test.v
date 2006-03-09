(* $Id: Test.v,v 1.5 2004/07/13 15:25:36 lcf Exp $ *)

Require Export E.
Require Export FTA.
Require Export Series_extr.
Require Export Sqrt.
(* Require Export Pi. *)

Open Scope nat_scope.

Definition half (_ : unit) : IR := Half (R:=IR).
Definition sqrt_two (_ : unit) : IR :=
  sqrt Two (less_leEq _ _ _ (pos_two IR)).
Definition sqrt_two_lcf : unit -> IR :=
  fun _ => (sqrt' Two (less_leEq _ _ _ (pos_two IR))).

Definition one_R : IR := OneR.
Definition x_plus_one : cpoly_cring IR := One[+X*]One.
Definition x_plus_one_4 := x_plus_one[^]4.
Definition sixteen_R (_ : unit) : IR := cpoly_apply _ x_plus_one_4 one_R.


Definition one_C : CC := One.
Definition x_minus_one : cpoly_cring CC := [--]One[+X*]One.
Definition x2_minus_two : cpoly_cring CC := [--]Two[+X*](Zero[+X*]One).

Lemma one_C_ap_zero : one_C[#]Zero.
simpl in |- *. unfold cc_ap in |- *.
simpl in |- *. left.
apply one_ap_zero.
Qed.

Lemma x_minus_one_is_nonConst : nonConst CC x_minus_one.
unfold nonConst in |- *.
exists 1.
auto.
simpl in |- *.
apply one_C_ap_zero.
Qed.

Lemma x2_minus_two_is_nonConst : nonConst CC x2_minus_two.
unfold nonConst in |- *.
exists 2.
auto.
simpl in |- *.
apply one_C_ap_zero.
Qed.

Definition R_observer (r : Cauchy_IR) := CS_seq _ r.

Definition one_fta (_ : unit) : CC :=
  let (x, _) := FTA x_minus_one x_minus_one_is_nonConst in x.

Definition sqrt_two_fta (_ : unit) : CC :=
  let (x, _) := FTA x2_minus_two x2_minus_two_is_nonConst in x.

Definition C_Re_observer (c : CC) := Re c.

Definition C_Im_observer (c : CC) := Im c.

(* A new & more efficient E definition. *)

Definition my_fact (n : nat) : Cauchy_IR :=
  inject_Q Q_as_COrdField (inject_Z (pos_fact n)).

Lemma my_fact_ap_zero : forall n : nat, my_fact n[#]Zero.
intros.
red in |- *.
simpl in |- *.
unfold R_ap in |- *.
right.
unfold R_lt in |- *.
exists 0.
exists (inject_Z 1).
constructor.
intros.

red in |- *.
intro H0.
red in H0.
simpl in H0.
unfold Qlt, Zlts in H0.
inversion H0.
rewrite Pmult_comm in H2.
simpl in H2.
rewrite Pmult_comm in H2.
simpl in H2.
generalize H2.
case (pos_fact n); intros; inversion H1.
Qed.

(* Set Printing Coercions. _* for debug *_ *)

Lemma my_fact_pos_fact :
 forall n : nat, pring Cauchy_IR (pos_fact n)[=]my_fact n.
intros.
unfold my_fact in |- *.
astepl (nring (R:=Cauchy_IR) (nat_of_P (pos_fact n))).
astepr (inject_Q Q_as_COrdField (nring (nat_of_P (pos_fact n)))).
apply (ing_nring Q_as_COrdField).
apply (ing_eq Q_as_COrdField).
astepr (inject_Z (nat_of_P (pos_fact n))).
apply nring_Q.
rewrite convert_is_POS.
rational.
Qed.

Axiom my_fact' : nat -> IR. 
Axiom my_fact_ap_zero' : forall n : nat, my_fact' n[#]Zero.
Axiom my_fact_pos_fact' : forall n : nat, pring IR (pos_fact n)[=]my_fact' n.

Hint Resolve my_fact_pos_fact': algebra.

Definition new_e_series (n : nat) := One[/]_[//]my_fact_ap_zero' n.

Lemma new_e_series_conv : convergent new_e_series.
apply ratio_test_conv.
exists 1.
exists (OneR [/]TwoNZ).
apply pos_div_two'; apply pos_one.
split.
apply less_leEq; apply pos_div_two; apply pos_one.
intros.
unfold new_e_series in |- *.
eapply leEq_wdr.
2: apply mult_commutes.
eapply leEq_wdr.
2: apply AbsIR_mult_pos.
2: apply less_leEq; apply pos_div_two; apply pos_one.
eapply leEq_wdl.
2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
eapply leEq_wdr.
2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
rstepr
 ((One[*]One)[/]_[//]
  mult_resp_ap_zero _ _ _ (two_ap_zero IR) (my_fact_ap_zero' n)).
rstepr
 (One[/]_[//]mult_resp_ap_zero _ _ _ (two_ap_zero IR) (my_fact_ap_zero' n)).
apply recip_resp_leEq.
astepl ((Two:IR)[*]Zero); apply mult_resp_less_lft.
astepr (pring IR (pos_fact n)). 
apply pring_pos.
apply pos_two.
astepl (Two[*]nring (R:=IR) (nat_of_P (pos_fact n))).
astepr (nring (R:=IR) (nat_of_P (pos_fact (S n)))).
replace (nat_of_P (pos_fact (S n))) with (S n * nat_of_P (pos_fact n)).
eapply leEq_wdr.
2: apply eq_symmetric_unfolded; apply nring_comm_mult.
apply mult_resp_leEq_rht.
apply nring_leEq; auto with arith.
apply nring_nonneg.
simpl (pos_fact (S n)) in |- *.
rewrite nat_of_P_mult_morphism.
rewrite nat_of_P_o_P_of_succ_nat_eq_succ; auto.
astepl (pring IR (pos_fact (S n))).
apply my_fact_pos_fact'.
astepl (Two[*]pring IR (pos_fact n)).
algebra.
apply less_leEq; apply mult_resp_pos; apply recip_resp_pos.
astepr (pring IR (pos_fact n)). 
apply pring_pos.
apply pos_two.
apply less_leEq; apply recip_resp_pos.
astepr (pring IR (pos_fact (S n))). 
apply pring_pos.
Qed.

Definition new_E := series_sum _ new_e_series_conv.

(*
Definition cosone := (Cos One).

Definition logtwo := (Log Two (pos_two _)).
*)
