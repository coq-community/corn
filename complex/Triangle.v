(* $Id$ *)

Require Export CComplex.

(** ** The triangle inequality *)

Lemma triangle : forall x y : CC, AbsCC (x[+]y)[<=]AbsCC x[+]AbsCC y.
intros.
elim x. intros x1 x2.
elim y. intros y1 y2.
unfold AbsCC in |- *. simpl in |- *.
apply power_cancel_leEq with 2. auto.
AStepl (Zero[+]ZeroR).
apply plus_resp_leEq_both; apply sqrt_nonneg.
AStepl (One[*](x1[+]y1)[*](x1[+]y1)[+]One[*](x2[+]y2)[*](x2[+]y2)).
RStepr
 (sqrt (One[*]x1[*]x1[+]One[*]x2[*]x2) (cc_abs_aid _ x1 x2)[^]2[+]
  sqrt (One[*]y1[*]y1[+]One[*]y2[*]y2) (cc_abs_aid _ y1 y2)[^]2[+]
  Two[*]sqrt (One[*]x1[*]x1[+]One[*]x2[*]x2) (cc_abs_aid _ x1 x2)[*]
  sqrt (One[*]y1[*]y1[+]One[*]y2[*]y2) (cc_abs_aid _ y1 y2)).
AStepr
 (One[*]x1[*]x1[+]One[*]x2[*]x2[+](One[*]y1[*]y1[+]One[*]y2[*]y2)[+]
  Two[*]sqrt (One[*]x1[*]x1[+]One[*]x2[*]x2) (cc_abs_aid _ x1 x2)[*]
  sqrt (One[*]y1[*]y1[+]One[*]y2[*]y2) (cc_abs_aid _ y1 y2)).
apply shift_leEq_rht.
RStepr
 (Two[*]
  (sqrt (One[*]x1[*]x1[+]One[*]x2[*]x2) (cc_abs_aid _ x1 x2)[*]
   sqrt (One[*]y1[*]y1[+]One[*]y2[*]y2) (cc_abs_aid _ y1 y2)[-]
   (x1[*]y1[+]x2[*]y2))).
apply mult_resp_nonneg. apply less_leEq. apply pos_two.
apply shift_leEq_lft.
apply power_cancel_leEq with 2. auto.
apply mult_resp_nonneg; apply sqrt_nonneg.
AStepr
 (sqrt (One[*]x1[*]x1[+]One[*]x2[*]x2) (cc_abs_aid _ x1 x2)[^]2[*]
  sqrt (One[*]y1[*]y1[+]One[*]y2[*]y2) (cc_abs_aid _ y1 y2)[^]2).
AStepr ((One[*]x1[*]x1[+]One[*]x2[*]x2)[*](One[*]y1[*]y1[+]One[*]y2[*]y2)).
apply shift_leEq_rht.
RStepr ((x1[*]y2[-]x2[*]y1)[^]2).
apply sqr_nonneg.
Qed.

Lemma triangle_Sum :
 forall (m n : nat) (z : nat -> CC),
 m <= S n -> AbsCC (Sum m n z)[<=]Sum m n (fun i : nat => AbsCC (z i)).
intros. induction  n as [| n Hrecn]; intros.
generalize (toCle _ _ H); clear H; intro H.
inversion H.
unfold Sum in |- *. unfold Sum1 in |- *.
AStepl (AbsCC Zero).
AStepr ZeroR.
AStepr (AbsCC Zero).
apply leEq_reflexive. rename H1 into H2. rename X into H1.
inversion H1.
unfold Sum in |- *. unfold Sum1 in |- *. simpl in |- *.
cut (AbsCC (Zero[+]z 0[-]Zero)[<=]Zero[+]AbsCC (z 0)[-]Zero).
auto.
apply eq_imp_leEq.
RStepr (AbsCC (z 0)).
apply AbsCC_wd.
rational.
elim (le_lt_eq_dec _ _ H); intro y.
AStepl (AbsCC (Sum m n z[+]z (S n))).
apply leEq_wdr with (Sum m n (fun i : nat => AbsCC (z i))[+]AbsCC (z (S n))).
apply leEq_transitive with (AbsCC (Sum m n z)[+]AbsCC (z (S n))).
apply triangle.
apply plus_resp_leEq.
apply Hrecn. auto with arith.
apply eq_symmetric_unfolded. apply Sum_last with (f := fun i : nat => AbsCC (z i)).
rewrite y. unfold Sum in |- *. unfold Sum1 in |- *.
AStepl (AbsCC Zero).
AStepr ZeroR.
AStepr (AbsCC Zero).
apply leEq_reflexive.
Qed.

(*
Def_inition AbsCC_fun :=
	(Build_CSetoid_fun CC IR AbsCC AbsCC_wd AbsCC_strext).
Def_inition CC_is_CMetricField :=
(Build_is_CMetricField CC AbsCC_fun AbsCC_nonneg AbsCC_resp_mult triangle).

Def_inition CC_MF := (Build_CMetricField CC AbsCC_fun CC_is_CMetricField).

Def_inition CC_Cauchy_real := [s:nat->CC_MF][n:nat](Re (s n)).
Def_inition CC_Cauchy_imag := [s:nat->CC_MF][n:nat](Im (s n)).


Ax_iom is_Cauchy_real :
	(s : (MCauchySeq CC_MF)) (Cauchy_prop (CC_Cauchy_real s)).

Ax_iom is_Cauchy_imag :
	(s : (MCauchySeq CC_MF)) (Cauchy_prop (CC_Cauchy_imag s)).

Def_inition MCauchy2Cauchy1 := [s : (MCauchySeq CC_MF)]
	(Build_CauchySeq IR (CC_Cauchy_real s)(is_Cauchy_real s)).

Def_inition MCauchy2Cauchy2 := [s : (MCauchySeq CC_MF)]
	(Build_CauchySeq IR (CC_Cauchy_imag s)(is_Cauchy_imag s)).

Def_inition MakeMCauchy := [s_r : (CauchySeq IR); s_i : (CauchySeq IR)]
	[n:nat](Build_CC_set (s_r n)(s_i n)).

Ax_iom is_MCauchy :
	(s_r : (CauchySeq IR); s_i : (CauchySeq IR))
	 (MCauchy_prop CC_MF (MakeMCauchy s_r s_i)).

Def_inition Cauchy2MCauchy := [s_r : (CauchySeq IR); s_i : (CauchySeq IR)]
	(Build_MCauchySeq CC_MF (MakeMCauchy s_r s_i)
		(is_MCauchy s_r s_i)).

Def_inition LimCC := [s:(MCauchySeq CC_MF)]
	(Build_CC_set (Lim (MCauchy2Cauchy1 s))(Lim (MCauchy2Cauchy2 s))).
*)

