(* $Id$ *)

Require Export CPoly_Contin.

(** * Intermediate Value Theorem *)

Section Nested_Intervals.
(** ** Nested intervals

%\begin{convention}% Let [a,b:nat->IR] be sequences such that:
- [a] is increasing;
- [b] is decreasing;
- [(i:nat)((a i) [<] (b i))];
- for every positive real number [eps], there is an [i] such that [(b i) [<] (a i)[+]eps].

%\end{convention}%
*)

Variables a b : nat -> IR.
Hypothesis a_mon : forall i : nat, a i[<=]a (S i).
Hypothesis b_mon : forall i : nat, b (S i)[<=]b i.
Hypothesis a_b : forall i : nat, a i[<]b i.
Hypothesis b_a : forall eps : IR, Zero[<]eps -> {i : nat | b i[<=]a i[+]eps}.

Lemma a_mon' : forall i j : nat, i <= j -> a i[<=]a j.
intros.
apply local_mon'_imp_mon'; auto.
Qed.

Lemma b_mon' : forall i j : nat, i <= j -> b j[<=]b i.
intros.
set (b' := fun i : nat => [--](b i)) in *.
AStepl ([--][--](b j)).
AStepr ([--][--](b i)).
fold (b' i) (b' j) in |- *.
apply inv_resp_leEq.
apply local_mon'_imp_mon'.
unfold b' in |- *; intro; apply inv_resp_leEq; auto.
auto.
Qed.

Lemma a_b' : forall i j : nat, a i[<]b j.
intros.
elim (le_lt_dec i j); intro.
apply leEq_less_trans with (a j).
apply a_mon'. auto.
auto.
apply less_leEq_trans with (b i).
auto.
apply b_mon'. auto with arith.
Qed.

Lemma intervals_cauchy : Cauchy_prop a.
unfold Cauchy_prop in |- *.
unfold AbsSmall in |- *.
intro eps. intros H.
elim (b_a eps H). intro n. intros. exists n.
intro i. intros.
split; apply less_leEq.
apply less_leEq_trans with ZeroR.
AStepr ([--]ZeroR).
apply inv_resp_less. auto.
AStepl (a n[-]a n).
apply minus_resp_leEq.
apply a_mon'. auto.
apply shift_minus_less'.
apply less_leEq_trans with (b n).
apply a_b'.
auto.
Qed.

(* begin hide *)
Let a' := Build_CauchySeq _ a intervals_cauchy.
(* end hide *)

Lemma Cnested_intervals_limit :
 {z : IR | forall i : nat, a i[<=]z | forall i : nat, z[<=]b i}.
exists (Lim a').
intros.
unfold leEq in |- *. unfold Not in |- *. intros.
elim (Lim_less_so_seq_less a' (a i)). intro n. intros H0.
elim (le_lt_dec n i); intro H1.
cut (Not (a i[<]a i)). intro H2.
unfold Not in H1. elim H2. apply H0. auto.
apply less_irreflexive_unfolded.
cut (forall i j : nat, i <= j -> a i[<=]a j). intro a_mon''.
unfold leEq in a_mon''. unfold Not in a_mon''.
elim a_mon'' with i n. auto with arith.
apply H0.
auto.
intros. apply a_mon'; auto.
auto.
unfold leEq in |- *. unfold Not in |- *. intros i H.
elim (less_Lim_so_less_seq a' (b i) H). intro n. intros H0.
elim (le_lt_dec n i); intro H1.
cut (Not (a i[<]b i)). unfold Not in |- *. intro.
elim H2. auto. apply less_antisymmetric_unfolded.
apply H0.
auto.
cut (Not (a n[<]b n)). unfold Not in |- *. intro H2.
apply H2. auto. apply less_antisymmetric_unfolded.
apply leEq_less_trans with (b i).
apply b_mon'. auto with arith.
apply H0. auto.
Qed.

(** %\begin{convention}% Let [f] be a continuous real function.
%\end{convention}%
*)

Variable f : CSetoid_un_op IR.
Hypothesis f_contin : contin f.

Lemma f_contin_pos :
 forall z : IR,
 Zero[<]f z ->
 {eps : IR | Zero[<]eps |
 forall x : IR, x[<=]z[+]eps -> z[<=]x[+]eps -> Zero[<]f x}.
intros z H.
unfold contin in f_contin.
unfold continAt in f_contin.
unfold funLim in f_contin.
unfold AbsSmall in f_contin.
elim (f_contin z (f z [/]TwoNZ) (pos_div_two _ _ H)). intro eps. intros H1 H2.
exists eps.
auto. intros.
elim (H2 x). intros H5 H6.
AStepl (f z[-]f z).
apply shift_minus_less.
apply shift_less_plus'. 
apply leEq_less_trans with (f z [/]TwoNZ). auto. apply pos_div_two'. auto.
split.
apply shift_leEq_minus.
RStepl (x[-]eps).
apply shift_minus_leEq. auto.
apply shift_minus_leEq. AStepr (x[+]eps). auto.
Qed.

Lemma f_contin_neg :
 forall z : IR,
 f z[<]Zero ->
 {eps : IR | Zero[<]eps |
 forall x : IR, x[<=]z[+]eps -> z[<=]x[+]eps -> f x[<]Zero}.
intros.
unfold contin in f_contin.
unfold continAt in f_contin.
unfold funLim in f_contin.
unfold AbsSmall in f_contin.
cut (Zero[<][--](f z)). intro H0.
elim (f_contin z ([--](f z) [/]TwoNZ) (pos_div_two _ _ H0)). intro eps. intros H2 H3.
exists eps.
auto. intros.
elim (H3 x). intros H6 H7.
RStepr (f z[-][--][--](f z)).
apply shift_less_minus'.
apply shift_plus_less. 
apply less_leEq_trans with (f z [/]TwoNZ). 
AStepl (f z). apply inv_cancel_less. RStepl ([--](f z) [/]TwoNZ). apply pos_div_two'. auto.
RStepl ([--]([--](f z) [/]TwoNZ)). auto.
split.
apply shift_leEq_minus.
RStepl (x[-]eps).
apply shift_minus_leEq. auto.
apply shift_minus_leEq. AStepr (x[+]eps). auto.
AStepl ([--]ZeroR).
apply inv_resp_less. auto.
Qed.

Hypothesis f_a : forall i : nat, f (a i)[<=]Zero.
Hypothesis f_b : forall i : nat, Zero[<=]f (b i).

Lemma Cnested_intervals_zero : {z : IR | a 0[<=]z /\ z[<=]b 0 /\ f z[=]Zero}.
elim Cnested_intervals_limit. intro z. intros H0 H1. exists z.
split. auto. split. auto.
apply not_ap_imp_eq.
unfold Not in |- *.
intros H2.
elim (ap_imp_less _ _ _ H2); intros H3.
elim (f_contin_neg z H3). intro eps. intros H5 H6.
elim (b_a eps). intro i. intros H7.
cut (b i[<=]z[+]eps). intro.
cut (z[<=]b i[+]eps). intro.
unfold leEq in f_b. unfold Not in f_b.
apply f_b with i. apply H6. auto. auto.
apply leEq_transitive with (b i). auto.
AStepl (b i[+]Zero). apply plus_resp_leEq_lft. apply less_leEq. auto.
apply leEq_transitive with (a i[+]eps). auto.
apply plus_resp_leEq. auto. auto.
elim (f_contin_pos z H3). intro eps. intros H5 H6.
elim (b_a eps). intro i. intros H7.
cut (a i[<=]z[+]eps). intro.
cut (z[<=]a i[+]eps). intro.
unfold leEq in f_a. unfold Not in f_a.
apply f_a with i. apply H6. auto. auto.
apply leEq_transitive with (b i). auto.
auto. apply leEq_transitive with z. auto.
AStepl (z[+]Zero). apply less_leEq. apply plus_resp_less_lft. auto.
auto.
Qed.

End Nested_Intervals.

Section Bisection.
(** ** Bissections *)

Variable f : CSetoid_un_op IR.
Hypothesis
  f_apzero_interval :
    forall a b : IR, a[<]b -> {c : IR | a[<=]c /\ c[<=]b | f c[#]Zero}.
Variables a b : IR.
Hypothesis a_b : a[<]b.
Hypothesis f_a : f a[<=]Zero.
Hypothesis f_b : Zero[<=]f b.

(**
%\begin{convention}% Let [Small] denote [Two[/]ThreeNZ], [lft] be [(Two[*]a[+]b)[/]ThreeNZ] and [rht] be [(a[+]Two[*]b)[/]ThreeNZ].
%\end{convention}%
*)

(* begin hide *)
Let Small : IR := Two [/]ThreeNZ.
Let lft := (Two[*]a[+]b) [/]ThreeNZ.
Let rht := (a[+]Two[*]b) [/]ThreeNZ.
(* end hide *)

Lemma a_lft : a[<]lft.
unfold lft in |- *.
apply shift_less_div.
apply pos_three.
RStepl (Two[*]a[+]a).
apply plus_resp_less_lft.
auto.
Qed.

Lemma rht_b : rht[<]b.
unfold rht in |- *.
apply shift_div_less.
apply pos_three.
RStepr (b[+]Two[*]b).
apply plus_resp_less_rht.
auto.
Qed.

Lemma lft_rht : lft[<]rht.
unfold lft in |- *. unfold rht in |- *.
apply div_resp_less_rht.
RStepl (a[+]b[+]a).
RStepr (a[+]b[+]b).
apply plus_resp_less_lft.
auto.
apply pos_three.
Qed.

Lemma smaller_lft : rht[-]a[=]Small[*](b[-]a).
unfold Small in |- *. unfold rht in |- *.
rational.
Qed.

Lemma smaller_rht : b[-]lft[=]Small[*](b[-]a).
unfold Small in |- *. unfold lft in |- *.
rational.
Qed.

Hint Resolve smaller_lft smaller_rht: algebra.

Lemma Cbisect' :
 {a' : IR |
 {b' : IR | a'[<]b' |
 a[<=]a' /\
 b'[<=]b /\ b'[-]a'[<=]Small[*](b[-]a) /\ f a'[<=]Zero /\ Zero[<=]f b'}}.
elim (f_apzero_interval lft rht lft_rht). intro c. intro H.
elim H. intros H0 H2 H3.
cut ({f c[<=]Zero} + {Zero[<=]f c}).
intro H4; inversion_clear H4.
exists c. exists b.
apply leEq_less_trans with rht. auto. apply rht_b.
split. apply leEq_transitive with lft. apply less_leEq. apply a_lft. auto.
split. apply leEq_reflexive.
split. AStepr (b[-]lft). apply minus_resp_leEq_rht. auto.
split. auto. auto.
exists a. exists c.
apply less_leEq_trans with lft. apply a_lft. auto.
split. apply leEq_reflexive.
split. apply less_leEq. apply leEq_less_trans with rht. auto. apply rht_b.
split. 
AStepr (rht[-]a). apply minus_resp_leEq. auto. 
split. auto. auto.
elim (ap_imp_less _ _ _ H3); intros.
left. apply less_leEq. auto.
right. apply less_leEq. auto.
Qed.

End Bisection.

Section Bisect_Interval.

(** ** Bisection gives an interval
Same conventions as before.
*)

Variable f : CSetoid_un_op IR.
Hypothesis
  C_f_apzero_interval :
    forall a b : IR, a[<]b -> {c : IR | a[<=]c /\ c[<=]b | f c[#]Zero}.

(* begin hide *)
Let Small : IR := Two [/]ThreeNZ.
(* end hide *)

Record bisect_interval : Type := 
  {interval_lft : IR;
   interval_rht : IR;
   interval_lft_rht : interval_lft[<]interval_rht;
   interval_f_lft : f interval_lft[<=]Zero;
   interval_f_rht : Zero[<=]f interval_rht}.

Lemma Cbisect_exists :
 forall I : bisect_interval,
 {I' : bisect_interval |
 interval_rht I'[-]interval_lft I'[<=]
 Small[*](interval_rht I[-]interval_lft I) /\
 interval_lft I[<=]interval_lft I' /\ interval_rht I'[<=]interval_rht I}.
intros.
elim
 (Cbisect' f C_f_apzero_interval _ _ (interval_lft_rht I) (
    interval_f_lft I) (interval_f_rht I)).
intro lft. intro H.
elim H. intro rht. intros H1 H2. elim H2. intros H3 H4. elim H4. intros H5 H6.
elim H6. intros H7 H8.
elim H8. intros H9 H10.
exists (Build_bisect_interval lft rht H1 H9 H10).
simpl in |- *.
unfold Small in |- *.
split. auto. split. auto. auto.
Qed.

Definition bisect (I : bisect_interval) : bisect_interval :=
  ProjT1 (Cbisect_exists I).

Lemma bisect_prop :
 forall I : bisect_interval,
 interval_rht (bisect I)[-]interval_lft (bisect I)[<=]
 Small[*](interval_rht I[-]interval_lft I) /\
 interval_lft I[<=]interval_lft (bisect I) /\
 interval_rht (bisect I)[<=]interval_rht I.
intros.
unfold bisect in |- *.
apply proj2_sigT. 
Qed.

End Bisect_Interval.

Section IVT_Op.
(** ** IVT for operations
Same conventions as before.
*)

Variable f : CSetoid_un_op IR.
Hypothesis f_contin : contin f.
Hypothesis
  f_apzero_interval :
    forall a b : IR, a[<]b -> {c : IR | a[<=]c /\ c[<=]b | f c[#]Zero}.
Variables a b : IR.
Hypothesis a_b : a[<]b.
Hypothesis f_a : f a[<=]Zero.
Hypothesis f_b : Zero[<=]f b.

(* begin hide *)
Let Small : IR := Two [/]ThreeNZ.
(* end hide *)

Fixpoint interval_sequence (n : nat) : bisect_interval f :=
  match n with
  | O => Build_bisect_interval f a b a_b f_a f_b
  | S m => bisect f f_apzero_interval (interval_sequence m)
  end.

Let a_ (i : nat) := interval_lft _ (interval_sequence i).
Let b_ (i : nat) := interval_rht _ (interval_sequence i).

Lemma intervals_smaller : forall i : nat, b_ i[-]a_ i[<=]Small[^]i[*](b[-]a).
intros.
induction  i as [| i Hreci]; intros.
unfold a_ in |- *. unfold b_ in |- *. simpl in |- *.
RStepr (b[-]a).
apply leEq_reflexive.
apply leEq_transitive with (Small[*](b_ i[-]a_ i)).
elim (bisect_prop f f_apzero_interval (interval_sequence i)).
intros H H0.
elim H0; intros H1 H2.
auto.
simpl in |- *.
replace (nexp _ i Small) with (Small[^]i). 2: auto.
RStepr (Small[*](Small[^]i[*](b[-]a))).
apply mult_resp_leEq_lft.
auto.
apply less_leEq.
unfold Small in |- *. apply div_resp_pos. apply pos_three. apply pos_two.
Qed.

Lemma intervals_small'' : forall i : nat, Small[^]i[*]nring i[<=]One.
intros.
apply mult_cancel_leEq with (Three[^]i:IR).
apply nexp_resp_pos. apply pos_three.
AStepr (Three[^]i:IR).
apply leEq_wdl with (nring i[*]Two[^]i:IR).
2: RStepr (nring i[*](Small[^]i[*]Three[^]i)).
2: AStepr (nring i[*](Small[*]Three)[^]i).
2: cut (Small[*]Three[=]Two); Algebra.
2: unfold Small in |- *; rational.
induction  i as [| i Hreci].
simpl in |- *. AStepl ZeroR. apply less_leEq. apply pos_one.
elim (zerop i); intro y.
rewrite y. simpl in |- *.
RStepl (Two:IR). RStepr (Three:IR).
apply less_leEq. apply two_less_three.
elim (le_lt_eq_dec _ _ (lt_le_S _ _ y)); intros H0.
apply mult_cancel_leEq with (nring i:IR).
AStepl (nring 0:IR). apply nring_less. auto.
apply leEq_wdl with (nring (S i)[*]Two[*](nring i[*]Two[^]i:IR)).
2: simpl in |- *; rational.
apply leEq_wdr with (nring i[*]Three[*]Three[^]i:IR).
2: simpl in |- *; rational.
apply leEq_transitive with (nring i[*]Three[*](nring i[*]Two[^]i:IR)).
apply mult_resp_leEq_rht.
simpl in |- *.
RStepl (nring i[*]Two[+](Two:IR)).
RStepr (nring i[*]Two[+](nring i:IR)).
apply plus_resp_leEq_lft.
elim (le_lt_eq_dec _ _ (lt_le_S _ _ H0)); intros H1.
apply less_leEq. apply nring_less. auto.
rewrite <- H1. apply leEq_reflexive.
apply less_leEq. apply mult_resp_pos.
AStepl (nring 0:IR). apply nring_less. auto.
apply nexp_resp_pos. apply pos_two.
apply mult_resp_leEq_lft. auto.
apply less_leEq. apply mult_resp_pos.
AStepl (nring 0:IR). apply nring_less. auto.
apply pos_three.
rewrite <- H0.
RStepl (nring (R:=IR) 8).
RStepr (nring (R:=IR) 9).
apply nring_leEq. auto.
Qed.

Lemma intervals_small' :
 forall eps : IR, Zero[<]eps -> {i : nat | Small[^]i[*](b[-]a)[<=]eps}.
intros.
cut (eps[#]Zero). intro H0.
elim (Archimedes (b[-]a[/] eps[//]H0)). intro i. intros H1. exists i.
AStepr (eps[*]One).
apply shift_leEq_mult' with H0. auto.
apply leEq_transitive with (Small[^]i[*]nring i).
AStepl (Small[^]i[*](b[-]a[/] eps[//]H0)).
apply mult_resp_leEq_lft.
auto.
apply nexp_resp_nonneg.
apply less_leEq.
AStepl (ZeroR [/]ThreeNZ). unfold Small in |- *.
apply div_resp_less_rht. apply pos_two. apply pos_three.
apply intervals_small''.
apply Greater_imp_ap. auto.
Qed.

Lemma intervals_small :
 forall eps : IR, Zero[<]eps -> {i : nat | b_ i[<=]a_ i[+]eps}.
intros eps H.
elim (intervals_small' eps H). intro i. intros. exists i.
apply shift_leEq_plus'.
apply leEq_transitive with (Small[^]i[*](b[-]a)).
apply intervals_smaller.
auto.
Qed.

Lemma Civt_op : {z : IR | a[<=]z /\ z[<=]b /\ f z[=]Zero}.
cut (forall i : nat, a_ i[<=]a_ (S i)). intro H.
cut (forall i : nat, b_ (S i)[<=]b_ i). intro H0.
cut (forall i : nat, a_ i[<]b_ i). intro H1.
cut (forall i : nat, f (a_ i)[<=]Zero). intro H2.
cut (forall i : nat, Zero[<=]f (b_ i)). intro H3.
elim (Cnested_intervals_zero a_ b_ H H0 H1 intervals_small f f_contin H2 H3).
intro z. intro H4. exists z.
exact H4.
intros. exact (interval_f_rht _ (interval_sequence i)).
intros. exact (interval_f_lft _ (interval_sequence i)).
intros. exact (interval_lft_rht _ (interval_sequence i)).
intros. elim (bisect_prop f f_apzero_interval (interval_sequence i)).
intros H0 H1. elim H1. intros H2 H3.
unfold b_ in |- *. simpl in |- *. 
assumption.
intros. elim (bisect_prop f f_apzero_interval (interval_sequence i)).
intros H H0. elim H0. intros H1 H2.
unfold a_ in |- *. simpl in |- *. auto.
Qed.

End IVT_Op.

Section IVT_Poly.

(** ** IVT for polynomials *)

Lemma Civt_poly :
 forall f : cpoly_cring IR,
 f[#]Zero ->
 forall a b : IR,
 a[<]b ->
 f ! a[<=]Zero ->
 Zero[<=]f ! b -> {x : IR | a[<=]x /\ x[<=]b /\ f ! x[=]Zero}.
intros.
cut ({x : IR | a[<=]x /\ x[<=]b /\ cpoly_csetoid_op _ f x[=]Zero}).
intro. auto.
apply Civt_op; auto.
apply cpoly_op_contin.
intros.
change {c : IR | a0[<=]c /\ c[<=]b0 | f ! c[#]Zero} in |- *.
apply Cpoly_apzero_interval. auto. auto.
Qed.

End IVT_Poly.
