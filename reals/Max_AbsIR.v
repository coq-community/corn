
(** printing Max %\ensuremath{\max}% *)
(** printing Min %\ensuremath{\min}% *)

Require Export CauchySeq.

Section Maximum.

Section Max_function.
(** ** Maximum, Minimum and Absolute Value

%\begin{convention}%
Let [x] and [y] be reals
(we will define the maximum of [x] and [y]).
%\end{convention}%
*)

Variables x y : IR.

Definition Max_seq : nat -> IR.
intro i.
elim (less_cotransitive_unfolded IR Zero (one_div_succ i)) with (x[-]y).
  3: apply one_div_succ_pos.
 intro H; apply x.
intro H; apply y.
Defined.

Lemma Max_seq_char : forall n,
 Zero [<] x[-]y and Max_seq n [=] x or x[-]y [<] one_div_succ n and Max_seq n [=] y.
intros.
unfold Max_seq in |- *.
elim less_cotransitive_unfolded; intro H; simpl in |- *.
 left; split; algebra.
right; split; algebra.
Qed.

Lemma Cauchy_Max_seq : Cauchy_prop Max_seq.
apply Cauchy_prop1_prop.
intro k.
exists k; intros m H.
unfold Max_seq in |- *.
elim less_cotransitive_unfolded; intro Hm; simpl in |- *;
 elim less_cotransitive_unfolded; intro Hk; simpl in |- *.

astepr ZeroR; split; apply less_leEq.
 astepr ( [--]ZeroR); apply inv_resp_less; apply one_div_succ_pos.
apply one_div_succ_pos.

apply leEq_imp_AbsSmall; apply less_leEq; auto.

apply AbsSmall_minus.
apply leEq_imp_AbsSmall; apply less_leEq; auto.
apply less_leEq_trans with (one_div_succ (R:=IR) m); auto.
apply one_div_succ_resp_leEq; auto.

astepr ZeroR; split; apply less_leEq.
 astepr ( [--]ZeroR); apply inv_resp_less; apply one_div_succ_pos.
apply one_div_succ_pos.
Qed.

Definition Max_CauchySeq : CauchySeqR.
unfold CauchySeqR in |- *.
apply Build_CauchySeq with Max_seq.
exact Cauchy_Max_seq.
Defined.

Definition MAX : IR.
apply Lim.
exact Max_CauchySeq.
Defined.

(**
Constructively, the elementary properties of the maximum function are:
- [x [<=] Max (x,y)],
- [x [<=] Max (y,x)],
- [z [<] Max(x,y) -> z [<] x or z [<] y].

(This can be more concisely expressed as
[z [<] Max(x,y) Iff z [<] x or z [<] y]).
From these elementary properties we can prove all other properties, including
strong extensionality.
With strong extensionality, we can make the binary operation [Max].
(So [Max] is [MAX] coupled with some proofs.)
*)

Lemma lft_leEq_MAX : x [<=] MAX.
astepr (Zero[+]MAX); apply shift_leEq_plus.
red in |- *; apply approach_zero_weak.
intros e He.
apply leEq_wdl with (Lim (Cauchy_const x) [-]MAX).
 2: apply cg_minus_wd;
     [ apply eq_symmetric_unfolded; apply Lim_const | algebra ].
unfold MAX in |- *.
eapply leEq_wdl.
 2: apply Lim_minus.
simpl in |- *.
elim (Archimedes (One[/] e[//]pos_ap_zero _ _ He)); intros n Hn.
cut (Zero [<] nring (R:=IR) n).
intro posn.
apply str_seq_leEq_so_Lim_leEq.
exists n; intros i Hi.
simpl in |- *.
unfold Max_seq in |- *.
elim less_cotransitive_unfolded; intro H; simpl in |- *.
 astepl ZeroR; apply less_leEq; auto.
apply less_leEq; eapply less_transitive_unfolded.
apply H.
unfold one_div_succ, Snring in |- *; apply shift_div_less.
 apply pos_nring_S.
apply shift_less_mult' with (pos_ap_zero _ _ He).
 auto.
eapply leEq_less_trans.
 apply Hn.
apply nring_less; auto with arith.

eapply less_leEq_trans.
 2: apply Hn.
apply recip_resp_pos; auto.
Qed.

Lemma rht_leEq_MAX : y [<=] MAX.
unfold MAX in |- *.
apply leEq_seq_so_leEq_Lim.
intro i; simpl in |- *.
unfold Max_seq in |- *.
elim less_cotransitive_unfolded; intro H; simpl in |- *.
 2: apply leEq_reflexive.
apply less_leEq; astepl (Zero[+]y).
apply shift_plus_less; auto.
Qed.

Lemma less_MAX_imp : forall z : IR, z [<] MAX -> z [<] x or z [<] y.
intros z H.
unfold MAX in H.
elim (less_Lim_so_less_seq _ _ H).
intros N HN.
simpl in HN.
elim (Max_seq_char N); intro Hseq; inversion_clear Hseq; [ left | right ];
 astepr (Max_seq N); auto with arith.
Qed.

End Max_function.

Lemma MAX_strext : bin_op_strext _ MAX.
unfold bin_op_strext in |- *.
unfold bin_fun_strext in |- *.
intros x1 x2 y1 y2 H.
generalize (ap_imp_less _ _ _ H); intro H0.
elim H0; intro H1.
 generalize (less_MAX_imp _ _ _ H1); intro H2.
 elim H2; intro H3.
  left.
  apply less_imp_ap.
  apply leEq_less_trans with (MAX x1 y1); auto.
  apply lft_leEq_MAX.
 right.
 apply less_imp_ap.
 apply leEq_less_trans with (MAX x1 y1); auto.
 apply rht_leEq_MAX.
generalize (less_MAX_imp _ _ _ H1); intro H2.
elim H2; intro.
 left.
 apply Greater_imp_ap.
 apply leEq_less_trans with (MAX x2 y2); auto.
 apply lft_leEq_MAX.
right.
apply Greater_imp_ap.
apply leEq_less_trans with (MAX x2 y2); auto.
apply rht_leEq_MAX.
Qed.

Lemma MAX_wd : bin_op_wd IR MAX.
unfold bin_op_wd in |- *.
apply bin_fun_strext_imp_wd.
exact MAX_strext.
Qed.

Section properties_of_Max.

(** *** Maximum *)

Definition Max := Build_CSetoid_bin_op _ MAX MAX_strext.

Lemma Max_wd_unfolded : forall x y x' y',
 x [=] x' -> y [=] y' -> Max x y [=] Max x' y'.
cut (bin_op_wd _ MAX); [ intro | apply MAX_wd ].
red in H.
red in H.
intros; apply H; assumption.
Qed.

Lemma lft_leEq_Max : forall x y : IR, x [<=] Max x y.
unfold Max in |- *.
simpl in |- *.
exact lft_leEq_MAX.
Qed.

Lemma rht_leEq_Max : forall x y : IR, y [<=] Max x y.
unfold Max in |- *.
simpl in |- *.
exact rht_leEq_MAX.
Qed.

Lemma less_Max_imp : forall x y z : IR, z [<] Max x y -> z [<] x or z [<] y.
unfold Max in |- *.
simpl in |- *.
exact less_MAX_imp.
Qed.

Lemma Max_leEq : forall x y z : IR, x [<=] z -> y [<=] z -> Max x y [<=] z.
unfold Max in |- *.
simpl in |- *.
intros.
unfold leEq in |- *.
intro H1.
generalize (less_MAX_imp _ _ _ H1); intro H2.
elim H2; intros.
elim H.
assumption.
elim H0.
assumption.
Qed.

Lemma Max_less : forall x y z : IR, x [<] z -> y [<] z -> Max x y [<] z.
intros.
elim (smaller _ (z[-]x) (z[-]y)). intro e. intros H1 H2. elim H2. clear H2. intros H2 H3.
cut (z[-]e [/]TwoNZ [<] z). intro H4.
elim (less_cotransitive_unfolded _ _ _ H4 (Max x y)); intros H5.
elim (less_Max_imp _ _ _ H5); intros H6.
cut (Not (e [/]TwoNZ [<] z[-]x)). intro H7. elim H7.
apply less_leEq_trans with e; auto.
apply pos_div_two'; auto.
apply less_antisymmetric_unfolded.
apply shift_minus_less. apply shift_less_plus'. auto.
cut (Not (e [/]TwoNZ [<] z[-]y)). intro H7. elim H7.
apply less_leEq_trans with e; auto.
apply pos_div_two'; auto.
apply less_antisymmetric_unfolded.
apply shift_minus_less. apply shift_less_plus'. auto.
auto.
apply shift_minus_less. astepl (z[+]Zero).
apply plus_resp_less_lft. apply pos_div_two. auto.
apply shift_less_minus. astepl x. auto.
apply shift_less_minus. astepl y. auto.
Qed.

Lemma equiv_imp_eq_max : forall x x' m, (forall y, x [<] y -> x' [<] y -> m [<] y) ->
 (forall y, m [<] y -> x [<] y) -> (forall y, m [<] y -> x' [<] y) -> Max x x' [=] m.
intros.
apply lt_equiv_imp_eq; intros.
apply X.
apply leEq_less_trans with (Max x x').
apply lft_leEq_Max. auto.
apply leEq_less_trans with (Max x x').
apply rht_leEq_Max. auto.
apply Max_less; auto.
Qed.

Lemma Max_id : forall x : IR, Max x x [=] x.
intros.
apply equiv_imp_eq_max; auto.
Qed.

Lemma Max_comm : forall x y : IR, Max x y [=] Max y x.
cut (forall x y : IR, Max x y [<=] Max y x).
intros.
apply leEq_imp_eq.
apply H.
apply H.
intros.
apply Max_leEq.
apply rht_leEq_Max.
apply lft_leEq_Max.
Qed.

Lemma leEq_imp_Max_is_rht : forall x y : IR, x [<=] y -> Max x y [=] y.
intros.
apply leEq_imp_eq.
apply Max_leEq.
assumption.
apply leEq_reflexive.
apply rht_leEq_Max.
Qed.

Lemma Max_is_rht_imp_leEq : forall x y : IR, Max x y [=] y -> x [<=] y.
intros.
unfold leEq in |- *.
intro H0.
generalize (less_leEq _ _ _ H0); intro H1.
generalize (leEq_imp_Max_is_rht _ _ H1); intro.
cut (y [=] x).
intro.
elim (less_irreflexive_unfolded _ x).
astepl y.
assumption.
astepl (Max x y).
astepr (Max y x).
apply Max_comm.
Qed.

Lemma Max_minus_eps_leEq : forall x y e,
 Zero [<] e -> {Max x y[-]e [<=] x} + {Max x y[-]e [<=] y}.
intros.
cut (Max x y[-]e [<] x or Max x y[-]e [<] y).
intro H0; elim H0; intros; clear H0.
left; apply less_leEq; assumption.
right; apply less_leEq; assumption.
apply less_Max_imp.
apply shift_minus_less.
apply shift_less_plus'.
astepl ZeroR; assumption.
Qed.

Lemma max_one_ap_zero : forall x : IR, Max x One [#] Zero.
intros.
apply ap_symmetric_unfolded.
apply less_imp_ap.
apply less_leEq_trans with OneR.
apply pos_one.
apply rht_leEq_Max.
Qed.

Lemma pos_max_one : forall x : IR, Zero [<] Max x One.
intro.
apply less_leEq_trans with OneR; [ apply pos_one | apply rht_leEq_Max ].
Qed.

Lemma x_div_Max_leEq_x :
 forall x y : IR, Zero [<] x -> (x[/] Max y One[//]max_one_ap_zero _) [<=] x.
intros.
apply shift_div_leEq'.
apply pos_max_one.
astepl (One[*]x).
apply mult_resp_leEq_rht;
 [ apply rht_leEq_Max | apply less_leEq; assumption ].
Qed.

Lemma max_plus : forall (a b c : IR),
Max (a[+]c) (b[+]c) [=] Max a b [+] c.
intros.
apply equiv_imp_eq_max; intros.
apply shift_plus_less.
apply Max_less; apply shift_less_minus; auto.
apply leEq_less_trans with (Max a b [+]c); auto.
apply plus_resp_leEq.
apply lft_leEq_Max.
apply leEq_less_trans with (Max a b [+]c); auto.
apply plus_resp_leEq.
apply rht_leEq_Max.
Qed.

Lemma max_mult : forall (a b c : IR), Zero [<] c -> 
(Max (c[*]a) (c[*]b)) [=] c[*](Max a b).
intros a b c H.
assert (H1 : c [#] Zero).
apply pos_ap_zero; auto.
assert (H2 : Zero [<=] c).
apply less_leEq; auto.
assert (forall y : IR, c[*]a[<]y -> c[*]b[<]y -> c[*]Max a b[<]y).
intros.
astepl (Max a b [*]c).
apply shift_mult_less with H1; auto.
apply Max_less;
apply shift_less_div; auto.
auto.
astepl (c[*]a).
auto.
astepl (c[*]b).
auto.
assert (forall y : IR, c[*]Max a b[<]y -> c[*]a[<]y).
intros.
apply leEq_less_trans with (c[*]Max a b); auto.
apply mult_resp_leEq_lft; auto.
apply lft_leEq_MAX.
auto.
assert (forall y : IR, c[*]Max a b[<]y -> c[*]b[<]y).
intros.
apply leEq_less_trans with (c[*]Max a b); auto.
apply mult_resp_leEq_lft; auto.
apply rht_leEq_MAX.
auto.
apply equiv_imp_eq_max; auto.
Qed.

End properties_of_Max.

End Maximum.

Hint Resolve Max_id: algebra.

Section Minimum.

(** *** Mininum

The minimum is defined by the formula 
[Min(x,y) [=] [--]Max( [--]x,[--]y)].
*)

Definition MIN (x y : IR) : IR := [--] (Max [--]x [--]y).

Lemma MIN_wd : bin_op_wd _ MIN.
intros x1 x2 y1 y2.
unfold MIN in |- *; algebra.
Qed.

Lemma MIN_strext : bin_op_strext _ MIN.
intros x1 x2 y1 y2 H.
unfold MIN in H.
assert (H':=(un_op_strext_unfolded _ _ _ _ H)).
elim (bin_op_strext_unfolded _ _ _ _ _ _ H');
 intro H1; [left | right]; exact (un_op_strext_unfolded _ _ _ _ H1).
Qed.

Definition Min : CSetoid_bin_op IR := Build_CSetoid_bin_op _ MIN MIN_strext.

Lemma Min_wd_unfolded : forall x y a b,
 x [=] a /\ y [=] b -> (Min x y) [=] (Min a b).
intros; inversion H.
apply MIN_wd; auto.
Qed.

Lemma Min_strext_unfolded : forall x y a b,
 (Min x y) [#] (Min a b) -> x [#] a or y [#] b.
intros.
apply MIN_strext; auto.
Qed.

Lemma Min_leEq_lft : forall x y : IR, Min x y [<=] x.
intros.
simpl in |- *; unfold MIN.
rstepr ( [--][--]x).
apply inv_resp_leEq.
apply lft_leEq_Max.
Qed.

Lemma Min_leEq_rht : forall x y : IR, Min x y [<=] y.
intros.
simpl; unfold MIN.
rstepr ( [--][--]y).
apply inv_resp_leEq.
apply rht_leEq_Max.
Qed.

Lemma Min_less_imp : forall x y z : IR, Min x y [<] z -> x [<] z or y [<] z.
simpl; unfold MIN.
intros.
cut ( [--]z [<] [--]x or [--]z [<] [--]y).
intros H0.
elim H0; intro.
left.
apply inv_cancel_less; assumption.
right.
apply inv_cancel_less; assumption.
apply less_Max_imp.
apply inv_cancel_less.
apply less_wdr with z.
assumption.
algebra.
Qed.

Lemma leEq_Min : forall x y z : IR, z [<=] x -> z [<=] y -> z [<=] Min x y.
intros.
simpl; unfold MIN.
rstepl ( [--][--]z).
apply inv_resp_leEq.
apply Max_leEq; apply inv_resp_leEq; assumption.
Qed.

Lemma less_Min : forall x y z : IR, z [<] x -> z [<] y -> z [<] Min x y.
intros.
simpl; unfold MIN.
rstepl ( [--][--]z).
apply inv_resp_less.
apply Max_less; apply inv_resp_less; assumption.
Qed.

Lemma equiv_imp_eq_min : forall x x' m, (forall y, y [<] x -> y [<] x' -> y [<] m) ->
 (forall y, y [<] m -> y [<] x) -> (forall y, y [<] m -> y [<] x') -> Min x x' [=] m.
intros.
simpl; unfold MIN.
astepr ( [--][--]m).
apply un_op_wd_unfolded.
apply equiv_imp_eq_max.
intros.
rstepr ( [--][--]y).
apply inv_resp_less.
apply X.
rstepr ( [--][--]x).
apply inv_resp_less.
assumption.
rstepr ( [--][--]x').
apply inv_resp_less.
assumption.
intros.
rstepr ( [--][--]y).
apply inv_resp_less.
apply X0.
rstepr ( [--][--]m).
apply inv_resp_less.
assumption.
intros.
rstepr ( [--][--]y).
apply inv_resp_less.
apply X1.
rstepr ( [--][--]m).
apply inv_resp_less.
assumption.
Qed.

Lemma Min_id : forall x : IR, Min x x [=] x.
intro.
simpl; unfold MIN.
astepr ( [--][--]x).
apply un_op_wd_unfolded; apply Max_id.
Qed.

Lemma Min_comm : forall x y : IR, Min x y [=] Min y x.
intros.
simpl; unfold MIN.
apply un_op_wd_unfolded; apply Max_comm.
Qed.

Lemma leEq_imp_Min_is_lft : forall x y : IR, x [<=] y -> Min x y [=] x.
intros.
simpl; unfold MIN.
astepr ( [--][--]x).
apply un_op_wd_unfolded.
apply eq_transitive_unfolded with (Max [--]y [--]x).
apply Max_comm.
apply leEq_imp_Max_is_rht.
apply inv_resp_leEq.
assumption.
Qed.

Lemma Min_is_lft_imp_leEq : forall x y : IR, Min x y [=] x -> x [<=] y.
simpl; unfold MIN.
intros.
rstepl ( [--][--]x).
rstepr ( [--][--]y).
apply inv_resp_leEq.
apply Max_is_rht_imp_leEq.
astepl ( [--][--] (Max [--]y [--]x)).
apply eq_transitive_unfolded with ( [--][--] (Max [--]x [--]y)).
apply un_op_wd_unfolded; apply un_op_wd_unfolded; apply Max_comm.
apply un_op_wd_unfolded; assumption.
Qed.

Lemma leEq_Min_plus_eps : forall x y e,
 Zero [<] e -> {x [<=] Min x y[+]e} + {y [<=] Min x y[+]e}.
intros.
cut (x [<] Min x y[+]e or y [<] Min x y[+]e).
intro H0; elim H0; intros; clear H0.
left; apply less_leEq; assumption.
right; apply less_leEq; assumption.
apply Min_less_imp.
apply shift_less_plus'.
astepl ZeroR; assumption.
Qed.

Variables a b : IR.

Lemma Min_leEq_Max : Min a b [<=] Max a b.
intros.
apply leEq_transitive with a; [ apply Min_leEq_lft | apply lft_leEq_Max ].
Qed.

Lemma Min_leEq_Max' : forall z : IR, Min a z [<=] Max b z.
intros; apply leEq_transitive with z.
apply Min_leEq_rht.
apply rht_leEq_Max.
Qed.

Lemma Min3_leEq_Max3 : forall c : IR, Min (Min a b) c [<=] Max (Max a b) c.
intros; eapply leEq_transitive.
apply Min_leEq_rht.
apply rht_leEq_Max.
Qed.

Lemma Min_less_Max : forall c d : IR, a [<] b -> Min a c [<] Max b d.
intros.
apply leEq_less_trans with a.
apply Min_leEq_lft.
apply less_leEq_trans with b.
assumption.
apply lft_leEq_Max.
Qed.

Lemma ap_imp_Min_less_Max : a [#] b -> Min a b [<] Max a b.
intro Hap; elim (ap_imp_less _ _ _ Hap);
 (intro H;
   [ eapply leEq_less_trans;
      [ idtac | eapply less_leEq_trans; [ apply H | idtac ] ] ]).
apply Min_leEq_lft.
apply rht_leEq_Max.
apply Min_leEq_rht.
apply lft_leEq_Max.
Qed.

Lemma Min_less_Max_imp_ap : Min a b [<] Max a b -> a [#] b.
intro H.
elim (Min_less_imp _ _ _ H); clear H; intro H; elim (less_Max_imp _ _ _ H);
 intro H0.
elimtype False; exact (less_irreflexive _ _ H0).
apply less_imp_ap; auto.
apply Greater_imp_ap; auto.
elimtype False; exact (less_irreflexive _ _ H0).
Qed.

End Minimum.

(***********************************)
Section Absolute.
(***********************************)

(** *** Absolute value *)

Definition ABSIR (x : IR) : IR := Max x [--]x.


Lemma ABSIR_strext : un_op_strext _ ABSIR.
unfold un_op_strext in |- *.
unfold fun_strext in |- *.
unfold ABSIR in |- *.
intros.
generalize (csbf_strext _ _ _ Max); intro H0.
unfold bin_fun_strext in H0.
generalize (H0 _ _ _ _ X); intro H1.
elim H1.
intro H2.
assumption.
intro H2.
apply zero_minus_apart.
generalize (minus_ap_zero _ _ _ H2); intro H3.
generalize (inv_resp_ap_zero _ _ H3); intro H4.
cut (x[-]y [=] [--] ( [--]x[-][--]y)).
intro.
astepl ( [--] ( [--]x[-][--]y)). auto.
rational.
Qed.

Lemma ABSIR_wd : un_op_wd _ ABSIR.
unfold un_op_wd in |- *.
apply fun_strext_imp_wd.
exact ABSIR_strext.
Qed.

Definition AbsIR : CSetoid_un_op IR := Build_CSetoid_un_op _ ABSIR ABSIR_strext.

Lemma AbsIR_wd : forall x y : IR, x [=] y -> AbsIR x [=] AbsIR y.
algebra.
Qed.

Lemma AbsIR_wdl : forall x y e, x [=] y -> AbsIR x [<] e -> AbsIR y [<] e.
Proof.
intros.
apply less_wdl with (AbsIR x).
assumption.
algebra.
Qed.

Lemma AbsIR_wdr : forall x y e, x [=] y -> e [<] AbsIR x -> e [<] AbsIR y.
Proof.
intros.
apply less_wdr with (AbsIR x).
assumption.
algebra.
Qed.

Lemma AbsIRz_isz : AbsIR Zero [=] Zero.
intros. unfold AbsIR in |- *. simpl in |- *. unfold ABSIR in |- *.
Step_final (Max Zero Zero).
Qed.

Lemma AbsIR_nonneg : forall x : IR, Zero [<=] AbsIR x.
intro x; intro H.
cut (Zero [<] ZeroR).
apply less_irreflexive.
apply less_wdl with (AbsIR x); auto.
eapply eq_transitive_unfolded.
2: apply AbsIRz_isz.
apply AbsIR_wd.
unfold AbsIR in H; simpl in H; unfold ABSIR in H.
apply leEq_imp_eq; apply less_leEq.
apply leEq_less_trans with (Max x [--]x).
apply lft_leEq_Max.
assumption.
apply inv_cancel_less.
apply leEq_less_trans with (Max x [--]x).
apply rht_leEq_Max.
astepr ZeroR; auto.
Qed.

Lemma AbsIR_pos : forall x : IR, x [#] Zero -> Zero [<] AbsIR x.
intros.
cut (x [<] Zero or Zero [<] x).
2: apply ap_imp_less; assumption.
intros H0.
unfold AbsIR in |- *; simpl in |- *; unfold ABSIR in |- *.
elim H0.
intro.
apply less_leEq_trans with ( [--]x).
astepl ( [--]ZeroR).
apply inv_resp_less.
assumption.
apply rht_leEq_Max.
intro.
apply less_leEq_trans with x.
assumption.
apply lft_leEq_Max.
Qed.

Lemma AbsIR_cancel_ap_zero : forall x : IR, AbsIR x [#] Zero -> x [#] Zero.
intros.
apply un_op_strext_unfolded with AbsIR.
apply ap_wdr_unfolded with ZeroR.
assumption.
apply eq_symmetric_unfolded; apply AbsIRz_isz.
Qed.

Lemma AbsIR_resp_ap_zero : forall x : IR, x [#] Zero -> AbsIR x [#] Zero.
intros.
apply ap_symmetric_unfolded; apply less_imp_ap.
apply AbsIR_pos; assumption.
Qed.

Lemma leEq_AbsIR : forall x : IR, x [<=] AbsIR x.
intros.
unfold AbsIR in |- *; simpl in |- *; unfold ABSIR in |- *; apply lft_leEq_Max.
Qed.

Lemma inv_leEq_AbsIR : forall x : IR, [--]x [<=] AbsIR x.
intros.
unfold AbsIR in |- *; simpl in |- *; unfold ABSIR in |- *; apply rht_leEq_Max.
Qed.

Lemma AbsSmall_e : forall e x : IR, AbsSmall e x -> Zero [<=] e.
intros.
red in H.
cut ( [--]e [<=] e).
2: inversion_clear H; apply leEq_transitive with x; assumption.
intro.
apply mult_cancel_leEq with (Two:IR); astepl ZeroR.
apply pos_two.
rstepr (e[+]e).
apply shift_leEq_plus; astepl ( [--]e).
assumption.
Qed.

Lemma AbsSmall_imp_AbsIR : forall x y : IR, AbsSmall y x -> AbsIR x [<=] y.
intros.
unfold AbsIR in |- *; simpl in |- *; unfold ABSIR in |- *.
inversion_clear H.
apply Max_leEq.
assumption.
apply inv_cancel_leEq.
astepr x; auto.
Qed.

Lemma AbsIR_eq_AbsSmall : forall x e : IR, [--]e [<=] x -> x [<=] e -> AbsSmall e x.
intros.
unfold AbsSmall in |- *.
auto.
Qed.

Lemma AbsIR_imp_AbsSmall : forall x y : IR, AbsIR x [<=] y -> AbsSmall y x.
intros.
unfold AbsSmall in |- *.
simpl in H.
unfold ABSIR in H.
simpl in H.
split.
generalize (rht_leEq_Max x [--]x).
intro H1.
generalize (leEq_transitive _ _ (MAX x [--]x) _ H1 H).
intro H2.
rstepr ( [--][--]x).
apply inv_resp_leEq.
assumption.
generalize (lft_leEq_Max x [--]x).
intro H1.
generalize (leEq_transitive _ _ (MAX x [--]x) _ H1 H).
auto.
Qed.

Lemma AbsSmall_transitive : forall e x y : IR,
 AbsSmall e x -> AbsIR y [<=] AbsIR x -> AbsSmall e y.
intros.
apply AbsIR_imp_AbsSmall.
eapply leEq_transitive.
apply H0.
apply AbsSmall_imp_AbsIR; assumption.
Qed.

Lemma zero_less_AbsIR_plus_one : forall q : IR, Zero [<] AbsIR q[+]One.
intros.
apply less_leEq_trans with (Zero[+]OneR).
rstepr OneR; apply pos_one.
apply plus_resp_leEq; apply AbsIR_nonneg.
Qed.

Lemma AbsIR_inv : forall x : IR, AbsIR x [=] AbsIR [--]x.
intros.
unfold AbsIR in |- *; simpl in |- *; unfold ABSIR in |- *.
apply eq_transitive_unfolded with (Max [--][--]x [--]x).
apply bin_op_wd_unfolded; algebra.
apply Max_comm.
Qed.

Lemma AbsIR_minus : forall x y : IR, AbsIR (x[-]y) [=] AbsIR (y[-]x).
intros.
eapply eq_transitive_unfolded.
apply AbsIR_inv.
apply AbsIR_wd; rational.
Qed.

Lemma AbsIR_mult : forall (x c: IR) (H : Zero [<]c),
c[*] AbsIR (x) [=] AbsIR (c[*]x).
intros.
unfold AbsIR.
simpl.
unfold ABSIR.
rstepr (Max (c[*]x) (c[*]([--]x))).
apply eq_symmetric_unfolded.
apply max_mult; auto.
Qed.


Lemma AbsIR_eq_x : forall x : IR, Zero [<=] x -> AbsIR x [=] x.
intros.
unfold AbsIR in |- *; simpl in |- *; unfold ABSIR in |- *.
apply eq_transitive_unfolded with (Max [--]x x).
apply Max_comm.
apply leEq_imp_Max_is_rht.
apply leEq_transitive with ZeroR.
2: assumption.
astepr ( [--]ZeroR).
apply inv_resp_leEq.
assumption.
Qed.

Lemma AbsIR_eq_inv_x : forall x : IR, x [<=] Zero -> AbsIR x [=] [--]x.
intros.
apply eq_transitive_unfolded with (AbsIR [--]x).
apply AbsIR_inv.
apply AbsIR_eq_x.
astepl ( [--]ZeroR).
apply inv_resp_leEq.
assumption.
Qed.

Lemma less_AbsIR : forall x y, Zero [<] x -> x [<] AbsIR y -> x [<] y or y [<] [--]x.
intros x y H H0.
simpl in H0.
unfold ABSIR in H0.
cut (x [<] y or x [<] [--]y).
intro H1; inversion_clear H1.
left; assumption.
right; astepl ( [--][--]y); apply inv_resp_less; assumption.
apply less_Max_imp; assumption.
Qed.

Lemma leEq_distr_AbsIR : forall x y : IR,
 Zero [<] x -> x [<=] AbsIR y -> {x [<=] y} + {y [<=] [--]x}.
intros.
cut (x[*]Three [/]FourNZ [<] AbsIR y); intros.
elim (less_AbsIR (x[*]Three [/]FourNZ) y); intros;
 [ left | right | idtac | auto ].
astepr (Zero[+]y); apply shift_leEq_plus.
red in |- *; apply approach_zero.
cut (forall e : IR, Zero [<] e -> e [<] x [/]TwoNZ -> x[-]y [<] e); intros.
cut (x [/]FourNZ [<] x [/]TwoNZ); intros.
2: rstepl ((x [/]TwoNZ) [/]TwoNZ); apply pos_div_two'; apply pos_div_two;
    auto.
rename X3 into H4.
elim (less_cotransitive_unfolded _ _ _ H4 e); intro.
apply leEq_less_trans with (x [/]FourNZ); auto.
apply less_leEq.
apply shift_minus_less; apply shift_less_plus'.
rstepl (x[*]Three [/]FourNZ); auto.
rename X1 into H2. apply H2; auto.
apply shift_minus_less; apply shift_less_plus'.
cut (x[-]e [<] AbsIR y); intros.
2: apply less_leEq_trans with x; auto.
2: apply shift_minus_less; apply shift_less_plus'; astepl ZeroR; auto.
elim (less_AbsIR (x[-]e) y); auto.
intro; elimtype False.
apply (less_irreflexive_unfolded _ y).
eapply leEq_less_trans.
2: apply a.
apply less_leEq; eapply less_transitive_unfolded.
apply b.
astepl (Zero[-] (x[-]e)).
apply shift_minus_less.
astepr (x[*]Three [/]FourNZ[+]x[-]e).
apply shift_less_minus; astepl e.
eapply less_leEq_trans.
rename X2 into H3. apply H3.
apply less_leEq.
rstepl (x[*] (Zero[+]Zero[+]One [/]TwoNZ));
 rstepr (x[*] (One[+]One [/]FourNZ[+]One [/]TwoNZ)).
apply mult_resp_less_lft; auto.
apply plus_resp_less_rht; apply plus_resp_less_leEq.
apply pos_one.
apply less_leEq; apply pos_div_four; apply pos_one.
apply shift_less_minus; astepl e.
eapply less_leEq_trans.
rename X2 into H3. apply H3.
apply less_leEq; apply pos_div_two'; auto.
astepr (Zero[+][--]x); apply shift_leEq_plus.
apply leEq_wdl with (y[+]x).
2: unfold cg_minus in |- *; algebra.
red in |- *; apply approach_zero.
cut (forall e : IR, Zero [<] e -> e [<] x [/]TwoNZ -> y[+]x [<] e); intros.
cut (x [/]FourNZ [<] x [/]TwoNZ); intros.
2: rstepl ((x [/]TwoNZ) [/]TwoNZ); apply pos_div_two'; apply pos_div_two;
    auto.
rename X3 into H4.
elim (less_cotransitive_unfolded _ _ _ H4 e); intro.
apply leEq_less_trans with (x [/]FourNZ); auto.
apply less_leEq; apply shift_plus_less.
rstepr ( [--] (x[*]Three [/]FourNZ)); auto.
rename X1 into H2. apply H2; auto.
cut (x[-]e [<] AbsIR y); intros.
2: apply less_leEq_trans with x; auto.
2: apply shift_minus_less; apply shift_less_plus'; astepl ZeroR; auto.
elim (less_AbsIR (x[-]e) y); auto.
intro; elimtype False.
apply (less_irreflexive_unfolded _ y).
eapply leEq_less_trans.
2: apply a.
apply less_leEq; eapply less_transitive_unfolded.
apply b.
apply shift_less_minus; apply shift_plus_less'.
eapply less_transitive_unfolded.
rename X2 into H3. apply H3.
rstepl (x[*] (Zero[+]Zero[+]One [/]TwoNZ));
 rstepr (x[*] (One[+]One [/]FourNZ[+]One [/]TwoNZ)).
apply mult_resp_less_lft; auto.
apply plus_resp_less_rht; apply plus_resp_less_leEq.
apply pos_one.
apply less_leEq; apply pos_div_four; apply pos_one.
intro.
rstepl (y[-][--]x).
apply shift_minus_less.
rstepr ( [--] (x[-]e)); auto.
apply shift_less_minus; astepl e.
eapply less_leEq_trans.
rename X2 into H3. apply H3.
apply less_leEq; apply pos_div_two'; auto.
astepl (ZeroR[*]Three [/]FourNZ).
apply mult_resp_less; auto.
apply pos_div_four; apply pos_three.
apply less_leEq_trans with x; auto.
astepr (x[*]One).
astepr (x[*]Four [/]FourNZ).
apply mult_resp_less_lft; auto.
apply div_resp_less.
apply pos_four.
apply three_less_four.
Qed.

Lemma AbsIR_approach_zero : forall x, (forall e, Zero [<] e -> AbsIR x [<=] e) -> x [=] Zero.
intros.
apply leEq_imp_eq.
red in |- *; apply approach_zero_weak.
intros e H0.
eapply leEq_transitive; [ apply leEq_AbsIR | exact (H e H0) ].
astepl ( [--]ZeroR); astepr ( [--][--]x); apply inv_resp_leEq.
red in |- *; apply approach_zero_weak.
intros e H0.
eapply leEq_transitive; [ apply inv_leEq_AbsIR | exact (H e H0) ].
Qed.

Lemma AbsSmall_approach :
forall (a b : IR),
  (forall (e : IR), Zero[<]e -> AbsSmall (a[+]e) b) -> AbsSmall a b.
unfold AbsSmall.
intros a b H.
split.
assert (forall e : IR, Zero[<]e -> [--]a[-]b[<=]e).
intros. 
assert ([--](a[+]e)[<=]b /\ b[<=]a[+]e).
apply H; auto. destruct H0.
apply shift_minus_leEq.
apply shift_leEq_plus'.
astepl ([--]a[+][--]e).
astepl ([--](a[+]e)).
auto.
astepr (b[+]Zero).
apply shift_leEq_plus'.
unfold leEq.
apply approach_zero_weak; auto.
assert (forall e : IR, Zero[<]e -> b[-]a[<=]e).
intros. 
assert ([--](a[+]e)[<=]b /\ b[<=]a[+]e).
apply H; auto. destruct H0.
apply shift_minus_leEq.
astepr (a[+]e).
auto.
astepr (a[+]Zero).
apply shift_leEq_plus'.
unfold leEq.
apply approach_zero_weak; auto.
Qed.

Lemma AbsIR_eq_zero : forall x : IR, AbsIR x [=] Zero -> x [=] Zero.
intros.
apply AbsIR_approach_zero; intros.
astepl ZeroR; apply less_leEq; auto.
Qed.

Lemma Abs_Max : forall a b : IR, AbsIR (a[-]b) [=] Max a b[-]Min a b.
intros.
apply leEq_imp_eq.
apply leEq_wdl with (Max (a[-]b) (b[-]a)).
2: simpl in |- *; unfold ABSIR in |- *.
2: apply Max_wd_unfolded; rational.
apply Max_leEq.
unfold cg_minus in |- *; apply plus_resp_leEq_both.
apply lft_leEq_Max.
apply inv_resp_leEq; apply Min_leEq_rht.
unfold cg_minus in |- *; apply plus_resp_leEq_both.
apply rht_leEq_Max.
apply inv_resp_leEq; apply Min_leEq_lft.
astepr (Zero[+]AbsIR (a[-]b)).
apply shift_leEq_plus.
red in |- *; apply approach_zero_weak.
intros.
do 2 apply shift_minus_leEq.
eapply leEq_wdr.
2: apply CSemiGroups.plus_assoc.
apply shift_leEq_plus'.
rename X into H.
elim (Max_minus_eps_leEq a b e H); intro.
apply leEq_transitive with a.
assumption.
apply shift_leEq_plus'.
apply leEq_Min.
apply shift_minus_leEq; apply shift_leEq_plus'.
astepl ZeroR; apply AbsIR_nonneg.
apply shift_minus_leEq; apply shift_leEq_plus'.
apply leEq_AbsIR.
apply leEq_transitive with b.
assumption.
apply shift_leEq_plus'.
apply leEq_Min.
apply shift_minus_leEq; apply shift_leEq_plus'.
rstepl ( [--] (a[-]b)); apply inv_leEq_AbsIR.
apply shift_minus_leEq; apply shift_leEq_plus'.
astepl ZeroR; apply AbsIR_nonneg.
Qed.

Lemma AbsIR_str_bnd : forall a b e : IR, AbsIR (a[-]b) [<] e -> b [<] a[+]e.
intros.
apply shift_less_plus'.
apply leEq_less_trans with (AbsIR (a[-]b)); auto.
eapply leEq_wdr; [ apply leEq_AbsIR | apply AbsIR_minus ].
Qed.

Lemma AbsIR_bnd : forall a b e : IR, AbsIR (a[-]b) [<=] e -> b [<=] a[+]e.
intros.
apply shift_leEq_plus'.
apply leEq_transitive with (AbsIR (a[-]b)); auto.
eapply leEq_wdr; [ apply leEq_AbsIR | apply AbsIR_minus ].
Qed.

End Absolute.

Hint Resolve AbsIRz_isz: algebra.

Section SeqMax.

(** *** Bound of sequence *)

Variable seq : nat -> IR.

Fixpoint SeqBound0 (n : nat) : IR :=
    match n with
     | O => Zero
     | S m => Max (AbsIR (seq m)) (SeqBound0 m)
    end.

Lemma SeqBound0_greater : forall (m n : nat), 
m < n -> AbsIR (seq m) [<=] SeqBound0 n.
intros.
elim H.
simpl. apply lft_leEq_MAX.
intros. simpl.
apply leEq_transitive with (SeqBound0 m0); auto.
apply rht_leEq_MAX.
Qed.
 
End SeqMax.

Section Part_Function_Max.

(** *** Functional Operators

The existence of these operators allows us to lift them to functions.  We will define the maximum, minimum and absolute value of two partial functions.

%\begin{convention}%
Let [F,G:PartIR] and denote by [P] and [Q] their respective domains.
%\end{convention}%
*)

Variables F G : PartIR.

(* begin hide *)
Let P := Dom F.
Let Q := Dom G.
(* end hide *)

Lemma part_function_Max_strext : forall x y (Hx : Conj P Q x) (Hy : Conj P Q y),
 Max (F x (Prj1 Hx)) (G x (Prj2 Hx)) [#] Max (F y (Prj1 Hy)) (G y (Prj2 Hy)) -> 
 x [#] y.
intros. rename X into H.
elim (cs_bin_op_strext _ _ _ _ _ _ H).
exact (pfstrx _ F _ _ _ _).
exact (pfstrx _ G _ _ _ _).
Qed.

Definition FMax := Build_PartFunct IR _ (conj_wd (dom_wd _ _) (dom_wd _ _))
 (fun x Hx => Max (F x (Prj1 Hx)) (G x (Prj2 Hx))) part_function_Max_strext.

End Part_Function_Max.

Section Part_Function_Abs.

Variables F G : PartIR.

(* begin hide *)
Let P := Dom F.
Let Q := Dom G.
(* end hide *)

Definition FMin := {--} (FMax {--}F {--}G).
Definition FAbs := FMax F {--}F.

Lemma FMin_char : forall x Hx Hx' Hx'', FMin x Hx [=] Min (F x Hx') (G x Hx'').
intros.
Opaque Max.
simpl in |- *; unfold MIN; algebra.
Qed.

Transparent Max.

Lemma FAbs_char : forall x Hx Hx', FAbs x Hx [=] AbsIR (F x Hx').
intros.
simpl in |- *; unfold ABSIR in |- *; apply MAX_wd; algebra.
Qed.

End Part_Function_Abs.

Hint Resolve FAbs_char: algebra.

Lemma FAbs_char' : forall F x Hx, AbsIR (FAbs F x Hx) [=] AbsIR (F x (ProjIR1 Hx)).
intros.
eapply eq_transitive_unfolded.
 apply AbsIR_eq_x.
 2: apply FAbs_char.
eapply leEq_wdr.
 2: apply eq_symmetric_unfolded; apply FAbs_char with (Hx' := ProjIR1 Hx).
apply AbsIR_nonneg.
Qed.

Lemma FAbs_nonneg : forall F x Hx, Zero [<=] FAbs F x Hx.
intros.
eapply leEq_wdr.
 2: apply eq_symmetric_unfolded; apply FAbs_char with (Hx' := ProjIR1 Hx).
apply AbsIR_nonneg.
Qed.

Hint Resolve FAbs_char': algebra.

Section Inclusion.

Variables F G : PartIR.

(* begin hide *)
Let P := Dom F.
Let Q := Dom G.
(* end hide *)

(**
%\begin{convention}% Let [R:IR->CProp].
%\end{convention}%
*)

Variable R : IR -> CProp.

Lemma included_FMax : included R P -> included R Q -> included R (Dom (FMax F G)).
intros; simpl in |- *; apply included_conj; assumption.
Qed.

Lemma included_FMax' : included R (Dom (FMax F G)) -> included R P.
intro H; simpl in H; eapply included_conj_lft; apply H.
Qed.

Lemma included_FMax'' : included R (Dom (FMax F G)) -> included R Q.
intro H; simpl in H; eapply included_conj_rht; apply H.
Qed.

Lemma included_FMin : included R P -> included R Q -> included R (Dom (FMin F G)).
intros; simpl in |- *; apply included_conj; assumption.
Qed.

Lemma included_FMin' : included R (Dom (FMin F G)) -> included R P.
intro H; simpl in H; eapply included_conj_lft; apply H.
Qed.

Lemma included_FMin'' : included R (Dom (FMin F G)) -> included R Q.
intro H; simpl in H; eapply included_conj_rht; apply H.
Qed.

Lemma included_FAbs : included R P -> included R (Dom (FAbs F)).
intros; simpl in |- *; apply included_conj; assumption.
Qed.

Lemma included_FAbs' : included R (Dom (FAbs F)) -> included R P.
intro H; simpl in H; eapply included_conj_lft; apply H.
Qed.

End Inclusion.

Hint Resolve included_FMax included_FMin included_FAbs : included.

Hint Immediate included_FMax' included_FMin' included_FAbs'
  included_FMax'' included_FMin'' : included.
