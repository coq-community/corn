(* $Id$ *)

Require Export NRootIR.
Require Export FunctSums.

(** printing Norm_Funct %\ensuremath{\|\cdot\|}% *)

Section Definitions_and_Basic_Results.

(** *Continuity

Constructively, continuity is the most fundamental property of any function---so strongly that no example is known of a constructive function that is not continuous.  However, the classical definition of continuity is not good for our purposes, as it is not true, for example, that a function which is continuous in a compact interval is uniformly continuous in that same interval (for a discussion of this see Bishop 1967).  Thus, our notion of continuity will be the uniform one#. #%\footnote{%Similar remarks apply to convergence of sequences of functions, which we will define ahead, and elsewhere; we will refrain from discussing this issue at those places.%}.%

%\begin{convention}% Throughout this section, [a] and [b] will be real numbers, [I] will denote the compact interval $[a,b]$#[a,b]# and [F,G,H] will denote arbitrary partial functions with domains respectively [P,Q] and [R].
%\end{convention}%

** Definitions and Basic Results

Here we define continuity and prove some basic properties of continuous functions.
*)

Variables a b : IR.
Hypothesis Hab : a[<=]b.
(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Variable F : PartIR.
(* begin hide *)
Let P := Dom F.
(* end hide *)

Definition Continuous_I :=
  included I P
  and (forall e : IR,
       Zero[<]e ->
       {d : IR | Zero[<]d |
       forall x y : IR,
       I x ->
       I y ->
       forall Hx Hy, AbsIR (x[-]y)[<=]d -> AbsIR (F x Hx[-]F y Hy)[<=]e}).

(**
For convenience, we distinguish the two properties of continuous functions.
*)

Lemma contin_imp_inc : Continuous_I -> included (Compact Hab) P.
intro H; elim H; intros; assumption.
Qed.

Lemma contin_prop :
 Continuous_I ->
 forall e : IR,
 Zero[<]e ->
 {d : IR | Zero[<]d |
 forall x y : IR,
 I x ->
 I y -> forall Hx Hy, AbsIR (x[-]y)[<=]d -> AbsIR (F x Hx[-]F y Hy)[<=]e}.
intro H; elim H; do 2 intro; assumption.
Qed.

(**
Assume [F] to be continuous in [I].  Then it has a least upper bound and a greater lower bound on [I].
*)

Hypothesis contF : Continuous_I.

(* begin hide *)
Let Hinc' := contin_imp_inc contF.
(* end hide *)

Lemma Continuous_I_imp_tb_image : totally_bounded (fun_image F I).
assert (H := compact_is_totally_bounded a b Hab).
elim contF; intros H0 H1.
split.
elim H; clear H; intros H2 H3.
elim H2; clear H2; intros x H.
exists (Part F x (H0 _ H)).
exists x; split.
auto.
split.
apply H0; auto.
Algebra.
intros e H2.
elim (H1 _ H2).
intros d H3 H4.
clear H1.
elim H; clear H.
intros non_empty H.
elim H with d; clear H.
intros l Hl' Hl.
2: assumption.
exists (map2 F l (fun (x : IR) (Hx : member x l) => H0 x (Hl' x Hx))).
intros x H.
clear Hl; induction  l as [| a0 l Hrecl].
elimtype CFalse; assumption.
simpl in H; elim H; clear H; intro H1.
cut (forall x : IR, member x l -> compact a b Hab x).
intro H.
apply Hrecl with H.
eapply map2_wd.
apply H1.
intros x0 H.
apply Hl'; left; assumption.
exists a0.
split.
apply Hl'; right; Algebra.
split.
apply H0; apply Hl'; right; Algebra.
intro; eapply eq_transitive_unfolded.
2: apply eq_symmetric_unfolded; apply H1.
Algebra.
intros x H; simpl in |- *.
elim H; intros x0 H1.
elim H1; clear H1; intros Hy' H1.
elim H1; intros Hy'' Hy.
elim (Hl x0 Hy'); intros x1 Hx1 H5.
exists (F x1 (H0 x1 (Hl' x1 Hx1))).
apply map2_pres_member; assumption.
AStepr (F x0 Hy''[-]F x1 (H0 x1 (Hl' x1 Hx1))).
apply AbsIR_imp_AbsSmall.
apply H4.
assumption.
apply Hl'; assumption.
apply AbsSmall_imp_AbsIR; assumption.
Qed.

Lemma Continuous_I_imp_lub : {x : IR | fun_lub_IR F I x}.
unfold fun_lub_IR in |- *.
apply totally_bounded_has_lub.
apply Continuous_I_imp_tb_image.
Qed.

Lemma Continuous_I_imp_glb : {x : IR | fun_glb_IR F I x}.
unfold fun_glb_IR in |- *.
apply totally_bounded_has_glb.
apply Continuous_I_imp_tb_image.
Qed.

(**
We now make this glb and lub into operators.
*)

Definition lub_funct := ProjT1 Continuous_I_imp_lub.
Definition glb_funct := ProjT1 Continuous_I_imp_glb.

(**
These operators have the expected properties.
*)

Lemma lub_is_lub : fun_lub_IR F I lub_funct.
exact (ProjT2 Continuous_I_imp_lub).
Qed.

Lemma glb_is_glb : fun_glb_IR F I glb_funct.
exact (ProjT2 Continuous_I_imp_glb).
Qed.

Lemma glb_prop : forall x : IR, I x -> forall Hx, glb_funct[<=]F x Hx.
intros.
elim glb_is_glb.
intros.
apply a0.
exists x.
split; Algebra.
Qed.

Lemma lub_prop : forall x : IR, I x -> forall Hx, F x Hx[<=]lub_funct.
intros.
elim lub_is_lub.
intros.
apply a0.
exists x.
split; Algebra.
Qed.

(**
The norm of a function is defined as being the supremum of its absolute value; that is equivalent to the following definition (which is often more convenient to use).
*)

Definition Norm_Funct := Max lub_funct [--]glb_funct.

(**
The norm effectively bounds the absolute value of a function.
*)

Lemma norm_bnd_AbsIR :
 forall x : IR, I x -> forall Hx : P x, AbsIR (F x Hx)[<=]Norm_Funct.
intros.
generalize lub_is_lub.
generalize glb_is_glb.
intros; simpl in |- *; unfold ABSIR in |- *.
apply Max_leEq.
apply leEq_transitive with lub_funct.
apply lub_prop; auto.
unfold Norm_Funct in |- *; apply lft_leEq_Max.

apply leEq_transitive with ([--]glb_funct).
apply inv_resp_leEq.
apply glb_prop; auto.
unfold Norm_Funct in |- *; apply rht_leEq_Max.
Qed.

(**
The following is another way of characterizing the norm:
*)

Lemma Continuous_I_imp_abs_lub :
 {z : IR | forall x : IR, I x -> forall Hx : P x, AbsIR (F x Hx)[<=]z}.
exists Norm_Funct.
exact norm_bnd_AbsIR.
Qed.

(**
We now prove some basic properties of the norm---namely that it is positive, and that it provides a least upper bound for the absolute value of its argument.
*)

Lemma positive_norm : Zero[<=]Norm_Funct.
apply leEq_transitive with (AbsIR (FRestr Hinc' a (compact_inc_lft _ _ _))).
apply AbsIR_nonneg.
simpl in |- *; apply norm_bnd_AbsIR; unfold I in |- *; apply compact_inc_lft.
Qed.

Lemma norm_fun_lub :
 forall e : IR,
 Zero[<]e ->
 {x : IR | I x and (forall Hx' : P x, Norm_Funct[-]e[<]AbsIR (F x Hx'))}.
intros e H.
cut {x : IR | I x and (forall Hx' : P x, Norm_Funct[<]AbsIR (F x Hx')[+]e)}.
intro H0.
elim H0; intros y Hy.
elim Hy; clear H0 Hy; intros Hy Hy'.
exists y; split.
auto.
intro; apply shift_minus_less; apply Hy'.
generalize lub_is_lub.
generalize glb_is_glb.
intros H0 H1.
cut {x : IR | I x and (forall Hx' : P x, F x Hx'[<]glb_funct[+]e [/]TwoNZ)}.
cut {x : IR | I x and (forall Hx' : P x, lub_funct[-]e [/]TwoNZ[<]F x Hx')}.
intros H2 H3.
elim H2; intros x Hx.
elim Hx; clear H2 Hx; intros Hx Hx0.
elim H3; intros x' Hx'.
elim Hx'; clear H3 Hx'; intros Hx' Hx'0.
elim
 (cotrans_less_unfolded _ _ _ (pos_div_two _ _ H) ([--]glb_funct[-]lub_funct));
 intro H2.
exists x'; split.
auto.
unfold Norm_Funct in |- *.
intro; eapply less_wdl.
2: apply eq_symmetric_unfolded; apply leEq_imp_Max_is_rht.
apply shift_less_plus.
RStepl ([--](glb_funct[+]e)).
eapply less_leEq_trans.
2: apply inv_leEq_AbsIR.
apply inv_resp_less.
eapply less_transitive_unfolded.
apply Hx'0 with (Hx' := Hx'1).
apply plus_resp_less_lft.
apply pos_div_two'; assumption.
AStepl (Zero[+]lub_funct); apply less_leEq; apply shift_plus_less.
assumption.
exists x; split.
auto.
unfold Norm_Funct in |- *.
intro; apply less_leEq_trans with (lub_funct[+]e [/]TwoNZ).
apply Max_less.
apply shift_less_plus'; AStepl ZeroR.
apply pos_div_two; assumption.
apply shift_less_plus'; assumption.
apply shift_leEq_plus.
RStepl (lub_funct[-]e [/]TwoNZ).
eapply leEq_transitive.
apply less_leEq; apply Hx0 with (Hx' := Hx'1).
apply leEq_AbsIR.
elim H1; clear H1; intros H2 H3.
elim (H3 _ (pos_div_two _ _ H)).
intros x Hx; elim Hx; clear Hx; intros y Hx'; elim Hx'; clear Hx';
 intros Hx' Hx''; elim Hx''; clear Hx''; intros Hx'' Hx'''.
exists y; split.
auto.
intro; apply shift_minus_less; apply shift_less_plus'.
eapply less_wdl; [ apply q | Algebra ].
elim H0; clear H0; intros H2 H3.
elim (H3 _ (pos_div_two _ _ H)).
intros x Hx; elim Hx; clear Hx; intros y Hx'; elim Hx'; clear Hx';
 intros Hx' Hx''; elim Hx''; clear Hx''; intros Hx'' Hx'''.
exists y; split.
auto.
intro; apply shift_less_plus'.
eapply less_wdl; [ apply q | Algebra ].
Qed.

Lemma leEq_Norm_Funct :
 forall e : IR,
 (forall x : IR, I x -> forall Hx : P x, AbsIR (F x Hx)[<=]e) ->
 Norm_Funct[<=]e.
intros e H.
AStepr (Zero[+]e); apply shift_leEq_plus.
red in |- *; apply approach_zero_weak.
intros d Hd.
apply shift_minus_leEq.
elim (norm_fun_lub d Hd); intros x Hx.
elim Hx; clear Hx; intros Hx Hx'.
apply plus_cancel_leEq_rht with ([--](AbsIR (F x (Hinc' x Hx)))).
AStepl (Norm_Funct[-]AbsIR (F x (Hinc' x Hx))).
apply less_leEq; apply less_leEq_trans with d.
apply shift_minus_less; apply shift_less_plus'; apply Hx'.
RStepr (d[+](e[-]AbsIR (F x (Hinc' x Hx)))).
AStepl (d[+]Zero); apply plus_resp_leEq_lft.
apply shift_leEq_minus; AStepl (AbsIR (F x (Hinc' x Hx))); apply H;
 assumption.
Qed.

Lemma less_Norm_Funct :
 forall e : IR,
 (forall x : IR, I x -> forall Hx : P x, AbsIR (F x Hx)[<]e) ->
 Norm_Funct[<=]e.
intros x H.
apply leEq_Norm_Funct.
intros; apply less_leEq; apply H; assumption.
Qed.

End Definitions_and_Basic_Results.

Implicit Arguments Continuous_I [a b].
Implicit Arguments Norm_Funct [a b Hab F].

Section Local_Results.

(** **Algebraic Properties

We now state and prove some results about continuous functions.  Assume that [I] is included in the domain of both [F] and [G].
*)

Variables a b : IR.
Hypothesis Hab : a[<=]b.
(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Variables F G : PartIR.

(* begin hide *)
Let P := Dom F.
Let Q := Dom G.
(* end hide *)

Hypothesis incF : included (Compact Hab) P.
Hypothesis incG : included (Compact Hab) Q.

(**
The first result does not require the function to be continuous; however, its preconditions are easily verified by continuous functions, which justifies its inclusion in this section.
*)

Lemma cont_no_sign_change :
 forall e : IR,
 Zero[<]e ->
 forall x y : IR,
 I x ->
 I y ->
 forall (Hx : P x) (Hy : P y),
 AbsIR (F x Hx[-]F y Hy)[<=]e ->
 e[<]AbsIR (F x Hx) ->
 (Zero[<]F x Hx -> Zero[<]F y Hy) and (F x Hx[<]Zero -> F y Hy[<]Zero).
intros e H x y H0 H1 Hx Hy H2 H3.
set (fx := F x Hx) in *.
set (fy := F y Hy) in *.
split; intro H4.
cut (e[<]fx).
intro H5.
AStepl (e[-]e).
apply shift_minus_less; apply shift_less_plus'.
apply less_leEq_trans with (fx[-]fy).
apply minus_resp_less; assumption.
eapply leEq_transitive; [ apply leEq_AbsIR | assumption ].
elim (less_AbsIR _ _ H H3); intro H6.
assumption.
elimtype False.
cut (Zero[<][--]e).
intro; cut (e[<]Zero).
exact (less_antisymmetric_unfolded _ _ _ H).
AStepl ([--][--]e); AStepr ([--]ZeroR); apply inv_resp_less; assumption.
apply less_transitive_unfolded with fx; assumption.
AStepr (e[-]e).
apply shift_less_minus.
apply less_leEq_trans with (fy[-]fx).
2: eapply leEq_transitive.
3: apply H2.
2: eapply leEq_wdr; [ apply leEq_AbsIR | apply AbsIR_minus ].
unfold cg_minus in |- *; apply plus_resp_less_lft.
elim (less_AbsIR _ _ H H3); intro H6.
apply less_transitive_unfolded with ZeroR.
apply less_transitive_unfolded with fx; assumption.
AStepl ([--]ZeroR); apply inv_resp_less; assumption.
AStepl ([--][--]e); apply inv_resp_less; assumption.
Qed.

Lemma cont_no_sign_change_pos :
 forall e : IR,
 Zero[<]e ->
 forall x y : IR,
 I x ->
 I y ->
 forall (Hx : P x) (Hy : P y),
 AbsIR (F x Hx[-]F y Hy)[<=]e ->
 e[<]AbsIR (F x Hx) -> e[<]F x Hx -> Zero[<]F y Hy.
intros e H x y H0 H1 Hx Hy H2 H3 H4.
elim (cont_no_sign_change e H x y H0 H1 Hx Hy H2 H3); intros H5 H6.
apply H5.
apply less_transitive_unfolded with e; auto.
Qed.

Lemma cont_no_sign_change_neg :
 forall e : IR,
 Zero[<]e ->
 forall x y : IR,
 I x ->
 I y ->
 forall (Hx : P x) (Hy : P y),
 AbsIR (F x Hx[-]F y Hy)[<=]e ->
 e[<]AbsIR (F x Hx) -> F x Hx[<][--]e -> F y Hy[<]Zero.
intros e H x y H0 H1 Hx Hy H2 H3 H4.
elim (cont_no_sign_change e H x y H0 H1 Hx Hy H2 H3); intros H5 H6.
apply H6.
apply less_transitive_unfolded with ([--]e).
assumption.
AStepr ([--]ZeroR); apply inv_resp_less; assumption.
Qed.

(**
Being continuous is an extensional property.
*)

Lemma Continuous_I_wd : Feq I F G -> Continuous_I Hab F -> Continuous_I Hab G.
intros H H0.
elim H0; clear H0; intros Hinc H0.
elim H; clear H; intros incF' H'.
elim H'; clear H'; intros incG' H.
split.
apply incG'.
intros e He; elim (H0 e He); clear H0; intros d H0 H1.
exists d.
assumption.
intros x y H2 H3 Hx Hy H4.
apply leEq_wdl with (AbsIR (F x (incF' x H2)[-]F y (incF' y H3))).
apply H1; assumption.
simpl in H.
apply AbsIR_wd.
apply cg_minus_wd; apply H; assumption.
Qed.

(**
A continuous function remains continuous if you restrict its domain.
*)

Lemma included_imp_contin :
 forall c d Hcd,
 included (compact c d Hcd) (Compact Hab) ->
 Continuous_I Hab F -> Continuous_I Hcd F.
intros c d Hcd H H0.
elim H0; clear H0; intros incF' contF.
split.
apply included_trans with (Compact Hab); [ apply H | apply incF' ].
intros e He; elim (contF e He); intros e' H0 H1.
exists e'.
assumption.
intros; apply H1.
apply H; assumption.
apply H; assumption.
assumption.
Qed.

(**
Constant functions and identity are continuous.
*)

Lemma Continuous_I_const : forall c : IR, Continuous_I Hab [-C-]c.
intro.
split.
Included.
intros; exists OneR.
apply pos_one.
intros.
apply leEq_wdl with (AbsIR Zero).
AStepl ZeroR; apply less_leEq; assumption.
Algebra.
Qed.

Lemma Continuous_I_id : Continuous_I Hab FId.
split.
Included.
intros; exists e.
assumption.
intros; assumption.
Qed.

(**
Assume [F] and [G] are continuous in [I].  Then functions derived from these through algebraic operations are also continuous, provided (in the case of reciprocal and division) some extra conditions are met.
*)

Hypothesis contF : Continuous_I Hab F.
Hypothesis contG : Continuous_I Hab G.

Lemma Continuous_I_plus : Continuous_I Hab (F{+}G).
clear incF incG.
elim contF; intros incF' contF'.
elim contG; intros incG' contG'.
split.
Included.
intros.
elim (contF' (e [/]TwoNZ)).
elim (contG' (e [/]TwoNZ)).
clear contF contG contF' contG'.
2: apply pos_div_two; assumption.
2: apply pos_div_two; assumption.
intros df H0 H1 dg H2 H3.
exists (Min df dg).
apply less_Min; assumption.
intros.
simpl in |- *.
apply
 leEq_wdl
  with
    (AbsIR
       (F x (ProjIR1 Hx)[-]F y (ProjIR1 Hy)[+]
        (G x (ProjIR2 Hx)[-]G y (ProjIR2 Hy)))).
RStepr (e [/]TwoNZ[+]e [/]TwoNZ).
eapply leEq_transitive.
apply triangle_IR.
apply plus_resp_leEq_both.
simpl in |- *; apply H3; try assumption.
apply leEq_transitive with (Min df dg); [ assumption | apply Min_leEq_rht ].
simpl in |- *; apply H1; try assumption.
apply leEq_transitive with (Min df dg); [ assumption | apply Min_leEq_lft ].
apply AbsIR_wd; rational.
Qed.

Lemma Continuous_I_inv : Continuous_I Hab {--}F.
clear incF.
elim contF; intros incF' contF'.
split.
Included.
intros e H.
elim (contF' e H).
intros d H0 H1.
exists d.
assumption.
intros; simpl in |- *.
apply leEq_wdl with (AbsIR (F x Hx[-]F y Hy)).
apply H1; assumption.
eapply eq_transitive_unfolded.
apply AbsIR_inv.
apply AbsIR_wd; rational.
Qed.

Lemma Continuous_I_mult : Continuous_I Hab (F{*}G).
clear incF incG.
elim contF; intros incF' contF'.
elim contG; intros incG' contG'.
split; [ Included | intros e H ].
cut {xf : IR | forall (x : IR) (Hx : I x) (Hx' : P x), AbsIR (F x Hx')[<=]xf}.
cut {xg : IR | forall (x : IR) (Hx : I x) (Hx' : Q x), AbsIR (G x Hx')[<=]xg}.
2: unfold I, Q in |- *; apply Continuous_I_imp_abs_lub; assumption.
2: unfold I, P in |- *; apply Continuous_I_imp_abs_lub; assumption.
intros H0 H1.
elim H0; clear H0; intros x H2.
elim H1; clear H1; intros x0 H0.
elim (contF' (e [/]TwoNZ[/] Max x One[//]max_one_ap_zero _)); clear contF.
elim (contG' (e [/]TwoNZ[/] Max x0 One[//]max_one_ap_zero _)); clear contG.
intros dg H1 H3 df H4 H5.
2: apply div_resp_pos.
2: apply pos_max_one.
2: apply pos_div_two; assumption.
2: apply div_resp_pos.
2: apply pos_max_one.
2: apply pos_div_two; assumption.
exists (Min df dg).
apply less_Min; assumption.
intros; simpl in |- *.
RStepr (e [/]TwoNZ[+]e [/]TwoNZ).
apply
 leEq_wdl
  with
    (AbsIR
       (F x1 (ProjIR1 Hx)[*](G x1 (ProjIR2 Hx)[-]G y (ProjIR2 Hy))[+]
        (F x1 (ProjIR1 Hx)[-]F y (ProjIR1 Hy))[*]G y (ProjIR2 Hy))).
eapply leEq_transitive.
apply triangle_IR.
apply plus_resp_leEq_both.
eapply leEq_wdl.
2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
apply
 leEq_transitive with (x0[*]AbsIR (G x1 (ProjIR2 Hx)[-]G y (ProjIR2 Hy))).
apply mult_resp_leEq_rht.
apply H0; assumption.
apply AbsIR_nonneg.
apply
 leEq_transitive
  with (Max x0 One[*]AbsIR (G x1 (ProjIR2 Hx)[-]G y (ProjIR2 Hy))).
apply mult_resp_leEq_rht; [ apply lft_leEq_Max | apply AbsIR_nonneg ].
AStepl (AbsIR (G x1 (ProjIR2 Hx)[-]G y (ProjIR2 Hy))[*]Max x0 One).
apply shift_mult_leEq with (max_one_ap_zero x0);
 [ apply pos_max_one | simpl in |- *; apply H3 ]; try assumption.
apply leEq_transitive with (Min df dg); [ assumption | apply Min_leEq_rht ].
eapply leEq_wdl.
2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
apply leEq_transitive with (AbsIR (F x1 (ProjIR1 Hx)[-]F y (ProjIR1 Hy))[*]x).
apply mult_resp_leEq_lft; [ apply H2 | apply AbsIR_nonneg ]; assumption.
apply
 leEq_transitive
  with (AbsIR (F x1 (ProjIR1 Hx)[-]F y (ProjIR1 Hy))[*]Max x One).
apply mult_resp_leEq_lft;
 [ apply lft_leEq_Max with (y := OneR) | apply AbsIR_nonneg ].
apply shift_mult_leEq with (max_one_ap_zero x);
 [ apply pos_max_one | simpl in |- *; apply H5 ]; try assumption.
apply leEq_transitive with (Min df dg); [ assumption | apply Min_leEq_lft ].
apply AbsIR_wd; rational.
Qed.

Lemma Continuous_I_max : Continuous_I Hab (FMax F G).
clear incF incG.
elim contF; intros incF contF'.
elim contG; intros incG contG'.
split.
 Included.
intros e He.
elim (contF' (e [/]TwoNZ) (pos_div_two _ _ He)); intros dF dFpos HdF.
elim (contG' (e [/]TwoNZ) (pos_div_two _ _ He)); intros dG dGpos HdG.
clear contF contG contF' contG'.
exists (Min dF dG).
 apply less_Min; auto.
intros x y Hx' Hy' Hx Hy Hxy.
assert (AbsIR (x[-]y)[<=]dF).
 eapply leEq_transitive; [ apply Hxy | apply Min_leEq_lft ].
assert (AbsIR (x[-]y)[<=]dG).
 eapply leEq_transitive; [ apply Hxy | apply Min_leEq_rht ].
assert (HF := HdF x y Hx' Hy' (ProjIR1 Hx) (ProjIR1 Hy) H).
assert (HG := HdG x y Hx' Hy' (ProjIR2 Hx) (ProjIR2 Hy) H0).
Opaque AbsIR Max.
simpl in |- *.
Transparent AbsIR Max.
set (Fx := F x (ProjIR1 Hx)) in *.
set (Fy := F y (ProjIR1 Hy)) in *.
set (Gx := G x (ProjIR2 Hx)) in *.
set (Gy := G y (ProjIR2 Hy)) in *.
elim (AbsIR_imp_AbsSmall _ _ HF); intros HF1 HF2.
elim (AbsIR_imp_AbsSmall _ _ HG); intros HG1 HG2.
apply leEq_wdl with (AbsIR (Max Fx Gx[-]Max Fx Gy[+](Max Fx Gy[-]Max Fy Gy))).
 2: apply AbsIR_wd; rational.
RStepr (e [/]TwoNZ[+]e [/]TwoNZ).
eapply leEq_transitive.
 apply triangle_IR.
apply plus_resp_leEq_both; apply AbsSmall_imp_AbsIR; split.
   apply shift_zero_leEq_minus'.
   RStepr (e [/]TwoNZ[+]Max Fx Gx[-]Max Fx Gy).
   apply shift_zero_leEq_minus.
   apply Max_leEq.
    apply leEq_transitive with (e [/]TwoNZ[+]Fx).
     apply shift_leEq_plus; AStepl ZeroR; apply less_leEq; apply pos_div_two;
      auto.
    apply plus_resp_leEq_lft; apply lft_leEq_Max.
   apply leEq_transitive with (e [/]TwoNZ[+]Gx).
    2: apply plus_resp_leEq_lft; apply rht_leEq_Max.
   apply shift_leEq_plus.
   apply inv_cancel_leEq; RStepr (Gx[-]Gy); auto.
  apply shift_minus_leEq; apply Max_leEq.
   apply leEq_transitive with (e [/]TwoNZ[+]Fx).
    apply shift_leEq_plus; AStepl ZeroR; apply less_leEq; apply pos_div_two;
     auto.
   apply plus_resp_leEq_lft; apply lft_leEq_Max.
  apply leEq_transitive with (e [/]TwoNZ[+]Gy).
   2: apply plus_resp_leEq_lft; apply rht_leEq_Max.
  apply shift_leEq_plus; auto.
 apply shift_zero_leEq_minus'.
 RStepr (e [/]TwoNZ[+]Max Fx Gy[-]Max Fy Gy).
 apply shift_zero_leEq_minus.
 apply Max_leEq.
  apply leEq_transitive with (e [/]TwoNZ[+]Fx).
   apply shift_leEq_plus.
   apply inv_cancel_leEq; RStepr (Fx[-]Fy); auto.
  apply plus_resp_leEq_lft; apply lft_leEq_Max.
 apply leEq_transitive with (e [/]TwoNZ[+]Gy).
  2: apply plus_resp_leEq_lft; apply rht_leEq_Max.
 apply shift_leEq_plus; AStepl ZeroR; apply less_leEq; apply pos_div_two;
  auto.
apply shift_minus_leEq; apply Max_leEq.
 apply leEq_transitive with (e [/]TwoNZ[+]Fy).
  apply shift_leEq_plus; auto.
 apply plus_resp_leEq_lft; apply lft_leEq_Max.
apply leEq_transitive with (e [/]TwoNZ[+]Gy).
 apply shift_leEq_plus; AStepl ZeroR; apply less_leEq; apply pos_div_two;
  auto.
apply plus_resp_leEq_lft; apply rht_leEq_Max.
Qed.

(* begin show *)
Hypothesis Hg' : bnd_away_zero I G.
Hypothesis Hg'' : forall (x : IR) (Hx : I x) (Hx' : Q x), G x Hx'[#]Zero.
(* end show *)

Lemma Continuous_I_recip : Continuous_I Hab {1/}G.
clear incF incG.
elim contG; intros incG' contG'.
split.
Included; assumption.
elim Hg'; intros Haux Hg2.
elim Hg2; clear Haux Hg2; intros c H H0.
intros.
elim contG' with (c[*]c[*]e); clear contG contG'.
intros d H2 H3.
exists d.
assumption.
intros x y H4 H5 Hx Hy H6.
simpl in |- *.
set (Hxx := incG' x H4) in *.
set (Hyy := incG' y H5) in *.
apply
 leEq_wdl
  with
    (AbsIR
       (G y Hyy[-]G x Hxx[/] _[//]
        mult_resp_ap_zero _ _ _ (Hg'' x H4 Hxx) (Hg'' y H5 Hyy))).
apply
 leEq_wdl
  with
    (AbsIR (G y Hyy[-]G x Hxx)[/] _[//]
     AbsIR_resp_ap_zero _
       (mult_resp_ap_zero _ _ _ (Hg'' x H4 Hxx) (Hg'' y H5 Hyy))).
apply
 leEq_transitive
  with
    (AbsIR (G y Hyy[-]G x Hxx)[/] _[//]
     mult_resp_ap_zero _ _ _ (pos_ap_zero _ _ H) (pos_ap_zero _ _ H)).
RStepl
 (AbsIR (G y Hyy[-]G x Hxx)[*]
  (One[/] _[//]
   AbsIR_resp_ap_zero _
     (mult_resp_ap_zero _ _ _ (Hg'' x H4 Hxx) (Hg'' y H5 Hyy)))).
RStepr
 (AbsIR (G y Hyy[-]G x Hxx)[*]
  (One[/] _[//]
   mult_resp_ap_zero _ _ _ (pos_ap_zero _ _ H) (pos_ap_zero _ _ H))).
apply mult_resp_leEq_lft.
apply recip_resp_leEq.
AStepl (ZeroR[*]Zero); apply mult_resp_less_both; try apply leEq_reflexive;
 assumption.
eapply leEq_wdr.
2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
apply mult_resp_leEq_both; try (apply less_leEq; assumption).
eapply leEq_wdr; [ apply (H0 x H4 Hxx) | Algebra ].
eapply leEq_wdr; [ apply (H0 y H5 Hyy) | Algebra ].
apply AbsIR_nonneg.
apply shift_div_leEq'.
AStepl (ZeroR[*]Zero); apply mult_resp_less_both; try apply leEq_reflexive;
 assumption.
eapply leEq_wdl.
2: apply AbsIR_minus.
apply H3; assumption.
apply eq_symmetric_unfolded; apply AbsIR_division.
apply AbsIR_wd.
rational.
AStepl (ZeroR[*]Zero); apply mult_resp_less_both; try apply leEq_reflexive.
AStepl (ZeroR[*]Zero); apply mult_resp_less_both; try apply leEq_reflexive;
 assumption.
assumption.
Qed.

End Local_Results.

Hint Resolve contin_imp_inc: included.

Section Corolaries.

Variables a b : IR.
Hypothesis Hab : a[<=]b.
(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Variables F G : PartIR.

(* begin hide *)
Let P := Dom F.
Let Q := Dom G.
(* end hide *)

Hypothesis contF : Continuous_I Hab F.
Hypothesis contG : Continuous_I Hab G.

(**
The corresponding properties for subtraction, division and multiplication by a scalar are easily proved as corollaries; exponentiation is proved by induction, appealing to the results on product and constant functions.
*)

Lemma Continuous_I_minus : Continuous_I Hab (F{-}G).
apply Continuous_I_wd with (F{+}{--}G).
FEQ.
apply Continuous_I_plus.
apply contF.
apply Continuous_I_inv; apply contG.
Qed.

Lemma Continuous_I_scal : forall c : IR, Continuous_I Hab (c{**}F).
intros.
unfold Fscalmult in |- *.
apply Continuous_I_mult.
apply Continuous_I_const.
apply contF.
Qed.

Lemma Continuous_I_nth : forall n : nat, Continuous_I Hab (F{^}n).
simple induction n.
apply Continuous_I_wd with ([-C-]OneR).
apply FNth_zero'; apply contin_imp_inc; auto.
apply Continuous_I_const.
clear n; intros.
apply Continuous_I_wd with (F{*}F{^}n).
apply FNth_mult'; apply contin_imp_inc; auto.
apply Continuous_I_mult; assumption.
Qed.

Lemma Continuous_I_min : Continuous_I Hab (FMin F G).
unfold FMin in |- *.
apply Continuous_I_inv; apply Continuous_I_max; apply Continuous_I_inv; auto.
Qed.

Lemma Continuous_I_abs : Continuous_I Hab (FAbs F).
unfold FAbs in |- *.
apply Continuous_I_max; try apply Continuous_I_inv; auto.
Qed.

Hypothesis Hg' : bnd_away_zero I G.
Hypothesis Hg'' : forall (x : IR) (Hx : I x) (Hx' : Q x), G x Hx'[#]Zero.

Lemma Continuous_I_div : Continuous_I Hab (F{/}G).
apply Continuous_I_wd with (F{*}{1/}G).
FEQ.
apply Continuous_I_mult.
assumption.
apply Continuous_I_recip; assumption.
Qed.

End Corolaries.

(*
Section Absolute_Value.

_** **Other Useful Results
*_

Variables a,b:IR.
Hypothesis Hab:(a [<=] b).
_* begin hide *_
Local I:=(Compact Hab).
_* end hide *_

Variable F : PartIR.
Hypothesis contF : (Continuous_I Hab F).

_* begin hide *_
Local P:=(Dom F).
_* end hide *_

Section Lemmas.

Hypothesis incF : (included (Compact Hab) P).

_**
Next we prove that the absolute value of a function is continuous if the original function also is; we start by unfolding a previous lemma in more pratical forms:
*_

End Lemmas.

_**
From these two lemmas it easy to prove our result.
*_

Lemma Continuous_I_abs : (Continuous_I Hab (FAbs F)).
Elim contF; Intros incF contF'.
Split; [Included | Intros e He].
Cut e[/]FourNZ [<] e[/]ThreeNZ.
Intro.
Cut (Zero [<] e[/]FourNZ); [Intro | Apply pos_div_four; Assumption].
Elim (contF' ? H0).
Intros d Hd H2.
Exists d.
Assumption.
Intros.
Elim Hx; Clear Hx; Intros Hx Hx'.
Elim Hy; Clear Hy; Intros Hy Hy'.
Cut (e[/]FourNZ [<] (AbsIR (F x Hx)))+((AbsIR (F x Hx)) [<] e[/]ThreeNZ).
2: Apply cotrans_less_unfolded.
Intro.
Inversion_clear H5.
Cut (e[/]FourNZ [<] (F x Hx))+((F x Hx) [<] [--](e[/]FourNZ)); [Intro | Apply less_AbsIR; Assumption].
Inversion_clear H5.
Cut (Zero [<] (F y Hy)).
2: Exact (cont_no_sign_change_pos e[/]FourNZ (pos_div_four ?? He) x y H1 H3 Hx Hy (H2 x y H1 H3 Hx Hy H4) H6 H7).
Intro.
Apply leEq_wdl with (AbsIR (F x Hx)[-](F y Hy)).
Apply leEq_transitive with e[/]FourNZ.
Simpl; Apply H2; Assumption.
Apply less_leEq; Apply pos_div_four'; Assumption.
Apply AbsIR_wd.
Apply eq_symmetric_unfolded; Apply cg_minus_wd; (EApply eq_transitive_unfolded;
  [Idtac | Apply AbsIR_eq_x; Apply less_leEq]).
Apply FAbs_char.
Apply less_transitive_unfolded with e[/]FourNZ.
Apply pos_div_four; Assumption.
Assumption.
Apply FAbs_char.
Assumption.
Cut ((F y Hy) [<] Zero).
2: Exact (cont_no_sign_change_neg e[/]FourNZ (pos_div_four ?? He) x y H1 H3 Hx Hy (H2 x y H1 H3 Hx Hy H4) H6 H7).
Intro.
Apply leEq_wdl with (AbsIR (F y Hy)[-](F x Hx)).
Apply leEq_transitive with e[/]FourNZ.
Apply leEq_wdl with (AbsIR (F x Hx)[-](F y Hy)); [Simpl; Apply H2 | Apply AbsIR_minus]; Assumption.
Apply less_leEq; Apply pos_div_four'; Assumption.
Apply AbsIR_wd.
RStepl ([--](F x Hx))[-]([--](F y Hy)).
Apply eq_symmetric_unfolded; Apply cg_minus_wd; (EApply eq_transitive_unfolded;
  [Idtac | Apply AbsIR_eq_inv_x; Apply less_leEq]).
Apply FAbs_char.
Apply less_transitive_unfolded with [--](e[/]FourNZ).
Assumption.
AStepr [--](Zero::IR); Apply inv_resp_less; Apply pos_div_four; Assumption.
Apply FAbs_char.
Assumption.
EApply leEq_transitive.
Apply triangle_IR_minus.
RStepr e[/]ThreeNZ[+](e[/]ThreeNZ[+]e[/]ThreeNZ).
Apply plus_resp_leEq_both; (EApply leEq_wdl; [Idtac | Apply eq_symmetric_unfolded; EApply eq_transitive_unfolded; [Idtac | Apply AbsIR_eq_x]]).
Apply less_leEq; Apply H6; Assumption.
Algebra.
Apply AbsIR_nonneg.
2: Apply AbsIR_wd; Apply (FAbs_char ? y (Hy,Hy') Hy).
Apply leEq_wdl with (AbsIR (F x Hx)[-]((F x Hx)[-](F y Hy))).
2: Apply AbsIR_wd; Rational.
EApply leEq_transitive.
Apply triangle_IR_minus.
Apply plus_resp_leEq_both.
Apply less_leEq; Apply H6; Assumption.
EApply leEq_transitive.
Simpl; Apply H2; Assumption.
Apply less_leEq; Assumption.
Simpl; Apply AbsIR_nonneg.
Assumption.
RStepl e[*](One[/]FourNZ); RStepr e[*](One[/]ThreeNZ).
Apply mult_resp_less_lft.
Apply recip_resp_less.
Apply pos_three.
Apply three_less_four.
Assumption.
Qed.

End Absolute_Value.
*)

Section Other.

Section Sums.

(**
We finally prove that the sum of an arbitrary family of continuous functions is still a continuous function.
*)

Variables a b : IR.
Hypothesis Hab : a[<=]b.
Hypothesis Hab' : a[<]b.

(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Lemma Continuous_I_Sum0 :
 forall f : nat -> PartIR,
 (forall n : nat, Continuous_I Hab (f n)) ->
 forall n : nat, Continuous_I Hab (FSum0 n f).
intros.
induction  n as [| n Hrecn].
eapply Continuous_I_wd.
apply FSum0_0.
2: apply Continuous_I_const.
intro; apply contin_imp_inc; auto.
eapply Continuous_I_wd.
apply FSum0_S.
intro; apply contin_imp_inc; auto.
apply Continuous_I_plus; auto.
Qed.

Lemma Continuous_I_Sumx :
 forall (n : nat) (f : forall i : nat, i < n -> PartIR),
 (forall (i : nat) Hi, Continuous_I Hab (f i Hi)) ->
 Continuous_I Hab (FSumx n f).
intro; induction  n as [| n Hrecn]; intros f contF.
simpl in |- *; apply Continuous_I_const.
simpl in |- *; apply Continuous_I_plus.
apply Hrecn.
intros; apply contF.
apply contF.
Qed.

Lemma Continuous_I_Sum :
 forall f : nat -> PartIR,
 (forall n : nat, Continuous_I Hab (f n)) ->
 forall m n : nat, Continuous_I Hab (FSum m n f).
intros.
eapply Continuous_I_wd.
apply Feq_symmetric; apply FSum_FSum0'.
intro; apply contin_imp_inc; auto.
apply Continuous_I_minus; apply Continuous_I_Sum0; auto.
Qed.

End Sums.

(**
For practical purposes, these characterization results are useful:
*)

Lemma lub_charact :
 forall (a b : IR) Hab (F : PartIR) (contF : Continuous_I Hab F) (z : IR),
 fun_lub_IR F (compact a b Hab) z -> z[=]lub_funct _ _ _ _ contF.
intros a b Hab F contF z H.
elim H; intros Hz Hz'; clear H.
assert (H := lub_is_lub _ _ _ _ contF).
set (y := lub_funct _ _ _ _ contF) in *.
elim H; intros Hy Hy'; clear H.
apply leEq_imp_eq; apply shift_zero_leEq_minus'; apply inv_cancel_leEq;
 AStepr ZeroR; red in |- *; apply approach_zero; intros e He.

RStepl (z[-]y).
apply shift_minus_less.
elim (Hz' e He); intros x Hx.
intro H.
apply less_leEq_trans with (x[+]e).
apply shift_less_plus'; auto.
AStepr (y[+]e).
apply plus_resp_leEq; apply Hy.
auto.

RStepl (y[-]z).
apply shift_minus_less.
elim (Hy' e He); intros x Hx.
intro H.
apply less_leEq_trans with (x[+]e).
apply shift_less_plus'; auto.
AStepr (z[+]e).
apply plus_resp_leEq; apply Hz.
auto.
Qed.

Lemma glb_charact :
 forall (a b : IR) Hab (F : PartIR) (contF : Continuous_I Hab F) (z : IR),
 fun_glb_IR F (compact a b Hab) z -> z[=]glb_funct _ _ _ _ contF.
intros a b Hab F contF z H.
elim H; intros Hz Hz'; clear H.
assert (H := glb_is_glb _ _ _ _ contF).
set (y := glb_funct _ _ _ _ contF) in *.
elim H; intros Hy Hy'; clear H.
apply leEq_imp_eq; apply shift_zero_leEq_minus'; apply inv_cancel_leEq;
 AStepr ZeroR; red in |- *; apply approach_zero; intros e He.

RStepl (z[-]y).
apply shift_minus_less.
elim (Hy' e He); intros x Hx.
intro H.
apply leEq_less_trans with x.
apply Hz; auto.
apply shift_less_plus; auto.

RStepl (y[-]z).
apply shift_minus_less.
elim (Hz' e He); intros x Hx.
intro H.
apply leEq_less_trans with x.
apply Hy; auto.
apply shift_less_plus; auto.
Qed.

(**
The following result is also extremely useful, as it allows us to set a lower bound on the glb of a function.
*)

Lemma leEq_glb :
 forall a b Hab (F : PartIR) contF x,
 (forall y : IR, Compact Hab y -> forall Hy, x[<=]F y Hy) ->
 x[<=]glb_funct a b Hab F contF.
intros a b Hab F contF x H.
elim (glb_is_glb _ _ _ _ contF); intros.
AStepr (glb_funct _ _ _ _ contF[+]Zero); apply shift_leEq_plus'.
red in |- *; apply approach_zero_weak.
intros e H0.
elim (b0 _ H0); intro y; intros.
apply less_leEq; eapply leEq_less_trans.
2: apply q.
apply minus_resp_leEq.
elim p; intros z Hz.
elim Hz; intros H1 H2.
elim H2; intros H3 H4.
AStepr (F z H3); auto.
Qed.

(**
The norm is also an extensional property.
*)

Lemma Norm_Funct_wd :
 forall (a b : IR) (Hab : a[<=]b) (F G : PartIR),
 Feq (Compact Hab) F G ->
 forall (contF : Continuous_I Hab F) (contG : Continuous_I Hab G),
 Norm_Funct contF[=]Norm_Funct contG.
intros a b Hab F G H contF contG.
elim H; intros incF H''.
elim H''; clear H''; intros incG H''.
unfold Norm_Funct in |- *; apply bin_op_wd_unfolded.
generalize (lub_is_lub _ _ _ _ contF); intro Hlub.
apply lub_charact.
elim Hlub; clear Hlub; intros H0 H1.
split.
intros x H2.
apply H0.
apply fun_image_wd with G.
apply Feq_symmetric; auto.
auto.
intros e H2.
elim (H1 e H2); intro x; intros.
exists x.
apply fun_image_wd with F; auto.
auto.

apply un_op_wd_unfolded.
generalize (glb_is_glb _ _ _ _ contF); intro Hglb.
apply glb_charact.
elim Hglb; intros H0 H1.
split.
intros x H2.
apply H0.
apply fun_image_wd with G.
apply Feq_symmetric; auto.
auto.
intros e H2.
elim (H1 e H2); intro x; intros.
exists x.
apply fun_image_wd with F; auto.
auto.
Qed.

(**
The value of the norm is covariant with the length of the interval.
*)

Lemma included_imp_norm_leEq :
 forall a b c d Hab Hcd F contF1 contF2,
 included (compact c d Hcd) (compact a b Hab) ->
 Norm_Funct (a:=c) (b:=d) (Hab:=Hcd) (F:=F) contF2[<=]
 Norm_Funct (a:=a) (b:=b) (Hab:=Hab) (F:=F) contF1.
intros.
apply leEq_Norm_Funct; intros.
apply norm_bnd_AbsIR; auto.
Qed.

End Other.

Hint Resolve Continuous_I_const Continuous_I_id Continuous_I_plus
  Continuous_I_inv Continuous_I_minus Continuous_I_mult Continuous_I_scal
  Continuous_I_recip Continuous_I_max Continuous_I_min Continuous_I_div
  Continuous_I_nth Continuous_I_abs: continuous.
