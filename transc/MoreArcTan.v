(*
Copyright © 2006 Russell O’Connor

Permission is hereby granted, free of charge, to any person obtaining a copy of
this proof and associated documentation files (the "Proof"), to deal in
the Proof without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Proof, and to permit persons to whom the Proof is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Proof.

THE PROOF IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE PROOF OR THE USE OR OTHER DEALINGS IN THE PROOF.
*)

Require Export InvTrigonom.
Require Import CornTac.

(** Various properties of ArcTangent.*)

Lemma Dom_Tang_ArcTan : forall x, (Dom Tang (ArcTan x)).
Proof.
 intros x.
 apply Tang_Domain'.
 apply ArcTan_range.
Qed.

Lemma ArcTan_zero : ArcTan [0][=][0].
Proof.
 assert (Z:Dom Tang [0]).
  apply Tang_Domain'.
  split; auto with *.
 stepl (ArcTan (Tan _ Z)).
  apply ArcTan_Tan; auto with *.
 apply pfwdef.
 apply Tan_zero.
Qed.

Lemma ArcTan_one : ArcTan [1][=]Pi[/]FourNZ.
Proof.
 assert (Z:Dom Tang (Pi[/]FourNZ)).
  apply Tang_Domain'.
  split; auto with *.
 stepl (ArcTan (Tan _ Z)).
  apply ArcTan_Tan; auto with *.
 apply pfwdef.
 apply Tan_QuarterPi.
Qed.

Hint Resolve ArcTan_zero ArcTan_one: algebra.

Lemma ArcTan_inv : forall x, ArcTan [--]x[=][--](ArcTan x).
Proof.
 intros x.
 stepr (ArcTan [--](Tan (ArcTan x) (Dom_Tang_ArcTan x))).
  apply ArcTan_wd.
  apply un_op_wd_unfolded.
  apply Tan_ArcTan.
 assert (H:(olor ([--](Pi[/]TwoNZ)) (Pi[/]TwoNZ) [--](ArcTan x))).
  destruct (ArcTan_range x).
  split.
   apply inv_resp_less; assumption.
  rstepr ([--][--](Pi[/]TwoNZ)).
  apply inv_resp_less; assumption.
 stepr (ArcTan (Tan _ (Tang_Domain' _ H))).
  apply ArcTan_wd.
  apply eq_symmetric.
  apply Tan_inv.
 destruct H.
 apply ArcTan_Tan; assumption.
Qed.

Lemma ArcTan_resp_less : forall x y, x[<]y -> ArcTan x[<]ArcTan y.
Proof.
 intros x y H.
 unfold ArcTan.
 eapply (Derivative_imp_resp_less realline I).
     apply Derivative_ArcTan.
    assumption.
   constructor.
  constructor.
 intros contF'.
 set (F:={1/}([-C-][1]{+}FId{^}2):PartIR) in *.
 assert (Hz0:forall z:IR, [0][<][1][+][1][*]z[*]z).
  intros z.
  apply less_leEq_trans with [1].
   apply pos_one.
  apply shift_leEq_plus'.
  rstepl ([0]:IR).
  rstepr (z[^]2).
  apply sqr_nonneg.
 assert (Hz:forall z, Dom F z).
  intros z.
  repeat constructor.
  simpl.
  intros _.
  apply Greater_imp_ap.
  apply Hz0.
 set (z:=Max (AbsIR x) (AbsIR y)).
 apply less_leEq_trans with (F z (Hz z)).
  simpl.
  apply shift_less_div.
   apply Hz0.
  rstepl ([0]:IR).
  apply pos_one.
 apply leEq_glb.
 simpl.
 intros a [Ha0 Ha1] H0.
 apply recip_resp_leEq.
  apply Hz0.
 clear H0 contF' F Hz.
 apply plus_resp_leEq_lft.
 apply shift_leEq_rht.
 rstepr ((z[-]a)[*](z[-][--]a)).
 unfold z.
 apply mult_resp_nonneg; apply shift_leEq_lft; eapply leEq_transitive.
    apply Ha1.
   apply Max_leEq; (eapply leEq_transitive;[apply leEq_AbsIR|]).
    apply lft_leEq_Max.
   apply rht_leEq_Max.
  apply inv_resp_leEq.
  apply Ha0.
 unfold MIN, Min.
 rstepl (Max [--]x [--]y).
 apply Max_leEq; (eapply leEq_transitive;[apply inv_leEq_AbsIR|]).
  apply lft_leEq_Max.
 apply rht_leEq_Max.
Qed.

Lemma ArcTan_resp_leEq : forall x y, x[<=]y -> ArcTan x[<=]ArcTan y.
Proof.
 intros x y Hxy.
 rewrite -> leEq_def.
 intros H.
 apply (leEq_less_or_equal _ _ _ Hxy).
 intros H0.
 generalize H; clear H.
 change (Not (ArcTan y[<]ArcTan x)).
 rewrite <- leEq_def.
 destruct H0.
  apply less_leEq.
  apply ArcTan_resp_less.
  assumption.
 stepr (ArcTan x).
  apply leEq_reflexive.
 apply ArcTan_wd.
 assumption.
Qed.

Lemma ArcTan_pos : forall x, [0][<]x -> [0][<]ArcTan x.
Proof.
 intros x Hx.
 csetoid_rewrite_rev ArcTan_zero.
 apply ArcTan_resp_less.
 assumption.
Qed.

Lemma ArcTan_recip : forall x Hx, [0][<]x -> ArcTan ([1][/]x[//]Hx)[=]Pi[/]TwoNZ[-](ArcTan x).
Proof.
 intros x Hx Hx0.
 assert (H0:olor [--](Pi [/]TwoNZ) (Pi [/]TwoNZ) ([--](ArcTan x)[+]Pi[/]TwoNZ)).
  split.
   apply shift_less_plus.
   rstepl ([--]Pi).
   apply inv_resp_less.
   apply less_transitive_unfolded with (Pi[/]TwoNZ).
    destruct (ArcTan_range x); assumption.
   auto with *.
  apply shift_plus_less.
  rstepr ([--][0]:IR).
  apply inv_resp_less.
  apply ArcTan_pos.
  assumption.
 rstepr ([--](ArcTan x)[+]Pi[/]TwoNZ).
 stepr (ArcTan (Tan _ (Tang_Domain' _ H0))); [| now destruct H0; apply ArcTan_Tan; assumption].
 apply ArcTan_wd.
 apply eq_symmetric.
 assert (H1:Dom Tang ([--](ArcTan x))).
  apply Tang_Domain'.
  destruct (ArcTan_range x).
  split.
   apply inv_resp_less; assumption.
  rstepr ([--][--](Pi[/]TwoNZ)).
  apply inv_resp_less.
  assumption.
 assert (H2:(Tan [--](ArcTan x) H1)[#][0]).
  stepl ([--](Tan (ArcTan x) (Dom_Tang_ArcTan x))); [| now apply eq_symmetric; apply Tan_inv].
  rstepr ([--][0]:IR).
  apply inv_resp_ap.
  apply Greater_imp_ap.
  csetoid_rewrite_rev (Tan_ArcTan x (Dom_Tang_ArcTan x)).
  assumption.
 eapply eq_transitive.
  apply (Tan_plus_HalfPi _ (Tang_Domain' _ H0) H1 H2).
 apply mult_cancel_lft with (Tan [--](ArcTan x) H1).
  assumption.
 apply mult_cancel_lft with x.
  apply Greater_imp_ap; assumption.
 rstepl ([--]x:IR).
 rstepr (Tan [--](ArcTan x) H1).
 stepr ([--](Tan (ArcTan x) (Dom_Tang_ArcTan x))).
  apply un_op_wd_unfolded.
  apply Tan_ArcTan.
 apply eq_symmetric.
 apply Tan_inv.
Qed.

Lemma ArcTan_plus_ArcTan : forall x y Hxy,
 ([--][1][<=]x) -> (x[<=][1]) -> ([--][1][<=]y) -> (y[<=][1]) ->
 ArcTan x [+] ArcTan y [=] ArcTan ((x[+]y)[/]([1][-]x[*]y)[//]Hxy).
Proof.
 cut (forall x y Hxy, ([--][1][<=]x) -> (x[<=][1]) -> ([--][1][<=]y) -> (y[<][1]) ->
   ArcTan x [+] ArcTan y [=] ArcTan ((x[+]y)[/]([1][-]x[*]y)[//]Hxy)).
  intros G x y Hxy Hx0 Hx1 Hy0 Hy1.
  apply (not_ap_imp_eq).
  intros H.
  apply (leEq_less_or_equal _ _ _ Hx1).
  intros Hx1'.
  apply (leEq_less_or_equal _ _ _ Hy1).
  intros Hy1'.
  generalize H; clear H.
  apply (eq_imp_not_ap).
  clear Hy1.
  destruct Hy1' as [Hy1|Hy1].
   apply G; assumption.
  assert (Hxy':([1][-]y[*]x)[#][0]).
   rstepl ([1][-]x[*]y).
   assumption.
  rstepl (ArcTan y[+]ArcTan x).
  stepr (ArcTan ((y[+]x)[/]([1][-]y[*]x)[//]Hxy')); [| now apply ArcTan_wd; rational].
  apply G; try assumption.
   stepl ([1]:IR); [| now apply eq_symmetric; assumption].
   apply leEq_reflexive.
  destruct Hx1' as [c|c]; try assumption.
  elimtype False.
  refine (eq_imp_not_ap _ _ _ _ Hxy').
  unfold cg_minus.
  csetoid_rewrite c.
  csetoid_rewrite Hy1.
  rstepl ([0]:IR).
  apply eq_reflexive.
 cut (forall x y Hxy, ([--][1][<=]x) -> (x[<=][1]) -> ([--][1][<]y) -> (y[<][1]) ->
   ArcTan x [+] ArcTan y [=] ArcTan ((x[+]y)[/]([1][-]x[*]y)[//]Hxy)).
  intros G x y Hxy Hx0 Hx1 Hy0 Hy1.
  apply (not_ap_imp_eq).
  intros H.
  apply (leEq_less_or_equal _ _ _ Hx0).
  intros Hx0'.
  apply (leEq_less_or_equal _ _ _ Hx1).
  intros Hx1'.
  apply (leEq_less_or_equal _ _ _ Hy0).
  intros Hy0'.
  generalize H; clear H.
  apply (eq_imp_not_ap).
  clear Hy0.
  destruct Hy0' as [Hy0|Hy0].
   apply G; assumption.
  assert (Hxy':([1][-]y[*]x)[#][0]).
   rstepl ([1][-]x[*]y).
   assumption.
  destruct Hx0' as [Hx0'|Hx0']; destruct Hx1' as [Hx1'|Hx1'].
     rstepl (ArcTan y[+]ArcTan x).
     stepr (ArcTan ((y[+]x)[/]([1][-]y[*]x)[//]Hxy')); [| now apply ArcTan_wd; rational].
     apply G; try assumption.
      stepr ([--][1]:IR); [| easy ].
      apply leEq_reflexive.
     stepl ([--][1]:IR); [| easy ].
     apply shift_zero_leEq_minus'.
     rstepr (Two:IR).
     apply less_leEq; apply pos_two.
    csetoid_replace (ArcTan y) ([--](ArcTan x)).
     rstepl ([0]:IR).
     stepl (ArcTan [0]); [| now apply ArcTan_zero].
     apply ArcTan_wd.
     rstepl ([0][/]([1][-]x[*]y)[//]Hxy).
     apply div_wd.
      csetoid_rewrite Hx1'.
      csetoid_rewrite_rev Hy0.
      rational.
     apply eq_reflexive.
    stepl (ArcTan ([--]x)).
     apply ArcTan_inv.
    apply ArcTan_wd.
    csetoid_rewrite Hx1'.
    assumption.
   elimtype False.
   refine (eq_imp_not_ap _ _ _ _ Hxy').
   unfold cg_minus.
   csetoid_rewrite_rev Hx0'.
   csetoid_rewrite_rev Hy0.
   rational.
  elimtype False.
  refine (eq_imp_not_ap _ [--][1] [1] _ _).
   now stepr x.
  apply ap_symmetric.
  apply zero_minus_apart.
  rstepl (Two:IR).
  apply two_ap_zero.
 intros x y Hxy Hx0 Hx1 Hy0 Hy1.
 assert (X:olor [--](Pi [/]TwoNZ) (Pi [/]TwoNZ) (ArcTan x[+]ArcTan y)).
  split.
   rstepl ([--](Pi[/]FourNZ)[+][--](Pi[/]FourNZ)).
   csetoid_rewrite_rev (ArcTan_one).
   csetoid_replace ([--](ArcTan [1])) (ArcTan ([--][1])).
    apply plus_resp_leEq_less.
     apply ArcTan_resp_leEq; assumption.
    apply ArcTan_resp_less; assumption.
   apply eq_symmetric; apply ArcTan_inv.
  rstepr ((Pi[/]FourNZ)[+](Pi[/]FourNZ)).
  csetoid_rewrite_rev (ArcTan_one).
  apply plus_resp_leEq_less.
   apply ArcTan_resp_leEq; assumption.
  apply ArcTan_resp_less; assumption.
 elim X; intros X0 X1.
 csetoid_rewrite_rev (ArcTan_Tan _ X0 X1 (Tang_Domain' _ X)).
 apply ArcTan_wd.
 assert (Y:([1][-]Tan _ (Dom_Tang_ArcTan x)[*]Tan _ (Dom_Tang_ArcTan y))[#][0]).
  unfold cg_minus.
  csetoid_rewrite_rev (Tan_ArcTan _ (Dom_Tang_ArcTan x)).
  csetoid_rewrite_rev (Tan_ArcTan _ (Dom_Tang_ArcTan y)).
  assumption.
 stepr (Tan _ (Dom_Tang_ArcTan x)[+]Tan _ (Dom_Tang_ArcTan y)[/]_[//]Y).
  apply Tan_plus.
 apply div_wd; unfold cg_minus; csetoid_rewrite_rev (Tan_ArcTan _ (Dom_Tang_ArcTan x));
   csetoid_rewrite_rev (Tan_ArcTan _ (Dom_Tang_ArcTan y)); apply eq_reflexive.
Qed.

Section ArcTan_Series.

(**
** ArcTan Series
In this section we show the convergence of ArcTan's power series.

First we show the convergence of the series for 1/(1+x^2)
*)

Lemma bellcurve_series_convergent_IR : fun_series_convergent_IR (olor ([--][1]) [1]) (fun (i:nat) => ([--][1])[^]i{**}Fid IR{^}(2*i)).
Proof.
 apply fun_series_convergent_wd_IR with (fun i => Fid IR{^}i[o]({--}(Fid IR{^}2))).
  intros n.
  FEQ.
  change ([--]([1][*]x[*]x)[^]n[=]([--][1])[^]n[*]x[^](2*n)).
  rstepl (([--][1][*](x[*]x))[^]n).
  stepl (([--][1])[^]n[*]((x[*]x)[^]n)); [| now apply eq_symmetric; apply mult_nexp].
  apply mult_wdr.
  replace (2*n)%nat with (n+n)%nat by auto with *.
  eapply eq_transitive.
   apply mult_nexp.
  apply nexp_plus.
 apply FSeries_Sum_comp_conv with (olor [--][1] [1]); [|Contin|apply fun_power_series_conv_IR].
 intros a b Hab Hinc.
 set (c:=Max (AbsIR a) (AbsIR b)).
 exists ([--](c[^]2)).
 exists (c[^]2).
 assert (X:[--](c[^]2)[<=]c[^]2).
  apply leEq_transitive with ([0]:IR).
   rstepr ([--][0]:IR).
   apply inv_resp_leEq.
   apply sqr_nonneg.
  apply sqr_nonneg.
 exists X.
 assert (A0:(c[^]2)[<][1]).
  rstepr ([1][^]2:IR).
  unfold c.
  apply nexp_resp_less.
    auto with *.
   eapply leEq_transitive.
    apply AbsIR_nonneg.
   apply lft_leEq_Max.
  apply Max_less; [destruct (Hinc _ (compact_inc_lft _ _ Hab))
    |destruct (Hinc _ (compact_inc_rht _ _ Hab))]; apply AbsIR_less; assumption.
 assert (A1:[--][1][<][--](c[^]2)).
  apply inv_resp_less.
  assumption.
 split.
  intros d [Hd0 Hd1].
  split.
   apply less_leEq_trans with ([--](c[^]2)); assumption.
  apply leEq_less_trans with (c[^]2); assumption.
 intros x Hx [Hx0 Hx1].
 simpl.
 cut (AbsSmall (c[^]2) ([--](x[^]2))).
  intros [A B]; split; assumption.
 apply inv_resp_AbsSmall.
 rstepl (c[*]c).
 rstepr (x[*]x).
 cut (AbsSmall c x).
  intros; apply mult_AbsSmall; assumption.
 unfold c.
 split.
  rstepr ([--][--]x).
  apply inv_resp_leEq.
  eapply leEq_transitive;[|apply lft_leEq_Max].
  eapply leEq_transitive;[|apply inv_leEq_AbsIR].
  apply inv_resp_leEq.
  assumption.
 eapply leEq_transitive;[|apply rht_leEq_Max].
 eapply leEq_transitive;[|apply leEq_AbsIR].
 assumption.
Qed.

Lemma bellcurve_series
     : forall (Hs:fun_series_convergent_IR (olor ([--][1]) [1]) (fun (i:nat) => ([--][1])[^]i{**}Fid IR{^}(2*i))),
       Feq (olor ([--][1]) [1]) (FSeries_Sum Hs) ({1/}([-C-][1]{+}FId{^}2)).
Proof.
 intros Hs.
 split.
  simpl.
  apply included_refl.
 split.
  apply included_trans with realline.
   intros x _; constructor.
  apply Continuous_imp_inc.
  apply ArcTan_def_lemma.
 intros c [Hc0 Hc1] D0 D1.
 assert (X:AbsIR ([--](c[^]2))[<][1]).
  csetoid_rewrite_rev (AbsIR_inv (c[^]2)).
  csetoid_rewrite (AbsIR_nexp_op 2 c).
  rstepr ([1][^]2:IR).
  apply nexp_resp_less.
    auto with *.
   apply AbsIR_nonneg.
  apply AbsIR_less; assumption.
 simpl.
 generalize (ext2 (S:=IR) (P:=Conj (fun _ : IR => True) (fun _ : IR => True))
   (R:=fun (x : IR) (_ : Conj (fun _ : IR => True) (fun _ : IR => True) x) =>
     [1][+][1][*]x[*]x[#][0]) (x:=c) D1).
 intros H.
 assert (Y:[1][-]([--](c[^]2))[#][0]).
  rstepl ([1][+][1][*]c[*]c).
  assumption.
 rstepr ([1][/]([1][-]([--](c[^]2)))[//]Y).
 stepr (series_sum (power_series [--](c[^]2)) (power_series_conv [--](c[^]2) X)); [| now
   apply (power_series_sum ([--](c[^]2)) X Y (power_series_conv _ X))].
 apply series_sum_wd.
 intros n.
 simpl.
 change ((([--][1])[^]n)[*]c[^](2*n)[=][--]([1][*]c[*]c)[^]n).
 rstepr ((([--][1])[*]c[*]c)[^]n).
 csetoid_rewrite_rev (nexp_mult _ c 2 n).
 csetoid_rewrite_rev (mult_nexp _ ([--][1]) (c[^]2) n).
 rational.
Qed.

(** Finally we show the convergence of the series for arctan.*)

(* Although the series converges on the closed interval [-1,1],
this proof only shows convergence on the open interval (-1,1).
*)

Lemma arctan_series_convergent_IR : fun_series_convergent_IR (olor ([--][1]) [1])
(fun (i:nat) => (([--][1])[^]i[/]nring (S (2*i))[//]nringS_ap_zero _ (2*i)){**}Fid IR{^}(2*i+1)).
Proof.
 intros y z Hyz Hinc.
 pose (C:=Max (AbsIR y) (AbsIR z)).
 assert (C[<][1]).
  unfold C.
  destruct (Hinc _ (compact_inc_lft _ _ Hyz)).
  destruct (Hinc _ (compact_inc_rht _ _ Hyz)).
  apply Max_less; apply AbsIR_less; assumption.
 assert ([0][<=]C).
  unfold C.
  eapply leEq_transitive.
   apply AbsIR_nonneg.
  apply lft_leEq_Max.
 apply fun_ratio_test_conv.
  intros n.
  Contin.
 exists 0.
 exists C.
  assumption.
 split.
  assumption.
 intros x Hx n _ Hx0 Hx1.
 generalize (nringS_ap_zero IR (2 * S n)).
 generalize (nringS_ap_zero IR (2 * n)).
 intros Z0 Z1.
 set (a := S (2 * S n)).
 set (b := 2*S n + 1).
 set (c:= S (2 * n)).
 set (d:= 2*n + 1).
 change (AbsIR (([--][1][^]S n[/]nring (R:=IR) a[//]Z1)[*]x[^]b)[<=]
   C[*]AbsIR (([--][1][^]n[/]nring (R:=IR) c[//]Z0)[*]x[^]d)).
 stepl (AbsIR (([--][1][^]S n[/]nring (R:=IR) a[//]Z1))[*]AbsIR (x[^]b)); [| now
   apply eq_symmetric; apply AbsIR_resp_mult].
 stepr (C[*](AbsIR (([--][1][^]n[/]nring (R:=IR) c[//]Z0))[*]AbsIR(x[^]d))); [| now
   apply mult_wdr; apply eq_symmetric; apply AbsIR_resp_mult].
 rstepr (AbsIR (([--][1][^]n[/]nring (R:=IR) c[//]Z0))[*](C[*]AbsIR(x[^]d))).
 apply mult_resp_leEq_both; try apply AbsIR_nonneg.
  stepl (AbsIR ([--][1][^]S n)[/]_[//](AbsIR_resp_ap_zero _ Z1)); [| now
    apply eq_symmetric; apply AbsIR_division].
  stepr ((AbsIR ([--][1][^]n)[/]_[//](AbsIR_resp_ap_zero _ Z0))); [| now
    apply eq_symmetric; apply AbsIR_division].
  assert (H0:forall n, AbsIR([--][1][^]n)[=][1]).
   intros i.
   csetoid_rewrite (AbsIR_nexp_op i ([--][1]:IR)).
   csetoid_rewrite_rev (AbsIR_inv [1]).
   stepl (([1]:IR)[^]i).
    apply one_nexp.
   apply nexp_wd.
   apply eq_symmetric; apply AbsIR_eq_x.
   apply less_leEq; apply pos_one.
  stepl ([1][/]AbsIR (nring (R:=IR) (S (2 * S n)))[//]
    AbsIR_resp_ap_zero (nring (R:=IR) (S (2 * S n))) Z1); [| now
      apply div_wd; try apply eq_reflexive; apply eq_symmetric; apply H0].
  stepr ([1][/]AbsIR (nring (R:=IR) (S (2 * n)))[//]
    AbsIR_resp_ap_zero (nring (R:=IR) (S (2 * n))) Z0); [| now
      apply div_wd; try apply eq_reflexive; apply eq_symmetric; apply H0].
  apply recip_resp_leEq; try (apply AbsIR_pos; assumption).
  eapply leEq_transitive;[|apply leEq_AbsIR].
  apply AbsSmall_imp_AbsIR.
  apply leEq_imp_AbsSmall.
   apply nring_nonneg.
  apply nring_leEq.
  auto with *.
 replace b with (2+d);[|unfold b, d; auto with *].
 stepl (AbsIR x[^](2+d)); [| now apply eq_symmetric; apply AbsIR_nexp_op].
 stepl (AbsIR x[^]2[*]AbsIR x[^]d); [| now apply nexp_plus].
 stepr (C[*]AbsIR x[^]d); [| now apply mult_wdr; apply eq_symmetric; apply AbsIR_nexp_op].
 apply mult_resp_leEq_rht; try (apply nexp_resp_nonneg; apply AbsIR_nonneg).
 apply leEq_transitive with (C[^]2).
  stepl (AbsIR(x[^]2)); [| now apply AbsIR_nexp_op].
  stepl (x[^]2); [| now apply eq_symmetric; apply AbsIR_eq_x; apply sqr_nonneg].
  apply shift_zero_leEq_minus'.
  rstepr ((C[-]x)[*](C[-][--]x)).
  unfold C.
  destruct Hx as [Y0 Y1].
  apply mult_resp_nonneg; apply shift_zero_leEq_minus.
   eapply leEq_transitive.
    apply Y1.
   eapply leEq_transitive.
    apply leEq_AbsIR.
   apply rht_leEq_Max.
  eapply leEq_transitive.
   apply inv_resp_leEq.
   apply Y0.
  eapply leEq_transitive.
   apply inv_leEq_AbsIR.
  apply lft_leEq_Max.
 rstepl (C[*]C).
 rstepr (C[*][1]).
 apply mult_resp_leEq_lft.
  apply less_leEq; assumption.
 assumption.
Qed.

Lemma arctan_series : forall c : IR,
       forall (Hs:fun_series_convergent_IR (olor ([--][1]) [1]) (fun (i:nat) => (([--][1])[^]i[/]nring (S (2*i))[//]nringS_ap_zero _ (2*i)){**}Fid IR{^}(2*i+1))) Hc,
       FSeries_Sum Hs c Hc[=]ArcTan c.
Proof.
 intros c Hs Hc.
 set (J:=olor [--][1] [1]).
 assert (HJ:proper J).
  simpl.
  apply shift_zero_less_minus'.
  rstepr (Two:IR).
  apply pos_nring_S.
 assert (Y0 : included J realline).
  intros a b; constructor.
 assert (Y1 : J [0]).
  split;[rstepr ([--][0]:IR);apply inv_resp_less|]; apply pos_one.
 stepl (([-S-] Included_imp_Continuous realline {1/}([-C-][1]{+}FId{^}2)
   ArcTan_def_lemma J Y0) [0] Y1 c Hc).
  apply: Integral_wd.
  apply Feq_reflexive.
  intros d Hd.
  eapply Continuous_imp_inc.
   apply ArcTan_def_lemma.
  constructor.
 apply cg_inv_unique_2.
 cut (Derivative J HJ (FSeries_Sum Hs) {1/}([-C-][1]{+}FId{^}2)).
  intros X.
  destruct (FTC2 J _ (Included_imp_Continuous _ _ ArcTan_def_lemma J Y0) [0] Y1 _ _ X) as [z Hz].
  clear X.
  apply eq_transitive with z.
   eapply eq_transitive; [|apply (Feq_imp_eq _ _ _ Hz _ Hc (Hc, Hc) I)].
   apply: bin_op_wd_unfolded;[|apply un_op_wd_unfolded]; apply pfwdef; apply eq_reflexive.
  apply eq_symmetric.
  eapply eq_transitive; [|apply (Feq_imp_eq _ _ _ Hz _ Y1 (Y1, Y1) I)].
  rstepl ([0][-][0]:IR).
  apply: cg_minus_wd.
   stepr (ArcTan [0]).
    assert (Z:Dom Tang [0]).
     repeat split; try constructor.
     intros [].
     stepl ([1]:IR).
      apply ring_non_triv.
     apply eq_symmetric.
     apply Cos_zero.
    stepl (ArcTan (Tan _ Z)).
     apply pfwdef.
     apply Tan_zero.
    apply ArcTan_Tan; [rstepr ([--][0]:IR); apply inv_resp_less|]; apply pos_HalfPi.
   unfold ArcTan, ArcTang.
   apply: Integral_wd.
   apply Feq_reflexive.
   intros d Hd.
   eapply Continuous_imp_inc.
    apply ArcTan_def_lemma.
   constructor.
  eapply eq_transitive.
   apply eq_symmetric.
   eapply (series_sum_zero conv_zero_series).
  simpl; apply series_sum_wd.
  intros n.
  eapply eq_transitive.
   apply eq_symmetric.
   apply cring_mult_zero.
  apply mult_wdr.
  apply eq_symmetric.
  apply (zero_nexp IR (2*n+1)).
  auto with *.
 clear -J.
 eapply Derivative_wdr.
  apply (bellcurve_series bellcurve_series_convergent_IR).
 apply Derivative_FSeries.
 intros n.
 rewrite plus_comm.
 simpl.
 Derivative_Help; [|apply Derivative_scal;apply Derivative_nth;Deriv].
 FEQ.
Qed.

End ArcTan_Series.
