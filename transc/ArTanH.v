(* Copyright © 1998-2006
 * Russell O’Connor
 *
 * This work is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This work is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this work; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 *)

Require Export Exponential.
Require Import CornTac.

(**
* Inverse Hyperbolic Tangent Function
The definition of the inverse hyperbolic tangent function.

area tangens hyperbolicus *)

Definition ArTangH : PartIR := Half{**}(Logarithm[o](([-C-]One{+}FId){/}([-C-]One{-}FId))).

Definition DomArTanH := olor ([--]One) One.

Lemma proper_DomArTanH : proper DomArTanH.
Proof.
 simpl.
 apply shift_zero_less_minus'.
 rstepr (Two:IR).
 apply pos_two.
Qed.

Lemma DomArTanH_Dom_ArTanH : included DomArTanH (Dom ArTangH).
Proof.
 intros x Hx.
 split.
  constructor.
 assert (X:Dom (([-C-]One{+}FId){/}([-C-]One{-}FId)) x).
  split.
   repeat constructor.
  split.
   repeat constructor.
  simpl.
  intros _.
  apply Greater_imp_ap.
  apply shift_zero_less_minus.
  destruct Hx; assumption.
 exists X.
 simpl.
 apply div_resp_pos.
  apply shift_zero_less_minus.
  destruct Hx; assumption.
 rstepr (x[-][--]One).
 apply shift_zero_less_minus.
 destruct Hx; assumption.
Qed.

Lemma Dom_ArTanH_DomArTanH : included (Dom ArTangH) DomArTanH.
Proof.
 intros x [_ [Hx0 Hx1]].
 simpl in Hx1.
 assert (Hx:=Hx0).
 destruct Hx as [_ [_ H]].
 simpl in H.
 assert (Hx:One[-]x[#]Zero).
  apply H.
  repeat constructor.
 clear H.
 destruct (ap_imp_less _ _ _ Hx) as [H|H].
  elim (less_irreflexive IR Zero).
  eapply less_transitive_unfolded.
   apply Hx1.
  apply mult_cancel_less with (x[-]One).
   apply inv_cancel_less.
   rstepl (One[-]x).
   rstepr (Zero:IR).
   assumption.
  rstepr (Zero[+][--]Zero:IR).
  rstepl (One[-]x[+][--]Two).
  apply plus_resp_less_both.
   assumption.
  apply inv_resp_less.
  apply pos_two.
 split.
  apply shift_zero_less_minus'.
  rstepr (One[+]x).
  rstepl (Zero[*](One[-]x)).
  eapply shift_mult_less.
   assumption.
  apply Hx1.
 apply shift_zero_less_minus'.
 assumption.
Qed.

Definition ArTanH (x:IR) (Hx:DomArTanH x) := ArTangH x (DomArTanH_Dom_ArTanH x Hx).

Lemma ArTanH_wd : forall (x y : IR) Hx Hy, x[=]y -> ArTanH x Hx[=]ArTanH y Hy.
Proof.
 intros x y Hx Hy H.
 apply pfwdef.
 assumption.
Qed.

Lemma ArTanH_maps_compact_lemma : maps_compacts_into DomArTanH (openl Zero)
  (([-C-]One{+}FId){/}([-C-]One{-}FId)).
Proof.
 intros a b Hab H.
 assert (Ha : Zero[<]One[-]a).
  apply shift_zero_less_minus.
  destruct (H _ (compact_inc_lft _ _ Hab)) as [_ A].
  assumption.
 assert (Ha' : One[-]a[#]Zero).
  apply Greater_imp_ap.
  assumption.
 exists (One[+]a[/]_[//]Ha').
 assert (Hb : Zero[<]One[-]b).
  apply shift_zero_less_minus.
  destruct (H _ (compact_inc_rht _ _ Hab)) as [_ A].
  assumption.
 assert (Hb' : One[-]b[#]Zero).
  apply Greater_imp_ap.
  assumption.
 exists (One[+](One[+]b[/]_[//]Hb')).
 assert (Hcd : (One[+]a[/]_[//]Ha')[<](One[+](One[+]b[/]_[//]Hb'))).
  rstepl (Zero[+](One[+]a[/]_[//]Ha')).
  apply plus_resp_less_leEq.
   apply pos_one.
  apply shift_leEq_div; try assumption.
  rstepl (((One[-]a[*]b)[+](a[-]b))[/]_[//]Ha').
  apply shift_div_leEq; try assumption.
  rstepr ((One[-]a[*]b)[+](b[-]a)).
  apply plus_resp_leEq_lft.
  apply shift_minus_leEq.
  rstepr (Two[*]b[-]a).
  apply shift_leEq_minus.
  rstepl (Two[*]a).
  apply mult_resp_leEq_lft; try assumption.
  apply less_leEq; apply pos_two.
 exists Hcd.
 split.
  intros y [Hy _].
  apply: less_leEq_trans;[|apply Hy].
  apply div_resp_pos.
   assumption.
  destruct (H _ (compact_inc_lft _ _ Hab)) as [A _].
  rstepr (a[-][--]One).
  apply shift_zero_less_minus.
  assumption.
 intros x Hx H0.
 simpl.
 assert (Zero[<]One[-]x).
  destruct (H0) as [_ A].
  rstepr ((One[-]b)[+](b[-]x)).
  rstepl (Zero[+]Zero:IR).
  apply plus_resp_less_leEq.
   assumption.
  apply shift_zero_leEq_minus.
  assumption.
 split.
  apply shift_leEq_div; try assumption.
  rstepl (((One[-]x[*]a)[+](a[-]x))[/]_[//]Ha').
  apply shift_div_leEq; try assumption.
  rstepr ((One[-]x[*]a)[+](x[-]a)).
  apply plus_resp_leEq_lft.
  apply shift_minus_leEq.
  rstepr (Two[*]x[-]a).
  apply shift_leEq_minus.
  rstepl (Two[*]a).
  apply mult_resp_leEq_lft; try assumption.
   destruct H0; assumption.
  apply less_leEq; apply pos_two.
 apply leEq_transitive with (Zero[+](One[+]b[/]_[//]Hb')).
  apply shift_div_leEq; try assumption.
  rstepr (((One[-]x[*]b)[+](b[-]x))[/]_[//]Hb').
  apply shift_leEq_div; try assumption.
  rstepl ((One[-]x[*]b)[+](x[-]b)).
  apply plus_resp_leEq_lft.
  apply shift_minus_leEq.
  rstepr (Two[*]b[-]x).
  apply shift_leEq_minus.
  rstepl (Two[*]x).
  apply mult_resp_leEq_lft; try assumption.
   destruct H0; assumption.
  apply less_leEq; apply pos_two.
 apply plus_resp_leEq.
 apply less_leEq; apply pos_one.
Qed.

Lemma Derivative_ArTanH : forall H, Derivative DomArTanH H ArTangH (Frecip ([-C-]One{-}FId{^}2)).
Proof.
 intros H.
 assert (bnd_away_zero_in_P ([-C-]One{-}FId) DomArTanH).
  clear H.
  intros a b Hab H.
  split.
   Included.
  exists (One[-]b).
   destruct (H _ (compact_inc_rht _ _ Hab)) as [_ A].
   apply shift_zero_less_minus.
   assumption.
  intros y Hy H0.
  simpl.
  eapply leEq_transitive;[|apply leEq_AbsIR].
  apply plus_resp_leEq_lft.
  apply inv_resp_leEq.
  destruct H0; assumption.
 unfold ArTangH.
 unfold Half.
 eapply Derivative_wdr; [|apply Derivative_scal;
   eapply (Derivative_comp DomArTanH (openl Zero) H CI);[apply ArTanH_maps_compact_lemma | Derivative_Help; apply Feq_reflexive|Deriv]].
  FEQ.
   apply included_FScalMult.
   apply included_FMult.
    apply included_FComp.
     Included.
    intros x Hx Hx0.
    split.
     repeat constructor.
    simpl; intros _.
    apply div_resp_ap_zero_rev.
    apply Greater_imp_ap.
    rstepr (x[-][--]One).
    apply shift_zero_less_minus.
    destruct Hx0; assumption.
   apply included_FDiv.
     repeat constructor.
    repeat constructor.
   intros x Hx0 Hx.
   simpl.
   apply Greater_imp_ap.
   rstepr ((One[-]x)[^]2).
   apply pos_square.
   apply Greater_imp_ap.
   apply shift_zero_less_minus.
   destruct Hx0; assumption.
  apply included_FRecip.
   repeat constructor.
  intros x Hx0 Hx.
  simpl.
  rstepl ((One[-]x)[*](x[-][--]One)).
  apply Greater_imp_ap.
  apply mult_resp_pos; apply shift_zero_less_minus; destruct Hx0; assumption.
 apply included_FDiv.
   repeat constructor.
  repeat constructor.
 intros x H0 Hx.
 simpl.
 rstepl ((One[-]x)[^]2).
 apply Greater_imp_ap.
 apply pos_square.
 apply Greater_imp_ap.
 apply shift_zero_less_minus.
 destruct H0; assumption.
Qed.

Lemma Continuous_ArTanH : Continuous DomArTanH ArTangH.
Proof.
 eapply Derivative_imp_Continuous with (pI:=proper_DomArTanH).
 apply Derivative_ArTanH.
Qed.
(* begin hide *)
Hint Resolve ArTanH_wd: algebra.
Hint Resolve Continuous_ArTanH: continuous.
Hint Resolve Derivative_ArTanH: derivate.
(* end hide *)
(** Properties ofthe Inverse Hyperbolic Tangent Function. *)

Lemma ArTanH_inv : forall x Hx Hx', ArTanH [--]x Hx[=][--](ArTanH x Hx').
Proof.
 intros x Hx Hx'.
 unfold ArTanH, ArTangH.
 generalize (DomArTanH_Dom_ArTanH).
 intros X.
 simpl in X.
 set (A:=(ProjT2 (Prj2 (X [--]x Hx)))).
 set (B:=(ProjT2 (Prj2 (X x Hx')))).
 change (Half (R:=IR)[*]Log _ A[=][--](Half (R:=IR)[*]Log _ B)).
 generalize A B.
 clear A B.
 intros A B.
 rstepr (Half[*][--](Log _ B)).
 apply mult_wdr.
 apply cg_inv_unique.
 assert (C:=mult_resp_pos _ _ _ B A).
 astepl (Log _ C).
 astepr (Log _ (pos_one IR)).
 apply Log_wd.
 rational.
Qed.

Lemma ArTanH_zero : forall H, ArTanH Zero H[=]Zero.
Proof.
 intros H.
 apply mult_cancel_lft with (Two:IR).
  apply nringS_ap_zero.
 rstepr (Zero:IR).
 rstepl (ArTanH Zero H[+]ArTanH Zero H).
 assert (X:DomArTanH [--]Zero).
  eapply iprop_wd.
   apply H.
  rational.
 astepl (ArTanH Zero H[+]ArTanH _ X).
 csetoid_rewrite (ArTanH_inv _ X H).
 rational.
Qed.

(** PowerSeries for the Inverse Hyperbolic Tangent Function. *)
Lemma ArTanH_series_coef_lemma : forall (R:COrdField) n, odd n -> (nring (R:=R) n)[#]Zero.
Proof.
 intros R [|n] H.
  elimtype False.
  inversion H.
 apply nringS_ap_zero.
Qed.

Definition ArTanH_series_coef (n:nat) :=
match (even_odd_dec n) with
| left _ => Zero
| right H => One[/](nring n)[//](ArTanH_series_coef_lemma IR n H)
end.

Definition ArTanH_ps := FPowerSeries Zero ArTanH_series_coef.

Lemma ArTanH_series_lemma :
forall n : nat,
Feq DomArTanH
  (Half (R:=IR){**}
   ((Log_ps n[o][-C-]One{+}FId){-}(Log_ps n[o][-C-]One{-}FId)))
  (ArTanH_ps n).
Proof.
 unfold Log_ps, ArTanH_ps.
 unfold FPowerSeries.
 intros n.
 FEQ.
  apply included_FScalMult.
  apply included_FMinus; apply included_FComp;  Included;  repeat constructor.
 simpl.
 change (Half (R:=IR)[*] (Log_series_coef n[*](One[+]x[-]One)[^]n[-]
   Log_series_coef n[*](One[-]x[-]One)[^]n)[=] ArTanH_series_coef n[*]nexp IR n (x[-]Zero)).
 unfold ArTanH_series_coef.
 destruct n as [|n].
  destruct (even_odd_dec 0) as [A|A]; try inversion A.
  simpl; rational.
 rstepl (Half (R:=IR)[*] (Log_series_coef (S n)[*](x[^]S n[-]([--]x)[^]S n))).
 destruct (even_odd_dec (S n)) as [A|A]; unfold cg_minus.
  csetoid_rewrite (inv_nexp_even _ x _ A).
  rational.
 csetoid_rewrite (inv_nexp_odd _ x _ A).
 unfold Half.
 rstepl (Log_series_coef (S n)[*](x[^]S n)).
 apply mult_wd;[|change (x[^]S n[=](x[+][--]Zero)[^]S n); rational].
 unfold Log_series_coef.
 apply div_wd; try apply eq_reflexive.
 csetoid_rewrite (inv_nexp_even IR One _ (even_S _ A)).
 algebra.
Qed.

Lemma ArTanH_series_lemma2 :
fun_series_convergent_IR DomArTanH
  (fun n : nat =>
   Half (R:=IR){**}
   ((Log_ps n[o][-C-]One{+}FId){-}(Log_ps n[o][-C-]One{-}FId))).
Proof.
 apply FSeries_Sum_scal_conv;[|Contin].
 apply FSeries_Sum_minus_conv; apply FSeries_Sum_comp_conv with (olor Zero Two);
   try apply Log_series_convergent_IR; try Contin; intros a b Hab H; simpl.
  exists (One[+]a); exists (One[+]b).
  assert (H0:One[+]a[<=]One[+]b).
   apply plus_resp_leEq_lft; assumption.
  exists H0.
  split.
   intros c [Hc0 Hc1].
   split.
    eapply less_leEq_trans;[|apply Hc0].
    destruct (H _ (compact_inc_lft _ _ Hab)) as [A _].
    apply shift_less_plus'.
    rstepl ([--]One:IR).
    assumption.
   eapply leEq_less_trans;[apply Hc1|].
   rstepr (One[+]One:IR).
   apply plus_resp_less_lft.
   destruct (H _ (compact_inc_rht _ _ Hab)) as [_ A].
   assumption.
  intros x _ [Hx0 Hx1].
  split; apply plus_resp_leEq_lft; assumption.
 exists (One[-]b); exists (One[-]a).
 assert (H0:One[-]b[<=]One[-]a).
  apply plus_resp_leEq_lft.
  apply inv_resp_leEq; assumption.
 exists H0.
 split.
  intros c [Hc0 Hc1].
  split.
   eapply less_leEq_trans;[|apply Hc0].
   destruct (H _ (compact_inc_rht _ _ Hab)) as [_ A].
   apply shift_zero_less_minus.
   assumption.
  eapply leEq_less_trans;[apply Hc1|].
  rstepr (One[+][--][--]One:IR).
  apply plus_resp_less_lft.
  apply inv_resp_less.
  destruct (H _ (compact_inc_lft _ _ Hab)) as [A _].
  assumption.
 intros x _ [Hx0 Hx1].
 split; apply plus_resp_leEq_lft; apply inv_resp_leEq; assumption.
Qed.

Lemma ArTanH_series_convergent_IR : fun_series_convergent_IR DomArTanH ArTanH_ps.
Proof.
 eapply fun_series_convergent_wd_IR;[|apply ArTanH_series_lemma2].
 apply ArTanH_series_lemma.
Qed.

Lemma ArTanH_series : forall c : IR,
 forall (Hs:fun_series_convergent_IR DomArTanH ArTanH_ps) Hc0 Hc1,
 FSeries_Sum Hs c Hc0[=]ArTanH c Hc1.
Proof.
 intros c Hs Hc0 Hc1.
 unfold ArTanH.
 set (F:=([-C-](Half (R:=IR)){*} ((Logarithm[o][-C-]One{+}FId){-}(Logarithm[o][-C-]One{-}FId)))).
 assert (F0:Dom F c).
  destruct Hc0 as [A B].
  repeat (constructor || exists (CAnd_intro _ _ CI CI)); simpl.
   apply shift_less_plus'.
   rstepl ([--]One:IR).
   assumption.
  apply shift_zero_less_minus.
  assumption.
 apply eq_transitive with (F c F0).
  apply (Feq_imp_eq DomArTanH); try assumption.
  eapply Feq_transitive.
   apply Feq_symmetric.
   apply (FSeries_Sum_wd' _ _ _ ArTanH_series_lemma2 Hs ArTanH_series_lemma).
  assert (B0:maps_compacts_into_weak DomArTanH (olor Zero Two) ([-C-]One{+}FId)).
   intros a b Hab H; simpl.
   exists (One[+]a); exists (One[+]b).
   assert (H0:One[+]a[<=]One[+]b).
    apply plus_resp_leEq_lft; assumption.
   exists H0.
   split.
    clear c Hc0 Hc1 F0.
    intros c [Hc0 Hc1].
    split.
     eapply less_leEq_trans;[|apply Hc0].
     destruct (H _ (compact_inc_lft _ _ Hab)) as [A _].
     apply shift_less_plus'.
     rstepl ([--]One:IR).
     assumption.
    eapply leEq_less_trans;[apply Hc1|].
    rstepr (One[+]One:IR).
    apply plus_resp_less_lft.
    destruct (H _ (compact_inc_rht _ _ Hab)) as [_ A].
    assumption.
   intros x _ [Hx0 Hx1].
   split; apply plus_resp_leEq_lft; assumption.
  assert (A0:fun_series_convergent_IR DomArTanH (fun n : nat => Log_ps n[o]([-C-]One{+}FId))).
   apply FSeries_Sum_comp_conv with (olor Zero Two); try apply Log_series_convergent_IR; try Contin.
  assert (B1:maps_compacts_into_weak DomArTanH (olor Zero Two) ([-C-]One{-}FId)).
   intros a b Hab H; simpl.
   exists (One[-]b); exists (One[-]a).
   assert (H0:One[-]b[<=]One[-]a).
    apply plus_resp_leEq_lft.
    apply inv_resp_leEq; assumption.
   exists H0.
   split.
    clear c Hc0 Hc1 F0.
    intros c [Hc0 Hc1].
    split.
     eapply less_leEq_trans;[|apply Hc0].
     destruct (H _ (compact_inc_rht _ _ Hab)) as [_ A].
     apply shift_zero_less_minus.
     assumption.
    eapply leEq_less_trans;[apply Hc1|].
    rstepr (One[+][--][--]One:IR).
    apply plus_resp_less_lft.
    apply inv_resp_less.
    destruct (H _ (compact_inc_lft _ _ Hab)) as [A _].
    assumption.
   intros x _ [Hx0 Hx1].
   split; apply plus_resp_leEq_lft; apply inv_resp_leEq; assumption.
  assert (A1:fun_series_convergent_IR DomArTanH (fun n : nat => Log_ps n[o]([-C-]One{-}FId))).
   apply FSeries_Sum_comp_conv with (olor Zero Two); try apply Log_series_convergent_IR; try Contin.
  assert (A2:fun_series_convergent_IR DomArTanH (fun n : nat => ((Log_ps n[o][-C-]One{+}FId){-}(Log_ps n[o][-C-]One{-}FId)))).
   apply FSeries_Sum_minus_conv; assumption.
  assert (A3:Feq (olor Zero Two) (FSeries_Sum (J:=olor Zero Two) (f:=Log_ps) Log_series_convergent_IR) Logarithm).
   split.
    Included.
   split.
    intros x [H _].
    assumption.
   intros; apply Log_series.
  eapply Feq_transitive.
   unfold Fscalmult.
   eapply (FSeries_Sum_scal _ _ A2).
   Contin.
  unfold F.
  apply Feq_mult.
   apply Feq_reflexive.
   repeat constructor.
  eapply Feq_transitive.
   apply (FSeries_Sum_minus _ _ _ A0 A1).
  apply Feq_minus.
   eapply Feq_transitive.
    apply (FSeries_Sum_comp DomArTanH (olor Zero Two)); try assumption.
    Contin.
   assert (X:forall (x : IR) (Hx : Dom ([-C-]One{+}FId) x),
     DomArTanH x -> olor Zero Two (([-C-]One{+}FId) x Hx)).
    intros x Hx [C0 C1].
    simpl; split.
     apply shift_less_plus'.
     rstepl ([--]One:IR).
     assumption.
    rstepr (One[+]One:IR).
    apply plus_resp_less_lft.
    assumption.
   eapply Feq_comp; try apply A3; try (apply Feq_reflexive; Included); assumption.
  eapply Feq_transitive.
   apply (FSeries_Sum_comp DomArTanH (olor Zero Two)); try assumption.
   Contin.
  assert (X:forall (x : IR) (Hx : Dom ([-C-]One{-}FId) x),
    DomArTanH x -> olor Zero Two (([-C-]One{-}FId) x Hx)).
   intros x Hx [C0 C1].
   simpl; split.
    apply shift_less_minus.
    rstepl (x:IR).
    assumption.
   rstepr (One[-][--]One:IR).
   apply plus_resp_less_lft.
   apply inv_resp_less.
   assumption.
  eapply Feq_comp; try apply A3; try (apply Feq_reflexive; Included); assumption.
 apply: mult_wdr.
 apply eq_symmetric.
 apply: Log_div.
Qed.
