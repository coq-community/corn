(*
Copyright © 2006-2008 Russell O’Connor

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

Require Import CoRN.ftc.FTC.
Require Export CoRN.ftc.Composition.

(**
** Integration by substitution
Here we prove integration by substition. Simply put, this lemma shows that
int((F[o]G)*G', a .. b) = int(F, G(a) .. G(b)), assuming that
G is differentiable on [[c, d]] and that
F is continuous on [[c0, d0]] and that G maps compact intervals into [[c0, d0]].
*)

Lemma IntegrationBySubstition :
 forall a b
 (Hab: Min a b[<=]Max a b)
 c d (Hcd: c[<]d)
 (Habcd: included (Compact Hab) (Compact (less_leEq _ _ _ Hcd)))
 G (HGa: Dom G a) (HGb: Dom G b)
 G' (HGG': Derivative_I Hcd G G')
 (HGaGb: Min (G a HGa) (G b HGb)[<=]Max (G a HGa) (G b HGb))
 F
 c0 d0 (Hc0d0: c0[<=]d0)
 (HGF: maps_into_compacts G F _ _ Hab _ _ Hc0d0)
 (HFG: Continuous_I Hab ((F[o]G){*}G'))
 (HF: Continuous_I HGaGb F)
 (HFc0d0: Continuous_I Hc0d0 F),
 Integral HFG[=]Integral HF.
Proof.
 intros.
 assert(X1:=leEq_less_or_equal _ _ _ Hab).
 apply not_ap_imp_eq.
 intros X0.
 apply X1.
 clear X1.
 intros X1.
 revert X0.
 apply (eq_imp_not_ap).
 destruct X1 as [X1|X1].
  assert(X:=leEq_less_or_equal _ _ _ Hc0d0).
  apply not_ap_imp_eq.
  intros X0.
  apply X.
  clear X.
  intros X.
  revert X0.
  apply (eq_imp_not_ap).
  destruct X as [X|X].
   set (J:=clcr c0 d0).
   assert (HFJ:Continuous J F).
    eapply (Continuous_Int J Hc0d0 Hc0d0); apply HFc0d0.
   assert (Jc0:J c0).
    split.
     apply leEq_reflexive.
    assumption.
   set (F0:=([-S-]HFJ) _ Jc0).
   assert (dF : Derivative J X F0 F).
    unfold F0; apply FTC1.
   apply eq_symmetric.
   assert (HF':Continuous_I (Min_leEq_Max (G a HGa) (G b HGb)) F).
    Contin.
   apply eq_transitive with (Integral HF').
    apply Integral_wd'; apply eq_reflexive.
   set (FGx:=Derivative_imp_inc J X F0 F dF).
   assert (JGa:J (G a HGa)).
    destruct HGF as [HGF0 HGF1].
    change (Compact Hc0d0 (G a HGa)).
    apply HGF1.
    apply compact_Min_lft.
   assert (JGb:J (G b HGb)).
    destruct HGF as [HGF0 HGF1].
    change (Compact Hc0d0 (G b HGb)).
    apply HGF1.
    apply compact_Min_rht.
   apply eq_transitive with ((F0 (G b HGb) (FGx _ JGb))[-](F0 (G a HGa) (FGx _ JGa))).
    unfold FGx.
    apply Barrow.
    apply HFJ.
   apply eq_symmetric.
   assert (HFG':Continuous_I (Min_leEq_Max a b) ((F[o]G){*}G')).
    Contin.
   apply eq_transitive with (Integral HFG').
    apply Integral_wd'; apply eq_reflexive.
   set (I:=clcr (Min a b) (Max a b)).
   assert (dFG:Derivative I X1 (F0[o]G) ((F[o]G){*}G')).
    apply (Derivative_Int I Hab X1 X1).
    assert (dF0 : Derivative_I X F0 F).
     apply (Int_Derivative J Hc0d0 X).
     assumption.
    eapply Derivative_I_comp.
      eapply (included_imp_deriv _ _ Hcd).
       apply Habcd.
      apply HGG'.
     apply dF0.
    destruct HGF as [HGF0 HGF1].
    split.
     Included.
    exact HGF1.
   set (HFGx := Derivative_imp_inc I X1 _ _ dFG).
   stepr (((F0[o]G) b (HFGx b (compact_Min_rht _ _ Hab)))[-]
     ((F0[o]G) a (HFGx a (compact_Min_lft _ _ Hab)))).
    unfold HFGx.
    apply Barrow.
    eapply (Continuous_Int I Hab Hab).
    apply HFG.
   generalize (HFGx a (compact_Min_lft a b Hab)) (HFGx b (compact_Min_rht a b Hab)).
   generalize (FGx (G b HGb) JGb) (FGx (G a HGa) JGa).
   generalize F0 G HGb HGa.
   clear -a b.
   intros F G p1 p2 p3 p4 p5 p6.
   simpl.
   algebra.
  assert (Y:G a HGa[=]G b HGb).
   destruct HGF as [HGF0 HGF1].
   apply leEq_imp_eq.
    apply leEq_transitive with d0.
     destruct (HGF1 _ HGa (compact_Min_lft _ _ Hab)); assumption.
    stepl c0; [| assumption].
    destruct (HGF1 _ HGb (compact_Min_rht _ _ Hab)); assumption.
   apply leEq_transitive with d0.
    destruct (HGF1 _ HGb (compact_Min_rht _ _ Hab)); assumption.
   stepl c0; [| assumption].
   destruct (HGF1 _ HGa (compact_Min_lft _ _ Hab)); assumption.
  stepl ([0]:IR).
   apply eq_symmetric; apply Integral_empty.
   assumption.
  assert (Z:(Continuous_I Hab [-C-][0])).
   Contin.
  stepr (Integral Z).
   rstepl ([0][*](b[-]a)).
   apply eq_symmetric.
   apply Integral_const.
  apply Integral_wd.
  FEQ.
  simpl.
  simpl in Hx'.
  apply eq_symmetric.
  apply x_mult_zero.
  change ([0]:IR) with ([-C-][0] x I).
  apply Feq_imp_eq with (I:=Compact (less_leEq _ _ _ X1)); auto.
  apply Derivative_I_unique with G.
   eapply included_imp_deriv;[|apply HGG'].
   auto.
  apply Derivative_I_wdl with ([-C-](G a HGa)); [|apply Derivative_I_const].
  FEQ.
   eapply included_trans.
    apply Habcd.
   eapply derivative_imp_inc.
   apply HGG'.
  rename H0 into X2. destruct HGF as [HGF0 HGF1].
  simpl.
  apply leEq_imp_eq.
   apply leEq_transitive with d0.
    destruct (HGF1 _ HGa (compact_Min_lft _ _ Hab)); assumption.
   stepl c0; [| assumption].
   destruct (HGF1 _ Hx'0 X2); assumption.
  apply leEq_transitive with d0.
   destruct (HGF1 _ Hx'0 X2); assumption.
  stepl c0; [| assumption].
  destruct (HGF1 _ HGa (compact_Min_lft _ _ Hab)); assumption.
 assert (Hab':a[=]b).
  apply not_ap_imp_eq.
  intros X0.
  apply (eq_imp_not_ap _ _ _ X1).
  apply less_imp_ap.
  apply ap_imp_Min_less_Max.
  assumption.
 apply eq_transitive with ([0]:IR).
  apply Integral_empty.
  assumption.
 apply eq_symmetric.
 apply Integral_empty.
 algebra.
Qed.

(** This lemma is a special instance of substituion that ties
 integration on [[0, 1]] with general integration on [[a, b]].
 It says that int(F((b-a)*x+a), x=0 .. 1) = int(F, a .. b).
*)

Lemma IntegrationSubs01 : forall a b
 (Hab: Min a b[<=]Max a b)
 (H01: [0][<=][1])
 F
 (HFG: Continuous_I H01 ((F[o]([-C-](b[-]a){*}(Fid IR){+}[-C-]a))))
 (HF: Continuous_I Hab F),
 (b[-]a)[*]integral _ _ _ _ HFG[=]Integral HF.
Proof.
 intros.
 assert (HFG0:Continuous_I (a:=[0]) (b:=[1]) H01 ((b[-]a){**}(F[o][-C-](b[-]a){*}FId{+}[-C-]a))).
  Contin.
 stepr (integral _ _ _ _ HFG0).
  apply eq_symmetric.
  apply integral_comm_scal.
 assert (HFG1:Continuous_I (a:=[0]) (b:=[1]) H01 ((F[o][-C-](b[-]a){*}FId{+}[-C-]a){*}[-C-](b[-]a))).
  Contin.
 stepr (integral _ _ _ _ HFG1).
  apply integral_wd.
  FEQ.
 assert (H01':Min [0] [1][<=]Max [0] [1]).
  apply Min_leEq_Max.
 assert (HFG2:Continuous_I H01' ((F[o][-C-](b[-]a){*}FId{+}[-C-]a){*}[-C-](b[-]a))).
  apply (included_imp_contin _ _ H01).
   apply included2_compact.
    apply compact_inc_lft.
   apply compact_inc_rht.
  assumption.
 stepr (Integral HFG2).
  apply eq_symmetric.
  apply Integral_integral.
 clear - H01.
 set (G:=[-C-](b[-]a){*}FId{+}[-C-]a) in *.
 assert (HG0 : Dom G [0]).
  repeat constructor.
 assert (HG1 : Dom G [1]).
  repeat constructor.
 assert (Hab':Min (G [0] HG0) (G [1] HG1)[<=]Max (G [0] HG0) (G [1] HG1)).
  apply Min_leEq_Max.
 assert (HF':Continuous_I Hab' F).
  apply (included_imp_contin _ _ Hab).
   unfold G.
   apply included2_compact.
    apply (compact_wd _ _ Hab a).
     apply compact_Min_lft.
    simpl.
    rational.
   apply (compact_wd _ _ Hab b).
    apply compact_Min_rht.
   simpl.
   rational.
  assumption.
 stepl (Integral HF').
  apply Integral_wd'; simpl; rational.
 apply eq_symmetric.
 assert (X:included (Compact H01') (Compact (less_leEq _ _ _ (pos_one IR)))).
  apply included2_compact.
   apply compact_inc_lft.
  apply compact_inc_rht.
 eapply (IntegrationBySubstition).
    apply X.
   unfold G.
   New_Deriv.
    apply Feq_reflexive.
    repeat constructor.
   apply (included_Feq (Compact (less_leEq IR [0] [1] (pos_one IR))) realline).
    repeat constructor.
   FEQ.
  split.
   apply contin_imp_inc.
   apply HF'.
  intros x Hx [H0 H1].
  assert (H0':[0][<=]x).
   stepl (Min [0] [1]);[assumption|].
   apply leEq_imp_Min_is_lft.
   apply (less_leEq _ _ _ (pos_one IR)).
  assert (H1':x[<=][1]).
   stepr (Max [0] [1]);[assumption|].
   apply leEq_imp_Max_is_rht.
   apply (less_leEq _ _ _ (pos_one IR)).
  unfold G.
  simpl.
  split.
   stepl (Min a b); [| apply MIN_wd; rational].
   assert (Z:=leEq_or_leEq _ a b).
   rewrite -> leEq_def.
   intros Z0.
   apply Z.
   clear Z.
   intros Z.
   revert Z0.
   change (Not ((b[-]a)[*]x[+]a[<]Min a b)).
   rewrite <- leEq_def.
   destruct Z.
    stepl a; [| apply eq_symmetric; apply leEq_imp_Min_is_lft; auto].
    apply shift_leEq_plus.
    rstepl ([0]:IR).
    apply mult_resp_nonneg; auto.
    apply shift_leEq_lft.
    assumption.
   stepl (Min b a); [| apply Min_comm].
   stepl b; [| apply eq_symmetric; apply leEq_imp_Min_is_lft; auto].
   apply shift_leEq_plus.
   apply shift_leEq_rht.
   rstepr ((a[-]b)[*]([1][-]x)).
   apply mult_resp_nonneg; apply shift_leEq_lft; assumption.
  stepr (Max a b); [| apply MAX_wd;rational].
  assert (Z:=leEq_or_leEq _ a b).
  rewrite -> leEq_def.
  intros Z0.
  apply Z.
  clear Z.
  intros Z.
  revert Z0.
  change (Not (Max a b[<](b[-]a)[*]x[+]a)).
  rewrite <- leEq_def.
  destruct Z.
   stepr b; [| apply eq_symmetric; apply leEq_imp_Max_is_rht; auto].
   apply shift_plus_leEq.
   apply shift_leEq_rht.
   rstepr ((b[-]a)[*]([1][-]x)).
   apply mult_resp_nonneg; apply shift_leEq_lft; assumption.
  stepr (Max b a); [| apply Max_comm].
  stepr a; [| apply eq_symmetric; apply leEq_imp_Max_is_rht; auto].
  apply shift_plus_leEq.
  rstepr ([0]:IR).
  apply shift_leEq_rht.
  rstepr ((a[-]b)[*]x).
  apply mult_resp_nonneg; auto.
  apply shift_leEq_lft.
  assumption.
 assumption.
Qed.
