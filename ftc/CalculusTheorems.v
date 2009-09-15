(* Copyright © 1998-2006
 * Henk Barendregt
 * Luís Cruz-Filipe
 * Herman Geuvers
 * Mariusz Giero
 * Rik van Ginneken
 * Dimitri Hendriks
 * Sébastien Hinderer
 * Bart Kirkels
 * Pierre Letouzey
 * Iris Loeb
 * Lionel Mamane
 * Milad Niqui
 * Russell O’Connor
 * Randy Pollack
 * Nickolay V. Shmyrev
 * Bas Spitters
 * Dan Synek
 * Freek Wiedijk
 * Jan Zwanenburg
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

Require Export Rolle.
Require Export DiffTactics3.

Opaque Min Max.

Section Various_Theorems.

(**
* Calculus Theorems

This file is intended to present a collection of miscellaneous, mostly
technical results in differential calculus that are interesting or
useful in future work.

We begin with some properties of continuous functions.  Every
continuous function commutes with the limit of a numerical sequence
(sometimes called Heine continuity).
*)

Lemma Continuous_imp_comm_Lim : forall F x e, Zero [<] e ->
 Continuous (clcr (Lim x[-]e) (Lim x[+]e)) F -> forall Hx Hxn H,
 F (Lim x) Hx [=] Lim (Build_CauchySeq IR (fun n => F (x n) (Hxn n)) H).
intros F x e H H0 Hx Hxn H1.
set (a := Lim x) in *.
set (I := clcr (a[-]e) (a[+]e)) in *.
cut (compact_ I). intro H2.
2: simpl in |- *.
2: apply less_leEq; apply less_transitive_unfolded with a.
2: apply shift_minus_less; apply shift_less_plus'.
2: astepl ZeroR; auto.
2: apply shift_less_plus'.
2: astepl ZeroR; auto.
apply Limits_unique.
simpl in |- *.
intros eps H3.
set (H2' := H2) in *.
cut (Continuous_I (a:=Lend H2) (b:=Rend H2) H2' F). intro H4.
2: apply Int_Continuous; auto.
elim (contin_prop _ _ _ _ H4 _ H3); intros d H5 H6.
elim (Cauchy_complete x (Min d e)).
2: apply less_Min; auto.
intros N HN.
exists N; intros.
fold a in HN.
apply AbsIR_imp_AbsSmall.
elim (HN m H7); intros.
apply H6.
split; simpl in |- *.
unfold cg_minus in |- *; apply shift_plus_leEq'.
eapply leEq_transitive.
2: apply H8.
apply inv_resp_leEq; apply Min_leEq_rht.
apply shift_leEq_plus'.
eapply leEq_transitive.
apply H9.
apply Min_leEq_rht.
split; simpl in |- *.
apply shift_minus_leEq; apply shift_leEq_plus'.
astepl ZeroR; apply less_leEq; auto.
apply shift_leEq_plus'; astepl ZeroR.
apply less_leEq; auto.
apply AbsSmall_imp_AbsIR.
apply AbsSmall_leEq_trans with (Min d e).
apply Min_leEq_lft.
auto.
Qed.

(**
This is a tricky result: if [F] is continuous and positive in both [[a,b]]
and [(b,c]], then it is positive in [[a,c]].
*)

Lemma Continuous_imp_pos : forall a b c (Hac : a [<=] c), a [<=] b -> b [<] c ->
 forall F, Continuous_I Hac F -> (forall t, a [<=] t -> t [<=] b -> forall Ht, Zero [<] F t Ht) ->
 (forall t, b [<] t -> t [<=] c -> forall Ht, Zero [<] F t Ht) -> forall t, a [<=] t -> t [<=] c -> forall Ht, Zero [<] F t Ht.
intros a b c Hac H H0 F H1 H2 H3 t H4 H5 Ht.
elim H1; intros H6 H7; clear H1.
cut (Compact Hac b); [ intro H1 | split; auto ].
2: apply less_leEq; auto.
set (e := F b (H6 _ H1) [/]TwoNZ) in *.
cut (Zero [<] e); intros.
2: unfold e in |- *; apply pos_div_two; apply H2; auto.
2: apply leEq_reflexive.
elim H7 with e; auto.
intros d H9 H10.
cut (b[-]d [<] b).
2: apply shift_minus_less; apply shift_less_plus'.
2: astepl ZeroR; auto.
intro H11.
elim (less_cotransitive_unfolded _ _ _ H11 t); intro.
clear H11.
elim (less_cotransitive_unfolded _ _ _ H9 (t[-]b)); intro.
apply H3.
astepl (Zero[+]b); apply shift_plus_less; auto.
auto.
apply cont_no_sign_change_pos with (Hab := Hac) (e := e) (Hx := H6 _ H1);
 auto.
split; auto.
apply H10; auto.
split; auto.
apply AbsSmall_imp_AbsIR.
apply AbsIR_eq_AbsSmall.
rstepr ( [--] (t[-]b)); apply inv_resp_leEq.
apply less_leEq; auto.
apply less_leEq; apply shift_minus_less; apply shift_less_plus'; auto.
unfold e in |- *.
eapply less_leEq_trans.
apply pos_div_two'.
apply H2; auto.
apply leEq_reflexive.
apply leEq_AbsIR.
unfold e in |- *.
apply pos_div_two'.
apply H2; auto.
apply leEq_reflexive.
apply H2; auto.
apply less_leEq; auto.
Qed.

(**
Similar results for increasing functions:
*)

Lemma strict_inc_glues : forall a b c F (Hab : a [<=] b) (Hbc : b [<=] c) (Hac : a [<=] c),
 included (Compact Hac) (Dom F) ->
 (forall x y, Compact Hab x -> Compact Hab y -> x [<] y -> forall Hx Hy, F x Hx [<] F y Hy) ->
 (forall x y, Compact Hbc x -> Compact Hbc y -> x [<] y -> forall Hx Hy, F x Hx [<] F y Hy) ->
 forall x y, Compact Hac x -> Compact Hac y -> x [<] y -> forall Hx Hy, F x Hx [<] F y Hy.
do 7 intro. intros H H0 H1 x y H2 H3 H4 Hx Hy.
cut (Dom F a); [ intro Ha | apply H; apply compact_inc_lft ].
cut (Dom F b); [ intro Hb | apply H; split; auto ].
cut (Dom F c); [ intro Hc | apply H; apply compact_inc_rht ].
elim (less_cotransitive_unfolded _ _ _ H4 b); intro.
cut (Dom F (Min b y)); [ intro H5 | apply H; split ].
2: apply leEq_Min; auto; elim H3; auto.
2: eapply leEq_transitive; [ apply Min_leEq_lft | auto ].
apply less_leEq_trans with (F _ H5).
cut (Dom F (Min ((x[+]b) [/]TwoNZ) y)); [ intro Hxy | apply H; split ].
3: elim H3; intros; eapply leEq_transitive; [ apply Min_leEq_rht | auto ].
2: apply leEq_Min.
3: elim H3; auto.
2: apply shift_leEq_div; [ apply pos_two | rstepl (a[+]a) ].
2: apply plus_resp_leEq_both; elim H2; auto.
apply less_leEq_trans with (F _ Hxy).
apply H0; try split.
elim H2; auto.
apply less_leEq; auto.
apply leEq_Min.
2: elim H3; auto.
apply shift_leEq_div; [ apply pos_two | rstepl (a[+]a) ].
apply plus_resp_leEq_both; elim H2; auto.
eapply leEq_transitive.
apply Min_leEq_lft.
apply shift_div_leEq; [ apply pos_two | rstepr (b[+]b) ].
apply plus_resp_leEq; apply less_leEq; auto.
apply less_Min; auto.
apply shift_less_div; [ apply pos_two | rstepl (x[+]x) ].
apply plus_resp_leEq_less; [ apply leEq_reflexive | auto ].
apply part_mon_imp_mon' with (Compact Hab); auto.
intros x0 H6; apply H; inversion_clear H6; split; auto.
apply leEq_transitive with b; auto.
split.
apply leEq_Min.
apply shift_leEq_div; [ apply pos_two | rstepl (a[+]a) ].
apply plus_resp_leEq_both; auto; elim H2; auto.
elim H3; auto.
eapply leEq_transitive.
apply Min_leEq_lft.
apply shift_div_leEq; [ apply pos_two | rstepr (b[+]b) ].
apply plus_resp_leEq; apply less_leEq; auto.
split.
apply leEq_Min; auto; elim H3; auto.
apply Min_leEq_lft.
apply leEq_Min.
eapply leEq_transitive.
apply Min_leEq_lft.
apply shift_div_leEq; [ apply pos_two | rstepr (b[+]b) ].
apply plus_resp_leEq; apply less_leEq; auto.
apply Min_leEq_rht.
rewrite leEq_def; intro H6.
cut (y [<=] b). intro H7.
apply (less_irreflexive_unfolded _ (F y Hy)).
eapply less_wdr.
apply H6.
apply pfwdef; eapply eq_transitive_unfolded.
apply Min_comm.
apply leEq_imp_Min_is_lft; auto.
rewrite leEq_def; intro H7.
apply (less_irreflexive_unfolded _ (F y Hy)).
eapply less_transitive_unfolded.
apply H6.
apply less_wdl with (F b Hb).
2: apply pfwdef; apply eq_symmetric_unfolded; apply leEq_imp_Min_is_lft;
    apply less_leEq; auto.
apply H1; auto.
apply compact_inc_lft.
split; [ apply less_leEq | elim H3 ]; auto.

cut (Dom F (Max b x)); [ intro H5 | apply H; split ].
3: apply Max_leEq; auto; elim H2; auto.
2: eapply leEq_transitive; [ apply Hab | apply lft_leEq_Max ].
apply leEq_less_trans with (F _ H5).
2: cut (Dom F (Max ((y[+]b) [/]TwoNZ) x)); [ intro Hxy | apply H; split ].
3: elim H2; intros; eapply leEq_transitive; [ apply a0 | apply rht_leEq_Max ].
3: apply Max_leEq.
4: elim H2; auto.
3: apply shift_div_leEq; [ apply pos_two | rstepr (c[+]c) ].
3: apply plus_resp_leEq_both; elim H3; auto.
2: apply leEq_less_trans with (F _ Hxy).
3: apply H1; try split.
6: elim H3; auto.
5: apply less_leEq; auto.
4: apply Max_leEq.
5: elim H2; auto.
4: apply shift_div_leEq; [ apply pos_two | rstepr (c[+]c) ].
4: apply plus_resp_leEq_both; elim H3; auto.
3: eapply leEq_transitive.
4: apply lft_leEq_Max.
3: apply shift_leEq_div; [ apply pos_two | rstepl (b[+]b) ].
3: apply plus_resp_leEq; apply less_leEq; auto.
3: apply Max_less; auto.
3: apply shift_div_less; [ apply pos_two | rstepr (y[+]y) ].
3: apply plus_resp_less_lft; auto.
2: apply part_mon_imp_mon' with (Compact Hbc); auto.
2: intros x0 H6; apply H; inversion_clear H6; split; auto.
2: apply leEq_transitive with b; auto.
3: split.
4: apply Max_leEq.
4: apply shift_div_leEq; [ apply pos_two | rstepr (c[+]c) ].
4: apply plus_resp_leEq_both; auto; elim H3; auto.
4: elim H2; auto.
3: eapply leEq_transitive.
4: apply lft_leEq_Max.
3: apply shift_leEq_div; [ apply pos_two | rstepl (b[+]b) ].
3: apply plus_resp_leEq; apply less_leEq; auto.
2: split.
3: apply Max_leEq; auto; elim H2; auto.
2: apply lft_leEq_Max.
2: apply Max_leEq.
2: eapply leEq_transitive.
3: apply lft_leEq_Max.
2: apply shift_leEq_div; [ apply pos_two | rstepl (b[+]b) ].
2: apply plus_resp_leEq; apply less_leEq; auto.
2: apply rht_leEq_Max.
rewrite leEq_def; intro H6.
cut (b [<=] x); rewrite leEq_def; intro H7.
apply (less_irreflexive_unfolded _ (F x Hx)).
eapply less_wdl.
apply H6.
apply pfwdef; apply leEq_imp_Max_is_rht; rewrite leEq_def; auto.
apply (less_irreflexive_unfolded _ (F x Hx)).
eapply less_transitive_unfolded.
2: apply H6.
apply less_wdr with (F b Hb).
2: apply pfwdef; apply eq_symmetric_unfolded; eapply eq_transitive_unfolded.
2: apply Max_comm.
2: apply leEq_imp_Max_is_rht; apply less_leEq; auto.
apply H0; auto.
2: apply compact_inc_rht.
split; [ elim H2 | apply less_leEq ]; auto.
Qed.

Lemma strict_inc_glues' : forall a b c F, a [<] b -> b [<] c -> included (olor a c) (Dom F) ->
 (forall x y, olcr a b x -> olcr a b y -> x [<] y -> forall Hx Hy, F x Hx [<] F y Hy) ->
 (forall x y, clor b c x -> clor b c y -> x [<] y -> forall Hx Hy, F x Hx [<] F y Hy) ->
 forall x y, olor a c x -> olor a c y -> x [<] y -> forall Hx Hy, F x Hx [<] F y Hy.
intros a b c F Hab Hbc H H0 H1 x y H2 H3 H4 Hx Hy.
cut (Dom F b); [ intro Hb | apply H; split; auto ].
elim (less_cotransitive_unfolded _ _ _ H4 b); intro.
cut (Dom F (Min b y)); [ intro H5 | apply H; split ].
2: apply less_Min; auto; elim H3; auto.
2: eapply leEq_less_trans; [ apply Min_leEq_lft | auto ].
apply less_leEq_trans with (F _ H5).
cut (Dom F (Min ((x[+]b) [/]TwoNZ) y)); [ intro Hxy | apply H; split ].
3: elim H3; intros; eapply leEq_less_trans; [ apply Min_leEq_rht | auto ].
2: apply less_Min.
3: elim H3; auto.
2: apply shift_less_div; [ apply pos_two | rstepl (a[+]a) ].
2: apply plus_resp_less_both; elim H2; auto.
apply less_leEq_trans with (F _ Hxy).
apply H0; try split.
elim H2; auto.
apply less_leEq; auto.
apply less_Min.
2: elim H3; auto.
apply shift_less_div; [ apply pos_two | rstepl (a[+]a) ].
apply plus_resp_less_both; elim H2; auto.
eapply leEq_transitive.
apply Min_leEq_lft.
apply shift_div_leEq; [ apply pos_two | rstepr (b[+]b) ].
apply plus_resp_leEq; apply less_leEq; auto.
apply less_Min; auto.
apply shift_less_div; [ apply pos_two | rstepl (x[+]x) ].
apply plus_resp_leEq_less; [ apply leEq_reflexive | auto ].
apply part_mon_imp_mon' with (iprop (olcr a b)); auto.
intros x0 H6; apply H; inversion_clear H6; split; auto.
apply leEq_less_trans with b; auto.
split.
apply less_Min.
apply shift_less_div; [ apply pos_two | rstepl (a[+]a) ].
apply plus_resp_less_both; auto; elim H2; auto.
elim H3; auto.
eapply leEq_transitive.
apply Min_leEq_lft.
apply shift_div_leEq; [ apply pos_two | rstepr (b[+]b) ].
apply plus_resp_leEq; apply less_leEq; auto.
split.
apply less_Min; auto; elim H3; auto.
apply Min_leEq_lft.
apply leEq_Min.
eapply leEq_transitive.
apply Min_leEq_lft.
apply shift_div_leEq; [ apply pos_two | rstepr (b[+]b) ].
apply plus_resp_leEq; apply less_leEq; auto.
apply Min_leEq_rht.
rewrite leEq_def; intro H6.
cut (y [<=] b); rewrite leEq_def; intro H7.
apply (less_irreflexive_unfolded _ (F y Hy)).
eapply less_wdr.
apply H6.
apply pfwdef; eapply eq_transitive_unfolded.
apply Min_comm.
apply leEq_imp_Min_is_lft; rewrite leEq_def; auto.
apply (less_irreflexive_unfolded _ (F y Hy)).
eapply less_transitive_unfolded.
apply H6.
apply less_wdl with (F b Hb).
2: apply pfwdef; apply eq_symmetric_unfolded; apply leEq_imp_Min_is_lft;
    apply less_leEq; auto.
apply H1; auto.
split; auto; apply leEq_reflexive.
split; [ apply less_leEq | elim H3 ]; auto.

cut (Dom F (Max b x)); [ intro H5 | apply H; split ].
3: apply Max_less; auto; elim H2; auto.
2: eapply less_leEq_trans; [ apply Hab | apply lft_leEq_Max ].
apply leEq_less_trans with (F _ H5).
2: cut (Dom F (Max ((y[+]b) [/]TwoNZ) x)); [ intro Hxy | apply H; split ].
3: elim H2; intros; eapply less_leEq_trans; [ apply a0 | apply rht_leEq_Max ].
3: apply Max_less.
4: elim H2; auto.
3: apply shift_div_less; [ apply pos_two | rstepr (c[+]c) ].
3: apply plus_resp_less_both; elim H3; auto.
2: apply leEq_less_trans with (F _ Hxy).
3: apply H1; try split.
6: elim H3; auto.
5: apply less_leEq; auto.
4: apply Max_less.
5: elim H2; auto.
4: apply shift_div_less; [ apply pos_two | rstepr (c[+]c) ].
4: apply plus_resp_less_both; elim H3; auto.
3: eapply leEq_transitive.
4: apply lft_leEq_Max.
3: apply shift_leEq_div; [ apply pos_two | rstepl (b[+]b) ].
3: apply plus_resp_leEq; apply less_leEq; auto.
3: apply Max_less; auto.
3: apply shift_div_less; [ apply pos_two | rstepr (y[+]y) ].
3: apply plus_resp_less_lft; auto.
2: apply part_mon_imp_mon' with (iprop (clor b c)); auto.
2: intros x0 H6; apply H; inversion_clear H6; split; auto.
2: apply less_leEq_trans with b; auto.
3: split.
4: apply Max_less.
4: apply shift_div_less; [ apply pos_two | rstepr (c[+]c) ].
4: apply plus_resp_less_both; auto; elim H3; auto.
4: elim H2; auto.
3: eapply leEq_transitive.
4: apply lft_leEq_Max.
3: apply shift_leEq_div; [ apply pos_two | rstepl (b[+]b) ].
3: apply plus_resp_leEq; apply less_leEq; auto.
2: split.
3: apply Max_less; auto; elim H2; auto.
2: apply lft_leEq_Max.
2: apply Max_leEq.
2: eapply leEq_transitive.
3: apply lft_leEq_Max.
2: apply shift_leEq_div; [ apply pos_two | rstepl (b[+]b) ].
2: apply plus_resp_leEq; apply less_leEq; auto.
2: apply rht_leEq_Max.
rewrite leEq_def; intro H6.
cut (b [<=] x); rewrite leEq_def; intro H7.
apply (less_irreflexive_unfolded _ (F x Hx)).
eapply less_wdl.
apply H6.
apply pfwdef; apply leEq_imp_Max_is_rht; rewrite leEq_def; auto.
apply (less_irreflexive_unfolded _ (F x Hx)).
eapply less_transitive_unfolded.
2: apply H6.
apply less_wdr with (F b Hb).
2: apply pfwdef; apply eq_symmetric_unfolded; eapply eq_transitive_unfolded.
2: apply Max_comm.
2: apply leEq_imp_Max_is_rht; apply less_leEq; auto.
apply H0; auto.
split; [ elim H2 | apply less_leEq ]; auto.
split; auto; apply leEq_reflexive.
Qed.

Lemma strict_dec_glues : forall a b c F (Hab : a [<=] b) (Hbc : b [<=] c) (Hac : a [<=] c),
 included (Compact Hac) (Dom F) ->
 (forall x y, Compact Hab x -> Compact Hab y -> y[<]x -> forall Hx Hy, F x Hx [<] F y Hy) ->
 (forall x y, Compact Hbc x -> Compact Hbc y -> y[<]x -> forall Hx Hy, F x Hx [<] F y Hy) ->
 forall x y, Compact Hac x -> Compact Hac y -> y[<]x -> forall Hx Hy, F x Hx [<] F y Hy.
intros.
apply inv_cancel_less.
astepl ( {--}F y Hy); astepr ( {--}F x Hx).
apply strict_inc_glues with a b c Hab Hbc Hac; auto.
intros; simpl in |- *; apply inv_resp_less; auto.
intros; simpl in |- *; apply inv_resp_less; auto.
Qed.

Lemma strict_dec_glues' : forall a b c F, a [<] b -> b [<] c -> included (olor a c) (Dom F) ->
 (forall x y, olcr a b x -> olcr a b y -> y[<]x -> forall Hx Hy, F x Hx [<] F y Hy) ->
 (forall x y, clor b c x -> clor b c y -> y[<]x -> forall Hx Hy, F x Hx [<] F y Hy) ->
 forall x y, olor a c x -> olor a c y -> y[<]x -> forall Hx Hy, F x Hx [<] F y Hy.
intros.
apply inv_cancel_less.
astepl ( {--}F y Hy); astepr ( {--}F x Hx).
apply strict_inc_glues' with a b c; auto.
intros; simpl in |- *; apply inv_resp_less; auto.
intros; simpl in |- *; apply inv_resp_less; auto.
Qed.

(** More on glueing intervals. *)

Lemma olor_pos_clor_nonneg : forall a b (F : PartIR),
 (forall x, olor a b x -> forall Hx, Zero [<] F x Hx) -> forall Ha,
 Zero [<=] F a Ha -> forall x, clor a b x -> forall Hx, Zero [<=] F x Hx.
intros a b F H Ha H0 x H1 Hx.
rewrite leEq_def; intros H2.
cut (Not (olor a b x)); intro H3.
cut (x [=] a). intro H4.
rewrite -> leEq_def in H0; apply H0.
eapply less_wdl; [ apply H2 | algebra ].
red in H3.
apply not_ap_imp_eq; intro H4.
inversion_clear H1.
elim (ap_imp_less _ _ _ H4); intros.
apply (less_irreflexive_unfolded _ a); apply leEq_less_trans with x; auto.
apply H3; split; auto.
apply (less_irreflexive_unfolded IR Zero);
 apply less_transitive_unfolded with (F x Hx); auto.
Qed.

Lemma olor_pos_olcr_nonneg : forall a b (F : PartIR),
 (forall x, olor a b x -> forall Hx, Zero [<] F x Hx) -> forall Hb,
 Zero [<=] F b Hb -> forall x, olcr a b x -> forall Hx, Zero [<=] F x Hx.
intros a b F H Ha H0 x H1 Hx.
rewrite leEq_def; intros H2.
cut (Not (olor a b x)); intro H3.
cut (x [=] b). intro H4.
rewrite -> leEq_def in H0; apply H0.
eapply less_wdl; [ apply H2 | algebra ].
red in H3.
apply not_ap_imp_eq; intro H4.
inversion_clear H1.
elim (ap_imp_less _ _ _ H4); intros.
apply H3; split; auto.
apply (less_irreflexive_unfolded _ b); apply less_leEq_trans with x; auto.
apply (less_irreflexive_unfolded IR Zero);
 apply less_transitive_unfolded with (F x Hx); auto.
Qed.

Lemma olor_pos_clcr_nonneg : forall a b (F : PartIR), a [<] b ->
 (forall x, olor a b x -> forall Hx, Zero [<] F x Hx) -> forall Ha, Zero [<=] F a Ha -> forall Hb, Zero [<=] F b Hb ->
 forall x, clcr a b x -> forall Hx, Zero [<=] F x Hx.
intros a b F Hab H Ha H0 Hb H1 x H2 Hx.
rewrite leEq_def; intros H3.
cut (Not (olor a b x)); intro H4.
elim (less_cotransitive_unfolded _ _ _ Hab x); intro H5.
cut (x [=] b). intro H6.
rewrite -> leEq_def in H1; apply H1.
eapply less_wdl; [ apply H3 | algebra ].
red in H4.
apply not_ap_imp_eq; intro H6.
inversion_clear H2.
elim (ap_imp_less _ _ _ H6); intros.
apply H4; split; auto.
apply (less_irreflexive_unfolded _ b); apply less_leEq_trans with x; auto.
cut (x [=] a); intros.
rewrite -> leEq_def in H0; apply H0.
eapply less_wdl; [ apply H3 | algebra ].
red in H4.
apply not_ap_imp_eq; intro.
inversion_clear H2.
elim (ap_imp_less _ _ _ X); intros.
apply (less_irreflexive_unfolded _ a); apply leEq_less_trans with x; auto.
apply H4; split; auto.
apply (less_irreflexive_unfolded IR Zero);
 apply less_transitive_unfolded with (F x Hx); auto.
Qed.

(**
Any function that has the null function as its derivative must be constant.
*)

Lemma FConst_prop : forall J pJ F', Derivative J pJ F' [-C-]Zero -> {c : IR | Feq J F' [-C-]c}.
intros J pJ F' H.
elim (nonvoid_point _ (proper_nonvoid _ pJ)); intros x0 Hx0.
exists (F' x0 (Derivative_imp_inc _ _ _ _ H x0 Hx0)).
FEQ. rename X into H0.
simpl in |- *.
apply cg_inv_unique_2.
apply AbsIR_approach_zero; intros e H1.
simpl in Hx'.
elim (Law_of_the_Mean _ _ _ _ H _ _ Hx0 H0 e H1).
intros y H2 H3.
eapply leEq_wdl.
apply (H3 (Derivative_imp_inc _ _ _ _ H _ Hx0) Hx CI).
apply AbsIR_wd; simpl in |- *; rational.
Qed.

(** As a corollary, two functions with the same derivative must differ
by a constant.
*)

Lemma Feq_crit_with_const : forall J pJ F G H,
 Derivative J pJ F H -> Derivative J pJ G H -> {c : IR | Feq J (F{-}G) [-C-]c}.
intros.
apply FConst_prop with pJ.
Derivative_Help; FEQ.
Qed.

(** This yields the following known result: any differential equation
of the form [f'=g] with initial condition [f(a) [=] b] has a unique solution.
*)

Lemma Feq_criterium : forall J pJ F G H, Derivative J pJ F H -> Derivative J pJ G H ->
 forall x, J x -> (forall Hx Hx', F x Hx [=] G x Hx') -> Feq J F G.
do 5 intro. intros H0 H1 x H2 H3.
elim (Feq_crit_with_const _ _ _ _ _ H0 H1); intros c Hc.
apply Feq_transitive with (F{-}G{+}G).
FEQ.
apply Feq_transitive with ( [-C-]Zero{+}G).
2: FEQ.
apply Feq_plus.
2: apply Feq_reflexive; Included.
apply Feq_transitive with ( [-C-]c).
auto.
FEQ. rename X into H4.
simpl in |- *.
elim Hc; intros H5 H6.
elim H6; clear H6; intros H7 H6.
clear Hc H5 H7 Hx' Hx.
simpl in H6.
cut (Conj (Dom F) (Dom G) x). intro H5.
apply eq_symmetric_unfolded; eapply eq_transitive_unfolded.
2: apply H6 with (Hx := H5); auto.
apply eq_symmetric_unfolded; apply x_minus_x; auto.
split.
exact (Derivative_imp_inc _ _ _ _ H0 _ H2).
exact (Derivative_imp_inc _ _ _ _ H1 _ H2).
Qed.

(**
Finally, a well known result: any function with a (strictly) positive
derivative is (strictly) increasing.  Although the two lemmas look
quite similar the proofs are completely different, both from the
formalization and from the mathematical point of view.
*)

Lemma Derivative_imp_resp_less : forall J pJ a b F F', Derivative J pJ F F' ->
 a [<] b -> J a -> J b -> (forall contF', Zero [<] glb_funct _ _ (Min_leEq_Max a b) F' contF') ->
 forall Ha Hb, F a Ha [<] F b Hb.
intros J pJ a b F F' derF Hab HaJ HbJ Hglb Ha Hb.
apply shift_zero_less_minus'.
cut (Continuous_I (Min_leEq_Max a b) F'). intro H.
2: apply included_imp_Continuous with J;
    [ apply Derivative_imp_Continuous' with pJ F | apply included_interval ];
    auto.
elim (glb_is_glb _ _ _ _ H).
simpl in |- *; intros Hglb1 Hglb2.
cut (Zero [<] glb_funct _ _ _ _ H); [ intro H0 | auto ].
elim
 (Law_of_the_Mean _ _ _ _ derF a b)
  with (e := (glb_funct _ _ _ _ H[*] (b[-]a)) [/]TwoNZ); 
 auto.
intros x H1 H2.
apply
 less_leEq_trans
  with
    (F' x (contin_imp_inc _ _ _ _ H x H1) [*] (b[-]a) [-]
     (glb_funct _ _ _ _ H[*] (b[-]a)) [/]TwoNZ).
rstepr
 ((F' x (contin_imp_inc _ _ _ _ H x H1) [-]glb_funct _ _ _ _ H [/]TwoNZ) [*]
  (b[-]a)).
apply mult_resp_pos.
apply shift_less_minus; astepl (glb_funct _ _ _ _ H [/]TwoNZ).
eapply less_leEq_trans.
apply pos_div_two'; auto.
apply glb_prop.
auto.
apply shift_less_minus; astepl a; auto.
apply shift_minus_leEq; apply shift_leEq_plus'.
rstepl
 ( [--]
  (Part _ _ Hb[-]Part _ _ Ha[-]
   Part _ _ (contin_imp_inc _ _ _ _ H _ H1) [*] (b[-]a))).
eapply leEq_transitive.
apply inv_leEq_AbsIR.
apply H2.
apply pos_div_two; apply mult_resp_pos; auto.
apply shift_less_minus; astepl a; auto.
Qed.

Lemma Derivative_imp_resp_leEq : forall J pJ a b F F', Derivative J pJ F F' ->
 a [<=] b -> J a -> J b -> (forall contF', Zero [<=] glb_funct _ _ (Min_leEq_Max b a) F' contF') ->
 forall Ha Hb, F a Ha [<=] F b Hb.
intros J pJ a b F F' derF Hab HaJ HbJ Hglb Ha Hb.
astepr (Zero[+]Part _ _ Hb); apply shift_leEq_plus.
cut (Continuous_I (Min_leEq_Max b a) F'). intro H.
2: apply included_imp_Continuous with J;
    [ apply Derivative_imp_Continuous' with pJ F | apply included_interval ];
    auto.
elim (glb_is_glb _ _ _ _ H).
simpl in |- *; intros Hglb1 Hglb2.
cut (Zero [<=] glb_funct _ _ _ _ H); [ intro H0 | auto ].
apply approach_zero_weak.
intros.
elim (Law_of_the_Mean _ _ _ _ derF b a) with (e := e); auto.
intros x H2 H3.
eapply leEq_transitive.
2: apply (H3 Hb Ha (contin_imp_inc _ _ _ _ H x H2)).
eapply leEq_transitive.
2: apply leEq_AbsIR.
rstepl (Part _ _ Ha[-]Part _ _ Hb[-][--]Zero).
unfold cg_minus at 1 3 in |- *; apply plus_resp_leEq_lft.
apply inv_resp_leEq.
rstepl ( [--] (Part _ _ (contin_imp_inc _ _ _ _ H _ H2) [*] (b[-]a))).
apply inv_resp_leEq.
apply mult_resp_nonneg.
eapply leEq_transitive; [ apply H0 | apply Hglb1 ].
exists x.
split. auto.
split; algebra.
apply (contin_imp_inc _ _ _ _ H); auto.
apply shift_leEq_minus; astepl a; auto.
Qed.

Lemma Derivative_imp_resp_less' : forall J pJ a b F F', Derivative J pJ F F' ->
 a [<] b -> J a -> J b -> (forall contF', Zero [<=] glb_funct _ _ (Min_leEq_Max b a) F' contF') ->
 forall Ha Hb, F a Ha [#] F b Hb -> F a Ha [<] F b Hb.
intros J pJ a b F F' H H0 H1 H2 H3 Ha Hb H4.
elim (ap_imp_less _ _ _ H4); intro; auto.
elimtype False.
apply less_irreflexive_unfolded with (x := F a Ha).
apply leEq_less_trans with (F b Hb); auto.
apply Derivative_imp_resp_leEq with J pJ F'; auto.
apply less_leEq; auto.
Qed.

(** From these results we can finally prove that exponentiation to a
real power preserves the less or equal than relation!
*)

Lemma nexp_resp_leEq_odd : forall n, odd n -> forall x y : IR, x [<=] y -> x[^]n [<=] y[^]n.
intro; case n.
intros; elimtype False; inversion H.
clear n; intros.
astepl (Part (FId{^}S n) x CI).
astepr (Part (FId{^}S n) y CI).
apply
 Derivative_imp_resp_leEq with realline CI (nring (R:=IR) (S n) {**}FId{^}n).
Opaque nring.
Derivative_Help.
FEQ.
Transparent nring.
auto.
split.
split.
intros.
apply leEq_glb; intros.
simpl in |- *.
apply mult_resp_nonneg.
apply less_leEq; eapply leEq_less_trans.
2: apply less_plusOne.
apply nring_nonneg.
astepr (y0[^]n); apply nexp_even_nonneg.
inversion H; auto.
Qed.

End Various_Theorems.
