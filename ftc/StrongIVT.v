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

Require Export WeakIVT.
Require Export CalculusTheorems.

Section IVT'.

(**
** Strong IVT for partial functions

The IVT can be generalized to arbitrary partial functions; in the first
part, we will simply do that, repeating the previous construction.

The same notations and conventions apply as before.
*)

Variables a b : IR.
Hypothesis Hab' : a [<] b.
Hypothesis Hab : a [<=] b.

(* begin hide *)
Let I := Compact Hab.
Let I' := olor a b.
(* end hide *)

Variable F : PartIR.
Hypothesis contF : Continuous_I Hab F.
(* begin hide *)
Let incF := contin_imp_inc _ _ _ _ contF.
(* end hide *)

(* begin show *)
Hypothesis incrF : forall x y, I x -> I y -> x [<] y -> forall Hx Hy, F x Hx [<] F y Hy.
(* end show *)

(* begin hide *)
Let Ha := compact_inc_lft _ _ Hab.
Let Hb := compact_inc_rht _ _ Hab.

Let HFab' := incrF _ _ Ha Hb Hab' (incF _ Ha) (incF _ Hb).
(* end hide *)

(* begin show *)
Variable z : IR.
Hypothesis Haz : F a (incF _ Ha) [<] z.
Hypothesis Hzb : z [<] F b (incF _ Hb).
(* end show *)

Lemma IVT'_seq_lemma : forall (xy : IR ** IR) (x:=fstT xy) (y:=sndT xy)
 (Hxy : (I x) ** (I y)) (Hx:=fstT Hxy) (Hy:=sndT Hxy),
 x [<] y -> F x (incF _ Hx) [<] z and z [<] F y (incF _ Hy) ->
 {xy0 : IR ** IR | let x0 := fstT xy0 in let y0 := sndT xy0 in
 {Hxy0 : (I x0) ** (I y0) | let Hx0 := fstT Hxy0 in let Hy0 := sndT Hxy0 in
 x0 [<] y0 and F x0 (incF _ Hx0) [<] z and z [<] F y0 (incF _ Hy0) |
 y0[-]x0 [=] Two [/]ThreeNZ[*] (y[-]x) /\ x [<=] x0 /\ y0 [<=] y}}.
Proof.
 (* begin hide *)
 do 6 intro. intros H H0.
 set (x1 := (Two[*]x[+]y) [/]ThreeNZ) in *.
 set (y1 := (x[+]Two[*]y) [/]ThreeNZ) in *.
 cut (x1 [<] y1). intro H1.
  2: unfold x1, y1 in |- *; apply lft_rht; auto.
 cut (I x1). intro H2.
  cut (I y1). intro H3.
   cut (F x1 (incF _ H2) [<] F y1 (incF _ H3)); [ intro H4 | auto ].
   elim (less_cotransitive_unfolded _ _ _ H4 z); intros.
    exists (pairT x1 y); exists (pairT H2 Hy); simpl in |- *; repeat split; auto.
        apply less_transitive_unfolded with y1; unfold x1, y1 in |- *; [ apply lft_rht | apply rht_b ]; auto.
       auto.
       elim H0; auto.
      unfold x1 in |- *; apply smaller_rht.
     unfold x1 in |- *; apply less_leEq; apply a_lft; auto.
    apply leEq_reflexive.
   exists (pairT x y1); exists (pairT Hx H3); simpl in |- *; repeat split; auto.
       apply less_transitive_unfolded with x1; unfold x1, y1 in |- *; [ apply a_lft | apply lft_rht ]; auto.
      elim H0; auto.
     unfold y1 in |- *; apply smaller_lft; auto.
    apply leEq_reflexive.
   apply less_leEq; unfold y1 in |- *; apply rht_b; auto.
  unfold y1 in |- *; inversion_clear Hx; inversion_clear Hy; split.
   apply leEq_transitive with x; auto.
   apply less_leEq; apply less_transitive_unfolded with x1; unfold x1 in |- *;
     [ apply a_lft | apply lft_rht ]; auto.
  apply leEq_transitive with y; auto.
  apply less_leEq; apply rht_b; auto.
 unfold x1 in |- *; inversion_clear Hx; inversion_clear Hy; split.
  apply leEq_transitive with x; auto.
  apply less_leEq; apply a_lft; auto.
 apply leEq_transitive with y; auto.
 apply less_leEq; apply less_transitive_unfolded with y1; unfold y1 in |- *;
   [ apply lft_rht | apply rht_b ]; auto.
Qed.
(* end hide *)

Record IVT'_aux_seq_type : Type :=
  {IVT'seq1 : IR;
   IVT'seq2 : IR;
   IVT'H1   : I IVT'seq1;
   IVT'H2   : I IVT'seq2;
   IVT'prf  : IVT'seq1 [<] IVT'seq2;
   IVT'z1   : F IVT'seq1 (incF _ IVT'H1) [<] z;
   IVT'z2   : z [<] F IVT'seq2 (incF _ IVT'H2)}.

Definition IVT'_iter : IVT'_aux_seq_type -> IVT'_aux_seq_type.
Proof.
 intro Haux; elim Haux; intros.
 elim (IVT'_seq_lemma (pairT IVT'seq3 IVT'seq4) (pairT IVT'H3 IVT'H4) IVT'prf0
   (CAnd_intro _ _ IVT'z3 IVT'z4)).
 intro x; elim x; simpl in |- *; clear x; intros.
 elim p.
 intro x; elim x; simpl in |- *; clear x; intros.
 inversion_clear p0.
 inversion_clear X0.
 inversion_clear q.
 inversion_clear H0.
 apply Build_IVT'_aux_seq_type with a0 b0 a1 b1; auto.
Defined.

Definition IVT'_seq : nat -> IVT'_aux_seq_type.
Proof.
 intro n; induction  n as [| n Hrecn].
  apply Build_IVT'_aux_seq_type with a b Ha Hb; auto.
 apply (IVT'_iter Hrecn).
Defined.

Definition a'_seq n := IVT'seq1 (IVT'_seq n).
Definition b'_seq n := IVT'seq2 (IVT'_seq n).

Definition a'_seq_I n : I (a'_seq n) := IVT'H1 (IVT'_seq n).
Definition b'_seq_I n : I (b'_seq n) := IVT'H2 (IVT'_seq n).

Lemma a'_seq_less_b'_seq : forall n, a'_seq n [<] b'_seq n.
Proof.
 exact (fun n => IVT'prf (IVT'_seq n)).
Qed.

Lemma a'_seq_less_z : forall n, F _ (incF _ (a'_seq_I n)) [<] z.
Proof.
 exact (fun n => IVT'z1 (IVT'_seq n)).
Qed.

Lemma z_less_b'_seq : forall n, z [<] F _ (incF _ (b'_seq_I n)).
Proof.
 exact (fun n => IVT'z2 (IVT'_seq n)).
Qed.

Lemma a'_seq_mon : forall i : nat, a'_seq i [<=] a'_seq (S i).
Proof.
 intro.
 unfold a'_seq in |- *.
 simpl in |- *.
 elim (IVT'_seq i); simpl in |- *; intros.
 elim IVT'_seq_lemma; simpl in |- *; intro.
 elim x; simpl in |- *; clear x; intros.
 elim p; clear p; intro.
 elim x; simpl in |- *; clear x; intros.
 case q; clear q; simpl in |- *; intros.
 case a2; clear a2; simpl in |- *; intros.
 elim p; clear p; simpl in |- *; intros.
 elim b2; clear b2; simpl in |- *; auto.
Qed.

Lemma b'_seq_mon : forall i : nat, b'_seq (S i) [<=] b'_seq i.
Proof.
 intro.
 unfold b'_seq in |- *.
 simpl in |- *.
 elim (IVT'_seq i); simpl in |- *; intros.
 elim IVT'_seq_lemma; simpl in |- *; intro.
 elim x; simpl in |- *; clear x; intros.
 elim p; clear p; intro.
 elim x; simpl in |- *; clear x; intros.
 case q; clear q; simpl in |- *; intros.
 case a2; clear a2; simpl in |- *; intros.
 elim p; clear p; simpl in |- *; intros.
 elim b2; clear b2; simpl in |- *; auto.
Qed.

Lemma a'_seq_b'_seq_dist_n : forall n,
 b'_seq (S n) [-]a'_seq (S n) [=] Two [/]ThreeNZ[*] (b'_seq n[-]a'_seq n).
Proof.
 intro.
 unfold a'_seq, b'_seq in |- *.
 simpl in |- *.
 elim (IVT'_seq n); simpl in |- *; intros.
 elim IVT'_seq_lemma; simpl in |- *; intro.
 elim x; simpl in |- *; clear x; intros.
 elim p; clear p; intro.
 elim x; simpl in |- *; clear x; intros.
 case q; clear q; simpl in |- *; intros.
 case a2; clear a2; simpl in |- *; intros.
 elim p; clear p; simpl in |- *; intros.
 elim b2; clear b2; simpl in |- *; auto.
Qed.

Lemma a'_seq_b'_seq_dist : forall n, b'_seq n[-]a'_seq n [=] (Two [/]ThreeNZ) [^]n[*] (b[-]a).
Proof.
 simple induction n.
  simpl in |- *; algebra.
 clear n; intros.
 astepr (Two [/]ThreeNZ[*] (Two [/]ThreeNZ) [^]n[*] (b[-]a)).
 astepr (Two [/]ThreeNZ[*] ((Two [/]ThreeNZ) [^]n[*] (b[-]a))).
 astepr (Two [/]ThreeNZ[*] (b'_seq n[-]a'_seq n)).
 apply a'_seq_b'_seq_dist_n.
Qed.

Lemma a'_seq_Cauchy : Cauchy_prop a'_seq.
Proof.
 intros e H.
 elim (intervals_small' a b e H); intros i Hi.
 exists i; intros.
 apply AbsIR_imp_AbsSmall.
 eapply leEq_transitive.
  2: apply Hi.
 eapply leEq_wdl.
  2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
  2: apply shift_leEq_minus; astepl (a'_seq i).
  2: apply local_mon'_imp_mon'; auto; exact a'_seq_mon.
 eapply leEq_wdr.
  2: apply a'_seq_b'_seq_dist.
 apply minus_resp_leEq.
 apply less_leEq; apply a_b'.
   exact a'_seq_mon.
  exact b'_seq_mon.
 exact a'_seq_less_b'_seq.
Qed.

Lemma b'_seq_Cauchy : Cauchy_prop b'_seq.
Proof.
 intros e H.
 elim (intervals_small' a b e H); intros i Hi.
 exists i; intros.
 apply AbsIR_imp_AbsSmall.
 eapply leEq_transitive.
  2: apply Hi.
 eapply leEq_wdl.
  2: apply AbsIR_minus.
 eapply leEq_wdl.
  2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
  2: apply shift_leEq_minus; astepl (b'_seq m).
  2: astepl ( [--][--] (b'_seq m)); astepr ( [--][--] (b'_seq i)).
  2: apply inv_resp_leEq; apply local_mon'_imp_mon' with (f := fun n => [--] (b'_seq n)); auto.
  2: intro; apply inv_resp_leEq; apply b'_seq_mon.
 eapply leEq_wdr.
  2: apply a'_seq_b'_seq_dist.
 unfold cg_minus in |- *; apply plus_resp_leEq_lft.
 apply inv_resp_leEq.
 apply less_leEq; apply a_b'.
   exact a'_seq_mon.
  exact b'_seq_mon.
 exact a'_seq_less_b'_seq.
Qed.

Let xa := Lim (Build_CauchySeq _ _ a'_seq_Cauchy).
Let xb := Lim (Build_CauchySeq _ _ b'_seq_Cauchy).

Lemma a'_seq_b'_seq_lim : xa [=] xb.
Proof.
 unfold xa, xb in |- *; clear xa xb.
 apply cg_inv_unique_2.
 apply eq_symmetric_unfolded.
 eapply eq_transitive_unfolded.
  2: apply Lim_minus.
 simpl in |- *.
 apply Limits_unique.
 simpl in |- *.
 intros eps H.
 elim (intervals_small' a b eps H); intros i Hi.
 exists i; intros.
 apply AbsIR_imp_AbsSmall.
 eapply leEq_transitive.
  2: apply Hi.
 eapply leEq_wdl.
  2: apply AbsIR_minus.
 eapply leEq_wdl.
  2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
  2: apply shift_leEq_minus; astepl (a'_seq m[-]b'_seq m).
  2: apply shift_minus_leEq; astepr (b'_seq m).
  2: apply less_leEq; apply a'_seq_less_b'_seq.
 eapply leEq_wdr.
  2: apply a'_seq_b'_seq_dist.
 rstepl (b'_seq m[-]a'_seq m).
 unfold cg_minus in |- *; apply plus_resp_leEq_both.
  astepl ( [--][--] (b'_seq m)); astepr ( [--][--] (b'_seq i)).
  apply inv_resp_leEq; apply local_mon'_imp_mon' with (f := fun n => [--] (b'_seq n)); auto.
  intro; apply inv_resp_leEq; apply b'_seq_mon.
 apply inv_resp_leEq; apply local_mon'_imp_mon'; auto; exact a'_seq_mon.
Qed.

Lemma xa'_in_interval : I xa.
Proof.
 split.
  unfold xa in |- *.
  apply leEq_seq_so_leEq_Lim.
  simpl in |- *.
  intro; elim (a'_seq_I i); auto.
 unfold xa in |- *.
 apply seq_leEq_so_Lim_leEq.
 simpl in |- *.
 intro; elim (a'_seq_I i); auto.
Qed.

Lemma IVT'_I : {x : IR | I' x | forall Hx, F x Hx [=] z}.
Proof.
 elim (IVT_I a b Hab' Hab F contF) with z; try apply less_leEq; auto.
 intros x H H0.
 exists x; auto.
 elim H; intros; split; apply leEq_not_eq; auto.
  apply pfstrx with F (incF _ Ha) (incF _ H).
  apply less_imp_ap; astepr z; auto.
 apply pfstrx with F (incF _ H) (incF _ Hb).
 apply less_imp_ap; astepl z; auto.
Qed.

End IVT'.

(**
** Other formulations

We now generalize the various statements of the intermediate value
theorem to more widely applicable forms.
*)

Lemma Weak_IVT : forall I F, Continuous I F -> forall a b Ha Hb (HFab : F a Ha [<] F b Hb),
 I a -> I b -> forall e, Zero [<] e -> forall y, Compact (less_leEq _ _ _ HFab) y ->
 {x : IR | Compact (Min_leEq_Max a b) x | forall Hx, AbsIR (F x Hx[-]y) [<=] e}.
Proof.
 intros I F H a b Ha Hb HFab H0 H1 e H2 y H3.
 set (H5 := less_imp_ap _ _ _ HFab) in *.
 set (H6 := pfstrx _ _ _ _ _ _ H5) in *.
 elim (ap_imp_less _ _ _ H6); clear H6 H5; intro.
  cut (Continuous_I (Min_leEq_Max a b) F). intro H4.
   2: apply included_imp_Continuous with I; auto; apply included_interval; auto.
  set (incF := contin_imp_inc _ _ _ _ H4) in *.
  cut (Min a b [=] a).
   cut (Max a b [=] b); intros.
    2: apply leEq_imp_Max_is_rht; apply less_leEq; auto.
   2: apply leEq_imp_Min_is_lft; apply less_leEq; auto.
  set (Ha' := incF _ (compact_inc_lft _ _ (Min_leEq_Max a b))) in *.
  set (Hb' := incF _ (compact_inc_rht _ _ (Min_leEq_Max a b))) in *.
  cut (F _ Ha' [<] F _ Hb'). intro H7.
   apply Weak_IVT_ap_lft with (HFab := H7); auto.
   apply compact_wd' with (Hab := less_leEq _ _ _ HFab); algebra.
  astepl (F a Ha); astepr (F b Hb); auto.
 cut (Continuous_I (Min_leEq_Max b a) F). intro H4.
  2: apply included_imp_Continuous with I; auto; apply included_interval; auto.
 set (incF := contin_imp_inc _ _ _ _ H4) in *.
 cut (Min a b [=] b).
  cut (Max a b [=] a); intros.
   2: eapply eq_transitive_unfolded;
     [ apply Max_comm | apply leEq_imp_Max_is_rht; apply less_leEq; auto ].
  2: eapply eq_transitive_unfolded;
    [ apply Min_comm | apply leEq_imp_Min_is_lft; apply less_leEq; auto ].
 set (Ha' := incF _ (compact_inc_lft _ _ (Min_leEq_Max b a))) in *.
 set (Hb' := incF _ (compact_inc_rht _ _ (Min_leEq_Max b a))) in *.
 cut (F _ Hb' [<] F _ Ha'). intro H7.
  elim (Weak_IVT_ap_rht _ _ _ _ H4 _ _ H7 _ H2 y); auto.
   intro x; intros.
   exists x; auto.
   apply compact_wd' with (Hab := Min_leEq_Max b a); [ apply Min_comm | apply Max_comm | auto ].
  apply compact_wd' with (Hab := less_leEq _ _ _ HFab); algebra.
   apply pfwdef; astepl (Max a b); apply Max_comm.
  apply pfwdef; astepl (Min a b); apply Min_comm.
 apply less_wdl with (F a Ha).
  apply less_wdr with (F b Hb).
   auto.
  apply pfwdef; astepl (Min a b); apply Min_comm.
 apply pfwdef; astepl (Max a b); apply Max_comm.
Qed.

Lemma IVT_inc : forall I F, Continuous I F -> forall a b Ha Hb, F a Ha [#] F b Hb ->
 I a -> I b -> (forall x y, I x -> I y -> x [<] y -> forall Hx Hy, F x Hx [<] F y Hy) ->
 forall y, Compact (Min_leEq_Max (F a Ha) (F b Hb)) y ->
 {x : IR | Compact (Min_leEq_Max a b) x | forall Hx, F x Hx [=] y}.
Proof.
 intros I F H a b Ha Hb H0 H1 H2 H3 y H4.
 set (H5 := pfstrx _ _ _ _ _ _ H0) in *.
 elim (ap_imp_less _ _ _ H5); clear H5; intro.
  cut (Continuous_I (Min_leEq_Max a b) F). intro H5.
   2: apply included_imp_Continuous with I; auto; apply included_interval; auto.
  cut (Min a b [=] a); [ intro | apply leEq_imp_Min_is_lft; apply less_leEq; auto ].
  cut (Max a b [=] b); [ intro | apply leEq_imp_Max_is_rht; apply less_leEq; auto ].
  cut (forall H H', F (Min a b) H [<] F (Max a b) H'); intros.
   2: apply H3; auto.
     2: apply iprop_wd with a; algebra.
    2: apply iprop_wd with b; algebra.
   2: astepl a; astepr b; auto.
  elim H4; intros.
  apply IVT_I with H5.
     apply ap_imp_Min_less_Max; apply less_imp_ap; auto.
    intros.
    apply H3; auto.
     apply (included_interval _ _ _ H1 H2 (Min_leEq_Max a b)); auto.
    apply (included_interval _ _ _ H1 H2 (Min_leEq_Max a b)); auto.
   eapply leEq_wdl.
    apply a1.
   astepr (F a Ha); apply leEq_imp_Min_is_lft; apply less_leEq; auto.
  eapply leEq_wdr.
   apply b0.
  astepr (F b Hb); apply leEq_imp_Max_is_rht; apply less_leEq; auto.
 cut (Continuous_I (Min_leEq_Max b a) F). intro H5.
  2: apply included_imp_Continuous with I; auto; apply included_interval; auto.
 cut (Min b a [=] b); [ intro | apply leEq_imp_Min_is_lft; apply less_leEq; auto ].
 cut (Max b a [=] a); [ intro | apply leEq_imp_Max_is_rht; apply less_leEq; auto ].
 cut (forall H H', F (Min b a) H [<] F (Max b a) H'). intro H8.
  2: apply H3; auto.
    2: apply iprop_wd with b; algebra.
   2: apply iprop_wd with a; algebra.
  2: astepl b; astepr a; auto.
 elim H4; intros.
 elim IVT_I with (contF := H5) (z := y); intros; auto.
     exists x; auto.
     apply compact_wd' with (Hab := Min_leEq_Max b a); auto.
      apply Min_comm.
     apply Max_comm.
    astepl b; astepr a; auto.
   apply H3; auto.
    apply (included_interval _ _ _ H2 H1 (Min_leEq_Max b a)); auto.
   apply (included_interval _ _ _ H2 H1 (Min_leEq_Max b a)); auto.
  eapply leEq_wdl.
   apply a0.
  astepr (F b Hb); eapply eq_transitive_unfolded.
   apply Min_comm.
  apply leEq_imp_Min_is_lft; apply less_leEq; auto.
 eapply leEq_wdr.
  apply b1.
 astepr (F a Ha); eapply eq_transitive_unfolded.
  apply Max_comm.
 apply leEq_imp_Max_is_rht; apply less_leEq; auto.
Qed.

Transparent Min.

Lemma IVT_dec : forall I F, Continuous I F -> forall a b Ha Hb, F a Ha [#] F b Hb ->
 I a -> I b -> (forall x y, I x -> I y -> x [<] y -> forall Hx Hy, F y Hy [<] F x Hx) ->
 forall y, Compact (Min_leEq_Max (F a Ha) (F b Hb)) y ->
 {x : IR | Compact (Min_leEq_Max a b) x | forall Hx, F x Hx [=] y}.
Proof.
 intros. try rename X4 into H.
 elim IVT_inc with (I := I) (F := {--}F) (a := a) (b := b) (y := [--]y) (Ha := Ha) (Hb := Hb); auto.
     intros x H5 H6.
     exists x; auto.
     intro.
     astepl ( [--][--] (F x Hx)); astepr ( [--][--]y).
     apply un_op_wd_unfolded; simpl in H6; apply H6.
    Contin.
   simpl in |- *; apply un_op_strext_unfolded with (cg_inv (c:=IR)).
   astepl (F a Ha); astepr (F b Hb); auto.
  intros; simpl in |- *; apply inv_resp_less; auto.
 inversion_clear H as (H0,H1); split; simpl in |- *; unfold MIN.
  apply inv_resp_leEq.
  eapply leEq_wdr.
   apply H1.
  apply Max_wd_unfolded; algebra.
 astepr ( [--][--] (Max [--] (F a Ha) [--] (F b Hb))).
 apply inv_resp_leEq; auto.
Qed.

Lemma IVT'_inc : forall I F, Continuous I F -> forall a b Ha Hb, F a Ha [#] F b Hb ->
 I a -> I b -> (forall x y, I x -> I y -> x [<] y -> forall Hx Hy, F x Hx [<] F y Hy) ->
 forall y, olor (Min (F a Ha) (F b Hb)) (Max (F a Ha) (F b Hb)) y ->
 {x : IR | olor (Min a b) (Max a b) x | forall Hx, F x Hx [=] y}.
Proof.
 intros I F H a b Ha Hb H0 H1 H2 H3 y H4.
 set (H5 := pfstrx _ _ _ _ _ _ H0) in *.
 elim (ap_imp_less _ _ _ H5); clear H5; intro.
  cut (Continuous_I (Min_leEq_Max a b) F). intro H5.
   2: apply included_imp_Continuous with I; auto; apply included_interval; auto.
  cut (Min a b [=] a); [ intro | apply leEq_imp_Min_is_lft; apply less_leEq; auto ].
  cut (Max a b [=] b); [ intro | apply leEq_imp_Max_is_rht; apply less_leEq; auto ].
  cut (forall H H', F (Min a b) H [<] F (Max a b) H'). intro H8.
   2: apply H3; auto.
     2: apply iprop_wd with a; algebra.
    2: apply iprop_wd with b; algebra.
   2: astepl a; astepr b; auto.
  elim H4; intros.
  apply IVT'_I with (Min_leEq_Max a b) H5.
     apply ap_imp_Min_less_Max; apply less_imp_ap; auto.
    intros.
    apply H3; auto.
     apply (included_interval _ _ _ H1 H2 (Min_leEq_Max a b)); auto.
    apply (included_interval _ _ _ H1 H2 (Min_leEq_Max a b)); auto.
   eapply less_wdl.
    apply a1.
   astepr (F a Ha); apply leEq_imp_Min_is_lft; apply less_leEq; auto.
  eapply less_wdr.
   apply b0.
  astepr (F b Hb); apply leEq_imp_Max_is_rht; apply less_leEq; auto.
 cut (Continuous_I (Min_leEq_Max b a) F). intro H5.
  2: apply included_imp_Continuous with I; auto; apply included_interval; auto.
 cut (Min b a [=] b); [ intro | apply leEq_imp_Min_is_lft; apply less_leEq; auto ].
 cut (Max b a [=] a); [ intro | apply leEq_imp_Max_is_rht; apply less_leEq; auto ].
 cut (forall H H', F (Min b a) H [<] F (Max b a) H'). intro H8.
  2: apply H3; auto.
    2: apply iprop_wd with b; algebra.
   2: apply iprop_wd with a; algebra.
  2: astepl b; astepr a; auto.
 elim H4; intros.
 elim IVT'_I with (contF := H5) (z := y); auto.
     intros x H9 H10; exists x; auto.
     elim H9; clear H9; intros H11 H12; split.
      eapply less_wdl; [ apply H11 | apply Min_comm ].
     eapply less_wdr; [ apply H12 | apply Max_comm ].
    apply ap_imp_Min_less_Max; apply less_imp_ap; auto.
   intros; apply H3; auto.
    apply (included_interval _ _ _ H2 H1 (Min_leEq_Max b a)); auto.
   apply (included_interval _ _ _ H2 H1 (Min_leEq_Max b a)); auto.
  eapply less_wdl.
   apply a0.
  astepr (F b Hb); eapply eq_transitive_unfolded.
   apply Min_comm.
  apply leEq_imp_Min_is_lft; apply less_leEq; auto.
 eapply less_wdr.
  apply b1.
 astepr (F a Ha); eapply eq_transitive_unfolded.
  apply Max_comm.
 apply leEq_imp_Max_is_rht; apply less_leEq; auto.
Qed.

Transparent Min.

Lemma IVT'_dec : forall I F, Continuous I F -> forall a b Ha Hb, F a Ha [#] F b Hb ->
 I a -> I b -> (forall x y, I x -> I y -> x [<] y -> forall Hx Hy, F y Hy [<] F x Hx) ->
 forall y, olor (Min (F a Ha) (F b Hb)) (Max (F a Ha) (F b Hb)) y ->
 {x : IR | olor (Min a b) (Max a b) x | forall Hx, F x Hx [=] y}.
Proof.
 intros.
 elim IVT'_inc with (I := I) (F := {--}F) (a := a) (b := b) (y := [--]y) (Ha := Ha) (Hb := Hb); auto.
     intros x H5 H6.
     exists x; auto.
     intro.
     astepl ( [--][--] (F x Hx)); astepr ( [--][--]y).
     apply un_op_wd_unfolded; simpl in H6; apply H6.
    Contin.
   simpl in |- *; apply un_op_strext_unfolded with (cg_inv (c:=IR)).
   astepl (F a Ha); astepr (F b Hb); auto.
  intros; simpl in |- *; apply inv_resp_less; auto.
 inversion_clear X4; split; simpl in |- *; unfold MIN.
  apply inv_resp_less.
  eapply less_wdr.
   apply X6.
  apply Max_wd_unfolded; algebra.
 astepr ( [--][--] (Max [--] (F a Ha) [--] (F b Hb))).
 apply inv_resp_less; auto.
Qed.
