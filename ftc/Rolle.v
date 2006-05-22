(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(* $Id$ *)

Require Export DiffTactics2.
Require Export MoreFunctions.

Section Rolle.

(** *Rolle's Theorem

We now begin to work with partial functions.  We begin by stating and proving Rolle's theorem in various forms and some of its corollaries.

%\begin{convention}% Assume that:
 - [a,b:IR] with [a [<] b] and denote by [I] the interval [[a,b]];
 - [F,F'] are partial functions such that [F'] is the derivative of [F] in [I];
 - [e] is a positive real number.

%\end{convention}%
*)

(* begin hide *)
Variables a b : IR.
Hypothesis Hab' : a [<] b.

Let Hab := less_leEq _ _ _ Hab'.
Let I := Compact Hab.

Variables F F' : PartIR.

Hypothesis derF : Derivative_I Hab' F F'.
Hypothesis Ha : Dom F a.
Hypothesis Hb : Dom F b.
(* end hide *)

(* begin show *)
Hypothesis Fab : F a Ha [=] F b Hb.
(* end show *)

(* begin hide *)
Variable e : IR.
Hypothesis He : Zero [<] e.

Let contF' : Continuous_I Hab F'.
apply deriv_imp_contin'_I with Hab' F.
assumption.
Qed.

Let derivF :
  forall e : IR,
  Zero [<] e ->
  {d : IR | Zero [<] d |
  forall x y : IR,
  I x ->
  I y ->
  forall Hx Hy Hx',
  AbsIR (x[-]y) [<=] d ->
  AbsIR (F y Hy[-]F x Hx[-]F' x Hx'[*] (y[-]x)) [<=] e[*]AbsIR (y[-]x)}.
elim derF.
intros a0 b0.
elim b0; intros H b1.
unfold I in |- *; assumption.
Qed.

Let Rolle_lemma2 :
  {d : IR | Zero [<] d |
  forall x y : IR,
  I x ->
  I y ->
  forall Hx Hy Hx',
  AbsIR (x[-]y) [<=] d ->
  AbsIR (F y Hy[-]F x Hx[-]F' x Hx'[*] (y[-]x)) [<=] e [/]TwoNZ[*]AbsIR (y[-]x)}.
exact (derivF _ (pos_div_two _ _ He)).
Qed.

Let df := proj1_sig2T _ _ _ Rolle_lemma2.

Let Hdf : Zero [<] df := proj2a_sig2T _ _ _ Rolle_lemma2.

Let Hf :
  forall x y : IR,
  I x ->
  I y ->
  forall Hx Hy Hx',
  AbsIR (x[-]y) [<=] df ->
  AbsIR (F y Hy[-]F x Hx[-]F' x Hx'[*] (y[-]x)) [<=] e [/]TwoNZ[*]AbsIR (y[-]x) :=
  proj2b_sig2T _ _ _ Rolle_lemma2.

Let Rolle_lemma3 :
  {d : IR | Zero [<] d |
  forall x y : IR,
  I x ->
  I y ->
  forall Hx Hy, AbsIR (x[-]y) [<=] d -> AbsIR (F' x Hx[-]F' y Hy) [<=] e [/]TwoNZ}.
elim contF'; intros.
exact (b0 _ (pos_div_two _ _ He)).
Qed.

Let df' := proj1_sig2T _ _ _ Rolle_lemma3.

Let Hdf' : Zero [<] df' := proj2a_sig2T _ _ _ Rolle_lemma3.

Let Hf' :
  forall x y : IR,
  I x ->
  I y ->
  forall Hx Hy,
  AbsIR (x[-]y) [<=] df' -> AbsIR (F' x Hx[-]F' y Hy) [<=] e [/]TwoNZ :=
  proj2b_sig2T _ _ _ Rolle_lemma3.

Let d := Min df df'.

Let Hd : Zero [<] d.
unfold d in |- *; apply less_Min; auto.
Qed.

Let incF : included (Compact Hab) (Dom F).
elim derF; intros; assumption.
Qed.

Let n := compact_nat a b d Hd.

Let fcp (i : nat) (Hi : i <= n) :=
  F (compact_part a b Hab' d Hd i Hi)
    (incF _ (compact_part_hyp a b Hab Hab' d Hd i Hi)).

Let Rolle_lemma1 :
  Sumx (fun (i : nat) (H : i < n) => fcp (S i) H[-]fcp i (lt_le_weak i n H)) [=] 
  Zero.
apply eq_transitive_unfolded with (fcp _ (le_n n) [-]fcp 0 (le_O_n n)).
apply Mengolli_Sum with (f := fun (i : nat) (H : i <= n) => fcp _ H).
red in |- *; do 3 intro.
rewrite H; intros.
unfold fcp in |- *; simpl in |- *; Algebra.
intros; Algebra.
apply eq_transitive_unfolded with (F b Hb[-]F a Ha).
unfold fcp, compact_part, n in |- *; simpl in |- *.
apply cg_minus_wd; apply pfwdef; rational.
astepr (F a Ha[-]F a Ha); apply cg_minus_wd.
apply eq_symmetric_unfolded; apply Fab.
Algebra.
Qed.

Let incF' : included (Compact Hab) (Dom F').
elim derF; intros.
elim b0; intros.
assumption.
Qed.

Let fcp' (i : nat) (Hi : i <= n) :=
  F' (compact_part a b Hab' d Hd i Hi)
    (incF' _ (compact_part_hyp a b Hab Hab' d Hd i Hi)).

Notation cp := (compact_part a b Hab' d Hd).

Let Rolle_lemma4 :
  {i : nat |
  {H : i < n |
  Zero [<] 
  (fcp' _ (lt_le_weak _ _ H) [+]e) [*] (cp (S i) H[-]cp i (lt_le_weak _ _ H))}}.
apply
 positive_Sumx
  with
    (f := fun (i : nat) (H : i < n) =>
          (fcp' _ (lt_le_weak _ _ H) [+]e) [*]
          (cp _ H[-]cp _ (lt_le_weak _ _ H))).
red in |- *; do 3 intro.
rewrite H; intros.
unfold fcp' in |- *; Algebra.
apply
 less_wdl
  with
    (Sumx (fun (i : nat) (H : i < n) => fcp _ H[-]fcp _ (lt_le_weak _ _ H))).
2: apply Rolle_lemma1.
apply Sumx_resp_less.
apply less_nring with (IR:COrdField); simpl in |- *; unfold n in |- *;
 apply pos_compact_nat; auto.
intros.
apply
 leEq_less_trans
  with
    ((fcp' i (lt_le_weak _ _ H) [+]e [/]TwoNZ) [*]
     (cp (S i) H[-]cp i (lt_le_weak _ _ H))).
2: apply mult_resp_less.
3: apply compact_less.
2: apply plus_resp_less_lft.
2: apply pos_div_two'; assumption.
rstepl
 (fcp' i (lt_le_weak _ _ H) [*] (cp _ H[-]cp _ (lt_le_weak _ _ H)) [+]
  (fcp _ H[-]fcp _ (lt_le_weak _ _ H) [-]
   fcp' i (lt_le_weak _ _ H) [*] (cp _ H[-]cp _ (lt_le_weak _ _ H)))).
eapply leEq_wdr.
2: apply eq_symmetric_unfolded; apply ring_distl_unfolded.
apply plus_resp_leEq_lft.
apply
 leEq_wdr with (e [/]TwoNZ[*]AbsIR (cp (S i) H[-]cp i (lt_le_weak _ _ H))).
2: apply mult_wd.
2: Algebra.
2: apply AbsIR_eq_x.
2: apply less_leEq; apply compact_less.
eapply leEq_transitive.
apply leEq_AbsIR.
unfold fcp, fcp' in |- *; apply Hf.
unfold I in |- *; apply compact_part_hyp.
unfold I in |- *; apply compact_part_hyp.
eapply leEq_wdl.
2: apply eq_symmetric_unfolded; apply AbsIR_minus.
apply leEq_transitive with d.
2: unfold d in |- *; apply Min_leEq_lft.
eapply leEq_wdl.
2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
apply compact_leEq.
apply less_leEq; apply compact_less.
Qed.

Let Rolle_lemma5 : {i : nat | {H : i <= n | [--]e [<] fcp' _ H}}.
elim Rolle_lemma4; intros i Hi; elim Hi; clear Hi; intros Hi Hi'.
exists i; exists (lt_le_weak _ _ Hi).
astepl (Zero[-]e); apply shift_minus_less.
eapply mult_cancel_less.
2: eapply less_wdl.
2: apply Hi'.
2: Algebra.
apply compact_less.
Qed.

Let Rolle_lemma6 :
  {i : nat |
  {H : i < n |
  (fcp' _ (lt_le_weak _ _ H) [-]e) [*] (cp (S i) H[-]cp i (lt_le_weak _ _ H)) [<] 
  Zero}}.
apply
 negative_Sumx
  with
    (f := fun (i : nat) (H : i < n) =>
          (fcp' _ (lt_le_weak _ _ H) [-]e) [*]
          (cp _ H[-]cp _ (lt_le_weak _ _ H))).
red in |- *; do 3 intro.
rewrite H; intros.
unfold fcp' in |- *; Algebra.
apply
 less_wdr
  with
    (Sumx (fun (i : nat) (H : i < n) => fcp _ H[-]fcp _ (lt_le_weak _ _ H))).
2: apply Rolle_lemma1.
apply Sumx_resp_less.
apply less_nring with (IR:COrdField); simpl in |- *; unfold n in |- *;
 apply pos_compact_nat; auto.
intros.
apply
 less_leEq_trans
  with
    ((fcp' _ (lt_le_weak _ _ H) [-]e [/]TwoNZ) [*]
     (cp _ H[-]cp _ (lt_le_weak _ _ H))).
apply mult_resp_less.
2: apply compact_less.
unfold cg_minus in |- *; apply plus_resp_less_lft.
apply inv_resp_less; apply pos_div_two'; assumption.
rstepr
 (fcp' _ (lt_le_weak _ _ H) [*] (cp _ H[-]cp _ (lt_le_weak _ _ H)) [+]
  [--]
  [--]
  (fcp _ H[-]fcp _ (lt_le_weak _ _ H) [-]
   fcp' _ (lt_le_weak _ _ H) [*] (cp _ H[-]cp _ (lt_le_weak _ _ H)))).
rstepl
 (fcp' _ (lt_le_weak _ _ H) [*] (cp _ H[-]cp _ (lt_le_weak _ _ H)) [-]
  e [/]TwoNZ[*] (cp _ H[-]cp _ (lt_le_weak _ _ H))).
unfold cg_minus at 1 in |- *; apply plus_resp_leEq_lft.
apply inv_resp_leEq;
 apply leEq_wdr with (e [/]TwoNZ[*]AbsIR (cp _ H[-]cp _ (lt_le_weak _ _ H))).
2: apply mult_wd.
2: Algebra.
2: apply AbsIR_eq_x.
2: apply less_leEq; apply compact_less.
eapply leEq_transitive.
apply inv_leEq_AbsIR.
unfold fcp, fcp' in |- *; apply Hf.
unfold I in |- *; apply compact_part_hyp.
unfold I in |- *; apply compact_part_hyp.
eapply leEq_wdl.
2: apply eq_symmetric_unfolded; apply AbsIR_minus.
apply leEq_transitive with d.
2: unfold d in |- *; apply Min_leEq_lft.
eapply leEq_wdl.
2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
apply compact_leEq.
apply less_leEq; apply compact_less.
Qed.

Let Rolle_lemma7 : {i : nat | {H : i <= n | fcp' _ H [<] e}}.
elim Rolle_lemma6; intros i Hi; elim Hi; clear Hi; intros Hi Hi'.
exists i; exists (lt_le_weak _ _ Hi).
astepr (e[+]Zero); apply shift_less_plus'.
eapply mult_cancel_less.
2: eapply less_wdr.
2: apply Hi'.
2: Algebra.
apply shift_less_minus.
astepl (cp _ (lt_le_weak _ _ Hi)).
unfold compact_part in |- *.
apply plus_resp_less_lft.
apply mult_resp_less.
simpl in |- *; apply less_plusOne.
apply div_resp_pos.
2: apply shift_less_minus; astepl a; auto.
apply pos_compact_nat; auto.
Qed.

Let j := ProjT1 Rolle_lemma5.

Let Hj := ProjT1 (ProjT2 Rolle_lemma5).

Let Hj' : [--]e [<] fcp' _ Hj.
exact (ProjT2 (ProjT2 Rolle_lemma5)).
Qed.

Let k := ProjT1 Rolle_lemma7.

Let Hk := ProjT1 (ProjT2 Rolle_lemma7).

Let Hk' : fcp' _ Hk [<] e.
exact (ProjT2 (ProjT2 Rolle_lemma7)).
Qed.

Let Rolle_lemma8 :
  forall (i : nat) (H : i <= n),
  AbsIR (fcp' _ H) [<] e or e [/]TwoNZ [<] AbsIR (fcp' _ H).
intros.
cut (e [/]TwoNZ [<] AbsIR (fcp' _ H) or AbsIR (fcp' _ H) [<] e).
intro H0; inversion_clear H0; [ right | left ]; assumption.
apply less_cotransitive_unfolded.
apply pos_div_two'; assumption.
Qed.

Let Rolle_lemma9 :
  {m : nat | {Hm : m <= n | AbsIR (fcp' _ Hm) [<] e}}
  or (forall (i : nat) (H : i <= n), e [/]TwoNZ [<] AbsIR (fcp' _ H)).
set (P := fun (i : nat) (H : i <= n) => AbsIR (fcp' _ H) [<] e) in *.
set (Q := fun (i : nat) (H : i <= n) => e [/]TwoNZ [<] AbsIR (fcp' _ H)) in *.
apply finite_or_elim with (P := P) (Q := Q).
red in |- *.
intros i i' Hii'; rewrite Hii'; intros Hi Hi' HP.
red in |- *; red in HP.
eapply less_wdl.
apply HP.
apply AbsIR_wd; unfold fcp' in |- *; Algebra.
red in |- *.
intros i i' Hii'; rewrite Hii'; intros Hi Hi' HQ.
red in |- *; red in HQ.
eapply less_wdr.
apply HQ.
apply AbsIR_wd; unfold fcp' in |- *; Algebra.
apply Rolle_lemma8.
Qed.

Let Rolle_lemma10 :
  {m : nat | {Hm : m <= n | AbsIR (fcp' _ Hm) [<] e}} ->
  {x : IR | I x | forall Hx, AbsIR (F' x Hx) [<=] e}.
intro H.
elim H; intros m Hm; elim Hm; clear H Hm; intros Hm Hm'.
exists (cp _ Hm).
red in |- *; apply compact_part_hyp.
intro; apply less_leEq; eapply less_wdl.
apply Hm'.
apply AbsIR_wd; unfold fcp' in |- *; Algebra.
Qed.

Let Rolle_lemma11 :
  (forall (i : nat) (H : i <= n), e [/]TwoNZ [<] AbsIR (fcp' _ H)) ->
  (forall H : 0 <= n, fcp' _ H [<] [--] (e [/]TwoNZ)) ->
  forall (i : nat) (H : i <= n), fcp' _ H [<] Zero.
intros H H0.
cut (forall H : 0 <= n, fcp' _ H [<] Zero).
intro.
simple induction i.
assumption.
intros i' Hrec HSi'.
astepr (e [/]TwoNZ[-]e [/]TwoNZ).
apply shift_less_minus.
cut (i' <= n).
2: auto with arith.
intro Hi'.
apply less_leEq_trans with (fcp' _ HSi'[-]fcp' _ Hi').
unfold cg_minus in |- *; apply plus_resp_less_lft.
cut (e [/]TwoNZ [<] fcp' _ Hi' or fcp' _ Hi' [<] [--] (e [/]TwoNZ)).
intro H2.
elim H2; clear H2; intro H3.
elimtype False.
cut (e [/]TwoNZ [<] Zero).
apply less_antisymmetric_unfolded.
apply pos_div_two; assumption.
eapply less_transitive_unfolded; [ apply H3 | apply Hrec ].
astepl ( [--][--] (e [/]TwoNZ)); apply inv_resp_less; assumption.
cut (e [/]TwoNZ [<] AbsIR (fcp' _ Hi')).
2: exact (H i' Hi').
intro H2.
apply less_AbsIR.
apply pos_div_two; assumption.
assumption.
eapply leEq_transitive.
apply leEq_AbsIR.
unfold fcp' in |- *; apply Hf'.
red in |- *; apply compact_part_hyp.
red in |- *; apply compact_part_hyp.
apply leEq_transitive with d.
2: unfold d in |- *; apply Min_leEq_rht.
eapply leEq_wdl.
2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
apply compact_leEq.
apply less_leEq; apply compact_less.
intro.
eapply less_transitive_unfolded.
apply (H0 H1).
astepr ( [--]ZeroR); apply inv_resp_less; apply pos_div_two; assumption.
Qed.

Let Rolle_lemma12 :
  (forall (i : nat) (H : i <= n), e [/]TwoNZ [<] AbsIR (fcp' _ H)) ->
  (forall H : 0 <= n, e [/]TwoNZ [<] fcp' _ H) ->
  forall (i : nat) (H : i <= n), Zero [<] fcp' _ H.
intros H H0.
cut (forall H : 0 <= n, Zero [<] fcp' _ H).
intro.
simple induction i.
assumption.
intros i' Hrec HSi'.
astepl ( [--]ZeroR); astepr ( [--][--] (fcp' _ HSi')); apply inv_resp_less.
astepr (e [/]TwoNZ[-]e [/]TwoNZ).
apply shift_less_minus'.
astepl (e [/]TwoNZ[-]fcp' _ HSi').
cut (i' <= n).
2: auto with arith.
intro Hi'.
apply less_leEq_trans with (fcp' _ Hi'[-]fcp' _ HSi').
unfold cg_minus in |- *; apply plus_resp_less_rht.
cut (e [/]TwoNZ [<] fcp' _ Hi' or fcp' _ Hi' [<] [--] (e [/]TwoNZ)).
intro H2; elim H2; clear H2; intro H3.
assumption.
elimtype False.
cut (Zero [<] [--] (e [/]TwoNZ)).
apply less_antisymmetric_unfolded.
astepr ( [--]ZeroR); apply inv_resp_less; apply pos_div_two; assumption.
eapply less_transitive_unfolded; [ apply (Hrec Hi') | apply H3 ].
cut (e [/]TwoNZ [<] AbsIR (fcp' _ Hi')).
2: exact (H i' Hi').
intro.
apply less_AbsIR.
apply pos_div_two; assumption.
assumption.
eapply leEq_transitive.
apply leEq_AbsIR.
unfold fcp' in |- *; apply Hf'.
red in |- *; apply compact_part_hyp.
red in |- *; apply compact_part_hyp.
apply leEq_transitive with d.
2: unfold d in |- *; apply Min_leEq_rht.
eapply leEq_wdl.
2: apply eq_symmetric_unfolded; apply AbsIR_minus.
eapply leEq_wdl.
2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
apply compact_leEq.
apply less_leEq; apply compact_less.
intro.
eapply less_transitive_unfolded.
2: apply (H0 H1).
apply pos_div_two; assumption.
Qed.

Let Rolle_lemma13 :
  (forall (i : nat) (H : i <= n), fcp' _ H [<] Zero)
  or (forall (i : nat) (H : i <= n), Zero [<] fcp' _ H) ->
  {x : IR | I x | forall Hx, AbsIR (F' x Hx) [<=] e}.
intro H; elim H; clear H; intro H0.
exists (cp _ Hj).
red in |- *; apply compact_part_hyp.
intro; simpl in |- *; unfold ABSIR in |- *; apply Max_leEq.
apply less_leEq; apply less_transitive_unfolded with ZeroR.
eapply less_wdl.
apply (H0 _ Hj).
unfold fcp' in |- *; Algebra.
assumption.
astepr ( [--][--]e); apply inv_resp_leEq.
apply less_leEq; eapply less_wdr.
apply Hj'.
unfold fcp' in |- *; Algebra.
exists (cp _ Hk).
red in |- *; apply compact_part_hyp.
intros.
simpl in |- *; unfold ABSIR in |- *; apply Max_leEq.
apply less_leEq; eapply less_wdl.
apply Hk'.
unfold fcp' in |- *; Algebra.
apply less_leEq; apply less_transitive_unfolded with ZeroR.
astepr ( [--]ZeroR); apply inv_resp_less; eapply less_wdr.
apply (H0 _ Hk).
unfold fcp' in |- *; rational.
assumption.
Qed.

Let Rolle_lemma15 :
  (forall (i : nat) (H : i <= n), e [/]TwoNZ [<] AbsIR (fcp' _ H)) ->
  fcp' _ (le_O_n n) [<] [--] (e [/]TwoNZ) or e [/]TwoNZ [<] fcp' _ (le_O_n n).
intro H.
cut (e [/]TwoNZ [<] fcp' _ (le_O_n n) or fcp' _ (le_O_n n) [<] [--] (e [/]TwoNZ)).
intro H0; inversion_clear H0; [ right | left ]; assumption.
apply less_AbsIR.
apply pos_div_two; assumption.
apply H.
Qed.
(* end hide *)

Theorem Rolle : {x : IR | I x | forall Hx, AbsIR (F' x Hx) [<=] e}.
elim Rolle_lemma9.
exact Rolle_lemma10.
intro.
apply Rolle_lemma13.
elim (Rolle_lemma15 b0).
left; apply Rolle_lemma11.
assumption.
intro.
eapply less_wdl.
apply a0.
unfold fcp' in |- *; Algebra.
right; apply Rolle_lemma12.
assumption.
intro.
eapply less_wdr.
apply b1.
unfold fcp' in |- *; Algebra.
Qed.

End Rolle.

Section Law_of_the_Mean.

(**
The following is a simple corollary:
*)

Variables a b : IR.
Hypothesis Hab' : a [<] b.

(* begin hide *)
Let Hab := less_leEq _ _ _ Hab'.
Let I := Compact Hab.
(* end hide *)

Variables F F' : PartIR.

Hypothesis HF : Derivative_I Hab' F F'.

(* begin show *)
Hypothesis HA : Dom F a.
Hypothesis HB : Dom F b.
(* end show *)

Lemma Law_of_the_Mean_I : forall e, Zero [<] e ->
 {x : IR | I x | forall Hx, AbsIR (F b HB[-]F a HA[-]F' x Hx[*] (b[-]a)) [<=] e}.
intros e H.
set (h := (FId{-} [-C-]a) {*} [-C-] (F b HB[-]F a HA) {-}F{*} [-C-] (b[-]a)) in *.
set (h' := [-C-] (F b HB[-]F a HA) {-}F'{*} [-C-] (b[-]a)) in *.
cut (Derivative_I Hab' h h').
intro H0.
cut {x : IR | I x | forall Hx, AbsIR (h' x Hx) [<=] e}.
intro H1.
elim H1; intros x Ix Hx.
exists x.
assumption.
intro.
eapply leEq_wdl.
apply (Hx (derivative_imp_inc' _ _ _ _ _ H0 x Ix)).
apply AbsIR_wd; simpl in |- *; rational.
unfold I, Hab in |- *;
 eapply
  Rolle
        with
        h
       (derivative_imp_inc _ _ _ _ _ H0 _ (compact_inc_lft _ _ _))
       (derivative_imp_inc _ _ _ _ _ H0 _ (compact_inc_rht _ _ _)).
assumption.
simpl in |- *; rational.
assumption.
unfold h, h' in |- *; clear h h'.
New_Deriv.
apply Feq_reflexive.
apply included_FMinus; Included.
apply eq_imp_Feq.
apply included_FMinus.
apply included_FPlus; Included.
Included.
Included.
intros.
simpl in |- *; rational.
Qed.

End Law_of_the_Mean.

Section Corollaries.

(**
We can also state these theorems without expliciting the derivative of [F].
*)

Variables a b : IR.
Hypothesis Hab' : a [<] b.

(* begin hide *)
Let Hab := less_leEq _ _ _ Hab'.
(* end hide *)
Variable F : PartIR.

(* begin show *)
Hypothesis HF : Diffble_I Hab' F.
(* end show *)

Theorem Rolle' : (forall Ha Hb, F a Ha [=] F b Hb) -> forall e, Zero [<] e ->
 {x : IR | Compact Hab x | forall Hx, AbsIR (PartInt (ProjT1 HF) x Hx) [<=] e}.
intros.
unfold Hab in |- *.
apply
 Rolle
  with
    F
    (diffble_imp_inc _ _ _ _ HF _ (compact_inc_lft a b Hab))
    (diffble_imp_inc _ _ _ _ HF _ (compact_inc_rht a b Hab)).
apply projT2.
apply H.
assumption.
Qed.

Lemma Law_of_the_Mean'_I : forall HA HB e, Zero [<] e ->
 {x : IR | Compact Hab x | forall Hx,
  AbsIR (F b HB[-]F a HA[-]PartInt (ProjT1 HF) x Hx[*] (b[-]a)) [<=] e}.
intros.
unfold Hab in |- *.
apply Law_of_the_Mean_I.
apply projT2.
assumption.
Qed.

End Corollaries.

Section Generalizations.

(**
The mean law is more useful if we abstract [a] and [b] from the
context---allowing them in particular to be equal.  In the case where
[F(a) [=] F(b)] we get Rolle's theorem again, so there is no need to
state it also in this form.

%\begin{convention}% Assume [I] is a proper interval, [F,F':PartIR].
%\end{convention}%
*)

Variable I : interval.
Hypothesis pI : proper I.

Variables F F' : PartIR.
(* begin show *)
Hypothesis derF : Derivative I pI F F'.
(* end show *)

(* begin hide *)
Let incF := Derivative_imp_inc _ _ _ _ derF.
Let incF' := Derivative_imp_inc' _ _ _ _ derF.
(* end hide *)

Theorem Law_of_the_Mean : forall a b, I a -> I b -> forall e, Zero [<] e ->
 {x : IR | Compact (Min_leEq_Max a b) x | forall Ha Hb Hx,
  AbsIR (F b Hb[-]F a Ha[-]F' x Hx[*] (b[-]a)) [<=] e}.
intros a b Ha Hb e He.
cut (included (Compact (Min_leEq_Max a b)) I). intro H.
2: apply included_interval'; auto.
elim
 (less_cotransitive_unfolded _ _ _ He
    (AbsIR (F b (incF _ Hb) [-]F a (incF _ Ha) [-]F' a (incF' _ Ha) [*] (b[-]a))));
 intros.
cut (Min a b [<] Max a b). intro H0.
cut (included (Compact (less_leEq _ _ _ H0)) I). intro H1.
2: apply included_interval'; auto.
elim (ap_imp_less _ _ _ (Min_less_Max_imp_ap _ _ H0)); intro.
cut (included (Compact (less_leEq _ _ _ a1)) I). intro H2.
2: apply included_trans with (Compact (less_leEq _ _ _ H0));
    [ apply compact_map2 | apply H1 ].
elim
 (Law_of_the_Mean_I _ _ a1 _ _
    (included_imp_Derivative _ _ _ _ derF _ _ a1 H2) (
    incF _ Ha) (incF _ Hb) e He).
intros x H3 H4.
exists x; auto.
apply compact_map2 with (Hab := less_leEq _ _ _ a1); auto.
intros.
eapply leEq_wdl.
apply (H4 Hx).
apply AbsIR_wd; Algebra.
cut (included (Compact (Min_leEq_Max b a)) (Compact (Min_leEq_Max a b))). intro H2.
cut (included (Compact (less_leEq _ _ _ b0)) I). intro H3.
2: apply included_trans with (Compact (Min_leEq_Max b a));
    [ apply compact_map2
    | apply included_trans with (Compact (less_leEq _ _ _ H0));
       [ apply H2 | apply H1 ] ].
elim
 (Law_of_the_Mean_I _ _ b0 _ _
    (included_imp_Derivative _ _ _ _ derF _ _ b0 H3) (
    incF _ Hb) (incF _ Ha) e He).
intros x H4 H5.
exists x; auto.
apply H2; apply compact_map2 with (Hab := less_leEq _ _ _ b0); auto.
intros.
eapply leEq_wdl.
apply (H5 Hx).
eapply eq_transitive_unfolded.
apply AbsIR_minus.
apply AbsIR_wd; rational.
intros x H2.
elim H2; clear H2; intros H3 H4; split.
eapply leEq_wdl; [ apply H3 | apply Min_comm ].
eapply leEq_wdr; [ apply H4 | apply Max_comm ].
apply ap_imp_Min_less_Max.
cut
 (Part _ _ (incF b Hb) [-]Part _ _ (incF a Ha) [#] Zero
  or Part _ _ (incF' a Ha) [*] (b[-]a) [#] Zero).
intro H0.
elim H0; clear H0; intro H1.
apply pfstrx with F (incF a Ha) (incF b Hb).
apply ap_symmetric_unfolded; apply zero_minus_apart; auto.
apply ap_symmetric_unfolded; apply zero_minus_apart.
eapply cring_mult_ap_zero_op; apply H1.
apply cg_minus_strext.
astepr ZeroR.
apply AbsIR_cancel_ap_zero.
apply Greater_imp_ap; auto.
exists a.
apply compact_Min_lft.
intros; apply less_leEq.
eapply less_wdl.
apply b0.
apply AbsIR_wd; Algebra.
Qed.

(**
We further generalize the mean law by writing as an explicit bound.
*)

Theorem Law_of_the_Mean_ineq : forall a b, I a -> I b -> forall c,
 (forall x,  Compact (Min_leEq_Max a b) x -> forall Hx, AbsIR (F' x Hx) [<=] c) ->
 forall Ha Hb, F b Hb[-]F a Ha [<=] c[*]AbsIR (b[-]a).
intros a b Ia Ib c Hc Ha Hb.
astepr (c[*]AbsIR (b[-]a) [+]Zero).
apply shift_leEq_plus'.
red in |- *; apply approach_zero_weak.
intros e H.
elim Law_of_the_Mean with a b e; auto.
intros x H0 H1.
cut (Dom F' x). intro H2.
eapply leEq_transitive.
2: apply (H1 Ha Hb H2).
eapply leEq_transitive.
2: apply leEq_AbsIR.
unfold cg_minus at 1 4 in |- *; apply plus_resp_leEq_lft.
apply inv_resp_leEq.
eapply leEq_transitive.
apply leEq_AbsIR.
eapply leEq_wdl.
2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
apply mult_resp_leEq_rht.
auto.
apply AbsIR_nonneg.
apply (Derivative_imp_inc' _ _ _ _ derF).
exact (included_interval I a b Ia Ib (Min_leEq_Max a b) x H0).
Qed.

End Generalizations.
