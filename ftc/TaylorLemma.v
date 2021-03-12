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

Require Export CoRN.ftc.Rolle.
From Coq Require Import Lia.

Opaque Min.

Section Taylor_Defs.

(**
* Taylor's Theorem

We now prove Taylor's theorem for the remainder of the Taylor
series.  This proof is done in two steps: first, we prove the lemma
for a proper compact interval; next we generalize the result to two
arbitrary (eventually equal) points in a proper interval.

** First case

We assume two different points [a] and [b] in the domain of [F] and
define the nth order derivative of [F] in the interval
[[Min(a,b),Max(a,b)]].
*)

Variables a b : IR.
Hypothesis Hap : a [#] b.

(* begin hide *)
Let Hab' := ap_imp_Min_less_Max _ _ Hap.
Let Hab := less_leEq _ _ _ Hab'.
Let I := Compact Hab.
(* end hide *)

Variable F : PartIR.
Hypothesis Ha : Dom F a.
Hypothesis Hb : Dom F b.

(* begin show *)
Let fi n (Hf : Diffble_I_n Hab' n F) i Hi := ProjT1 (Diffble_I_n_imp_deriv_n _ _ _
 i F (le_imp_Diffble_I _ _ _ _ _ (lt_n_Sm_le i n Hi) _ Hf)).
(* end show *)

(**
This last local definition is simply:
$f_i=f^{(i)}$#f<sub>i</sub>=f<sup>(i)</sup>#.
*)

(* begin hide *)
Lemma Taylor_lemma1 : forall n Hf i Hi,
 Derivative_I_n Hab' i F (PartInt (fi n Hf i Hi)).
Proof.
 intros.
 unfold fi in |- *.
 apply projT2.
Qed.
(* end hide *)

(**
Now we can define the Taylor sequence around [a].  The auxiliary
definition gives, for any [i], the function expressed by the rule
%\[g(x)=\frac{f^{(i)}
(a)}{i!}*(x-a)^i.\]%#g(x)=f<sup>(i)</sup>(a)/i!*(x-a)<sup>i</sup>.#
We denote by [A] and [B] the elements of [[Min(a,b),Max(a,b)]]
corresponding to [a] and [b].
*)

(* begin hide *)
Let TL_compact_a := compact_Min_lft _ _ Hab.
Let TL_compact_b := compact_Min_rht _ _ Hab.

Notation A := (Build_subcsetoid_crr IR _ _ TL_compact_a).
Notation B := (Build_subcsetoid_crr IR _ _ TL_compact_b).
(* end hide *)

(* begin show *)
Let funct_i n Hf i Hi := [-C-] (fi n Hf i Hi A [/] _[//] nring_fac_ap_zero _ i) {*} (FId{-} [-C-]a) {^}i.
(* end show *)

(* begin hide *)
Let funct_i' n Hf i Hi := PartInt (fi n Hf i Hi) {*}
 [-C-] ([1][/] _[//]nring_fac_ap_zero IR i) {*} ( [-C-]b{-}FId) {^}i.

Lemma TL_a_i : forall n Hf i Hi, Dom (funct_i n Hf i Hi) a.
Proof.
 split; split; simpl in |- *; auto.
Qed.

Lemma TL_b_i : forall n Hf i Hi, Dom (funct_i n Hf i Hi) b.
Proof.
 split; split; simpl in |- *; auto.
Qed.

Lemma TL_x_i : forall x, I x -> forall n Hf i Hi, Dom (funct_i n Hf i Hi) x.
Proof.
 split; split; simpl in |- *; auto.
Qed.

Lemma TL_a_i' : forall n Hf i Hi, Dom (funct_i' n Hf i Hi) a.
Proof.
 split; split; simpl in |- *; auto.
Qed.

Lemma TL_b_i' : forall n Hf i Hi, Dom (funct_i' n Hf i Hi) b.
Proof.
 split; split; simpl in |- *; auto.
Qed.

Lemma TL_x_i' : forall x, I x -> forall n Hf i Hi, Dom (funct_i' n Hf i Hi) x.
Proof.
 split; split; simpl in |- *; auto.
Qed.

Lemma Taylor_lemma2 : forall n Hf, ext_fun_seq (funct_i n Hf).
Proof.
 red in |- *; intros n Hf i j H H0 H' x y H1 Hx Hy.
 simpl in |- *.
 apply mult_wd.
  apply div_wd.
   2: rewrite H; algebra.
  generalize H' Hx Hy; clear Hy Hx H'.
  rewrite <- H; intros.
  cut (forall Ha1 Ha2, PartInt (fi n Hf i H0) a Ha1 [=] PartInt (fi n Hf i H') a Ha2); intros.
   simpl in H2.
   apply H2.
  apply Feq_imp_eq with (Compact Hab).
   unfold Hab in |- *; apply Derivative_I_n_unique with i F; apply Taylor_lemma1.
  apply TL_compact_a.
 rewrite H.
 astepl ((x[+][--]a) [^]j); Step_final ((y[+][--]a) [^]j).
Qed.

Lemma Taylor_lemma2' : forall n Hf, ext_fun_seq' (funct_i n Hf).
Proof.
 repeat intro.
 repeat split.
Qed.

Lemma Taylor_lemma3 : forall n Hf, ext_fun_seq (funct_i' n Hf).
Proof.
 red in |- *; intros n Hf i j H H0 H' x y H1 Hx Hy.
 simpl in |- *.
 apply mult_wd.
  apply mult_wd.
   2: rewrite H; algebra.
  generalize H' Hx Hy; clear Hy Hx H'.
  rewrite <- H; intros.
  cut (forall Hx' Hy', PartInt (fi n Hf i H0) x Hx' [=] PartInt (fi n Hf i H') y Hy'); intros.
   simpl in H2.
   apply H2.
  cut (Dom (PartInt (fi n Hf i H')) x); [ intro H2 | apply dom_wd with y; algebra ].
  apply eq_transitive_unfolded with (Part _ _ H2).
   apply Feq_imp_eq with (Compact Hab).
    unfold Hab in |- *; apply Derivative_I_n_unique with i F; apply Taylor_lemma1.
   simpl in Hx.
   elim Hx; intros.
   inversion_clear a0; auto.
  algebra.
 rewrite H.
 astepl ((b[+][--]x) [^]j); Step_final ((b[+][--]y) [^]j).
Qed.

Lemma Taylor_lemma3' : forall n Hf, ext_fun_seq' (funct_i' n Hf).
Proof.
 intros n Hf i j H H0 H' x y H1 H2.
 elim H2; intros.
 simpl in a0, b0.
 clear b0; inversion_clear a0 as (X,X0).
 inversion_clear X; repeat split.
  astepr x; auto.
 astepl x; auto.
Qed.
(* end hide *)

(**
Adding the previous expressions up to a given bound [n] gives us the
Taylor sum of order [n].
*)

Definition Taylor_seq' n Hf := FSumx _ (funct_i n Hf).

(* begin hide *)
Let Taylor_seq'_aux n Hf := FSumx _ (funct_i' n Hf).

Lemma TL_lemma_a : forall n Hf, Dom (Taylor_seq' n Hf) a.
Proof.
 intros.
 repeat split.
 apply FSumx_pred'.
  repeat split.
 repeat split.
Qed.
(* end hide *)

(**
It is easy to show that [b] is in the domain of this series, which allows us to write down the Taylor remainder around [b].
*)

Lemma TL_lemma_b : forall n Hf, Dom (Taylor_seq' n Hf) b.
Proof.
 intros.
 repeat split.
 apply FSumx_pred'.
  repeat split.
 repeat split.
Qed.

(* begin hide *)
Lemma TL_lemma_a' : forall n Hf, Dom (Taylor_seq'_aux n Hf) a.
Proof.
 intros.
 split.
  apply FSumx_pred'.
   red in |- *; intros.
   simpl in X.
   inversion_clear X.
   inversion_clear X0.
   simpl in |- *.
   split; split; auto.
   apply compact_wd with x; auto.
  intros.
  apply TL_a_i'.
 apply TL_a_i'.
Qed.

Lemma TL_lemma_b' : forall n Hf, Dom (Taylor_seq'_aux n Hf) b.
Proof.
 intros.
 split.
  apply FSumx_pred'.
   red in |- *; intros.
   simpl in X.
   inversion_clear X.
   inversion_clear X0.
   simpl in |- *.
   split; split; auto.
   apply compact_wd with x; auto.
  intros.
  apply TL_b_i'.
 apply TL_b_i'.
Qed.
(* end hide *)

Definition Taylor_rem n Hf := F b Hb[-]Taylor_seq' n Hf b (TL_lemma_b n Hf).

(* begin hide *)
Let g n Hf Hab := [-C-] (F b Hb) {-}Taylor_seq'_aux n Hf{-}
 [-C-] (Taylor_rem n Hf) {*} (( [-C-]b{-}FId) {*} [-C-] ([1][/] (b[-]a) [//]Hab)).

Lemma Taylor_lemma4 : forall n Hf Hab Ha', g n Hf Hab a Ha' [=] [0].
Proof.
 unfold g in |- *; clear g; intros.
 cut (Dom ( [-C-] (F b Hb) {-}Taylor_seq'_aux n Hf{-} [-C-] (Taylor_rem n Hf)) a). intro H.
  apply eq_transitive_unfolded with (Part _ _ H).
   Opaque Taylor_seq'_aux Taylor_rem.
   simpl in |- *; rational.
  Transparent Taylor_rem.
  unfold Taylor_rem in |- *.
  apply eq_transitive_unfolded with (Part _ _ (TL_lemma_b n Hf) [-]Part _ _ (TL_lemma_a' n Hf)).
   Opaque Taylor_seq'.
   simpl in |- *; rational.
  Transparent Taylor_seq' Taylor_seq'_aux.
  unfold Taylor_seq', Taylor_seq'_aux in |- *.
  cut (Dom (FSum 0 n (FSumx_to_FSum _ (funct_i n Hf))) b). intro H0.
   cut (Dom (FSum 0 n (FSumx_to_FSum _ (funct_i' n Hf))) a). intro H1.
    apply eq_transitive_unfolded with (Part _ _ H0[-]Part _ _ H1).
     apply eq_symmetric_unfolded; apply cg_minus_wd; apply FSum_FSumx_to_FSum.
        apply Taylor_lemma2.
       apply Taylor_lemma2'.
      apply Taylor_lemma3.
     apply Taylor_lemma3'.
    eapply eq_transitive_unfolded.
     simpl in |- *.
     apply eq_symmetric_unfolded; apply Sum_minus_Sum.
    apply Sum_zero.
     auto with arith.
    intros.
    cut (forall Hb' Ha', FSumx_to_FSum (S n) (funct_i n Hf) i b Hb'[-]
      FSumx_to_FSum (S n) (funct_i' n Hf) i a Ha' [=] [0]); auto.
    unfold FSumx_to_FSum in |- *.
    elim le_lt_dec; intro; simpl in |- *.
     algebra.
    intros.
    set (w := fi n Hf i b0 (Build_subcsetoid_crr _ _ _ TL_compact_a) [*]
      ([1][/] _[//]nring_fac_ap_zero IR i) [*] (b[+][--]a) [^]i) in *.
    astepr (w[-]w); unfold w in |- *; simpl in |- *.
    repeat first [ apply cg_minus_wd | simple apply mult_wd ]; try apply csf_wd_unfolded; algebra.
     rational.
    simpl in |- *; algebra.
   simpl in |- *; intro i.
   Opaque funct_i'.
   unfold FSumx_to_FSum in |- *.
   elim le_lt_dec; intro; simpl in |- *.
    auto.
   apply TL_a_i'.
  Opaque funct_i.
  simpl in |- *; intro i.
  unfold FSumx_to_FSum in |- *.
  elim le_lt_dec; intro; simpl in |- *.
   auto.
  apply TL_b_i.
 split; split; split.
  apply FSumx_pred'.
   red in |- *; intros.
   inversion_clear X.
   inversion_clear X0.
   simpl in X.
   split; split; auto.
   simpl in |- *; apply compact_wd with x; auto.
  intros; apply TL_a_i'.
 apply TL_a_i'.
Qed.

Transparent funct_i funct_i'.

Lemma Taylor_lemma5 : forall n Hf Hab Hb', g n Hf Hab b Hb' [=] [0].
Proof.
 unfold g in |- *; intros.
 cut (Dom ( [-C-] (F b Hb) {-}Taylor_seq'_aux n Hf) b). intro H.
  apply eq_transitive_unfolded with (Part _ _ H).
   Opaque Taylor_seq'_aux.
   simpl in |- *; rational.
  Transparent Taylor_seq'_aux.
  unfold Taylor_seq'_aux in |- *.
  cut (Dom (FSum 0 n (FSumx_to_FSum _ (funct_i' n Hf))) b). intro H0.
   apply eq_transitive_unfolded with (F b Hb[-]Part _ _ H0).
    Opaque FSumx.
    apply eq_transitive_unfolded with (F b Hb[-]FSumx (S n) (funct_i' n Hf) b (ProjIR2 H)).
     simpl in |- *; rational.
    apply cg_minus_wd.
     algebra.
    apply eq_symmetric_unfolded; apply FSum_FSumx_to_FSum.
     apply Taylor_lemma3.
    apply Taylor_lemma3'.
   simpl in |- *.
   astepr (Part _ _ Hb[-]Part _ _ Hb); apply cg_minus_wd.
    algebra.
   eapply eq_transitive_unfolded.
    apply Sum_first.
   astepr (Part _ _ Hb[+][0]); apply bin_op_wd_unfolded.
    cut (forall H', FSumx_to_FSum (S n) (funct_i' n Hf) 0 b H' [=] Part _ _ Hb); auto.
    unfold FSumx_to_FSum in |- *.
    elim le_lt_dec; intro; simpl in |- *.
     elimtype False; inversion a0.
    intros; simpl in |- *.
    rstepr (Part _ _ Hb[*][1][*][1]).
    apply mult_wdl.
    apply mult_wd.
     2: rational.
    apply eq_symmetric_unfolded.
    apply eq_transitive_unfolded with (PartInt (fi n Hf 0 b0) b TL_compact_b).
     2: simpl in |- *; apply csf_wd_unfolded; simpl in |- *; algebra.
    apply Feq_imp_eq with (Compact Hab).
     apply (ProjT2 (Diffble_I_n_imp_deriv_n _ _ _ _ _
       (le_imp_Diffble_I _ _ _ _ _ (lt_n_Sm_le 0 n b0) _ Hf))).
    apply TL_compact_b.
   apply Sum_zero.
    auto with arith.
   intros.
   cut (forall H', FSumx_to_FSum (S n) (funct_i' n Hf) i b H' [=] [0]); auto.
   unfold FSumx_to_FSum in |- *.
   elim le_lt_dec; intro; simpl in |- *.
    algebra.
   intro.
   astepr (fi n Hf i b0 (Build_subcsetoid_crr IR _ b (ProjIR1 (ProjIR1 H'))) [*]
     ([1][/] _[//]nring_fac_ap_zero _ i) [*][0]).
   apply mult_wdr.
   astepl ((b[-]b) [^]i).
   Step_final (ZeroR[^]i).
  intro i.
  Opaque funct_i'.
  unfold FSumx_to_FSum in |- *.
  elim le_lt_dec; intro; simpl in |- *.
   auto.
  apply TL_b_i'.
 split.
  simpl in |- *; auto.
 simpl in |- *.
 apply TL_lemma_b'.
Qed.

Transparent funct_i' FSumx.

Let funct_aux n Hf i Hi := PartInt (fi (S n) Hf (S i) (lt_n_S _ _ Hi)) {*}
  [-C-] ([1][/] _[//]nring_fac_ap_zero IR i) {*} ( [-C-]b{-}FId) {^}i.

Lemma Taylor_lemma6 :  forall n Hf Hf' i Hi, Derivative_I Hab'
 (PartInt (fi n Hf i Hi)) (PartInt (fi (S n) Hf' (S i) (lt_n_S _ _ Hi))).
Proof.
 intros.
 cut (Derivative_I_n Hab' 1 (PartInt (fi n Hf i Hi))
   (PartInt (fi (S n) Hf' (S i) (lt_n_S i (S n) Hi)))).
  intro H.
  simpl in H.
  elim H; intros f' H1 H2.
  apply Derivative_I_wdr with (PartInt f'); assumption.
 cut (S i = 1 + i); [ intro | lia ].
 cut (1 + i < S (S n)); [ intro | lia ].
 apply Derivative_I_n_wdr with (PartInt (fi (S n) Hf' _ H0)).
  apply Derivative_I_n_unique with (S i) F.
   generalize H0; clear H0.
   rewrite <- H; intro.
   apply Taylor_lemma1.
  apply Taylor_lemma1.
 apply Derivative_I_n_wdl with (n_deriv_I _ _ _ _ _
   (le_imp_Diffble_I _ _ _ _ _ (lt_n_Sm_le i n Hi) _ Hf)).
  2: apply Derivative_I_n_wdr with (n_deriv_I _ _ _ _ _
    (le_imp_Diffble_I _ _ _ _ _ (lt_n_Sm_le _ _ H0) _ Hf')).
   3: apply n_deriv_plus.
  apply Derivative_I_n_unique with i F.
   apply n_deriv_lemma.
  apply Taylor_lemma1.
 apply Derivative_I_n_unique with (1 + i) F.
  apply n_deriv_lemma.
 apply Taylor_lemma1.
Qed.

Ltac Lazy_Included :=
  repeat first
   [ simple apply included_IR
   | simple apply included_FPlus
   | simple apply included_FInv
   | simple apply included_FMinus
   | simple apply included_FMult
   | simple apply included_FNth
   | simple apply included_refl ].

Ltac Lazy_Eq :=
  repeat first
   [ simple apply bin_op_wd_unfolded
   | simple apply un_op_wd_unfolded
   | simple apply cg_minus_wd
   | simple apply div_wd
   | simple apply csf_wd_unfolded ]; algebra.

Lemma Taylor_lemma7 : forall n Hf Hf' i (Hi : 0 < i) Hi', Derivative_I Hab'
 (funct_i' n Hf i Hi') (funct_aux n Hf' i Hi'{-}funct_aux n Hf' (pred i) (lt_5 i (S n) Hi')).
Proof.
 do 5 intro.
 rewrite (S_pred _ _ Hi).
 set (p := pred i) in *; clearbody p; clear Hi i.
 intros.
 cut (Derivative_I Hab' (PartInt (fi n Hf _ Hi'))
   (PartInt (fi (S n) Hf' (S (S p)) (lt_n_S _ _ Hi')))); [ intro | apply Taylor_lemma6 ].
 unfold funct_aux, funct_i' in |- *.
 New_Deriv.
  apply Feq_reflexive.
  Lazy_Included.
 apply eq_imp_Feq.
   Lazy_Included.
  Lazy_Included.
 intros x X0 Hx Hx'.
 simpl in Hx, Hx'; simpl in |- *.
 set (fiSp1 := fi n Hf (S p) Hi') in *.
 set (fiSp2 := fi (S n) Hf' (S p) (lt_n_S p (S n) (lt_5 (S p) (S n) Hi'))) in *.
 cut (forall x y : subset I, scs_elem _ _ x [=] scs_elem _ _ y -> fiSp1 x [=] fiSp2 y); intros.
  set (x1 := Build_subcsetoid_crr IR _ _ (ProjIR1 (ProjIR1 (ProjIR1 Hx)))) in *.
  simpl in (value of x1); fold x1 in |- *.
  set (x2 := Build_subcsetoid_crr IR _ _ (ProjIR1 (ProjIR1 (ProjIR2 Hx')))) in *.
  simpl in (value of x2); fold x2 in |- *.
  set (x3 := Build_subcsetoid_crr IR _ _ (ProjIR1 (ProjIR1 (ProjIR1 (ProjIR2 Hx))))) in *.
  simpl in (value of x3); fold x3 in |- *.
  set (x4 := Build_subcsetoid_crr IR _ _ (ProjIR1 (ProjIR1 (ProjIR1 Hx')))) in *.
  simpl in (value of x4); fold x4 in |- *.
  set (x5 := Build_subcsetoid_crr IR _ _ (ProjIR1 (ProjIR2 (ProjIR1 (ProjIR2 Hx))))) in *.
  simpl in (value of x5); fold x5 in |- *.
  set (fiSSp := fi (S n) Hf' (S (S p)) (lt_n_S (S p) (S n) Hi')) in *.
  set (pp := [1][/] nring (fact p + p * fact p) [//]nring_fac_ap_zero IR (S p)) in *.
  set (bxp := nexp _ p (b[-]x)) in *.
  set (a1 := fiSp1 x1) in *; set (a5 := fiSSp x5) in *;
    simpl in (value of a1), (value of a5); fold a1 a5 in |- *.
  rstepl (a5[*]pp[*] (bxp[*] (b[-]x)) [-]a1[*] ((nring p[+][1]) [*]pp) [*]bxp).
  unfold a1, a5 in |- *; clear a1 a5.
  Lazy_Eq.
   unfold x4, x5 in |- *; algebra.
   simpl in |- *; algebra.
  unfold pp in |- *.
  rstepr (nring (S p) [*] ([1][/] _[//] mult_resp_ap_zero _ _ _ (nring_fac_ap_zero _ p)
    (pos_ap_zero _ _ (pos_nring_S IR p)))); simpl in |- *.
  apply mult_wdr; apply div_wd.
   algebra.
  clear X H bxp pp x5 x4 x3 x2 x1 fiSSp fiSp1 fiSp2 Hx.
  cut (fact p + p * fact p = fact p * S p).
   intro; rewrite H.
   eapply eq_transitive_unfolded.
    apply nring_comm_mult.
   algebra.
  transitivity (S p * fact p); auto with arith.
 unfold fiSp1, fiSp2 in |- *.
 apply eq_transitive_unfolded with (PartInt (fi n Hf (S p) Hi') (scs_elem _ _ x0) (scs_prf _ _ x0)).
  2: apply eq_transitive_unfolded with (PartInt (fi (S n) Hf' (S p) (lt_n_S _ _ (lt_5 _ _ Hi')))
    (scs_elem _ _ x0) (scs_prf _ _ x0)).
   simpl in |- *; apply csf_wd_unfolded.
   case x0; simpl in |- *; algebra.
  apply Feq_imp_eq with (Compact Hab).
   unfold Hab in |- *; apply Derivative_I_n_unique with (S p) F; apply Taylor_lemma1.
  apply scs_prf.
 simpl in |- *; apply csf_wd_unfolded.
 generalize H; case x0; case y; auto.
Qed.

Lemma Taylor_lemma8 : forall n Hf Hf' Hi,
  Derivative_I Hab' (funct_i' n Hf 0 Hi) (funct_aux n Hf' 0 Hi).
Proof.
 intros.
 cut (Derivative_I Hab' (PartInt (fi n Hf _ Hi)) (PartInt (fi (S n) Hf' 1 (lt_n_S _ _ Hi))));
   [ intro | apply Taylor_lemma6 ].
 unfold funct_aux, funct_i' in |- *; New_Deriv.
  apply Feq_reflexive; Lazy_Included.
 apply eq_imp_Feq.
   Lazy_Included.
  Lazy_Included.
 intros; simpl in |- *.
 apply eq_transitive_unfolded with (fi (S n) Hf' 1 (lt_n_S _ _ Hi)
   (Build_subcsetoid_crr _ _ _ (ProjIR1 (ProjIR2 (ProjIR1 (ProjIR2 Hx))))) [*]
     ([1][/] _[//]nring_fac_ap_zero IR 0) [*][1]).
  simpl in |- *; rational.
 Lazy_Eq; simpl in |- *; algebra.
Qed.

Lemma Taylor_lemma9 : forall n Hf Hf',
  Derivative_I Hab' (Taylor_seq'_aux n Hf) (funct_aux n Hf' n (lt_n_Sn n)).
Proof.
 intro; induction  n as [| n Hrecn].
  intros.
  unfold Taylor_seq'_aux in |- *; simpl in |- *.
  apply Derivative_I_wdl with (funct_i' 0 Hf 0 (lt_n_Sn 0)).
   apply eq_imp_Feq.
     split; split; simpl in |- *; auto.
    split; split; split; simpl in |- *; auto.
   intros; simpl in |- *.
   apply eq_transitive_unfolded with ([0][+] fi 0 Hf 0 (lt_n_Sn 0)
     (Build_subcsetoid_crr _ _ _ (ProjIR1 (ProjIR1 Hx))) [*]
       ([1][/] [0][+][1][//]nring_fac_ap_zero IR 0) [*][1]).
    simpl in |- *; rational.
   Lazy_Eq; simpl in |- *; algebra.
  apply Taylor_lemma8; assumption.
 cut {p : nat | S n = p}; [ intro H | exists (S n); auto ].
 elim H; intros p H0.
 rewrite H0.
 intros.
 unfold Taylor_seq'_aux in |- *; simpl in |- *.
 generalize Hf Hf'; clear Hf Hf'.
 rewrite <- H0; intros.
 cut (Diffble_I_n Hab' n F); [ intro H1 | apply le_imp_Diffble_I with (S n); [ lia | assumption ] ].
 apply Derivative_I_wdl with (Taylor_seq'_aux n H1{+}funct_i' _ Hf _ (lt_n_Sn (S n))).
  unfold Taylor_seq'_aux in |- *.
  apply eq_imp_Feq.
    repeat (split; auto). try rename X into H2.
    apply FSumx_pred'.
     red in |- *; intros. try rename X into H6.
     exact (Taylor_lemma3' _ _ _ _ H3 _ _ _ _ H4 H6).
    intros; simpl in |- *; repeat (split; auto).
   repeat (split; auto). try rename X into H2.
   apply FSumx_pred'.
    red in |- *; intros. try rename X into H6.
    exact (Taylor_lemma3' _ _ _ _ H3 _ _ _ _ H4 H6).
   intros; simpl in |- *; repeat (split; auto).
  intros x H2 Hx Hx'; simpl in |- *.
  repeat first [ simple apply mult_wd | simple apply bin_op_wd_unfolded | simple apply csf_wd_unfolded
    | simple apply eq_reflexive_unfolded ]; simpl in |- *.
    3: algebra.
   apply Feq_imp_eq with (Compact Hab).
    2: assumption.
   apply FSumx_wd'.
   intros; apply eq_imp_Feq.
     repeat (split; auto).
    repeat (split; auto).
   intros x0 H4; intros; simpl in |- *.
   repeat apply mult_wdl.
   apply eq_transitive_unfolded with (PartInt (fi n H1 i (lt_S _ _ H3)) x0 H4).
    simpl in |- *; apply csf_wd_unfolded; simpl in |- *; algebra.
   apply eq_transitive_unfolded with (PartInt (fi (S n) Hf i (lt_S _ _ (lt_S _ _ H'))) x0 H4).
    2: simpl in |- *; apply csf_wd_unfolded; simpl in |- *; algebra.
   apply Feq_imp_eq with (Compact Hab).
    unfold Hab in |- *; apply Derivative_I_n_unique with i F; apply Taylor_lemma1.
   auto.
  apply eq_transitive_unfolded with (PartInt (fi n H1 n (lt_n_Sn _)) x H2).
   2: apply eq_transitive_unfolded with (PartInt (fi (S n) Hf n (lt_S _ _ (lt_n_Sn _))) x H2).
    simpl in |- *; apply csf_wd_unfolded; simpl in |- *; algebra.
   2: simpl in |- *; apply csf_wd_unfolded; simpl in |- *; algebra.
  apply Feq_imp_eq with (Compact Hab).
   unfold Hab in |- *; apply Derivative_I_n_unique with n F; apply Taylor_lemma1.
  auto.
 apply Derivative_I_wdr with (funct_aux (S n) Hf' (pred (S n)) (lt_5 _ _ (lt_n_Sn (S n))) {+}
   (funct_aux _ Hf' _ (lt_n_Sn (S n)) {-}
     funct_aux (S n) Hf' (pred (S n)) (lt_5 _ _ (lt_n_Sn (S n))))).
  Opaque funct_aux.
  FEQ.
   Transparent funct_aux.
   repeat (split; auto).
  repeat (split; auto).
 apply Derivative_I_plus.
  apply Derivative_I_wdr with (funct_aux n Hf n (lt_n_Sn n)).
   apply eq_imp_Feq.
     repeat (split; auto).
    repeat (split; auto).
   intros x H2 Hx Hx'; simpl in |- *.
   repeat apply mult_wdl.
   apply eq_transitive_unfolded with (PartInt (fi (S n) Hf (S n) (lt_n_S _ _ (lt_n_Sn _))) x H2).
    2: apply eq_transitive_unfolded with (PartInt
      (fi (S (S n)) Hf' (S n) (lt_n_S _ _ (lt_5 _ _ (lt_n_Sn (S n))))) x H2).
     simpl in |- *; apply csf_wd_unfolded; simpl in |- *; algebra.
    2: simpl in |- *; apply csf_wd_unfolded; simpl in |- *; algebra.
   apply Feq_imp_eq with (Compact Hab).
    unfold Hab in |- *; apply Derivative_I_n_unique with (S n) F; apply Taylor_lemma1.
   auto.
  apply Hrecn.
 apply Taylor_lemma7.
 lia.
Qed.

Let g' n Hf Hf' Hab :=
 [-C-] (Taylor_rem n Hf[/] (b[-]a) [//]Hab) {-}funct_aux n Hf' n (lt_n_Sn n).

Lemma Taylor_lemma10 : forall n Hf Hf' Hab (H : a [#] b),
 Derivative_I Hab' (g n Hf Hab) (g' n Hf Hf' Hab).
Proof.
 unfold g, g' in |- *.
 intros.
 cut (Derivative_I Hab' (Taylor_seq'_aux n Hf) (funct_aux n Hf' n (lt_n_Sn n)));
   [ intro | apply Taylor_lemma9; assumption ].
 Opaque Taylor_rem funct_aux.
 New_Deriv.
  apply Feq_reflexive; Lazy_Included.
  Included.
 apply eq_imp_Feq.
   Lazy_Included.
   Included.
  Lazy_Included.
  Included.
 intros; simpl in |- *; rational.
Qed.

Transparent Taylor_rem funct_aux.
(* end hide *)

(**
Now Taylor's theorem.

%\begin{convention}% Let [e] be a positive real number.
%\end{convention}%
*)

Variable e : IR.
Hypothesis He : [0] [<] e.

(* begin hide *)
Lemma Taylor_lemma11 : forall n Hf Hf' H, {c : IR | I c |
  forall Hc, AbsIR (g' n Hf Hf' H c Hc) [<=] e[*]AbsIR ([1][/] (b[-]a) [//]H)}.
Proof.
 intros.
 cut (Dom (g n Hf H) (Min a b)). intro H0.
  cut (Dom (g n Hf H) (Max a b)). intro H1.
   cut (Dom (g n Hf H) a). intro H2.
    cut (Dom (g n Hf H) b). intro H3.
     unfold I, Hab in |- *; apply Rolle with (g n Hf H) H0 H1.
       apply Taylor_lemma10; auto.
      elim (ap_imp_less _ _ _ Hap); intro.
       apply eq_transitive_unfolded with ZeroR.
        eapply eq_transitive_unfolded.
         2: apply Taylor_lemma4 with (Ha' := H2).
        apply pfwdef; apply leEq_imp_Min_is_lft; apply less_leEq; auto.
       apply eq_symmetric_unfolded.
       eapply eq_transitive_unfolded.
        2: apply Taylor_lemma5 with (Hb' := H3).
       apply pfwdef; apply leEq_imp_Max_is_rht; apply less_leEq; auto.
      apply eq_transitive_unfolded with ZeroR.
       eapply eq_transitive_unfolded.
        2: apply Taylor_lemma5 with (Hb' := H3).
       apply pfwdef; eapply eq_transitive_unfolded.
        apply Min_comm.
       apply leEq_imp_Min_is_lft; apply less_leEq; auto.
      apply eq_symmetric_unfolded.
      eapply eq_transitive_unfolded.
       2: apply Taylor_lemma4 with (Ha' := H2).
      apply pfwdef; eapply eq_transitive_unfolded.
       apply Max_comm.
      apply leEq_imp_Max_is_rht; apply less_leEq; auto.
     astepl ([0][*]AbsIR ([1][/] _[//]H)).
     apply mult_resp_less.
      assumption.
     apply AbsIR_pos.
     apply div_resp_ap_zero_rev.
     apply one_ap_zero.
    split; split; split; simpl in |- *; auto.
      3: split; split.
     2: split; split; auto; apply TL_compact_b.
    apply FSumx_pred'; intros.
     2: apply TL_b_i'.
    red in |- *; intros. try rename X into H6.
    exact (Taylor_lemma3' _ _ _ _ H3 _ _ _ _ H4 H6).
   split; split; split; simpl in |- *; auto.
     3: split; split.
    2: split; split; auto; apply TL_compact_a.
   apply FSumx_pred'; intros.
    2: apply TL_a_i'.
   red in |- *; intros. try rename X into H5.
   exact (Taylor_lemma3' _ _ _ _ H2 _ _ _ _ H3 H5).
  split; split; split; simpl in |- *; auto.
    3: split; split.
   2: split; split; auto; apply compact_inc_rht.
  apply FSumx_pred'; intros.
   2: apply TL_x_i'.
   red in |- *; intros. try rename X into H4.
   exact (Taylor_lemma3' _ _ _ _ H1 _ _ _ _ H2 H4).
  unfold I in |- *; apply compact_inc_rht.
 split; split; split; simpl in |- *; auto.
   3: split; split.
  2: split; split; auto; apply compact_inc_lft.
 apply FSumx_pred'; intros.
  2: apply TL_x_i'.
  red in |- *; intros. try rename X into H3.
  exact (Taylor_lemma3' _ _ _ _ H0 _ _ _ _ H1 H3).
 unfold I in |- *; apply compact_inc_lft.
Qed.
(* end hide *)

(* begin show *)
Let deriv_Sn' n Hf' :=
 n_deriv_I _ _ Hab' (S n) F Hf'{*} [-C-] ([1][/] _[//]nring_fac_ap_zero _ n) {*} ( [-C-]b{-}FId) {^}n.
(* end show *)

(* begin hide *)
Lemma TLH : b[-]a [#] [0].
Proof.
 rstepl ( [--] (a[-]b)).
 apply inv_resp_ap_zero.
 apply minus_ap_zero; auto.
Qed.
(* end hide *)

Lemma Taylor_lemma : forall n Hf Hf', {c : IR | I c |
 forall Hc, AbsIR (Taylor_rem n Hf[-]deriv_Sn' n Hf' c Hc[*] (b[-]a)) [<=] e}.
Proof.
 intros.
 assert (H := TLH).
 cut {c : IR | I c | forall Hc, AbsIR (g' n Hf Hf' H c Hc) [<=] e[*]AbsIR ([1][/] _[//]H)};
   [ intro H0 | apply Taylor_lemma11; assumption ].
 elim H0; intros c Hc' Hc; clear H0; exists c.
  auto.
 intro.
 cut (Dom (funct_aux n Hf' n (lt_n_Sn n)) c). intro H0.
  apply leEq_wdl with (AbsIR (((Taylor_rem n Hf[/] _[//]H) [-]Part _ _ H0) [*] (b[-]a))).
   eapply leEq_wdl.
    2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
   apply shift_mult_leEq with (AbsIR_resp_ap_zero _ H).
    apply AbsIR_pos; apply H.
   rstepr (e[*] ([1][/] _[//]AbsIR_resp_ap_zero _ H)).
   apply leEq_wdr with (e[*]AbsIR ([1][/] _[//]H)).
    Opaque funct_aux.
    cut (Dom (g' n Hf Hf' H) c). intro H1.
     eapply leEq_wdl.
      apply (Hc H1).
     apply AbsIR_wd; unfold g' in |- *.
     Opaque Taylor_rem.
     simpl in |- *; rational.
    repeat (split; auto).
   apply mult_wdr.
   apply AbsIR_recip.
  apply eq_symmetric_unfolded.
  apply eq_transitive_unfolded
    with (AbsIR ((Taylor_rem n Hf[/] _[//]H) [-]Part _ _ H0) [*]AbsIR (b[-]a)).
   eapply eq_transitive_unfolded.
    2: apply AbsIR_resp_mult.
   apply AbsIR_wd.
   rstepr (Taylor_rem n Hf[-]Part _ _ H0[*] (b[-]a)).
   apply cg_minus_wd.
    algebra.
   apply mult_wdl.
   Transparent Taylor_rem funct_aux.
   unfold deriv_Sn', funct_aux in |- *.
   cut (Dom (n_deriv_I _ _ Hab' (S n) F Hf') c). intro H1.
    simpl in |- *; apply eq_transitive_unfolded with (n_deriv_I _ _ Hab' (S n) F Hf' c H1[*]
      ([1][/] _[//]nring_fac_ap_zero _ n) [*] (b[-]c) [^]n).
     repeat apply mult_wdl; apply pfwdef; algebra.
    repeat apply mult_wdl.
    apply eq_transitive_unfolded with (PartInt (fi (S n) Hf' (S n) (lt_n_S _ _ (lt_n_Sn _))) c Hc').
     2: simpl in |- *; apply csf_wd_unfolded; simpl in |- *; algebra.
    apply Feq_imp_eq with (Compact Hab).
     unfold Hab in |- *; apply Derivative_I_n_unique with (S n) F.
      apply n_deriv_lemma.
     apply Taylor_lemma1.
    auto.
   apply n_deriv_inc; auto.
  apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
 repeat (split; auto).
Qed.

End Taylor_Defs.
