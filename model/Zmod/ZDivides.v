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


(* ZDivides.v, by Vince Barany *)

Require Export ZBasics.

(**
* The Divides-function over Z
In this section the function Zdivides will be defined. Various facts
on this Zdivides will then be proved.
*)


Definition Zdivides (a b : Z) : Prop := exists q : Z, (q * a)%Z = b.


(* <Warning> : Grammar is replaced by Notation *)

(* <Warning> : Syntax is discontinued *)

Section zdivides.

Lemma Zdivides_ref : forall a : Z, Zdivides a a.
intro.
exists 1%Z.
auto with zarith.
Qed.

Lemma Zdivides_trans :
 forall a b c : Z, Zdivides a b -> Zdivides b c -> Zdivides a c.
intros.
unfold Zdivides in H; elim H; intros.
unfold Zdivides in H0; elim H0; intros.
exists (x0 * x)%Z.
rewrite <- H2.
rewrite <- H1.
auto with zarith.
Qed.

Lemma Zdivides_zero_rht : forall z : Z, Zdivides z 0.
intro.
exists 0%Z.
auto with zarith.
Qed.

Lemma Zdivides_zero_lft : forall z : Z, Zdivides 0 z -> z = 0%Z.
intro z.
intro Hdiv; elim Hdiv. 
auto with zarith.
Qed.

Lemma Zdivides_one : forall z : Z, Zdivides 1 z.
intro.
exists z.
auto with zarith.
Qed.


(* Zdivides_antysym see below *)

Lemma Zdivides_mult_intro_lft :
 forall a b c : Z, Zdivides (a * b) c -> Zdivides b c.
intros a b c H.
unfold Zdivides in H; elim H; intros q H_.
exists (q * a)%Z.
rewrite <- Zmult_assoc.
assumption.
Qed.

Lemma Zdivides_mult_intro_rht :
 forall a b c : Z, Zdivides (a * b) c -> Zdivides a c.
intros a b c H.
unfold Zdivides in H; elim H; intros q H_.
exists (q * b)%Z.
rewrite <- Zmult_assoc.
rewrite (Zmult_comm b a).
assumption.
Qed.

Lemma Zdivides_mult_lft : forall a b : Z, Zdivides b (a * b).
intros.
exists a.
auto with zarith.
Qed.

Lemma Zdivides_mult_rht : forall a b : Z, Zdivides a (a * b).
intros.
exists b.
auto with zarith.
Qed.

Lemma Zdivides_mult_elim_lft :
 forall a b c : Z, Zdivides a c -> Zdivides a (b * c).
intros.
apply (Zdivides_trans a c (b * c)).
assumption.
apply Zdivides_mult_lft.
Qed.

Lemma Zdivides_mult_elim_rht :
 forall a b c : Z, Zdivides a b -> Zdivides a (b * c).
intros.
apply (Zdivides_trans a b (b * c)).
assumption.
apply Zdivides_mult_rht.
Qed.

Lemma Zdivides_mult_cancel_lft :
 forall a b c : Z, Zdivides a b -> Zdivides (c * a) (c * b).
intros.
unfold Zdivides in H; elim H; intros.
exists x.
rewrite <- H0.
rewrite Zmult_assoc.
rewrite Zmult_assoc.
rewrite (Zmult_comm x c).
reflexivity.
Qed.

Lemma Zdivides_mult_cancel_rht :
 forall a b c : Z, Zdivides a b -> Zdivides (a * c) (b * c).
intros.
unfold Zdivides in H; elim H; intros.
exists x.
rewrite <- H0.
auto with zarith.
Qed.

Let Zdiv_one_is_one : forall a : Z, (a > 0)%Z -> Zdivides a 1 -> a = 1%Z.
intros a H0 H1.
unfold Zdivides in H1; elim H1; intros q H1_.
apply Zle_antisymm.
auto with zarith.
rewrite <- (Zplus_0_l a).
rewrite <- H1_.
rewrite <- (Zmult_1_l (0 + a)).
rewrite (Zplus_0_l a).
apply (Zmult_pos_mon_le_rht q 1 a); auto with zarith.
cut (q > 0)%Z; auto with zarith.
rewrite Zmult_comm in H1_.
apply (Zdiv_pos_pos a); auto with zarith.
Defined.

Lemma Zdivides_antisymm :
 forall a b : Z,
 (a > 0)%Z -> (b > 0)%Z -> Zdivides a b -> Zdivides b a -> a = b.
intros a b H01 H02 H1 H2.
unfold Zdivides in H1; elim H1; intros q1 H1_.
unfold Zdivides in H2; elim H2; intros q2 H2_.
generalize H2_; intro H12_.
rewrite <- H1_ in H12_.
rewrite Zmult_assoc in H12_.
rewrite Zmult_comm in H12_.
rewrite <- H1_.
rewrite <- (Zmult_1_l a).
assert (Zdivides q1 1).
replace 1%Z with (q2 * q1)%Z.
apply Zdivides_mult_elim_lft.
apply Zdivides_ref.
apply (Zunit_eq_one (q2 * q1) a). 
auto with zarith.
assumption.
replace q1 with 1%Z.
auto with zarith.
symmetry  in |- *.
rewrite Zmult_comm in H1_; rewrite <- H1_ in H02.
apply Zdiv_one_is_one; auto.
apply (Zdiv_pos_pos a); auto. 
Qed.

Lemma Zdivides_plus_elim :
 forall a b c : Z, Zdivides a b -> Zdivides a c -> Zdivides a (b + c).
intros a b c H1 H2.
unfold Zdivides in H1; elim H1; intros q1 H1_.
unfold Zdivides in H2; elim H2; intros q2 H2_.
exists (q1 + q2)%Z.
rewrite Zmult_plus_distr_l.
auto with zarith.
Qed.

Lemma Zdivides_opp_elim_lft :
 forall a b : Z, Zdivides a b -> Zdivides (- a) b.
intros a b H.
unfold Zdivides in H; elim H; intros q H_.
exists (- q)%Z.
rewrite Zmult_opp_opp.
assumption.
Qed.

Lemma Zdivides_opp_elim_rht :
 forall a b : Z, Zdivides a b -> Zdivides a (- b).
intros a b H.
unfold Zdivides in H; elim H; intros q H_.
exists (- q)%Z.
rewrite Zopp_mult_distr_l_reverse.
auto with zarith.
Qed.

Lemma Zdivides_opp_elim :
 forall a b : Z, Zdivides a b -> Zdivides (- a) (- b).
intros.
apply Zdivides_opp_elim_lft.
apply Zdivides_opp_elim_rht.
assumption.
Qed.

Lemma Zdivides_opp_intro_lft :
 forall a b : Z, Zdivides (- a) b -> Zdivides a b.
intros a b H.
rewrite <- (Zopp_involutive a).
apply (Zdivides_opp_elim_lft _ _ H).
Qed.

Lemma Zdivides_opp_intro_rht :
 forall a b : Z, Zdivides a (- b) -> Zdivides a b.
intros a b H.
rewrite <- (Zopp_involutive b).
apply (Zdivides_opp_elim_rht _ _ H).
Qed.

Lemma Zdivides_opp_intro :
 forall a b : Z, Zdivides (- a) (- b) -> Zdivides a b.
intros.
apply Zdivides_opp_intro_lft.
apply Zdivides_opp_intro_rht.
assumption.
Qed.

Lemma Zdivides_minus_elim :
 forall a b c : Z, Zdivides a b -> Zdivides a c -> Zdivides a (b - c).
intros.
unfold Zminus in |- *.
apply Zdivides_plus_elim.
assumption.
apply Zdivides_opp_elim_rht.
assumption.
Qed.

Lemma Zdivides_mult_elim :
 forall a b c d : Z, Zdivides a b -> Zdivides c d -> Zdivides (a * c) (b * d).
intros a b c d H1 H2.
unfold Zdivides in H1; elim H1; intros q1 H1_.
unfold Zdivides in H2; elim H2; intros q2 H2_.
exists (q1 * q2)%Z.
rewrite <- H1_.
rewrite <- H2_.
rewrite Zmult_assoc.
rewrite Zmult_assoc.
rewrite <- (Zmult_assoc q1 q2 a).
rewrite (Zmult_comm q2 a).
rewrite Zmult_assoc.
reflexivity.
Qed.

Lemma Zdivides_mult_ll :
 forall a b c d : Z,
 (a * b)%Z = (c * d)%Z -> a <> 0%Z -> Zdivides a c -> Zdivides d b.
intros a b c d Heq Ha Hdiv.
elim Hdiv; intros x Hx.
rewrite <- Hx in Heq.
exists x.
apply (Zmult_intro_lft a).
assumption.
rewrite Heq.
rewrite Zmult_assoc.
rewrite (Zmult_comm x a).
auto.
Qed.

Lemma Zdivides_mult_lr :
 forall a b c d : Z,
 (a * b)%Z = (d * c)%Z -> a <> 0%Z -> Zdivides a c -> Zdivides d b.
intros a b c d; rewrite (Zmult_comm d c); apply Zdivides_mult_ll.
Qed.

Lemma Zdivides_mult_rl :
 forall a b c d : Z,
 (b * a)%Z = (c * d)%Z -> a <> 0%Z -> Zdivides a c -> Zdivides d b.
intros a b c d; rewrite (Zmult_comm b a); apply Zdivides_mult_ll.
Qed.

Lemma Zdivides_mult_rr :
 forall a b c d : Z,
 (b * a)%Z = (d * c)%Z -> a <> 0%Z -> Zdivides a c -> Zdivides d b.
intros a b c d; rewrite (Zmult_comm b a); rewrite (Zmult_comm d c);
 apply Zdivides_mult_ll.
Qed.

Lemma Zdivides_abs_elim_lft :
 forall a b : Z, Zdivides a b -> Zdivides (Zabs a) b.
intros a b.
case a; simpl in |- *; auto.
intros p H. 
generalize (Zdivides_opp_elim_lft (Zneg p) b H).
simpl in |- *; auto.
Qed.

Lemma Zdivides_abs_elim_rht :
 forall a b : Z, Zdivides a b -> Zdivides a (Zabs b).
intros a b.
case b; simpl in |- *; auto.
intros p H. 
generalize (Zdivides_opp_elim_rht a (Zneg p) H).
simpl in |- *; auto.
Qed.

Lemma Zdivides_abs_elim :
 forall a b : Z, Zdivides a b -> Zdivides (Zabs a) (Zabs b).
intros.
apply Zdivides_abs_elim_lft.
apply Zdivides_abs_elim_rht.
assumption.
Qed.

Lemma Zdivides_abs_intro_lft :
 forall a b : Z, Zdivides (Zabs a) b -> Zdivides a b.
intros a b.
case a; simpl in |- *; auto.
intros p; apply (Zdivides_opp_intro_lft (Zneg p) b).
Qed.

Lemma Zdivides_abs_intro_rht :
 forall a b : Z, Zdivides a (Zabs b) -> Zdivides a b.
intros a b.
case b; simpl in |- *; auto.
intros p; apply (Zdivides_opp_intro_rht a (Zneg p)).
Qed.

Lemma Zdivides_abs_intro :
 forall a b : Z, Zdivides (Zabs a) (Zabs b) -> Zdivides a b.
intros.
apply Zdivides_abs_intro_lft.
apply Zdivides_abs_intro_rht.
assumption.
Qed.

Lemma Zdivisor_pos_le :
 forall a b : Z, (a > 0)%Z -> Zdivides b a -> (a >= b)%Z.
unfold Zdivides in |- *.
intros.
elim H0.
intros.
rewrite <- H1.
rewrite Zmult_comm.
apply Zmult_pos_mon.
rewrite Zmult_comm.
rewrite H1.
assumption.
Qed.

Lemma Zdivisor_small :
 forall a b : Z, Zdivides b a -> (Zabs a < b)%Z -> a = 0%Z.
intros a b Hdiv Hlt.
generalize (Zdivides_abs_elim_rht _ _ Hdiv); intro Hdivabs.
set (A := a). assert (HA : A = a). auto. generalize HA.
case A.
auto.
intros p Hp.
assert (Hfalse : (b < b)%Z).
apply (Zle_lt_trans b (Zabs a) b).
apply Zge_le.
apply (Zdivisor_pos_le (Zabs a) b).
rewrite <- Hp; simpl in |- *; auto with zarith.
assumption.
assumption.
elim (Zlt_irrefl b Hfalse).
intros p Hp.
assert (Hfalse : (b < b)%Z).
apply (Zle_lt_trans b (Zabs a) b).
apply Zge_le.
apply (Zdivisor_pos_le (Zabs a) b).
rewrite <- Hp; simpl in |- *.
auto with zarith.
assumption.
assumption.
elim (Zlt_irrefl b Hfalse).
Qed.

Lemma Zmodeq_small :
 forall a b c : Z,
 (0 <= a < c)%Z -> (0 <= b < c)%Z -> Zdivides c (a - b) -> a = b.
intros a b c Ha Hb Hc.
cut ((a - b)%Z = 0%Z); auto with zarith.
apply (Zdivisor_small (a - b) c).
assumption.
apply Zabs_lt_elim; auto with zarith.
Qed.

Lemma Zdiv_remainder_unique :
 forall a b q1 r1 q2 r2 : Z,
 a = (q1 * b + r1)%Z ->
 (0 <= r1 < b)%Z -> a = (q2 * b + r2)%Z -> (0 <= r2 < b)%Z -> r1 = r2.
intros a b q1 r1 q2 r2 Hq1 Hr1 Hq2 Hr2.
apply (Zmodeq_small r1 r2 b). 
assumption.
assumption.
assert ((r1 - r2)%Z = ((q2 - q1) * b)%Z).
 rewrite Hq1 in Hq2.
 rewrite BinInt.Zmult_minus_distr_r.
 auto with zarith.
rewrite H.
apply Zdivides_mult_elim_lft.
apply Zdivides_ref.
Qed.

Lemma Zdiv_quotient_unique :
 forall a b q1 r1 q2 r2 : Z,
 a = (q1 * b + r1)%Z ->
 (0 <= r1 < b)%Z -> a = (q2 * b + r2)%Z -> (0 <= r2 < b)%Z -> q1 = q2.
intros a b q1 r1 q2 r2 Hq1 Hr1 Hq2 Hr2.
assert (Hr : r1 = r2). 
 apply (Zdiv_remainder_unique a b q1 r1 q2 r2); assumption.
rewrite Hr in Hq1.
rewrite Hq1 in Hq2.
assert (Hb0 : b <> 0%Z).
 assert (Hbpos : (0 < b)%Z).
 apply (Zle_lt_trans 0 r1 b).
 tauto.
 tauto.
 auto with zarith.
assert (Hb : (q1 * b)%Z = (q2 * b)%Z).
 auto with zarith.
apply (Zmult_intro_rht _ _ _ Hb0 Hb).
Qed.

Lemma Zmod0_Zopp :
 forall a b : Z, b <> 0%Z -> (a mod b)%Z = 0%Z -> (a mod - b)%Z = 0%Z.
intros a b.
generalize (Z_mod_lt (Zabs a) (Zabs b)).
case a.
case b; unfold Zabs, Zopp, Zmod, Zdiv_eucl in |- *; auto with zarith.
case b; unfold Zabs, Zopp, Zmod, Zdiv_eucl in |- *.
 auto with zarith.
 intros p q.
  elim (Zdiv_eucl_POS q (Zpos p)); intros Q R.
  intros Hlt Hp HR; rewrite HR; auto with zarith.
 intros p q.
  elim (Zdiv_eucl_POS q (Zpos p)); intros Q R.
  case R. 
   auto with zarith.
   intro r'; intros H0 H1 H2.
   cut (Zpos r' = Zpos p); auto with zarith. 
   fold (- Zpos p)%Z in H2.
   auto with zarith.
   intro r'; intros H0 H1 H2.
   elim H0; auto with zarith.
case b; unfold Zabs, Zopp, Zmod, Zdiv_eucl in |- *.
 auto with zarith.
 intros p q.
  elim (Zdiv_eucl_POS q (Zpos p)); intros Q R.
  case R; intros r' H0; intros; try (cut (Zpos r' = Zpos p); elim H0);
   auto with zarith.
 intros p q.
  elim (Zdiv_eucl_POS q (Zpos p)); intros Q R.
  case R; intros; try discriminate; try tauto.
Qed.

Lemma Zdiv_Zopp :
 forall a b : Z, (a mod b)%Z = 0%Z -> (a / - b)%Z = (- (a / b))%Z.
intros a b.
unfold Zmod, Zdiv, Zdiv_eucl in |- *.
case a.
 auto.
 intro A.
 case b; unfold Zopp in |- *.
  auto.
  intro B.
   elim (Zdiv_eucl_POS A (Zpos B)); intros q r.
   intro Hr; rewrite Hr; auto.
  intro B.
   generalize (Z_mod_lt (Zpos A) (Zpos B)).
   unfold Zmod, Zdiv_eucl in |- *.
   elim (Zdiv_eucl_POS A (Zpos B)); intros q r.
   case r.
     intros _ HR; fold (- q)%Z in |- *; fold (- - q)%Z in |- *;
      rewrite Zopp_involutive; auto.
     intros R Hlt HR.
      assert (H : Zpos R = Zpos B).
       rewrite <- (Zplus_0_r (Zpos B)); rewrite <- HR; rewrite Zplus_assoc;
        fold (- Zpos B)%Z in |- *.
       auto with zarith.
      rewrite H in Hlt.
      elim Hlt; auto with zarith.
     intros R Hlt HR.
      elim Hlt; auto with zarith; intro Hfalse; elim Hfalse; auto with zarith.
 intro A.
 case b; unfold Zopp in |- *.
  auto.
  intro B.
   generalize (Z_mod_lt (Zpos A) (Zpos B)).
   unfold Zmod, Zdiv_eucl in |- *.
   elim (Zdiv_eucl_POS A (Zpos B)); intros q r.
   case r.
     intros _ HR; fold (- q)%Z in |- *; fold (- - q)%Z in |- *;
      rewrite Zopp_involutive; auto.
     intros R Hlt HR.
      assert (H : Zpos R = Zpos B).
       rewrite <- (Zplus_0_r (Zpos R)); rewrite <- HR; unfold Zminus in |- *;
        rewrite Zplus_assoc; auto with zarith.
      rewrite H in Hlt.
      elim Hlt; auto with zarith.
     intros R Hlt HR.
      elim Hlt; auto with zarith; intro Hfalse; elim Hfalse; auto with zarith.
  intro B.
   generalize (Z_mod_lt (Zpos A) (Zpos B)).
   unfold Zmod, Zdiv_eucl in |- *.
   elim (Zdiv_eucl_POS A (Zpos B)); intros q r.
   case r.
     intros _ HR; fold (- q)%Z in |- *; auto.
     intros; discriminate.
     intros; discriminate.
Qed.

Lemma Zmod0_Zdivides_pos :
 forall a b : Z, (b > 0)%Z -> Zdivides b a -> (a mod b)%Z = 0%Z.
intros a b Hb Hdiv.
elim Hdiv; intros q Hq.
rewrite (Z_div_mod_eq a b) in Hq; rewrite <- (Zplus_0_r (q * b)) in Hq.
symmetry  in |- *.
apply (Zdiv_remainder_unique (q * b + 0) b q 0 (a / b) (a mod b)).
reflexivity.
auto with zarith.
rewrite (Zmult_comm (a / b) b); exact Hq.
apply Z_mod_lt; auto with zarith.
exact Hb.
Qed.

Lemma Zdivides_Zmod0_pos :
 forall a b : Z, (b > 0)%Z -> (a mod b)%Z = 0%Z -> Zdivides b a.
intros a b Hb Hmod.
rewrite (Z_div_mod_eq a b).
rewrite (Zmult_comm b (a / b)); rewrite Hmod; rewrite Zplus_0_r.
exists (a / b)%Z.
reflexivity.
exact Hb.
Qed.

Lemma Zmod0_Zdivides :
 forall a b : Z, b <> 0%Z -> Zdivides b a -> (a mod b)%Z = 0%Z.
intros a b.
case b.
 tauto.
 intros p _; apply Zmod0_Zdivides_pos; auto with zarith.
 intros p _.
  generalize (Zmod0_Zdivides_pos a (Zpos p)); intro H.
  fold (- Zpos p)%Z in |- *.   
  intro Hdiv.
  apply Zmod0_Zopp.
  intro; discriminate.
  apply H.
  auto with zarith.
  rewrite <- (Zopp_involutive (Zpos p)).
  apply Zdivides_opp_elim_lft.
  assumption.
Qed.

Lemma Zdivides_Zmod0 :
 forall a b : Z, b <> 0%Z -> (a mod b)%Z = 0%Z -> Zdivides b a.
intros a b.
case b.
 tauto.
 intros p _; apply Zdivides_Zmod0_pos; auto with zarith.
 intros p _.
  generalize (Zdivides_Zmod0_pos a (Zpos p)); intro H.
  fold (- Zpos p)%Z in |- *.   
  intro Hmod.
  apply Zdivides_opp_elim_lft.
  apply H.
  auto with zarith.
  rewrite <- (Zopp_involutive (Zpos p)).
  apply Zmod0_Zopp.
  simpl in |- *; intros; discriminate.
  assumption.
Qed.

Lemma Zmod_mult_cancel_lft : forall a b : Z, ((a * b) mod a)%Z = 0%Z.
intros a b.
case a.
auto with zarith.
intro p. 
 apply Zmod0_Zdivides_pos. 
 auto with zarith.
 apply Zdivides_mult_elim_rht.
 apply Zdivides_ref.
intro p.
 apply Zmod0_Zdivides. 
 auto with zarith.
 apply Zdivides_mult_elim_rht.
 apply Zdivides_ref.
Qed.

Lemma Zmod_mult_cancel_rht : forall a b : Z, ((a * b) mod b)%Z = 0%Z.
intros a b.
rewrite Zmult_comm.
apply Zmod_mult_cancel_lft.
Qed.

Lemma Zdiv_mult_cancel_lft : forall a b : Z, a <> 0%Z -> (a * b / a)%Z = b.
intros a b.
case a.
 auto with zarith.
 intros p _. 
  apply
   (Zdiv_quotient_unique (Zpos p * b) (Zpos p) (Zpos p * b / Zpos p)
      ((Zpos p * b) mod Zpos p) b 0).
  rewrite (Zmult_comm (Zpos p * b / Zpos p) (Zpos p)).
  apply Z_div_mod_eq; auto with zarith.
  apply Z_mod_lt; auto with zarith.
  rewrite Zplus_0_r; auto with zarith.
  auto with zarith.
 intros p _. 
  fold (- Zpos p)%Z in |- *.
  rewrite Zdiv_Zopp.
  cut ((- Zpos p * b / Zpos p)%Z = (- b)%Z); auto with zarith.
  unfold Zopp in |- *; fold (- b)%Z in |- *.
  apply
   (Zdiv_quotient_unique (Zneg p * b) (Zpos p) (Zneg p * b / Zpos p)
      ((Zneg p * b) mod Zpos p) (- b) 0).
  rewrite (Zmult_comm (Zneg p * b / Zpos p) (Zpos p)).
  apply Z_div_mod_eq; auto with zarith.
  apply Z_mod_lt; auto with zarith.
  rewrite Zplus_0_r; rewrite Zmult_opp_comm; fold (- Zpos p)%Z in |- *;
   auto with zarith.
  auto with zarith.
  rewrite Zmult_opp_comm.
  apply Zmod_mult_cancel_lft.
Qed.

Lemma Zdiv_mult_cancel_rht : forall a b : Z, b <> 0%Z -> (a * b / b)%Z = a.
intros a b.
rewrite Zmult_comm.
apply Zdiv_mult_cancel_lft.
Qed.

Lemma Zdiv_plus_elim :
 forall a b d : Z,
 Zdivides d a -> Zdivides d b -> ((a + b) / d)%Z = (a / d + b / d)%Z.
intros a b d Ha Hb.
case (Zdec d).
intro Hd; rewrite Hd; case (a + b)%Z; case a; case b; simpl in |- *; auto.
intro Hd.
elim Ha; clear Ha; intros x Ha; rewrite <- Ha.
elim Hb; clear Hb; intros y Hb; rewrite <- Hb.
rewrite <- Zmult_plus_distr_l.
repeat rewrite Zdiv_mult_cancel_rht; auto.
Qed.

Lemma Zdiv_elim :
 forall a b d : Z,
 d <> 0%Z -> Zdivides d a -> Zdivides d b -> (a / d)%Z = (b / d)%Z -> a = b.
intros a b d Hd Ha Hb.
elim Ha; clear Ha; intros x Ha; rewrite <- Ha.
elim Hb; clear Hb; intros y Hb; rewrite <- Hb.
repeat rewrite Zdiv_mult_cancel_rht; auto.
intro Hxy; rewrite Hxy; auto.
Qed.

Lemma Zabs_div_lft : forall a : Z, (Zabs a / a)%Z = Zsgn a.
intro a.
rewrite Zmult_sgn_eq_abs.
case (Zdec a).
intro Ha. rewrite Ha. simpl in |- *. auto with zarith.
apply Zdiv_mult_cancel_rht.
Qed.

Lemma Zabs_div_rht : forall a : Z, (a / Zabs a)%Z = Zsgn a.
intro a.
set (A := Zabs a).
set (sa := Zsgn a).
replace a with (Zabs a * Zsgn a)%Z.
unfold sa in |- *; clear sa.
case (Zdec A).
unfold A in |- *; intro HA. 
 cut (a = 0%Z); auto with zarith. 
 intro Ha; rewrite Ha; auto with zarith.
unfold A in |- *; apply Zdiv_mult_cancel_lft.
rewrite Zmult_comm.
auto with zarith.
Qed.

Lemma Zdiv_same : forall a : Z, a <> 0%Z -> (a / a)%Z = 1%Z.
intros a.
case a.
tauto.
intros; apply Z_div_same; auto with zarith.
intros A HA.
fold (- Zpos A)%Z in |- *.
rewrite Zdiv_Zopp.
simpl in |- *.
replace (Zpos A) with (Zabs (Zneg A)); auto.
rewrite Zabs_div_rht.
auto.
replace (- Zpos A)%Z with (-1 * Zpos A)%Z; auto with zarith.
apply Zmod_mult_cancel_rht.
Qed.


Lemma Zmult_div_simpl_1 :
 forall a b c d : Z,
 (a * b)%Z = (c * d)%Z -> a <> 0%Z -> Zdivides a c -> Zdivides d b.
intros a b c d Heq Ha Hdiv.
elim Hdiv; intros x Hx.
rewrite <- Hx in Heq.
rewrite (Zmult_comm x a) in Heq.
rewrite <- Zmult_assoc in Heq.
exists x.
apply (Zmult_intro_lft a); auto.
Qed.

Lemma Zmult_div_simpl_2 :
 forall a b c d : Z,
 (a * b)%Z = (d * c)%Z -> a <> 0%Z -> Zdivides a c -> Zdivides d b.
intros a b c d; rewrite (Zmult_comm d c); apply Zmult_div_simpl_1.
Qed.

Lemma Zmult_div_simpl_3 :
 forall a b c d : Z,
 (b * a)%Z = (c * d)%Z -> a <> 0%Z -> Zdivides a c -> Zdivides d b.
intros a b c d; rewrite (Zmult_comm b a); apply Zmult_div_simpl_1.
Qed.

Lemma Zmult_div_simpl_4 :
 forall a b c d : Z,
 (b * a)%Z = (d * c)%Z -> a <> 0%Z -> Zdivides a c -> Zdivides d b.
intros a b c d; rewrite (Zmult_comm b a); rewrite (Zmult_comm d c);
 apply Zmult_div_simpl_1.
Qed.


Lemma Zdivides_dec : forall a b : Z, {Zdivides a b} + {~ Zdivides a b}.
intros a b.
case (Zdec b).
intro Hb.
 rewrite Hb.
 left.
 apply Zdivides_zero_rht.
intro Hb.
 case (Zdec a).
 intro Ha.
   rewrite Ha.
   right.
   intro H0.
   rewrite (Zdivides_zero_lft b H0) in Hb.
   elim Hb.
   auto.
 intro Ha.
 generalize (Zdivides_Zmod0 b a Ha).
 generalize (Zmod0_Zdivides b a Ha). 
 case (Zdec (b mod a)); auto.
Qed.


End zdivides.



Hint Resolve Zdivides_zero_lft: zarith.
Hint Resolve Zdivides_zero_rht: zarith.
Hint Resolve Zdivides_one: zarith.
Hint Resolve Zdivides_ref: zarith.
Hint Resolve Zdivides_trans: zarith.
Hint Resolve Zdivides_mult_intro_lft: zarith.
Hint Resolve Zdivides_mult_intro_rht: zarith.
Hint Resolve Zdivides_mult_lft: zarith.
Hint Resolve Zdivides_mult_rht: zarith.
Hint Resolve Zdivides_mult_elim_lft: zarith.
Hint Resolve Zdivides_mult_elim_rht: zarith.
Hint Resolve Zdivides_mult_cancel_lft: zarith.
Hint Resolve Zdivides_mult_cancel_rht: zarith.
Hint Resolve Zdivides_antisymm: zarith.
Hint Resolve Zdivides_plus_elim: zarith.
Hint Resolve Zdivides_opp_elim_lft: zarith.
Hint Resolve Zdivides_opp_elim_rht: zarith.
Hint Resolve Zdivides_opp_elim: zarith.
Hint Resolve Zdivides_opp_intro_lft: zarith.
Hint Resolve Zdivides_opp_intro_rht: zarith.
Hint Resolve Zdivides_opp_intro: zarith.
Hint Resolve Zdivides_minus_elim: zarith.
Hint Resolve Zdivides_mult_elim: zarith.
Hint Resolve Zdivides_mult_ll: zarith.
Hint Resolve Zdivides_mult_lr: zarith.
Hint Resolve Zdivides_mult_rl: zarith.
Hint Resolve Zdivides_mult_rr: zarith.
Hint Resolve Zdivides_abs_elim_lft: zarith.
Hint Resolve Zdivides_abs_elim_rht: zarith.
Hint Resolve Zdivides_abs_elim: zarith.
Hint Resolve Zdivides_abs_intro_lft: zarith.
Hint Resolve Zdivides_abs_intro_rht: zarith.
Hint Resolve Zdivides_abs_intro: zarith.
Hint Resolve Zdivisor_pos_le: zarith.
Hint Resolve Zdivisor_small: zarith.
Hint Resolve Zmodeq_small: zarith.
Hint Resolve Zdiv_remainder_unique: zarith.
Hint Resolve Zdiv_quotient_unique: zarith.
Hint Resolve Zmod0_Zopp: zarith.
Hint Resolve Zdiv_Zopp: zarith.
Hint Resolve Zmod0_Zdivides: zarith.
Hint Resolve Zdivides_Zmod0: zarith.
Hint Resolve Zmod_mult_cancel_lft: zarith.
Hint Resolve Zmod_mult_cancel_rht: zarith.
Hint Resolve Zdiv_mult_cancel_lft: zarith.
Hint Resolve Zdiv_mult_cancel_rht: zarith.
Hint Resolve Zdiv_plus_elim: zarith.
Hint Resolve Zdiv_elim: zarith.
Hint Resolve Zabs_div_lft: zarith.
Hint Resolve Zabs_div_rht: zarith.
Hint Resolve Zdiv_same: zarith.
Hint Resolve Zmult_div_simpl_1: zarith.
Hint Resolve Zmult_div_simpl_2: zarith.
Hint Resolve Zmult_div_simpl_3: zarith.
Hint Resolve Zmult_div_simpl_4: zarith.
Hint Resolve Zdivides_dec: zarith.


Section ineq.

Lemma Zmod_POS_nonNEG :
 forall a b p : positive, (Zpos a mod Zpos b)%Z <> Zneg p.
intros a b p.
generalize (Z_mod_lt (Zpos a) (Zpos b)).
intro H.
elim H.
intros H0 H1.
intro Hfalse.
rewrite Hfalse in H0.
elim H0.
auto with zarith.
auto with zarith.
Qed.

Lemma Zdiv_POS :
 forall a b : positive, (Zpos b * (Zpos a / Zpos b) <= Zpos a)%Z.
intros a b.
rewrite <- (Zplus_0_r (Zpos b * (Zpos a / Zpos b))).
set (lhs := (Zpos b * (Zpos a / Zpos b) + 0)%Z) in *.
rewrite (Z_div_mod_eq (Zpos a) (Zpos b)).
unfold lhs in |- *.
apply Zplus_le_compat_l.
auto with zarith.
generalize (Z_mod_lt (Zpos a) (Zpos b)).
intro H.
elim H.
auto with zarith.
auto with zarith.
auto with zarith.
Qed.

Lemma Zmod_lt_POS :
 forall a b : positive, (Zpos a < Zpos b)%Z -> (Zpos a mod Zpos b)%Z = Zpos a.
intros a b Hlt.
apply
 (Zdiv_remainder_unique (Zpos a) (Zpos b) (Zpos a / Zpos b)
    (Zpos a mod Zpos b) 0 (Zpos a)); auto with zarith.
rewrite Zmult_comm.
apply Z_div_mod_eq; auto with zarith.
apply Z_mod_lt; auto with zarith.
Qed.

Lemma Zdiv_lt_POS :
 forall a b : positive, (Zpos a < Zpos b)%Z -> (Zpos a / Zpos b)%Z = 0%Z.
intros a b Hlt.
apply
 (Zdiv_quotient_unique (Zpos a) (Zpos b) (Zpos a / Zpos b)
    (Zpos a mod Zpos b) 0 (Zpos a)); auto with zarith.
rewrite Zmult_comm.
apply Z_div_mod_eq; auto with zarith.
apply Z_mod_lt; auto with zarith.
Qed.

End ineq.


Hint Resolve Zmod_POS_nonNEG: zarith.
Hint Resolve Zdiv_POS: zarith.
Hint Resolve Zmod_lt_POS: zarith.
Hint Resolve Zdiv_lt_POS: zarith.
