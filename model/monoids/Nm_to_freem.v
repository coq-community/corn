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

Require Export CoRN.algebra.CMonoids.
Require Export CoRN.model.monoids.Nmonoid.
Require Export CoRN.model.setoids.Nfinsetoid.

Section p70text.

(**
** A morphism from the natural numbers to the free setoid with one element
*)

Let A:= (CSetoid_of_less 1).

(* begin hide *)
Let ZerolessOne: 0<1.
Proof.
 intuition.
Qed.

(* end hide *)

Fixpoint to_word (n:nat):(list (F 1)):=
match n with
|0 => (@nil (F 1))
|(S m)=> (cons (Build_F 1 0 ZerolessOne)(to_word m))
end.

Definition to_word_: nat_as_CMonoid -> (free_monoid_as_CMonoid A).
Proof.
 simpl.
 unfold Astar.
 unfold A.
 intro n.
 unfold CSetoid_of_less.
 simpl.
 apply to_word.
 exact n.
Defined.

Lemma  to_word_strext: (fun_strext to_word_).
Proof.
 simpl.
 unfold fun_strext.
 double induction x y.
    simpl.
    intuition.
   intros  n H2.
   simpl.
   unfold ap_nat.
   intros T H.
   set (H1:= (O_S n H)).
   elim H1.
  intros n H3.
  simpl.
  unfold ap_nat.
  intros T H.
  cut (0= (S n)).
   intro H2.
   set (H1:= (O_S n H2 )).
   elim H1.
  intuition.
 intros n H1 n0 H2.
 simpl.
 cut ( ap_fm A (to_word_ n0) (to_word_ n) -> S n0{#N}S n).
  intuition.
 intro H3.
 simpl in H2.
 set (H4:=(H2 n H3)).
 unfold ap_nat in H4 |- *.
 intro H5.
 apply H4.
 apply (eq_add_S n0 n H5).
Qed.

Definition to_word_as_CSetoid_fun:=
(Build_CSetoid_fun nat_as_CSetoid (free_csetoid_as_csetoid  A) to_word_ to_word_strext).

Lemma to_word_bijective: (bijective to_word_as_CSetoid_fun).
Proof.
 unfold bijective.
 split.
  unfold injective.
  simpl.
  intros a0.
  induction a0.
   intro a1.
   case a1.
    unfold ap_nat.
    intuition.
   simpl.
   intuition.
  intro a1.
  case a1.
   simpl.
   intuition.
  intros n H.
  unfold ap_nat in H.
  simpl.
  right.
  apply IHa0.
  unfold ap_nat.
  intro H1.
  rewrite H1 in H.
  apply H.
  reflexivity.
 unfold surjective.
 simpl.
 unfold Astar.
 unfold A.
 intro b.
 induction b.
  exists 0.
  simpl.
  exact I.
 elim IHb.
 intros c H.
 exists (S c).
 split.
  simpl in a.
  elim a.
  simpl.
  intuition.
 exact H.
Qed.

Lemma pres_plus_to_word:
forall (n m: nat_as_CMonoid),(to_word_ n)[+](to_word_ m)[=](to_word_ (n[+]m)).
Proof.
 simpl.
 intros n m.
 induction n.
  simpl.
  apply eq_fm_reflexive.
 simpl.
 intuition.
Qed.

End p70text.
