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

(** printing Zero %\ensuremath{\mathbf0}% #0# *)

Require Export Euclid.
Require Export Cmod.
Require Export CSemiGroups.
Require Export csetoid_rewrite.
Require Export Nsec.

(* Begin_SpecReals *)

(**
* Monoids %\label{section:monoids}%
** Definition of monoids
*)

Record is_CMonoid (M : CSemiGroup) (Zero : M) : Prop := 
  {runit : is_rht_unit (csg_op (c:=M)) Zero;
   lunit : is_lft_unit (csg_op (c:=M)) Zero}.

Record CMonoid : Type := 
  {cm_crr   :> CSemiGroup;
   cm_unit  :  cm_crr;
   cm_proof :  is_CMonoid cm_crr cm_unit}.

(**
%\begin{nameconvention}%
In the names of lemmas, we will denote [Zero] with [zero].
We denote [ [#] Zero] in the names of lemmas by [ap_zero]
(and not, e.g.%\% [nonzero]).
%\end{nameconvention}%
*)

(* Begin_SpecReals *)

(**
The predicate "non-zero" is defined.
In lemmas we will continue to write [x [#] Zero], rather than
[(nonZeroP x)], but the predicate is useful for some high-level definitions,
e.g. for the setoid of non-zeros.
*)

Notation Zero := (cm_unit _).

Definition nonZeroP (M : CMonoid) (x : M) : CProp := x [#] Zero.

(* End_SpecReals *)

Implicit Arguments nonZeroP [M].

(**
** Monoid axioms
%\begin{convention}% Let [M] be a monoid.
%\end{convention}%
*)
Section CMonoid_axioms.
Variable M : CMonoid.

Lemma CMonoid_is_CMonoid : is_CMonoid M (cm_unit M).
elim M; auto.
Qed.

Lemma cm_rht_unit : is_rht_unit csg_op (Zero:M).
elim CMonoid_is_CMonoid; auto.
Qed.

Lemma cm_lft_unit : is_lft_unit csg_op (Zero:M).
elim CMonoid_is_CMonoid; auto.
Qed.

End CMonoid_axioms.

(**
** Monoid basics
%\begin{convention}% Let [M] be a monoid.
%\end{convention}%
*)
Section CMonoid_basics.
Variable M : CMonoid.

Lemma cm_rht_unit_unfolded : forall x : M, x[+]Zero [=] x.
Proof cm_rht_unit M.

Lemma cm_lft_unit_unfolded : forall x : M, Zero[+]x [=] x.
Proof cm_lft_unit M.

Hint Resolve cm_rht_unit_unfolded cm_lft_unit_unfolded: algebra.

Lemma cm_unit_unique_lft : forall x : M, is_lft_unit csg_op x -> x [=] Zero.
intros x h. red in h.
Step_final (x[+]Zero).
Qed.

Lemma cm_unit_unique_rht : forall x : M, is_rht_unit csg_op x -> x [=] Zero.
intros x h. red in h.
Step_final (Zero[+]x).
Qed.

(* Begin_SpecReals *)

(**
The proof component of the monoid is irrelevant.
*)

Lemma is_CMonoid_proof_irr : forall (S:CSetoid) (Zero:S) (plus : CSetoid_bin_op S)
 (p q : associative plus), is_CMonoid (Build_CSemiGroup S plus p) Zero ->
 is_CMonoid (Build_CSemiGroup S plus q) Zero.
intros S one mult p q H.
elim H; intros runit0 lunit0.
simpl in runit0.
simpl in lunit0.
apply Build_is_CMonoid; simpl in |- *; assumption.
Qed.

(* End_SpecReals *)

(**
** Submonoids
%\begin{convention}%
Let [P] a predicate on [M] containing [Zero] and closed under [[+]].
%\end{convention}%
*)

Section SubCMonoids.
Variable P : M -> CProp.
Variable Punit : P Zero.
Variable op_pres_P : bin_op_pres_pred _ P csg_op.

Let subcrr : CSemiGroup := Build_SubCSemiGroup _ _ op_pres_P.

Lemma ismon_scrr : is_CMonoid subcrr (Build_subcsetoid_crr _ _ _ Punit).
split; red in |- *.

(* right unit *)
intro x. case x. intros scs_elem scs_prf.
apply (cm_rht_unit_unfolded scs_elem).

(* left unit *)
intro x. case x. intros scs_elem scs_prf.
apply (cm_lft_unit_unfolded scs_elem).
Qed.

Definition Build_SubCMonoid : CMonoid := Build_CMonoid subcrr _ ismon_scrr.

End SubCMonoids.

End CMonoid_basics.

Section Th13.
(** **Morphism, isomorphism and automorphism of Monoids
%\begin{convention}%
Let [M1 M2 M M':CMonoid].
%\end{convention}%
*)
Variable M1:CMonoid.
Variable M2:CMonoid.

Definition morphism (f:(CSetoid_fun M1 M2)):CProp:=
(f (Zero)[=]Zero /\ forall (a b:M1), (f (a[+]b))[=] (f a)[+](f b)).

Definition isomorphism (f:(CSetoid_fun M1 M2)):CProp:=
(morphism f) and (bijective f).

End Th13.

Section p71E2b1.

Definition isomorphic (M:CMonoid)(M':CMonoid): CProp:=
{f:(CSetoid_fun M M')|(isomorphism M M' f)}.

End p71E2b1.

Section Th14.
(**
%\begin{convention}%
Let [f:(CSetoid_fun M1 M2)] and [isof: (isomorphism M1 M2 f)].
%\end{convention}%
*)

Variable M1: CMonoid.
Variable M2: CMonoid.
Variable f: (CSetoid_fun M1 M2).
Variable isof: (isomorphism M1 M2 f).

Lemma iso_imp_bij: (bijective f).
unfold isomorphism in isof.
intuition.
Qed.

Lemma iso_inv: (isomorphism M2 M1 (Inv f (iso_imp_bij))).
unfold isomorphism.
split.
unfold morphism.
split.
unfold isomorphism in isof.
unfold morphism in isof.
elim isof.
intros H0 H1.
elim H0.
clear H0.
intros H3 H4. 
astepl ((Inv f iso_imp_bij) (f Zero)).
unfold Inv.
simpl.
apply inv2.

intros a b.
unfold isomorphism in isof.
elim isof.
intros H0 H1.
unfold bijective in H1.
elim H1.
clear H1.
intros H1 H2.
unfold surjective in H2.
set (Ha:= (H2 a)).
set (Hb:= (H2 b)).
elim Ha.
intros a' fa'a.
elim Hb.
intros b' fb'b.
unfold morphism in H0.
astepl ((Inv f iso_imp_bij) ((csg_op (c:=M2)) (f a') (f b'))).
astepl ((Inv f iso_imp_bij) ( f ( a'[+] b'))).
set (H3:= (inv2 M1 M2 f iso_imp_bij (a'[+]b'))).
astepl (a'[+]b').
astepr (a'[+] b').
intuition.

set (H4:=(inv2 M1 M2 f iso_imp_bij a')).
apply csbf_wd_unfolded.
astepr (Inv f iso_imp_bij (f a')).
intuition.

set (H5:= (inv2 M1 M2 f iso_imp_bij b')).
astepr (Inv f iso_imp_bij (f b')).
intuition.

intuition.

apply Inv_bij.
Qed.

End Th14.

Section p71R2.

Variable M:CMonoid.

Definition automorphism:= (isomorphism M M).

End p71R2.

Section p71E1.
(** **Power in a monoid
%\begin{convention}%
Let [M:CMonoid] and [c:M].
%\end{convention}%
*)

Variable M:CMonoid.
Variable c:M.

Fixpoint power_CMonoid (m:M)(n:nat){struct n}:M:=
match n with 
|0 => (cm_unit M)
|(S p) => m [+] (power_CMonoid m p)
end.

End p71E1.

Implicit Arguments power_CMonoid [M].

Lemma power_plus:forall (M:CMonoid)(a:M)(m n:nat),
  (power_CMonoid a (m+n))[=]
  (power_CMonoid a m)[+](power_CMonoid a n). 
intros M a m n.
induction m.
simpl.
apply eq_symmetric.
apply cm_lft_unit_unfolded.

simpl.
astepl (csbf_fun M M M (csg_op (c:=M)) a ((csbf_fun M M M (csg_op (c:=M)) (power_CMonoid a m)
          (power_CMonoid a n)))).
Algebra.
Qed.


(** **Cyclicity
*)

Definition is_generator (M:CMonoid)(u:M):CProp:=
  forall (m:M),{n:nat | (power_CMonoid u n)[=]m}.

Definition cyclic : CMonoid -> CProp :=
  fun M => 
  {u:M | (forall (m:M),{n:nat | (power_CMonoid u n)[=]m}):CProp}.

Section gen_cyc.

Lemma power_k:forall (M:CMonoid)(u:M)(k l s:nat),(is_generator M u)->
  ((k<l and 
  (power_CMonoid u  k [=] power_CMonoid u l)
  and ((forall (k0 l0:nat), (k0<k or (k0=k and l0<l))-> 
  (power_CMonoid u k0 [#] power_CMonoid u l0)))):CProp)->
  (power_CMonoid u  k)[=](power_CMonoid u (k+(s*(l-k)))).
intros M u k l s H.
unfold is_generator in H.
intros H0.
induction s.
simpl.
replace (k+0) with k.
intuition.

intuition.

simpl.
replace (k+((l-k)+s*(l-k)))  with (l + s*(l-k)).
2:intuition.
set (H1:= (power_plus M u l (s*(l-k)))).
astepr  (csbf_fun (csg_crr (cm_crr M)) (csg_crr (cm_crr M))
         (csg_crr (cm_crr M)) (csg_op (c:=cm_crr M)) 
         (power_CMonoid u l) (power_CMonoid u (s * (l - k)))).
elim H0.
clear H0.
intros H0 H0'.
elim H0'.
clear H0'.
intros H0' H0''.
cut ( power_CMonoid u l[=]power_CMonoid u k).
intro H4.
csetoid_rewrite H4.
2:apply eq_symmetric.
2:exact H0'.
set (H5:=(power_plus M  u k (s*(l-k)))).
cut (csbf_fun M M M (csg_op (c:=M)) (power_CMonoid  u k)
         (power_CMonoid u (s * (l - k)))[=]power_CMonoid u (k + s * (l - k))).
intros H6.
csetoid_rewrite H6.
exact IHs.

apply eq_symmetric.
exact H5.
Qed.

Lemma power_k_n:forall (M:CMonoid)(u:M)(k l n :nat)
  (H2:((Z_of_nat (l-k)>0)%Z)),(is_generator M u)->(k<n)->
  ((k<l and 
  (power_CMonoid u k [=] power_CMonoid u l)
  and ((forall (k0 l0:nat), (k0<k or (k0=k and l0<l))-> 
  (power_CMonoid u k0 [#] power_CMonoid u l0)))):CProp)->
  (power_CMonoid u n)[=](power_CMonoid u (k+(mod_nat (n-k) (l-k) H2))).
intros M u  k l n H2 H H15.
set (H13:=(power_k M u k l)).
intros H4.
cut ((l-k)>0)%Z.
intro H5.
set (H6:=(Z_div_mod_eq (n-k)(l-k) H5)).
2:intuition.
cut (((n - k) mod (l - k))= (n-k)%Z -((l - k) * ((n - k) / (l - k))))%Z.
2:intuition.
set (H7:=(mod_nat_correct (n-k) (l-k) H2)).
intro H8.
cut {s:nat | (mod_nat (n-k)(l-k) H2)=(n-k)-s*(l-k) and s*(l-k)<=(n-k)}.
intro H9.
elim H9.
clear H9.
intros s H9.
elim H9.
clear H9.
intros H9 H9'.
rewrite H9.
replace (power_CMonoid u n) with (power_CMonoid u ((k+s*(l-k))+((n-k)-s*(l-k)))).
2: replace ((k + s * (l - k))+((n - k) - s * (l - k))) with n.
2:reflexivity.

set (H10:=(power_plus M  u  (k+(s*(l-k))) ((n-k)-s*(l-k)))).
csetoid_rewrite H10.
set (H11:=(power_plus M u k (n-k-s*(l-k)))).
csetoid_rewrite H11.
csetoid_replace (power_CMonoid u (k + s * (l - k)))
                   (power_CMonoid u k).                                     
apply eq_reflexive.               

intuition.

cut (n=k+(n-k)).
intro H10.
cut (n=((k+(n-k))+(s*(l-k)-s*(l-k)))).
intro H11.
cut  ((k+(n-k))+(s*(l-k)-s*(l-k)) = (k + s * (l - k) + (n - k - s * (l - k)))).
intro H12.
rewrite<- H11 in H12.
exact H12.

apply minus4.
split.
intuition.
exact H9'.
rewrite<- H10.
cut ((s*(l-k)-s*(l-k))=0).
intro H11.
rewrite H11.
intuition.
intuition.

cut (n=n+(k-k)).
intro H10.
cut (n+(k-k)=k+(n-k)).
intro H11.
rewrite<- H10 in H11.
exact H11.

apply minus3.
split.
intuition.
intuition.
cut ((k-k)=0).
intro H10.
rewrite H10.
intuition.
intuition.
simpl.
cut (l-k>0).
intro H9.
set (H10:=(quotient (l-k) H9 (n-k))).
elim H10.
clear H10.
intros q H10.
exists q.
split.
elim H10.
clear H10.
intros r H10'.
elim H10'.
clear H10'.
intros H10' H10''.
3:intuition.
cut ((n-k)= q*(l-k)+ (mod_nat (n-k)(l-k) H2)).
intro H11.
intuition.
cut (r= (mod_nat (n-k)(l-k)H2)).
intro H11.
rewrite<- H11.
exact H10'.

simpl.
cut ((Z_of_nat r)=(mod_nat (n - k) (l - k) H2)).
intro H11.
intuition.

rewrite<- H7.
apply nat_Z_div with (n-k) q (l-k) ((Z_of_nat n - Z_of_nat k) / (Z_of_nat l - Z_of_nat k))%Z. 
exact H10'.
intuition.
cut (k<=l).
intro H11.
set (H12:=(inj_minus1 l k H11)).
rewrite H12.
cut (k<=n).
intro H14.
set (H16:=(inj_minus1 n k H14)).
rewrite H16.
exact H6.
intuition.
intuition.
set (H17:=(Z_mod_lt (Z_of_nat (n-k)) (Z_of_nat (l-k)))).
intuition.
elim H10.
clear H10.
intros r H10.
elim H10.
clear H10.
intros H10 H10'.
intuition.
Qed.

Lemma cyc_imp_comm: forall (M:CMonoid)(H:(cyclic M)), (commutes (@csg_op M)). 
intros M H.
unfold commutes.
intros x y.
unfold cyclic in H.
elim H.
clear H.
intros c0 H.
elim (H x).
intros nx Hx.
elim (H y).
intros ny Hy.
csetoid_rewrite_rev Hx.
csetoid_rewrite_rev Hy.
csetoid_rewrite_rev (power_plus M c0 nx ny).
replace (nx+ny) with (ny+nx).
csetoid_rewrite (power_plus M c0 ny nx).
apply eq_reflexive.
intuition.
Qed.

Lemma weakly_inj1:
  forall (M:CMonoid)(u:M)(k l a b:nat),(is_generator M u)->(a<l)->(b<l)->
  (k<l and (power_CMonoid u  k [=] power_CMonoid u l)
  and (forall (k0 l0:nat), (k0<k or (k0=k and l0<l))-> 
  (power_CMonoid u  k0 [#] power_CMonoid u l0)))->
  (power_CMonoid u a)[=](power_CMonoid u b) ->
a=b.
intros M u  k l a b H H0 H1.
unfold is_generator in H.
intros H3 H4.
elim (eq_nat_dec a b).
tauto.

intro H5.
elim (not_or a b H5).
clear H5.
intro H5.
cut False.
intuition.

set (H6:= (eq_imp_not_ap M (power_CMonoid u a)(power_CMonoid u b) H4)).
unfold Not in H6.
apply H6.
cut ((power_CMonoid u a[#]power_CMonoid u b) or 
   (power_CMonoid u (l-b)[#]power_CMonoid u (l-b))).
intro H7.
elim H7.
tauto.
clear H7.
intro H7.
set (H8:= (ap_irreflexive_unfolded M (power_CMonoid u (l-b)) H7)).
intuition.

apply bin_op_strext_unfolded with (@csg_op M).
csetoid_rewrite_rev (power_plus M u b (l-b)).
csetoid_rewrite_rev (power_plus M u a (l-b)).
elim H3.
clear H3.
intros H3 H7.
elim H7.
clear H7.
intros H7 H8.
replace (b+(l-b)) with l.
csetoid_rewrite_rev H7.
apply ap_symmetric_unfolded.
apply H8.
right.
intuition.

intuition.

clear H5.
intro H5.
cut False.
intuition.

set (H6:= (eq_imp_not_ap M (power_CMonoid u a)(power_CMonoid u b) H4)).
unfold Not in H6.
apply H6.
cut ((power_CMonoid u a[#]power_CMonoid u b) or 
   (power_CMonoid u (l-a)[#]power_CMonoid u (l-a))).
intro H7.
elim H7.
tauto.
clear H7.
intro H7.
set (H8:= (ap_irreflexive_unfolded M (power_CMonoid u (l-a)) H7)).
intuition.

apply bin_op_strext_unfolded with (@csg_op M).
csetoid_rewrite_rev (power_plus M u b (l-a)).
csetoid_rewrite_rev (power_plus M u a (l-a)).
elim H3.
clear H3.
intros H3 H7.
elim H7.
clear H7.
intros H7 H8.
replace (a+(l-a)) with l.
csetoid_rewrite_rev H7.
apply H8.
right.
intuition.

intuition.
Qed.

(**
%\begin{convention}%
Let [M:CMonoid].
%\end{convention}%
*)

Variable M:CMonoid.

Lemma generator_imp_cyclic: (forall (u:M),
  (is_generator M u)-> (cyclic M)):CProp.
intros u H.
unfold is_generator in H.
exists u.
exact H.
Qed.

End gen_cyc.

(** **Invertability
*)

Definition is_inverse S (op : CSetoid_bin_op S) Zero x x_inv : Prop :=
 op x x_inv [=] Zero /\ op x_inv x [=] Zero.

Implicit Arguments is_inverse [S].

Definition invertible (M:CMonoid): M -> CProp :=
fun m =>{inv: (CSetoid_un_op M) | (is_inverse csg_op (@cm_unit M) m (inv m))}.

Section D9M.
(** **Direct Product
%\begin{convention}%
Let [M1 M2:CMonoid]
%\end{convention}%
*)

Variable M1 M2: CMonoid.

Lemma  e1e2_is_rht_unit: 
  (is_rht_unit (dprod_as_csb_fun M1 M2)(pairT (@cm_unit M1)(@cm_unit M2))).
unfold is_rht_unit.
intro x.
case x.
intros x1 x2.
simpl.
split.
apply cm_rht_unit_unfolded.
apply cm_rht_unit_unfolded.
Qed.

Lemma  e1e2_is_lft_unit: 
  (is_lft_unit (dprod_as_csb_fun M1 M2)(pairT (@cm_unit M1)(@cm_unit M2))).
intro x.
case x.
intros x1 x2.
simpl.
split.
apply cm_lft_unit_unfolded.
apply cm_lft_unit_unfolded.
Qed.

Definition direct_product_is_CMonoid:=
  (Build_is_CMonoid (direct_product_as_CSemiGroup M1 M2)
  (pairT (@cm_unit M1)(@cm_unit M2))
   e1e2_is_rht_unit  e1e2_is_lft_unit).

Definition direct_product_as_CMonoid :=
  (Build_CMonoid (direct_product_as_CSemiGroup M1 M2)
  (pairT (@cm_unit M1)(@cm_unit M2)) direct_product_is_CMonoid).

End D9M.

Section p71E2b2.

Variable M1:CMonoid.
Variable M2:CMonoid.

Let f: (direct_product_as_CMonoid M1 M2)->
  (direct_product_as_CMonoid M2 M1).
simpl.
intro x.
elim x.
intros x1 x2.
exact (pairT x2 x1).
Defined.

Lemma f_strext': (fun_strext f ).
unfold fun_strext.
simpl.
intros x y.
case x.
intros x1 x2.
case y.
intros y1 y2.
simpl.
intuition.
Qed.

Definition f_as_CSetoid_fun_:= (Build_CSetoid_fun _ _ f f_strext').

Lemma isomorphic_PM1M2_PM2M1:
  (isomorphic (direct_product_as_CMonoid M1 M2) 
  (direct_product_as_CMonoid M2 M1)):CProp.
unfold isomorphic.
simpl.
exists f_as_CSetoid_fun_.
unfold isomorphism.
unfold morphism.
simpl.
split.
split.
intuition.
intros a b.
case a.
intros a0 a1.
case b.
intros b0 b1.
simpl.
intuition.

unfold bijective.
split.
unfold injective.
simpl.
intros a0 a1.
elim a0.
intros b0 b1.
elim a1.
intros c0 c1.
simpl.
intuition.

unfold surjective.
intro b.
elim b.
intros a0 a1.
exists (pairT a1 a0).
simpl.
intuition.
Qed.

End p71E2b2.


(** **The Monoids of Setoid functions and bijective Setoid functions.
*)

Definition FS_id (A : CSetoid) : FS_as_CSetoid A A.
intro A.
unfold FS_as_CSetoid in |- *.
simpl in |- *.
exact (id_un_op A).
Defined.

Lemma id_is_rht_unit :
 forall A : CSetoid, is_rht_unit (comp_as_bin_op A) (FS_id A).
unfold is_rht_unit in |- *.
unfold comp_as_bin_op in |- *.
unfold FS_id in |- *.
simpl in |- *.
unfold eq_fun in |- *.
unfold id_un_op in |- *.
simpl in |- *.
intuition.
Qed.

Lemma id_is_lft_unit :
 forall A : CSetoid, is_lft_unit (comp_as_bin_op A) (FS_id A).
unfold is_lft_unit in |- *.
unfold comp_as_bin_op in |- *.
unfold FS_id in |- *.
simpl in |- *.
unfold eq_fun in |- *.
unfold id_un_op in |- *.
simpl in |- *.
intuition.
Qed.

Definition FS_is_CMonoid (A : CSetoid) :=
  Build_is_CMonoid (FS_as_CSemiGroup A) (FS_id A) (
    id_is_rht_unit A) (id_is_lft_unit A).

Definition FS_as_CMonoid (A : CSetoid) :=
  Build_CMonoid (FS_as_CSemiGroup A) (FS_id A) (FS_is_CMonoid A).


Definition PS_as_CMonoid (A : CSetoid) :=
  Build_SubCMonoid (FS_as_CMonoid A) (bijective (A:=A) (B:=A)) (
    id_is_bij A) (comp_resp_bij A A A).  

(** **The free Monoid
*)

Lemma is_unit_Astar_empty_word: forall (A:CSetoid),
(is_unit (Astar_as_CSemiGroup A)(empty_word A)).
intro A.
unfold is_unit.
simpl.
intro a.
split.
apply eq_fm_reflexive.

unfold empty_word.
unfold app.
unfold ListType.app.
induction a.
apply eq_fm_reflexive.

simpl.
intuition.
Qed.

Section Th12.

(** 
%\begin{convention}%
Let [A:CSetoid].
%\end{convention}%
*)

Variable A:CSetoid.

Lemma nil_is_rht_unit: (is_rht_unit (app_as_csb_fun A) (empty_word A)).
unfold is_rht_unit.
simpl.
intro x.
induction x.
simpl.
intuition.

simpl.
intuition.
Qed.

Lemma nil_is_lft_unit: (is_lft_unit (app_as_csb_fun A) (empty_word A)).
unfold is_lft_unit.
simpl.
intro x.
induction x.
simpl.
intuition.

simpl.
intuition.
Qed.

Definition free_monoid_is_CMonoid: 
  is_CMonoid (Astar_as_CSemiGroup A) (empty_word A):=
  (Build_is_CMonoid (Astar_as_CSemiGroup A) (empty_word A) 
  nil_is_rht_unit nil_is_lft_unit).

Definition free_monoid_as_CMonoid:CMonoid:=
(Build_CMonoid (Astar_as_CSemiGroup A)(empty_word A) free_monoid_is_CMonoid).

End Th12.

(** **The unit in the setoid of Setoid functions
%\begin{convention}%
Let [X:CSetoid].
%\end{convention}%
*)

Section p67R2.
Variable X: CSetoid.
Lemma is_unit_FS_id:(is_unit (FS_as_CSemiGroup X) (FS_id X)).
unfold is_unit.
intros a.
set (H:= (id_is_rht_unit X a)).
set (H0:= (id_is_lft_unit X a)).
split.
exact H0.
exact H.
Qed.

End p67R2.

Section Th11.

(** **Intersection
The intersection of a collection of monoids is again a monoid.
%\begin{convention}%
Let [M:CMonoid], [I:type], [C:I->(M->CProp)], [Cunit: (C i Zero)] and
[op_pres_C:forall (i:I), (bin_op_pres_pred _ (C i) csg_op)].
%\end{convention}%
*)

Variable M:CMonoid.
Variable I:Type.
Variable C:I->(M->CProp).
Variable Cunit: forall (i:I), (C i Zero).
Variable op_pres_C: forall (i:I),(bin_op_pres_pred _ (C i) csg_op).

Definition K : M -> CProp :=
(fun m => forall (i:I), (C i m)).

Lemma op_pres_K: bin_op_pres_pred (cm_crr M) K (csg_op (c:=M)).
unfold K.
unfold bin_op_pres_pred.
unfold bin_op_pres_pred in op_pres_C.
intros x y Cx Cy i.
apply op_pres_C.
apply Cx.
apply Cy.
Qed.

Definition K_is_Monoid :CMonoid := (Build_SubCMonoid M K Cunit op_pres_K).

End Th11.

Section Th15.
(** The Monoid generated by a Subset
%\begin{convention}%
Let [M:CMonoid] and [D:M->CProp].
%\end{convention}%
*)

Variable M:CMonoid.

Fixpoint cm_Sum (l: list M) {struct l}: M :=
match l with
|nil => Zero
|cons a k => a [+] (cm_Sum k)
end.

Variable D : M -> CProp.

Definition Dbrack : M -> CProp := 
  fun m => {l: (list M)| (forall (a:M) , member a l -> (D a)) and 
                                        (cm_Sum l)[=]m}. 

Lemma Dbrack_unit: (Dbrack Zero).
unfold Dbrack.
exists (nil M).
simpl.
intuition.
Qed.


Lemma cm_Sum_app: 
forall (k l : (list M)), (cm_Sum (app M k l))[=] (cm_Sum k)[+](cm_Sum l).
intros k l.
induction k.
simpl.
apply eq_symmetric.
apply cm_lft_unit_unfolded.

simpl.
astepr (a [+] ( (cm_Sum k)[+](cm_Sum l))).
apply csbf_wd_unfolded.
intuition.

exact IHk.
Qed.

Lemma op_pres_Dbrack : bin_op_pres_pred _ Dbrack csg_op.
unfold bin_op_pres_pred.
intros x y.
unfold Dbrack.
intros Hx Hy.
elim Hx.
clear Hx.
intros lx Hx.
elim Hy.
clear Hy.
intros ly Hy.
exists (app M lx ly).
split.
intro a.
set (H:= (member_app M a ly lx)).
elim H.
intros H0 H1.
intros H2.
set (H3:= (H0 H2)).
elim H3.
(generalize Hx).
intuition.

(generalize Hy).
intuition.
elim Hx.
clear Hx.
intros Hx1 Hx2.
astepr ((cm_Sum lx)[+] y).
elim Hy.
clear Hy.
intros Hy1 Hy2.
astepr ( (cm_Sum lx)[+](cm_Sum ly) ).
apply cm_Sum_app.
Qed.

Definition Dbrack_as_CMonoid : CMonoid :=
(Build_SubCMonoid M Dbrack Dbrack_unit op_pres_Dbrack).


End Th15.


Hint Resolve cm_rht_unit_unfolded cm_lft_unit_unfolded: algebra.
