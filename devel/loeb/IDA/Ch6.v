Require Export CSemiGroups.

(* Remark blz 65 1 *)

Definition is_nullary_operation (S:CSetoid) (s:S):Prop := True.

Require Export Zsetoid.

Lemma is_nullary_operation_Z_0 : (is_nullary_operation Z_as_CSetoid 0%Z).
unfold is_nullary_operation.
intuition.
Qed.

(* Remark blz 65 2 *)

Require Export csetfun.

Fixpoint n_ary_operation (n:nat)(V:CSetoid){struct n}:CSetoid:=
match n with
|0 => V
|(S m)=> (FS_as_CSetoid V (n_ary_operation m V))
end.

Require Export Nsetoid.

Definition plus1 (n:nat)(m:nat): (n_ary_operation 1 nat_as_CSetoid).
simpl.
intros n  m.
apply (projected_bin_fun _ _ _ plus_is_bin_fun (plus_is_bin_fun n m)).
Defined.

Lemma to_plus1_strext:forall (n:nat), fun_strext (S1:=nat_as_CSetoid)
     (S2:=FS_as_CSetoid nat_as_CSetoid nat_as_CSetoid)
     (fun m : nat => plus1 n m).
intro n.
unfold plus1.
unfold fun_strext.
simpl.
intros x y H.
unfold ap_fun in H.
simpl in H.
elim H.
clear H.
intros a H.
set (H1:= plus_strext).
unfold bin_fun_strext in H1.
cut ((n+x{#N}n + y) or (a{#N}a)).
intro H2.
elim H2.
intro H3.
cut ((n{#N}n) or (x{#N}y)).
intro H4.
elim H4.
set (H5:=(ap_nat_irreflexive n)).
intro H6.
set (H7:= (H5 H6)).
contradiction.

intro H5.
exact H5.

apply H1.
exact H3.

intro H3.
set (H5:=(ap_nat_irreflexive a)).
set (H7:= (H5 H3)).
contradiction.

apply H1.
exact H.
Qed.

Definition plus2 (n:nat): (n_ary_operation 2 nat_as_CSetoid).
simpl.
intro n.
apply Build_CSetoid_fun with (fun m => (plus1 n m)).
apply to_plus1_strext.
Defined.


Lemma to_plus2_strext:fun_strext (S1:=nat_as_CSetoid)
     (S2:=FS_as_CSetoid nat_as_CSetoid
            (FS_as_CSetoid nat_as_CSetoid nat_as_CSetoid))
     (fun m : nat => plus2 m).
unfold fun_strext.
intros x y.
simpl.
unfold ap_fun.
simpl.
intro H.
elim H.
clear H.
unfold ap_fun.
intros a H.
elim H.
clear H.
intros a0 H.
unfold plus1 in H.
simpl in H.
set (H1:= (plus_strext)).
unfold bin_fun_strext in H1.
cut (((x+a){#N}(y+a)) or (a0 {#N} a0)).
intro H2.
elim H2.
clear H2.
intro H2.
set (H3:=(H1 x y a a H2)).
simpl in H3.
elim H3.
clear H3.
intro H3.
exact H3.
clear H3.
intro H3.
set (H5:=(ap_nat_irreflexive a)).
set (H7:= (H5 H3)).
contradiction.

set (H5:=(ap_nat_irreflexive a0)).
intro H6.
set (H7:= (H5 H6)).
contradiction.

apply H1.
exact H.
Qed.


Definition plus3 :(n_ary_operation 3 nat_as_CSetoid).
simpl.
apply Build_CSetoid_fun with (fun m => (plus2 m )).
apply to_plus2_strext.
Defined.

Definition on: nat_as_CSetoid -> nat_as_CSetoid -> nat_as_CSetoid ->
(n_ary_operation 3 nat_as_CSetoid)-> nat_as_CSetoid.
intros n m k p.
unfold n_ary_operation in p.
simpl in p.
elim p.
clear p.
intros pfun0 prf0.
set (pfun1 := (pfun0 n)).
elim pfun1.
clear pfun1.
intros pfun1 prf1.
set (pfun2:= (pfun1 m)).
elim pfun2.
clear pfun2.
intros pfun2 prf2.
set (pfun3:= (pfun2 k)).
exact pfun3.
Defined.


Let ex_3_ary: (on 3 5 7 plus3)[=] 3+5+7.
simpl.
reflexivity.
Qed.

(* blz 65 Example 1 *)

(* Print Zopp_is_fun.*)

(* Print Inv_as_un_op.
Geen goed voorbeeld: monoids komen hier al in voor en het is een heel onoverzichtelijk bewijs *)

(* blz 65 Example 2 *)

(* Print plus_is_bin_fun.*)

(* Print mult_as_bin_fun.*)

(* blz 66 Example 1 *)

(* Print plus_is_assoc.*)

(* Print Zplus_is_assoc.*)

(* Print Zmult_is_assoc.*)

Require Export Qsetoid.

(* Print Qplus_is_assoc.*)

(* Print Qmult_is_assoc.*)

(* blz 66 Examples 2 *)

Section p66E2.
Variable X: CSetoid.
Variable f: (FS_as_CSetoid X X).
Variable g: (FS_as_CSetoid X X).
Variable h: (FS_as_CSetoid X X).

(* Check comp_as_bin_op.*)

(* Check assoc_comp.*)

End p66E2.

(* blz 66 Example 2eblok 1 *)

Require Export Zsemigroup.

Lemma Zplus_is_CSemiGroup: (is_CSemiGroup Z_as_CSetoid Zplus_is_bin_fun).
unfold is_CSemiGroup.
exact Zplus_is_assoc.
Qed.

Lemma Zmult_is_CSemiGroup: (is_CSemiGroup Z_as_CSetoid Zmult_is_bin_fun).
unfold is_CSemiGroup.
exact Zmult_is_assoc.
Qed.

(* blz 66 Example % 3 *)

Lemma FS_is_CSemiGroup: 
forall (X:CSetoid),(is_CSemiGroup (FS_as_CSetoid X X) (comp_as_bin_op  X )).
unfold is_CSemiGroup.
exact assoc_comp.
Qed.

(* blz 66 Example % 4 *)
Section p66E2b4.

Variable A:CSetoid.

Definition Astar := (list A).

Definition empty_word := (nil A).

Definition app:= (app A).

Fixpoint eq_fm (m:Astar)(k:Astar){struct m}:Prop:=
match m with
|nil => match k with
        |nil => True
        |cons a l => False
        end
|cons b n => match k with
        |nil => False
        |cons a l => b[=]a /\ (eq_fm n l)
        end
end.                                 

Fixpoint ap_fm (m:Astar)(k:Astar){struct m}: CProp :=
match m with
|nil => match k with
        |nil => CFalse
        |cons a l => CTrue
        end
|cons b n => match k with
        |nil => CTrue  
        |cons a l => b[#]a or (ap_fm n l)
        end
end.                                

Lemma ap_fm_irreflexive: (irreflexive ap_fm).
unfold irreflexive.
intro x.
induction x.
simpl.
red.
intuition.

simpl.
red.
intro H.
apply IHx.
elim H.
clear H.
generalize (ap_irreflexive A a).
unfold Not.
intuition.

intuition.
Qed.


Lemma ap_fm_symmetric: Csymmetric ap_fm.
unfold Csymmetric.
intros x.
induction x.
intro y.
case  y.
simpl.
intuition.

simpl.
intuition.
simpl.
intro y.
case y.
simpl.
intuition.

simpl.
intros c l  H0.
elim H0.
generalize (ap_symmetric A a c).
intuition.
clear H0.
intro H0.
right.
apply IHx.
exact H0.
Qed.

Lemma ap_fm_cotransitive : (cotransitive ap_fm).
unfold cotransitive.
intro x.
induction x.
simpl.
intro y.
case y.
intuition.

intros c l H z.
case z.
simpl.
intuition.

intuition.

simpl.
intro y.
case y.
intros H z.
case z.
intuition.

simpl.
intuition.

intros c l H z.
case z.
intuition.

simpl.
intros c0 l0.
elim H.
clear H.
intro H.
generalize (ap_cotransitive A a c H c0).
intuition.

clear H.
intro H.
generalize (IHx l H l0).
intuition.
Qed.

Lemma ap_fm_tight : (tight_apart eq_fm ap_fm).
unfold tight_apart.
intros x.
induction x.
simpl.
intro y.
case y.
red.
unfold Not.
intuition.

intuition.

intro y.
simpl.
case y.
intuition.

intros c l.
generalize (IHx l).
red.
intro H0.
elim H0.
intros H1 H2.
split.
intro H3.
split.
red in H3.
generalize (ap_tight A a c).
intuition.

apply H1.
intro H4.
apply H3.
right.
exact H4.

intro H3.
elim H3.
clear H3.
intros H3 H4.
intro H5.
elim H5.
generalize (ap_tight A a c).
intuition.

apply H2.
exact H4.
Qed.

Definition free_csetoid_is_CSetoid:(is_CSetoid Astar eq_fm ap_fm):=
(Build_is_CSetoid Astar eq_fm ap_fm ap_fm_irreflexive ap_fm_symmetric ap_fm_cotransitive ap_fm_tight).

Definition free_csetoid_as_csetoid:CSetoid:=
(Build_CSetoid Astar eq_fm ap_fm free_csetoid_is_CSetoid).

Lemma app_strext:(bin_fun_strext free_csetoid_as_csetoid free_csetoid_as_csetoid free_csetoid_as_csetoid app).
unfold bin_fun_strext.
intros x1.
induction x1.
simpl.
intro x2.
case x2.
simpl.
intuition.

intuition.

intros x2 y1 y2.
simpl.
case x2.
case y2.
simpl.
intuition.

simpl.
intuition.

case y2.
simpl.
simpl in IHx1.
intros c l H.
elim H.
intuition.

clear H.
generalize (IHx1 l y1 (nil A)).
intuition.

simpl.
intros c l c0 l0.
intro H.
elim H.
intuition.

generalize (IHx1 l0 y1 (cons c l)).
intuition.
Qed.

Definition app_as_csb_fun: (CSetoid_bin_fun free_csetoid_as_csetoid free_csetoid_as_csetoid free_csetoid_as_csetoid):=
(Build_CSetoid_bin_fun free_csetoid_as_csetoid free_csetoid_as_csetoid free_csetoid_as_csetoid app app_strext).

Require Export CSemiGroups.

Lemma eq_fm_reflexive: forall (x:Astar), (eq_fm x x).
intro x.
induction x.
simpl.
intuition.

simpl.
intuition.
Qed.


Lemma Astar_is_CSemiGroup: (is_CSemiGroup free_csetoid_as_csetoid app_as_csb_fun).
unfold is_CSemiGroup.
unfold associative.
intros x.
unfold app_as_csb_fun.
simpl.
induction x.
simpl.
intros x y.
apply eq_fm_reflexive.

simpl.
intuition.
Qed.

Definition Astar_as_CSemiGroup:= (Build_CSemiGroup free_csetoid_as_csetoid app_as_csb_fun Astar_is_CSemiGroup).

End p66E2b4.

(* Definition 5 *)

Definition is_unit (S:CSemiGroup): S -> Prop :=
fun e => forall (a:S), e[+]a [=] a /\ a[+]e [=]a.

(* blz 67 Remark 1 *)

Require Export Zmonoid.

Lemma is_unit_Z_0 :(is_unit Z_as_CSemiGroup 0%Z).
unfold is_unit.
intro a.
simpl.
split.
reflexivity.
intuition.
Qed.

(* blz 67 Remark 2 *)

Section p67R2.
Variable X: CSetoid.
Lemma is_unit_FS_id:(is_unit (FS_as_CSemiGroup X) (FS_id X)).
unfold is_unit.
intros a.
set (H:= (id_is_rht_unit X a)).
set (H0:= (id_is_lft_unit X a)).
(* simpl in H.
simpl in H0.
simpl.*)
split.
exact H0.
exact H.
Qed.

End p67R2.

(* blz 67 Remark 3 *)

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


(* Lemma 6 *)

Lemma unique_unit : forall (S:CSemiGroup) (e f:S), 
(is_unit S e) /\ (is_unit S f) -> e[=]f.
intros S e f.
unfold is_unit.
intros H.
elim H.
clear H.
intros H0 H1.
elim (H0 f).
clear H0.
intros H2 H3.
elim (H1 e).
clear H1.
intros H4 H5.
astepr (e[+]f). 
astepl (e[+]f).
apply eq_reflexive.
Qed.

(* blz 67 Example 1 *)

Require Export Nmonoid.

(* Print nat_is_CMonoid.*)

Require Zmonoid.

(* Print Z_is_CMonoid.*)

(* Print Z_mul_is_CMonoid.*)

(* blz 67 Example 3 *)

(* Print FS_is_CMonoid.*)

(* blz 68 Example blok1 1 *)

Section p68E1b1.

Inductive M1:Set :=
e1:M1 | u:M1.

Definition M1_eq :(Relation M1):= fun a => fun b => (a=b).

Definition M1_ap : (Crelation M1):= fun a => fun b => Not (a=b).

Lemma M1_ap_irreflexive: (irreflexive M1_ap).
intro x.
unfold M1_ap.
red.
intuition.
Qed.

Lemma M1_ap_symmetric: (Csymmetric M1_ap).
unfold Csymmetric.
unfold M1_ap.
red.
intuition.
Qed.

Lemma M1_ap_cotransitive:  (cotransitive M1_ap).
unfold cotransitive.
unfold M1_ap.
unfold Not.
intros x y H z.
induction x.
induction y.
intuition.

induction z.
intuition.

intuition.

induction y.
induction z.
intuition.
intuition.
intuition.
Qed.

Lemma M1_eq_dec: forall(x:M1),(M1_eq x e1) or (M1_eq x u).
intros x.
induction x.
left.
unfold M1_eq.
reflexivity.

right.
unfold M1_eq.
reflexivity.
Qed.

Definition  is_e1 (x:M1):Prop :=
match x with
|e1 => True
|u => False
end.

Lemma not_M1_eq_e1_u:Not (M1_eq e1 u).
red.
intros  H.
change (is_e1 u).
unfold M1_eq in H.
rewrite<- H.
exact I.
Qed.

Lemma M1_ap_tight: (tight_apart  M1_eq M1_ap).
unfold tight_apart.
unfold M1_eq.
unfold M1_ap.
intros x y.
split.
induction x.
induction y.
intuition.

unfold Not.
intro H.
cut (e1=u -> False).
intuition.

apply not_M1_eq_e1_u.

induction y.
2:intuition.
2:unfold Not.
2:intuition.

unfold Not.
intro H.
cut (e1=u -> False ).
intuition.

apply not_M1_eq_e1_u.
Qed.

Definition M1_is_CSetoid:(is_CSetoid M1 M1_eq M1_ap) :=
(Build_is_CSetoid M1 M1_eq M1_ap M1_ap_irreflexive M1_ap_symmetric M1_ap_cotransitive M1_ap_tight).

Definition M1_as_CSetoid: CSetoid :=
(Build_CSetoid M1 M1_eq M1_ap M1_is_CSetoid).

Definition M1_mult (x:M1)(y:M1):M1:=
match x with
|e1 => y
|u => match y with
       |e1 => u
       |u => e1
       end
end.                   

Definition M1_CS_mult: M1_as_CSetoid -> M1_as_CSetoid -> M1_as_CSetoid.
simpl.
exact M1_mult.
Defined.

Lemma M1_CS_mult_strext:(bin_fun_strext M1_as_CSetoid M1_as_CSetoid M1_as_CSetoid M1_CS_mult).
unfold bin_fun_strext.
intros x1 x2 y1 y2.
case x1.
case x2.
case y1.
case y2.
simpl.
intuition.

simpl.
intuition.
case y2.
simpl.
intuition.
simpl.

intuition.

case y1.
case y2.
simpl.
intuition.

simpl.
unfold M1_ap.
unfold Not.
intuition.

case y2.
simpl.
unfold M1_ap.
unfold Not.
intuition.

simpl.
intro H.
left.
apply M1_ap_symmetric.
exact H.

case x2.
case y1.
case y2.
simpl.
intuition.

simpl.
unfold M1_ap.
unfold Not.
intuition.

case y2.
simpl.
unfold M1_ap.
unfold Not.
intuition.

simpl.
intro H.
left.
apply M1_ap_symmetric.
exact H.

case y1.
case y2.
simpl.
intuition.

simpl.
intro H.
right.
apply M1_ap_symmetric.
exact H.

case y2.
simpl.
intro H.
right.
apply M1_ap_symmetric.
exact H.

simpl.
unfold M1_ap.
unfold Not.
intuition.
Qed.

Definition M1_mult_as_bin_fun:=
(Build_CSetoid_bin_fun M1_as_CSetoid M1_as_CSetoid M1_as_CSetoid M1_CS_mult M1_CS_mult_strext).

Lemma M1_is_CSemiGroup:(is_CSemiGroup M1_as_CSetoid M1_mult_as_bin_fun).
unfold is_CSemiGroup.
unfold associative.
simpl.
unfold M1_CS_mult.
intros x y z.
case x.
case y.
case z.
simpl.
unfold M1_eq.
reflexivity.

simpl.
unfold M1_eq.
reflexivity.

case z.
simpl.
unfold M1_eq.
reflexivity.

simpl.
unfold M1_eq.
reflexivity.

case y.
case z.
simpl.
unfold M1_eq.
reflexivity.

simpl.
unfold M1_eq.
reflexivity.

case z.
simpl.
unfold M1_eq.
reflexivity.

simpl.
unfold M1_eq.
reflexivity.
Qed.

Require Export CMonoids.

Lemma e1_is_lft_unit: (is_lft_unit M1_mult_as_bin_fun e1).
unfold is_lft_unit.
simpl.
unfold M1_eq.
reflexivity.
Qed.

Lemma e1_is_rht_unit:(is_rht_unit M1_mult_as_bin_fun e1).
unfold is_rht_unit.
simpl.
unfold M1_eq.
unfold M1_CS_mult.
intro x.
case x.
simpl.
reflexivity.

simpl.
reflexivity.
Qed.

Definition M1_as_CSemiGroup:CSemiGroup:=
(Build_CSemiGroup M1_as_CSetoid M1_mult_as_bin_fun M1_is_CSemiGroup).

Definition M1_is_CMonoid:(is_CMonoid M1_as_CSemiGroup e1):=
(Build_is_CMonoid M1_as_CSemiGroup e1 e1_is_rht_unit e1_is_lft_unit).

Definition M1_as_CMonoid:CMonoid:=
(Build_CMonoid M1_as_CSemiGroup e1 M1_is_CMonoid).

Definition M2_mult (x:M1)(y:M1):M1:=
match x with
|e1 => y
|u => u
end.

Definition M2_CS_mult: M1_as_CSetoid -> M1_as_CSetoid -> M1_as_CSetoid.
simpl.
exact M2_mult.
Defined.

Lemma M2_CS_mult_strext: (bin_fun_strext M1_as_CSetoid M1_as_CSetoid M1_as_CSetoid M2_CS_mult).
unfold bin_fun_strext.
intros x1 x2 y1 y2.
case x1.
case x2.
case y1.
case y2.
simpl.
intuition.

simpl.
intuition.

case y2.
simpl.
intuition.

simpl.
intuition.

case y1.
case y2.
simpl.
intuition.

simpl.
intuition.

case y2.
simpl.
unfold M1_ap.
unfold Not.
intuition.

simpl.
intuition.

case x2.
case y1.
case y2.
simpl.
intuition.
simpl.
unfold M1_ap.
unfold Not.
intuition.

case y2.
simpl.
intuition.

simpl.
unfold M1_ap.
unfold Not.
intuition.

case y1.
case y2.
simpl.
intuition.

simpl.
intuition.

case y2.
simpl.
intuition.

simpl.
intuition.
Qed.

Definition M2_mult_as_bin_fun:= 
(Build_CSetoid_bin_fun M1_as_CSetoid M1_as_CSetoid M1_as_CSetoid M2_CS_mult M2_CS_mult_strext).

Lemma M2_is_CSemiGroup:(is_CSemiGroup M1_as_CSetoid M2_mult_as_bin_fun).
unfold is_CSemiGroup.
unfold associative.
simpl.
intros x y z.
case x.
case y.
case z.
simpl.
unfold M1_eq.
reflexivity.

simpl.
unfold M1_eq.
reflexivity.

case z.
simpl.
unfold M1_eq.
reflexivity.

simpl.
unfold M1_eq.
reflexivity.

case y.
case z.
simpl.
unfold M1_eq.
reflexivity.

simpl.
unfold M1_eq.
reflexivity.

simpl.
unfold M1_eq.
reflexivity.
Qed.
       
Definition M2_as_CSemiGroup:=
(Build_CSemiGroup M1_as_CSetoid M2_mult_as_bin_fun M2_is_CSemiGroup).

Lemma e1_is_lft_unit_M2: (is_lft_unit M2_mult_as_bin_fun e1). 
unfold is_lft_unit.
simpl.
unfold M1_eq.
reflexivity.
Qed.

Lemma e1_is_rht_unit_M2: (is_rht_unit M2_mult_as_bin_fun e1).
unfold is_rht_unit.
simpl.
intro x.
case x.
simpl.
unfold M1_eq.
reflexivity.

simpl.
unfold M1_eq.
reflexivity.
Qed.


Definition M2_is_CMonoid :=
(Build_is_CMonoid M2_as_CSemiGroup e1 e1_is_rht_unit_M2 e1_is_lft_unit_M2).

Definition M2_as_CMonoid:CMonoid:=
(Build_CMonoid M2_as_CSemiGroup e1 M2_is_CMonoid).

Lemma two_element_CMonoids:
forall (op :(CSetoid_bin_fun M1_as_CSetoid M1_as_CSetoid M1_as_CSetoid))
(H: (is_CSemiGroup M1_as_CSetoid op)),
(is_unit (Build_CSemiGroup M1_as_CSetoid op H) e1)-> 
(forall (x y:M1_as_CSetoid),(op x y)= (M1_mult_as_bin_fun x y)) or
(forall (x y:M1_as_CSetoid), (op x y)= (M2_mult_as_bin_fun x y)).
intros op H unit0.
cut (((op u u)=e1) or ((op u u)= u)).
intro H0.
unfold is_unit in unit0.
simpl in unit0.
elim H0.
clear H0.
intro H0.
left.
simpl.
intros x y.
unfold M1_CS_mult.
case x.
case y.
simpl.
set (unit1:= (unit0 e1)).
unfold M1_eq in unit1.
intuition.

simpl.
set (unit1:= (unit0 u)).
unfold M1_eq in unit1.
intuition.

case y.
simpl.
set (unit1:= (unit0 u)).
unfold M1_eq in unit1.
intuition.

simpl.
exact H0.

clear H0.
intro H0.
right.
simpl.
intros x y.
unfold M1_CS_mult.
case x.
case y.
simpl.
set (unit1:= (unit0 e1)).
unfold M1_eq in unit1.
intuition.

simpl.
set (unit1:= (unit0 u)).
unfold M1_eq in unit1.
intuition.

case y.
simpl.
set (unit1:= (unit0 u)).
unfold M1_eq in unit1.
intuition.

simpl.
exact H0.
apply (M1_eq_dec (op u u)).
Qed.

End p68E1b1.


(* blz 68 Example blok2 1 *)

(* Print Zplus_is_commut.*)

(* Print Zmult_is_commut. *)

(* Print Qplus_is_commut1. *)

(* Print Qmult_is_commut. *)



(* Definition 9 *)
Require Export CMonoids.
Section D9S.
Variable M1 M2: CSemiGroup.
Definition dprod (x:ProdCSetoid M1 M2)(y:ProdCSetoid M1 M2):
(ProdCSetoid M1 M2):=
let (x1, x2):= x in
let (y1, y2):= y in
(pairT (x1[+]y1) (x2 [+] y2)).

Lemma dprod_strext:(bin_fun_strext (ProdCSetoid M1 M2)(ProdCSetoid M1 M2)
(ProdCSetoid M1 M2)dprod).
unfold bin_fun_strext.
intros x1 x2 y1 y2.
unfold dprod.
case x1.
intros a1 a2.
case x2.
intros b1 b2.
case y1.
intros c1 c2.
case y2.
intros d1 d2.
simpl.
intro H.
elim H.
clear H.
intro H.
cut (a1[#]b1 or c1[#]d1).
intuition.

set (H0:= (@csg_op M1)).
unfold CSetoid_bin_op in H0.
set (H1:= (@csbf_strext M1 M1 M1 H0)).
unfold bin_fun_strext in H1.
apply H1.
exact H.


clear H.
intro H.
cut (a2[#]b2 or c2[#]d2).
intuition.

set (H0:= (@csg_op M2)).
unfold CSetoid_bin_op in H0.
set (H1:= (@csbf_strext M2 M2 M2 H0)).
unfold bin_fun_strext in H1.
apply H1.
exact H.
Qed.

Definition dprod_as_csb_fun:
CSetoid_bin_fun (ProdCSetoid M1 M2) (ProdCSetoid M1 M2)(ProdCSetoid M1 M2):=
(Build_CSetoid_bin_fun (ProdCSetoid M1 M2)(ProdCSetoid M1 M2)
(ProdCSetoid M1 M2) dprod dprod_strext).

Lemma direct_product_is_CSemiGroup: 
(is_CSemiGroup (ProdCSetoid M1 M2) dprod_as_csb_fun).
unfold is_CSemiGroup.
unfold associative.
intros x y z.
case x.
intros x1 x2.
case y.
intros y1 y2.
case z.
intros z1 z2.
simpl.
split.
apply CSemiGroup_is_CSemiGroup.
apply CSemiGroup_is_CSemiGroup.
Qed.

Definition direct_product_as_CSemiGroup:=
(Build_CSemiGroup (ProdCSetoid M1 M2) dprod_as_csb_fun 
direct_product_is_CSemiGroup).

End D9S.

Section D9M.
Variable M1 M2: CMonoid.

Lemma  e1e2_is_rht_unit: (is_rht_unit (dprod_as_csb_fun M1 M2)
(pairT (@cm_unit M1)(@cm_unit M2)) 
).
unfold is_rht_unit.
intro x.
case x.
intros x1 x2.
simpl.
intuition.
Qed.

Lemma  e1e2_is_lft_unit: (is_lft_unit (dprod_as_csb_fun M1 M2)
(pairT (@cm_unit M1)(@cm_unit M2)) 
).
intro x.
case x.
intros x1 x2.
simpl.
intuition.
Qed.

Definition direct_product_is_CMonoid:=
(Build_is_CMonoid (direct_product_as_CSemiGroup M1 M2)
(pairT (@cm_unit M1)(@cm_unit M2))
 e1e2_is_rht_unit  e1e2_is_lft_unit).

Definition direct_product_as_CMonoid :=
(Build_CMonoid (direct_product_as_CSemiGroup M1 M2)
(pairT (@cm_unit M1)(@cm_unit M2)) direct_product_is_CMonoid).

End D9M.

(* blz 69 Example *)

Section p69E1.

Let PM1M2:=(direct_product_as_CMonoid M1_as_CMonoid M2_as_CMonoid).

Let uu: PM1M2.
simpl.
exact (pairT u u).
Defined.

Let e1u: PM1M2.
simpl.
exact (pairT e1 u).
Defined.

Lemma ex_69 : uu [+] uu [=]e1u.
simpl.
unfold M1_eq.
intuition.
Qed.

End p69E1.


(* Theorem 11 *)
Section Th11.

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

(* Theorem 12 *)

Section Th12.

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



Definition free_monoid_is_CMonoid: is_CMonoid (Astar_as_CSemiGroup A) (empty_word A):=
(Build_is_CMonoid (Astar_as_CSemiGroup A) (empty_word A) nil_is_rht_unit nil_is_lft_unit).

Definition free_monoid_as_CMonoid:CMonoid:=
(Build_CMonoid (Astar_as_CSemiGroup A)(empty_word A) free_monoid_is_CMonoid).

End Th12.

(* blz 70 text *)

Section p70text.

Require Export lst2fun.

Let A:= (CSetoid_of_less 1).

Lemma ZerolessOne: 0<1.
intuition.
Qed.

Fixpoint to_word (n:nat):(list (F 1)):=
match n with
|0 => (nil (F 1))
|(S m)=> (cons (Build_F 1 0 ZerolessOne)(to_word m))
end.

Definition to_word_: nat_as_CMonoid -> (free_monoid_as_CMonoid A).
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
simpl.
unfold fun_strext.
double induction x y.
simpl.
intuition.

intros  n H2.
simpl.
unfold ap_nat.
unfold CNot.
intros T H.
set (H1:= (O_S n H)).
elim H1.

intros n H3.
simpl.
unfold ap_nat.
unfold CNot.
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
unfold CNot in H4 |- *.
intro H5.
apply H4.
apply (eq_add_S n0 n H5).
Qed.

Definition to_word_as_CSetoid_fun:=
(Build_CSetoid_fun nat_as_CSetoid (free_csetoid_as_csetoid  A) to_word_ to_word_strext).

Lemma to_word_bijective: (bijective to_word_as_CSetoid_fun).
unfold bijective.
split.
unfold injective.
simpl.
intros a0.
induction a0.
intro a1.
case a1.
unfold ap_nat.
unfold CNot.
intuition.

simpl.
intuition.

intro a1.
case a1.
simpl.
intuition.

intros n H.
unfold ap_nat in H.
unfold CNot in H.
simpl.
apply Cinright.
apply IHa0.
unfold ap_nat.
unfold CNot.
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
simpl.
intros n m.
induction n.
simpl.
apply eq_fm_reflexive.

simpl.
intuition.
Qed.

End p70text.


(* Definition 13 *)

Section Th13.

Variable M1:CMonoid.
Variable M2:CMonoid.

Definition morphism (f:(CSetoid_fun M1 M2)):CProp:=
(f (Zero)[=]Zero /\ forall (a b:M1), (f (a[+]b))[=] (f a)[+](f b)).

Definition isomorphism (f:(CSetoid_fun M1 M2)):CProp:=
(morphism f) and (bijective f).

End Th13.

(* blz 71 Example 1 *)

Section p71E1.

Variable M:CMonoid.
Variable c:M.

Fixpoint power_CMonoid (m:M)(n:nat){struct n}:M:=
match n with 
|0 => (cm_unit M)
|(S p) => m [+] (power_CMonoid m p)
end.

Definition power_CMonoid_CSetoid: M-> nat_as_CSetoid -> M.
simpl.
exact power_CMonoid.
Defined.

Variable is_generated_by: forall(m:M),{n:nat | (power_CMonoid c n)[=]m}.

Let f:= fun (H:forall(m:M),{n:nat | (power_CMonoid c n)[=]m})=>
fun (n:nat_as_CMonoid)=> power_CMonoid c n.

Lemma f_strext: (fun_strext (f is_generated_by)).
simpl.
unfold fun_strext.
simpl.
double induction x y.
unfold f.
simpl.
intro H.
set (H1:=(ax_ap_irreflexive M (@cs_eq  M) (@cs_ap M))).
unfold irreflexive in H1.
unfold Not in H1.
unfold ap_nat.
unfold CNot.
intro H2.
elim H1 with (cm_unit M).
apply CSetoid_is_CSetoid.

exact H.

unfold ap_nat.
unfold CNot.
intros n H H0.
set (H1:= (O_S n)).
intuition.

unfold ap_nat.
unfold CNot.
intros n H H0 H2.
set (H1:= (O_S n)).
cut (0=(S n)).
intuition.

intuition.

intros n H n0 H0.
unfold f.
simpl.
elim (@csg_op M).
simpl.
intros op op_strext H1.
unfold bin_fun_strext in op_strext.
set (H2:=(op_strext c c (power_CMonoid c n0) (power_CMonoid c n)H1)).
elim H2.
intros H3.
set (H4:=(ap_irreflexive_unfolded M c H3)).
elim H4.

intro H3.
unfold f in H0.
set (H4:= (H0 n H3)).
set (H5:= (not_eq_S n0 n)).
unfold ap_nat in H4 |- *.
unfold CNot in H4 |- *.
unfold not in H5.
intro H6.
elim H5.
intro H7.
elim H4.
exact H7.
exact H6.
Qed.

Definition f_as_CSetoid_fun:=
(Build_CSetoid_fun nat_as_CMonoid M (f is_generated_by) f_strext).

Lemma surjective_f: (surjective f_as_CSetoid_fun).
unfold surjective.
simpl.
intro b.
elim (is_generated_by b).
intros m H.
exists m.
unfold f.
exact H.
Qed.

End p71E1.

Section p71E1_.

Lemma M1_is_generated_by_u: (forall(m:M1_as_CMonoid),
{n:nat | (power_CMonoid M1_as_CMonoid u n)[=]m}):CProp.
simpl.
intro m.
induction m.
exists 0.
simpl.
set (H:= (eq_reflexive M1_as_CSetoid e1)).
intuition.

exists 1.
simpl.
set (H:= (eq_reflexive M1_as_CSetoid u)).
intuition.
Qed.

Lemma not_injective_f:
Not(injective (f_as_CSetoid_fun M1_as_CMonoid u M1_is_generated_by_u)).
red.
unfold injective.
simpl.
intro H.
set (H3:=(H 0 2)).
cut (0 {#N} 2).
intro H4.
set (H5:= (H3 H4)).
set (H6:=(ap_imp_neq _ (power_CMonoid M1_as_CMonoid u 0)
         (power_CMonoid M1_as_CMonoid u 2) H5)).
unfold cs_neq in H6.
simpl in H6.
apply H6.
set (H7:= (eq_reflexive_unfolded M1_as_CMonoid e1)).
intuition.

unfold ap_nat.
unfold CNot.
intro H4.
cut False.
intuition.
intuition.
Qed.

End p71E1_.

(* Print to_word_bijective.*)

Section p71E2.

Variable A:CSetoid.

Let L: (free_monoid_as_CMonoid A)-> nat_as_CMonoid.
simpl.
unfold Astar.
intros l.
exact (length l).
Defined.

Lemma L_strext: (fun_strext L).
simpl.
unfold fun_strext.
simpl.
unfold Astar.
intros x.
induction x.
intro y.
case y.
simpl.
unfold ap_nat.
unfold CNot.
intuition.

simpl.
intuition.

intro y.
case y.
simpl.
intuition.

simpl.
intros c l H.
right.
apply IHx.
unfold ap_nat in H |- *.
unfold CNot in H |- *.
intuition.
Qed.

Definition L_as_CSetoid_fun:=
(Build_CSetoid_fun _ _ L L_strext).

Lemma L_is_morphism: (morphism _ _ L_as_CSetoid_fun).
unfold morphism.
simpl.
split.
reflexivity.

unfold Astar.
intros a.
induction a.
simpl.
reflexivity.

simpl.
intuition.
Qed.

End p71E2.

(* blz 71 Remark 1 *)

Section p71R1.

Variable S1:CSemiGroup.
Variable S2:CSemiGroup.

Definition morphism_of_CSemiGroups (f:(CSetoid_fun S1 S2)):CProp:=
forall (a b:S1), (f (a[+]b))[=] (f a)[+](f b).

End p71R1.

Section p71R2.

Variable M:CMonoid.

Definition automorphism:= (isomorphism M M).

End p71R2.

(* Theorem 14 *)

Section Th14.

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

(* blz 71 Examples 2eblok 1 *)

Section p71E2b1.

Definition isomorphic (M:CMonoid)(M':CMonoid): CProp:=
{f:(CSetoid_fun M M')|(isomorphism M M' f)}.

Lemma not_isomorphic_M1_M2: Not (isomorphic M1_as_CMonoid M2_as_CMonoid).
unfold Not.
unfold isomorphic.
simpl.
unfold isomorphism.
unfold morphism.
simpl.
intro H.
elim H.
clear H.
intros f H.
elim H.
clear H.
intros H H0.
elim H.
clear H.
intros H H2.
unfold bijective in H0.
elim H0.
clear H0.
intros H0 H3.
unfold surjective in H3.
simpl in H3.
elim (H3 u).
intros x H4.
cut (M1_eq (f u) u).
intros H5.
set (H1:= not_M1_eq_e1_u).
unfold Not in H1.
apply H1.
unfold M1_eq in H, H2, H5 |- *.
set (H6:=(H2 u u)).
simpl in H6.
rewrite H in H6.
rewrite H5 in H6.
simpl in H6.
exact H6.

unfold M1_eq in H, H4 |- *.
set (H1:= (M1_eq_dec x)).
unfold M1_eq in H1.
elim H1.
intro H5.
rewrite H5 in H4.
rewrite H4 in H.
set (H6:= not_M1_eq_e1_u).
unfold Not in H6.
unfold M1_eq in H6.
elim H6.
cut (u=e1).
intuition.
exact H.

intro H5.
rewrite H5 in H4.
exact H4.
Qed.

End p71E2b1.

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

Definition f_as_CSetoid_fun_:=
(Build_CSetoid_fun _ _ f f_strext').

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

Section Th15.

Variable M:CMonoid.

Fixpoint cm_Sum (l: list M) {struct l}: M :=
match l with
|nil => Zero
|cons a k => a [+] (cm_Sum k)
end.

Variable D : M -> CProp.

Fixpoint member (A : Type) (n : A) (l : list A) {struct l} : CProp :=
  match l with
  | nil => CFalse
  | cons y m => member A n m or y = n
  end.

Implicit Arguments member [A].

Definition Dbrack : M -> CProp := 
fun m => {l: (list M)| (forall (a:M) , member a l -> (D a)) and (cm_Sum l)[=]m}. 

Lemma Dbrack_unit: (Dbrack Zero).
unfold Dbrack.
exists (nil M).
simpl.
intuition.
Qed.

Lemma member_app: forall (x:M) (l k: (list M)), (Iff (member x (app M k l)) 
                  ((member x k) or (member x l))).                                                                   
intros x l.
induction k.
simpl.
unfold Iff.
intuition.

simpl.
unfold Iff in IHk |- *.
elim IHk.
intros IHk0 IHk1.
split.
intros H0.
elim H0.
clear H0.
intro H0.
intuition.

intuition.

intro H0.
elim H0.
clear H0.
intro H0.
elim H0.
clear H0.
intro H0.
left.
apply IHk1.
left.
exact H0.

intuition.

clear H0.
intro H0.
left.
apply IHk1.
right.
exact H0.
Qed.

Lemma cm_Sum_app: 
forall (k l : (list M)), (cm_Sum (app M k l))[=] (cm_Sum k)[+](cm_Sum l).
intros k l.
induction k.
simpl.
intuition.

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
set (H:= (member_app a ly lx)).
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



