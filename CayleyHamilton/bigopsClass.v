(*
Copyright © 2009 Valentin Blot

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
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
Require Import finfun paths.

Require Import Setoid Morphisms.
Require Import OperationClasses.

Set Implicit Arguments.
Unset Strict Implicit.

Reserved Notation "\big [ op / idx ]_ i F"
  (at level 36, F at level 36, op, idx at level 10, i at level 0,
     right associativity,
           format "'[' \big [ op / idx ]_ i '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( <- r | P ) F"
  (at level 36, F at level 36, op, idx at level 10, r at level 50,
           format "'[' \big [ op / idx ]_ ( <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i <- r | P ) F"
  (at level 36, F at level 36, op, idx at level 10, i, r at level 50,
           format "'[' \big [ op / idx ]_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i <- r ) F"
  (at level 36, F at level 36, op, idx at level 10, i, r at level 50,
           format "'[' \big [ op / idx ]_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( m <= i < n | P ) F"
  (at level 36, F at level 36, op, idx at level 10, m, i, n at level 50,
           format "'[' \big [ op / idx ]_ ( m  <=  i  <  n  |  P )  F ']'").
Reserved Notation "\big [ op / idx ]_ ( m <= i < n ) F"
  (at level 36, F at level 36, op, idx at level 10, i, m, n at level 50,
           format "'[' \big [ op / idx ]_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i | P ) F"
  (at level 36, F at level 36, op, idx at level 10, i at level 50,
           format "'[' \big [ op / idx ]_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i : t | P ) F"
  (at level 36, F at level 36, op, idx at level 10, i at level 50,
           format "'[' \big [ op / idx ]_ ( i   :  t   |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i : t ) F"
  (at level 36, F at level 36, op, idx at level 10, i at level 50,
           format "'[' \big [ op / idx ]_ ( i   :  t ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i < n | P ) F"
  (at level 36, F at level 36, op, idx at level 10, i, n at level 50,
           format "'[' \big [ op / idx ]_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i < n ) F"
  (at level 36, F at level 36, op, idx at level 10, i, n at level 50,
           format "'[' \big [ op / idx ]_ ( i  <  n )  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i \in A | P ) F"
  (at level 36, F at level 36, op, idx at level 10, i, A at level 50,
           format "'[' \big [ op / idx ]_ ( i  \in  A  |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i \in A ) F"
  (at level 36, F at level 36, op, idx at level 10, i, A at level 50,
           format "'[' \big [ op / idx ]_ ( i  \in  A ) '/  '  F ']'").

Open Scope equiv_scope.
Open Scope signature_scope.

Delimit Scope big_scope with BIG.
Open Scope big_scope.

Definition reducebig R I idx op r (P : pred I) (F : I -> R) : R :=
  foldr (fun i x => if P i then op (F i) x else x) idx r.

Definition index_iota m n := iota m (n - m).

Definition index_enum (T : finType) := Finite.enum T.

Lemma mem_index_iota : forall m n i, i \in index_iota m n = (m <= i < n).
Proof.
move=> m n i; rewrite mem_iota; case le_m_i: (m <= i) => //=.
by rewrite -leq_sub_add leq_subS // -subn_gt0 subn_sub addnC subnK // subn_gt0.
Qed.

Lemma filter_index_enum : forall T P, filter P (index_enum T) = enum P.
Proof. by []. Qed.

Notation "\big [ op / idx ]_ ( <- r | P ) F" :=
  (reducebig idx op r P F) : big_scope.
Notation "\big [ op / idx ]_ ( i <- r | P ) F" :=
  (reducebig idx op r (fun i => P%B) (fun i => F)) : big_scope.
Notation "\big [ op / idx ]_ ( i <- r ) F" :=
  (reducebig idx op r (fun _ => true) (fun  i => F)) : big_scope.
Notation "\big [ op / idx ]_ ( m <= i < n | P ) F" :=
  (reducebig idx op (index_iota m n) (fun i : nat => P%B) (fun i : nat => F))
     : big_scope.
Notation "\big [ op / idx ]_ ( m <= i < n ) F" :=
  (reducebig idx op (index_iota m n) (fun _ => true) (fun i : nat => F))
     : big_scope.
Notation "\big [ op / idx ]_ ( i | P ) F" :=
  (reducebig idx op (index_enum _) (fun i => P%B) (fun i => F)) : big_scope.
Notation "\big [ op / idx ]_ i F" :=
  (reducebig idx op (index_enum _) (fun _ => true) (fun i => F)) : big_scope.
Notation "\big [ op / idx ]_ ( i : t | P ) F" :=
  (reducebig idx op (index_enum _) (fun i : t => P%B) (fun i : t => F))
     (only parsing) : big_scope.
Notation "\big [ op / idx ]_ ( i : t ) F" :=
  (reducebig idx op (index_enum _) (fun _ => true) (fun i : t => F))
     (only parsing) : big_scope.
Notation "\big [ op / idx ]_ ( i < n | P ) F" :=
  (\big[op/idx]_(i : ordinal n | P%B) F) : big_scope.
Notation "\big [ op / idx ]_ ( i < n ) F" :=
  (\big[op/idx]_(i : ordinal n) F) : big_scope.
Notation "\big [ op / idx ]_ ( i \in A | P ) F" :=
  (\big[op/idx]_(i | (i \in A) && P) F) : big_scope.
Notation "\big [ op / idx ]_ ( i \in A ) F" :=
  (\big[op/idx]_(i | i \in A) F) : big_scope.

Add Parametric Morphism R I `{Equivalence R req} : (@reducebig R I) with signature
  (req==>(req==>req==>req)==>@eq (seq I)==>(@eq I==>@eq bool)==>(pointwise_relation I req)==>req) as reducebig_morph.
move=> x y eqxy op1 op2 eqop12 r P1 P2 eqP12 F1 F2 eqF12.
elim: r=> //= h q HR; rewrite (eqP12 h h (refl_equal h)).
by case: (P2 h)=> //=; apply: eqop12=> //=; apply: eqF12.
Qed.

Section Extensionality.

Context `{Equivalence R req} {idx : R} {op : binop R}.
Context `{Morphism (binop R) (req==>req==>req) op}.

Section SeqExtension.

Variable I : Type.

Lemma big_filter : forall r (P : pred I) F,
  \big[op/idx]_(i <- filter P r) F i === \big[op/idx]_(i <- r | P i) F i.
Proof. by move=> r P F; elim: r; try reflexivity; move=> i r //=; case (P i); move=> Heq; rewrite <- Heq; reflexivity. Qed.

Lemma eq_bigl : forall r (P1 P2 : pred I) F, P1 =1 P2 ->
  \big[op/idx]_(i <- r | P1 i) F i === \big[op/idx]_(i <- r | P2 i) F i.
Proof.
move=> r P1 P2 F eqP12; rewrite <- big_filter, (eq_filter eqP12), big_filter; reflexivity.
Qed.

Lemma eq_bigr : forall r (P : pred I) F1 F2, (forall i, P i -> F1 i === F2 i) ->
  \big[op/idx]_(i <- r | P i) F1 i === \big[op/idx]_(i <- r | P i) F2 i.
Proof.
move=> r P F1 F2 eqF12.
elim: r => //=;try reflexivity; move=> x r H1.
case Px: (P x); last by assumption.
apply H0; [apply eqF12; assumption|rewrite -> H1; reflexivity].
Qed.

Lemma eq_big : forall r (P1 P2 : pred I) F1 F2,
  P1 =1 P2 -> (forall i, P1 i -> F1 i === F2 i) ->
  \big[op/idx]_(i <- r | P1 i) F1 i === \big[op/idx]_(i <- r | P2 i) F2 i.
Proof.
move=> r P1 P2 F1 F2; move/eq_bigl=> Heq; rewrite <- Heq=>{Heq}.
move/eq_bigr=> Heq; rewrite -> Heq=>{Heq}; reflexivity.
Qed.

Lemma congr_big : forall r1 r2 (P1 P2 : pred I) F1 F2,
  r1 = r2 -> P1 =1 P2 -> (forall i, P1 i -> F1 i === F2 i) ->
    \big[op/idx]_(i <- r1 | P1 i) F1 i === \big[op/idx]_(i <- r2 | P2 i) F2 i.
Proof. move=> r1 r2 P1 P2 F1 F2 <-{r2}; exact: eq_big. Qed.

Lemma big_filter_cond : forall r (P1 P2 : pred I) F,
  \big[op/idx]_(i <- filter P1 r | P2 i) F i
     === \big[op/idx]_(i <- r | P1 i && P2 i) F i.
Proof.
move=> r P1 P2 F; rewrite <- big_filter, <- (big_filter r).
apply congr_big=> [|i|]; try reflexivity.
by rewrite -filter_predI; apply: eq_filter => i; exact: andbC.
Qed.

Lemma big_nil : forall (P : pred I) F,
  \big[op/idx]_(i <- [::] | P i) F i === idx.
Proof. by reflexivity. Qed.

Lemma big_cons : forall i r (P : pred I) F,
  let x := \big[op/idx]_(j <- r | P j) F j in
  \big[op/idx]_(j <- i :: r | P j) F j === if P i then op (F i) x else x.
Proof. by reflexivity. Qed.

Lemma big_map : forall (J : eqType) (h : J -> I) r (P : pred I) F,
  \big[op/idx]_(i <- map h r | P i) F i
     === \big[op/idx]_(j <- r | P (h j)) F (h j).
Proof.
move=> J h r P F; elim: r;try reflexivity; move=> j r //=.
by case: (P (h j)); move=> Heq; rewrite -> Heq; reflexivity.
Qed.

Lemma big_nth : forall x0 r (P : pred I) F,
  \big[op/idx]_(i <- r | P i) F i
     === \big[op/idx]_(0 <= i < size r | P (nth x0 r i)) (F (nth x0 r i)).
Proof.
move=> x0 r P F; rewrite -{1}(mkseq_nth x0 r) /mkseq.
by rewrite -> (big_map (nth x0 r)); rewrite /index_iota subn0; reflexivity.
Qed.

Lemma big_hasC : forall r (P : pred I) F,
  ~~ has P r -> \big[op/idx]_(i <- r | P i) F i === idx.
Proof.
move=> r P F; rewrite <- big_filter; rewrite has_count count_filter.
case: filter => // _; exact: big_nil.
Qed.

Lemma big_pred0_eq : forall (r : seq I) F,
  \big[op/idx]_(i <- r | false) F i === idx.
Proof. by move=> r F; rewrite -> (big_hasC)=> //; try apply H; try reflexivity; rewrite has_pred0. Qed.

Lemma big_pred0 : forall r (P : pred I) F, P =1 xpred0 ->
  \big[op/idx]_(i <- r | P i) F i === idx.
Proof. move=> r P F; move/eq_bigl=> Heq; rewrite -> Heq; exact: big_pred0_eq. Qed.

Lemma big_cat_nested : forall r1 r2 (P : pred I) F,
  let x := \big[op/idx]_(i <- r2 | P i) F i in
  \big[op/idx]_(i <- r1 ++ r2 | P i) F i === \big[op/x]_(i <- r1 | P i) F i.
Proof. by move=> r1 r2 P F; rewrite /reducebig foldr_cat; reflexivity. Qed.

Lemma big_catl : forall r1 r2 (P : pred I) F, ~~ has P r2 ->
  \big[op/idx]_(i <- r1 ++ r2 | P i) F i === \big[op/idx]_(i <- r1 | P i) F i.
Proof. by move=> r1 r2 P F; rewrite -> big_cat_nested; move/big_hasC=> Heq; rewrite -> Heq; reflexivity. Qed.

Lemma big_catr : forall r1 r2 (P : pred I) F, ~~ has P r1 ->
  \big[op/idx]_(i <- r1 ++ r2 | P i) F i === \big[op/idx]_(i <- r2 | P i) F i.
Proof.
move=> r1 r2 P F; rewrite <- big_filter, <- (big_filter r2), filter_cat.
by rewrite has_count count_filter; case: filter; try reflexivity.
Qed.

Lemma big_const_seq : forall r (P : pred I) x,
  \big[op/idx]_(i <- r | P i) x === iter (count P r) (op x) idx.
Proof.
move=> r P x; elim: r; try reflexivity; move=> i r //=.
by case: (P i); move=> Heq; rewrite -> Heq; reflexivity.
Qed.

End SeqExtension.

Lemma big_cond_seq : forall (I : eqType) r (P : pred I) F,
  \big[op/idx]_(i <- r | P i) F i
    === \big[op/idx]_(i <- r | P i && (i \in r)) F i.
Proof.
move=> I r P F; rewrite <- !(big_filter r).
apply congr_big=> [|i|]; try reflexivity.
by apply: eq_in_filter => i ->; rewrite andbT.
Qed.

Lemma congr_big_nat : forall m1 n1 m2 n2 P1 P2 F1 F2,
    m1 = m2 -> n1 = n2 ->
    (forall i, m1 <= i < n2 -> P1 i = P2 i) ->
    (forall i, P1 i && (m1 <= i < n2) -> F1 i === F2 i) ->
  \big[op/idx]_(m1 <= i < n1 | P1 i) F1 i
    === \big[op/idx]_(m2 <= i < n2 | P2 i) F2 i.
Proof.
move=> m n _ _ P1 P2 F1 F2 <- <- eqP12 eqF12.
rewrite -> (big_cond_seq _ P1), -> (big_cond_seq _ P2).
apply: eq_big => i; rewrite ?inE /= !mem_index_iota; last exact: eqF12.
case inmn_i: (m <= i < n); rewrite ?(andbT, andbF) //; exact: eqP12.
Qed.

Lemma big_geq : forall m n (P : pred nat) F, m >= n ->
  \big[op/idx]_(m <= i < n | P i) F i === idx.
Proof. by move=> m n P F ge_m_n; rewrite /index_iota (eqnP ge_m_n); rewrite -> big_nil; reflexivity. Qed.

Lemma big_ltn_cond : forall m n (P : pred nat) F, m < n ->
  let x := \big[op/idx]_(m.+1 <= i < n | P i) F i in
  \big[op/idx]_(m <= i < n | P i) F i === if P m then op (F m) x else x.
Proof.
move=> m [//|n] P F le_m_n; rewrite /index_iota leq_subS //=.
by case: (P m); reflexivity.
Qed.

Lemma big_ltn : forall m n F, m < n ->
  \big[op/idx]_(m <= i < n) F i === op (F m) (\big[op/idx]_(m.+1 <= i < n) F i).
Proof. move=> *; exact: big_ltn_cond. Qed.

Lemma big_addn : forall m n a (P : pred nat) F,
  \big[op/idx]_(m + a <= i < n | P i) F i ===
     \big[op/idx]_(m <= i < n - a | P (i + a)) F (i + a).
Proof.
move=> m n a P F.
rewrite /index_iota subn_sub addnC iota_addl; rewrite -> (big_map (addn a)).
by apply: eq_big => ? *; rewrite addnC;try reflexivity.
Qed.

Lemma big_add1 : forall m n (P : pred nat) F,
  \big[op/idx]_(m.+1 <= i < n | P i) F i ===
     \big[op/idx]_(m <= i < n.-1 | P (i.+1)) F (i.+1).
Proof.
move=> m n P F; rewrite -addn1; rewrite -> big_addn, subn1.
by apply: eq_big => ? *; rewrite addn1;try reflexivity.
Qed.

Lemma big_nat_recl : forall n F,
  \big[op/idx]_(0 <= i < n.+1) F i ===
     op (F 0) (\big[op/idx]_(0 <= i < n) F i.+1).
Proof. by move=> n F; rewrite -> big_ltn=> //; rewrite -> big_add1;try reflexivity. Qed.

Lemma big_mkord : forall n (P : pred nat) F,
  \big[op/idx]_(0 <= i < n | P i) F i === \big[op/idx]_(i < n | P i) F i.
Proof.
move=> n P F; rewrite /index_iota subn0; rewrite <- (big_map (@nat_of_ord n)).
apply (reducebig_morph _); try reflexivity; try apply H0.
by rewrite /index_enum unlock val_ord_enum.
Qed.

Lemma big_nat_widen : forall m n1 n2 (P : pred nat) F, n1 <= n2 ->
  \big[op/idx]_(m <= i < n1 | P i) F i
      === \big[op/idx]_(m <= i < n2 | P i && (i < n1)) F i.
Proof.
move=> m n1 n2 P F len12; symmetry.
rewrite <- big_filter; rewrite filter_predI; rewrite -> big_filter.
apply (reducebig_morph _); try reflexivity; try apply H0.
rewrite /index_iota; set d1 := n1 - m; set d2 := n2 - m.
rewrite -(@subnK d1 d2) /=; last by rewrite leq_sub2r ?leq_addr.
have: ~~ has (fun i => i < n1) (iota (m + d1) (d2 - d1)).
  apply/hasPn=> i; rewrite mem_iota -leqNgt; case/andP=> le_mn1_i _.
  by apply: leq_trans le_mn1_i; rewrite -leq_sub_add.
rewrite -(addnC d1 (d2 - d1)) iota_add filter_cat has_filter /=; case: filter => // _.
rewrite cats0; apply/all_filterP; apply/allP=> i.
rewrite mem_iota; case/andP=> le_m_i lt_i_md1.
apply: (leq_trans lt_i_md1); rewrite subnKC // ltnW //.
rewrite -subn_gt0 -(ltn_add2l m) addn0; exact: leq_trans lt_i_md1.
Qed.

Lemma big_ord_widen_cond : forall n1 n2 (P : pred nat) (F : nat -> R),
     n1 <= n2 ->
  \big[op/idx]_(i < n1 | P i) F i
      === \big[op/idx]_(i < n2 | P i && (i < n1)) F i.
Proof.
move=> n1 n2 P F len12.
rewrite <- big_mkord, (big_nat_widen _ _ _ len12), big_mkord; reflexivity.
Qed.

Lemma big_ord_widen : forall n1 n2 (F : nat -> R),
 n1 <= n2 ->
  \big[op/idx]_(i < n1) F i === \big[op/idx]_(i < n2 | i < n1) F i.
Proof. by move=> *; apply: (big_ord_widen_cond (predT)). Qed.

Lemma big_ord_widen_leq : forall n1 n2 (P : pred 'I_(n1.+1)) F,
 n1 < n2 ->
  \big[op/idx]_(i < n1.+1 | P i) F i
      === \big[op/idx]_(i < n2 | P (inord i) && (i <= n1)) F (inord i).
Proof.
move=> n1 n2 P F len12; pose g G i := G (inord i : 'I_(n1.+1)).
pose e := big_ord_widen_cond (g _ P) (g _ F) len12; unfold g in e; rewrite <- e.
by apply: eq_big => i *; rewrite inord_val;try reflexivity.
Qed.

Lemma big_ord_narrow_cond : forall n1 n2 (P : pred 'I_n2) F,
  forall le_n1_n2 : n1 <= n2,
  let w := widen_ord le_n1_n2 in
  \big[op/idx]_(i < n2 | P i && (i < n1)) F i
    === \big[op/idx]_(i < n1 | P (w i)) F (w i).
Proof.
move=> [|n1] n2 P F ltn12 /=.
  rewrite -> !big_pred0.
    reflexivity.
    intro; inversion x; inversion H1.
    intro; rewrite andbF//.
rewrite -> (big_ord_widen_leq (fun i => P (widen_ord (m:=n2) ltn12 i)) (fun i => F (widen_ord (m:=n2) ltn12 i)) ltn12); apply: eq_big => i.
  rewrite ltnS; case: leqP => [le_i_n1|_]; last by rewrite !andbF.
  by congr (P _ && _); apply: val_inj; rewrite /= inordK.
case/andP=> _ le_i_n1.
assert (i = widen_ord (m:=n2) ltn12 (inord i)).
  by apply: val_inj; rewrite /= inordK.
rewrite <- H1; reflexivity.
Qed.

Lemma big_ord_narrow_cond_leq : forall n1 n2 (P : pred 'I_(n2.+1)) F,
  forall le_n1_n2 : n1 <= n2,
  let w := @widen_ord n1.+1 n2.+1 le_n1_n2 in
  \big[op/idx]_(i < n2.+1 | P i && (i <= n1)) F i
  === \big[op/idx]_(i < n1.+1 | P (w i)) F (w i).
Proof. move=> n1 n2; exact: big_ord_narrow_cond n1.+1 n2.+1. Qed.

Lemma big_ord_narrow : forall n1 n2 F,
  forall le_n1_n2 : n1 <= n2,
  let w := widen_ord le_n1_n2 in
  \big[op/idx]_(i < n2 | i < n1) F i === \big[op/idx]_(i < n1) F (w i).
Proof. move=> *; exact: (big_ord_narrow_cond (predT)). Qed.

Lemma big_ord_narrow_leq : forall n1 n2 F,
  forall le_n1_n2 : n1 <= n2,
  let w := @widen_ord n1.+1 n2.+1 le_n1_n2 in
  \big[op/idx]_(i < n2.+1 | i <= n1) F i === \big[op/idx]_(i < n1.+1) F (w i).
Proof. move=> *; exact: (big_ord_narrow_cond_leq (predT)). Qed.

Lemma big_ord0 : forall P F, \big[op/idx]_(i < 0 | P i) F i === idx.
Proof. by move=> P F; rewrite -> big_pred0 => [|[]]; try reflexivity. Qed.

Lemma big_ord_recl : forall n F,
  \big[op/idx]_(i < n.+1) F i ===
     op (F ord0) (\big[op/idx]_(i < n) F (@lift n.+1 ord0 i)).
Proof.
move=> n F; pose G i := F (inord i).
have eqFG: forall i, req (F i) (G i) by move=> i; rewrite /G inord_val;reflexivity.
transitivity (\big[op/idx]_(i < n.+1) G i); first by apply eq_bigr=> *; apply eqFG.
rewrite <- (big_mkord (S n) (fun _ => true) G), eqFG.
rewrite -> big_ltn=> //; rewrite -> big_add1=> /=; rewrite -> big_mkord.
apply H0; try reflexivity.
by apply: eq_bigr => i _; rewrite -> eqFG; reflexivity.
Qed.

Lemma big_const : forall (I : finType) (A : pred I) x,
  \big[op/idx]_(i \in A) x === iter #|A| (op x) idx.
Proof. by move=> I A x; rewrite -> big_const_seq, count_filter, cardE; reflexivity. Qed.

Lemma big_const_nat : forall m n x,
  \big[op/idx]_(m <= i < n) x === iter (n - m) (op x) idx.
Proof. by move=> *; rewrite -> big_const_seq; rewrite count_predT size_iota; reflexivity. Qed.

Lemma big_const_ord : forall n x,
  \big[op/idx]_(i < n) x === iter n (op x) idx.
Proof.
move=> n x; have e := big_const.
rewrite /in_mem /mem //= in e.
by rewrite -> e, card_ord; reflexivity.
Qed.

End Extensionality.

Section MonoidProperties.

Section Plain.
Context `{Equivalence R req} {op : binop R} {idm : R}.
Context {op_morph : Morphism (Equivalence.equiv==>Equivalence.equiv==>Equivalence.equiv) op}.
Context {op_assoc : associative op}.
Context {op_left_id : left_unit op idm}.
Context {op_right_id : right_unit op idm}.

Notation Local "*%M" := op (at level 0).
Notation Local "x * y" := (op x y).
Notation Local "1" := idm.

Lemma eq_big_idx_seq : forall idx' I r (P : pred I) F,
     right_unit *%M idx' -> has P r ->
   \big[*%M/idx']_(i <- r | P i) F i === \big[*%M/1]_(i <- r | P i) F i.
Proof.
move=> idx' I r P F op_idx'.
rewrite <- !(big_filter r), has_count, count_filter.
case/lastP: (filter P r) => {r p}// r i _.
rewrite <- cats1, !big_cat_nested; rewrite -> big_cons; rewrite -> big_nil => /=.
by rewrite -> op_right_id, op_idx'; reflexivity.
Qed.

Lemma eq_big_idx  : forall idx' (I : finType) i0 (P : pred I) F,
     P i0 -> right_unit *%M idx' ->
  \big[*%M/idx']_(i | P i) F i === \big[*%M/1]_(i | P i) F i.
Proof.
move=> idx' I i0 P F op_idx' Pi0; apply: eq_big_idx_seq => //.
by apply/hasP; exists i0; first rewrite /index_enum -enumT mem_enum.
Qed.

Lemma big1_eq : forall I r (P : pred I), \big[*%M/1]_(i <- r | P i) 1 === 1.
Proof.
move=> *; rewrite -> big_const_seq.
elim: (count _ _); try reflexivity; move=> n //= Heq; rewrite -> Heq; apply op_right_id.
Qed.

Lemma big1 : forall (I : finType) (P : pred I) F,
  (forall i, P i -> F i === 1) -> \big[*%M/1]_(i | P i) F i === 1.
Proof. by move=> I P F eq_F_1; rewrite -> (eq_bigr _ eq_F_1); rewrite -> big1_eq; reflexivity. Qed.

Lemma big1_seq : forall (I : eqType) r (P : pred I) F,
  (forall i, P i && (i \in r) -> F i === 1)
  -> \big[*%M/1]_(i <- r | P i) F i === 1.
Proof.
move=> I r P F eqF1; rewrite -> big_cond_seq; rewrite -> (eq_bigr _ eqF1).
by rewrite -> big1_eq;reflexivity.
Qed.

Lemma big_seq1 : forall I (i : I) F, \big[*%M/1]_(j <- [:: i]) F j === F i.
Proof. by move=> /= *; rewrite -> op_right_id; reflexivity. Qed.

Lemma big_mkcond : forall I r (P : pred I) F,
  \big[*%M/1]_(i <- r | P i) F i ===
     \big[*%M/1]_(i <- r) (if P i then F i else 1).
Proof.
move=> I r P F.
elim: r => //=; try reflexivity; move=> i r HR.
case P.
  by rewrite -> HR;reflexivity.
by rewrite -> op_left_id; exact HR.
Qed.

Lemma big_cat : forall I r1 r2 (P : pred I) F,
  \big[*%M/1]_(i <- r1 ++ r2 | P i) F i ===
     \big[*%M/1]_(i <- r1 | P i) F i * \big[*%M/1]_(i <- r2 | P i) F i.
Proof.
move=> I r1 r2 P F; rewrite -> !(big_mkcond _ P).
elim: r1 => [|i r1 IHr1].
 by rewrite -> big_nil; rewrite -> op_left_id; reflexivity.
by move=> /=; rewrite -> IHr1; apply assoc.
Qed.

Lemma big_pred1_eq : forall (I : finType) (i : I) F,
  \big[*%M/1]_(j | j == i) F j === F i.
Proof. by move=> I i F; rewrite <- big_filter; rewrite -> filter_index_enum; rewrite enum1; rewrite -> big_seq1;reflexivity. Qed.

Lemma big_pred1 : forall (I : finType) i (P : pred I) F,
  P =1 pred1 i -> \big[*%M/1]_(j | P j) F j === F i.
Proof. by move=> I i P F eqP; rewrite -> (eq_bigl _ _ eqP); exact: big_pred1_eq. Qed.

Lemma big_cat_nat : forall n m p (P : pred nat) F, m <= n -> n <= p ->
  \big[*%M/1]_(m <= i < p | P i) F i ===
   (\big[*%M/1]_(m <= i < n | P i) F i) * (\big[*%M/1]_(n <= i < p | P i) F i).
Proof.
move=> n m p F P le_mn le_np; rewrite <- big_cat.
rewrite -{2}(subnKC le_mn) -iota_add -subn_sub subnKC; [reflexivity|apply leq_sub2]=> //.
Qed.

Lemma big_nat1 : forall n F, \big[*%M/1]_(n <= i < n.+1) F i === F n.
Proof.
move=> n F; rewrite -> big_ltn; last by auto.
rewrite -> big_geq=> //; rewrite -> op_right_id; reflexivity.
Qed.

Lemma big_nat_recr : forall n F,
  \big[*%M/1]_(0 <= i < n.+1) F i === (\big[*%M/1]_(0 <= i < n) F i) * F n.
Proof.
move=> n F; rewrite -> (@big_cat_nat n), ?leqnSn, big_nat1=> //; reflexivity.
Qed.

Lemma big_ord_recr : forall n F,
  \big[*%M/1]_(i < n.+1) F i ===
     (\big[*%M/1]_(i < n) F (widen_ord (leqnSn n) i)) * F ord_max.
Proof.
move=> n F; transitivity (\big[*%M/1]_(0 <= i < n.+1) F (inord i)).
  by rewrite -> big_mkord; apply eq_bigr=> i; rewrite inord_val;reflexivity.
rewrite -> big_nat_recr, big_mkord; apply op_morph; last first.
  by (have: (inord n = @ord_max (S_pos_nat n)) by apply: val_inj; rewrite /= inordK); move <-; reflexivity.
by apply eq_bigr => [] i _; (have: (inord i = widen_ord (m:=n.+1) (leqnSn n) i) by apply: ord_inj; rewrite inordK //= leqW); move <-; reflexivity.
Qed.

Lemma big_sumType : forall (I1 I2 : finType) (P : pred (I1 + I2)) F,
  \big[*%M/1]_(i | P i) F i ===
        (\big[*%M/1]_(i | P (inl _ i)) F (inl _ i))
      * (\big[*%M/1]_(i | P (inr _ i)) F (inr _ i)).
Proof.
move=> I1 I2 P F.
rewrite /index_enum [@Finite.enum _]unlock /= /sum_enum; rewrite -> big_cat.
rewrite -> (big_map _ (Finite.enum I1)).
rewrite -> (big_map _ (Finite.enum I2)).
by reflexivity.
Qed.

Lemma big_split_ord : forall m n (P : pred 'I_(m + n)) F,
  \big[*%M/1]_(i | P i) F i ===
        (\big[*%M/1]_(i | P (lshift n i)) F (lshift n i))
      * (\big[*%M/1]_(i | P (rshift m i)) F (rshift m i)).
Proof.
move=> m n P F.
rewrite <- (big_map (lshift n) _ P F), <- (big_map (@rshift m _) _ P F), <- big_cat.
apply congr_big;move=> *;try reflexivity.
by apply: (inj_map (@val_inj _ _ _)); rewrite /index_enum -!enumT val_enum_ord map_cat -map_comp val_enum_ord -map_comp (map_comp (addn m)) val_enum_ord -iota_addl addn0 iota_add.
Qed.

End Plain.

Lemma cardD1x : forall (I : finType) (A : pred I) j,
  A j -> #|SimplPred A| = 1 + #|[pred i | A i && (i != j)]|.
Proof.
move=> I A j Aj; rewrite (cardD1 j) [j \in A]Aj; congr (_ + _).
by apply: eq_card => i; rewrite inE /= andbC.
Qed.

Section Abelian.

Context `{Equivalence R req} {op : binop R} {idm : R}.
Context {op_morph : Morphism (Equivalence.equiv==>Equivalence.equiv==>Equivalence.equiv) op}.
Context {op_assoc : associative op}.
Context {op_left_id : left_unit op idm}.
Context {op_right_id : right_unit op idm}.
Context {op_comm : commutative op}.

Notation Local "'*%M'" := op (at level 0).
Notation Local "x * y" := (op x y).
Notation Local "1" := idm.

(* sinon ca marche pas... *)
Existing Instance mulAC_comm_l.

Lemma eq_big_perm : forall (I : eqType) r1 r2 (P : pred I) F,
    perm_eq r1 r2 ->
  \big[*%M/1]_(i <- r1 | P i) F i === \big[*%M/1]_(i <- r2 | P i) F i.
Proof.
move=> I r1 r2 P F; move/perm_eqP; rewrite -> !(big_mkcond _ P).
elim: r1 r2 => [|i r1 IHr1] r2 eq_r12.
  by case: r2 eq_r12 => //;try reflexivity; move=> i r2; move/(_ (pred1 i)); rewrite /= eqxx.
have r2i: i \in r2 by rewrite -has_pred1 has_count -eq_r12 /= eqxx.
case/splitPr: r2 / r2i => [r3 r4] in eq_r12 *.
rewrite -> big_cat, -> !big_cons.
rewrite -> left_commut; apply op_morph; [reflexivity|]; rewrite <- big_cat; apply: IHr1 => a.
move/(_ a): eq_r12; rewrite !count_cat /= addnCA; exact: addnI.
Qed.

Lemma big_uniq : forall (I : finType) (r : seq I) F,
  uniq r -> \big[*%M/1]_(i <- r) F i === \big[*%M/1]_(i | i \in r) F i.
Proof.
move=> I r F uniq_r; rewrite <- (big_filter (index_enum I)); apply: eq_big_perm.
by rewrite filter_index_enum uniq_perm_eq ?enum_uniq // => i; rewrite mem_enum.
Qed.

Lemma big_split : forall I r (P : pred I) F1 F2,
  \big[*%M/1]_(i <- r | P i) (F1 i * F2 i) ===
    \big[*%M/1]_(i <- r | P i) F1 i * \big[*%M/1]_(i <- r | P i) F2 i.
Proof.
move=> I r P F1 F2.
elim: r => //=; first by symmetry; apply op_left_id.
move=> i r; case: (P i)=> Heq; rewrite -> Heq; try reflexivity.
rewrite -> !op_assoc; apply op_morph; try reflexivity; rewrite -> right_commut at 1; reflexivity.
Qed.

Lemma bigID : forall I r (a P : pred I) F,
  \big[*%M/1]_(i <- r | P i) F i
  === \big[*%M/1]_(i <- r | P i && a i) F i *
    \big[*%M/1]_(i <- r | P i && ~~ a i) F i.
Proof.
move=> I r a P F.
rewrite -> big_mkcond.
rewrite -> (big_mkcond _ (fun i => P i && a i)).
rewrite -> (big_mkcond _ (fun i => P i && ~~ a i)).
rewrite <- big_split; apply eq_bigr => i _.
by case: (P i) => //=; case: (a i) => //=; symmetry; try apply op_left_id; apply op_right_id.
Qed.

Lemma bigU : forall (I : finType) (A B : pred I) F,
  [disjoint A & B] ->
  \big[*%M/1]_(i \in [predU A & B]) F i ===
    (\big[*%M/1]_(i \in A) F i) * (\big[*%M/1]_(i \in B) F i).
Proof.
move=> I A B F dAB; rewrite -> (bigID _ (mem A)); apply op_morph.
  by apply eq_bigl; rewrite /mem // /in_mem; move=> i //=; rewrite orbK.
by apply eq_bigl; move=> i //=; have:= pred0P dAB i; rewrite andbC /= !inE; case: (i \in A).
Qed.

Lemma bigD1 : forall (I : finType) j (P : pred I) F,
  P j -> \big[*%M/1]_(i | P i) F i
    === F j * \big[*%M/1]_(i | P i && (i != j)) F i.
Proof.
move=> I j P F Pj; rewrite -> (bigID _ (pred1 j)).
apply op_morph; try reflexivity.
apply (big_pred1 (P:=fun i => P i && pred1 j i)).
by move=> i; rewrite /= andbC; case: eqP => // ->.
Qed.

Lemma partition_big : forall (I J : finType) (P : pred I) p (Q : pred J) F,
    (forall i, P i -> Q (p i)) ->
      \big[*%M/1]_(i | P i) F i ===
         \big[*%M/1]_(j | Q j) \big[*%M/1]_(i | P i && (p i == j)) F i.
Proof.
move=> I J P p Q F Qp; transitivity (\big[*%M/1]_(i | P i && Q (p i)) F i).
  by apply eq_bigl=> i; case Pi: (P i)=> [|//=]; rewrite Qp.
elim: {Q Qp}_.+1 {-2}Q (ltnSn #|Q|) => // n IHn Q.
case: (pickP Q) => [j Qj | Q0 _]; last first.
  by rewrite -> !big_pred0=> //; try reflexivity; move=> i//=; rewrite Q0 andbF.
rewrite ltnS (cardD1x Qj); rewrite -> (bigD1 (j:=j))=> //; move/IHn=> {n IHn} Heq; rewrite <- Heq.
rewrite -> (bigID _ (fun i => p i == j)); apply op_morph.
  by apply eq_bigl=> i//=; case: eqP => [-> | _]; rewrite ?Qj //= andbC //= andbC //=.
by apply eq_bigl=> i//=; rewrite andbA.
Qed.

Lemma reindex_onto : forall (I J : finType) (h : J -> I) h' (P : pred I) F,
   (forall i, P i -> h (h' i) = i) ->
  \big[*%M/1]_(i | P i) F i ===
    \big[*%M/1]_(j | P (h j) && (h' (h j) == j)) F (h j).
Proof.
move=> I J h h' P F h'K.
elim: {P}_.+1 {-3}P h'K (ltnSn #|P|) => //= n IHn P h'K.
case: (pickP P) => [i Pi | P0 _]; last first.
  rewrite -> big_pred0=> //; rewrite -> big_pred0=> //; [reflexivity|].
  by move=> j //=; rewrite P0.
rewrite ltnS (cardD1x Pi); move/IHn {n IHn} => IH.
rewrite -> (bigD1 (j:=i) _ Pi), (bigD1 (j:=h' i)); rewrite h'K ?Pi ?eq_refl //=; apply op_morph; try reflexivity.
rewrite -> IH.
  apply eq_bigl=> j//=; rewrite andbC -andbA (andbCA (P _)).
  by case: eqP => //= hK; congr (_ && ~~ _); apply/eqP/eqP=> [<-|->] //; rewrite h'K.
by move=> j//=; case/andP; auto.
Qed.

Lemma reindex : forall (I J : finType) (h : J -> I) (P : pred I) F,
  {on [pred i | P i], bijective h} ->
  \big[*%M/1]_(i | P i) F i === \big[*%M/1]_(j | P (h j)) F (h j).
Proof.
move=> I J h P F [h' hK h'K]; rewrite -> (reindex_onto _ h'K); apply eq_bigl=> j//=.
by rewrite !inE; case Pi: (P _); rewrite //= hK ?eqxx.
Qed.

Lemma pair_big_dep : forall (I J : finType) (P : pred I) (Q : I -> pred J) F,
  \big[*%M/1]_(i | P i) \big[*%M/1]_(j | Q i j) F i j ===
    \big[*%M/1]_(p | P p.1 && Q p.1 p.2) F p.1 p.2.
Proof.
move=> I J P Q F.
rewrite -> (partition_big (P:=fun p => P p.1 && Q p.1 p.2) (p:=fun p => p.1) (Q:=P))=> [|j]; last by case/andP.
apply eq_bigr=>i Pi.
rewrite -> (reindex_onto (h:=pair i) (h':=fun p => p.2)).
   by apply eq_bigl=> j; rewrite !eqxx [P i]Pi !andbT.
by case=> i' j /=; case/andP=> _ /=; move/eqP->.
Qed.

Lemma pair_big : forall (I J : finType) (P : pred I) (Q : pred J) F,
  \big[*%M/1]_(i | P i) \big[*%M/1]_(j | Q j) F i j ===
    \big[*%M/1]_(p | P p.1 && Q p.2) F p.1 p.2.
Proof. move=> *; exact: pair_big_dep. Qed.

Lemma pair_bigA : forall (I J : finType) (F : I -> J -> R),
  \big[*%M/1]_i \big[*%M/1]_j F i j === \big[*%M/1]_p F p.1 p.2.
Proof. move=> *; exact: pair_big_dep. Qed.

Lemma exchange_big_dep :
    forall (I J : finType) (P : pred I) (Q : I -> pred J) (xQ : pred J) F,
    (forall i j, P i -> Q i j -> xQ j) ->
  \big[*%M/1]_(i | P i) \big[*%M/1]_(j | Q i j) F i j ===
    \big[*%M/1]_(j | xQ j) \big[*%M/1]_(i | P i && Q i j) F i j.
Proof.
move=> I J P Q xQ F PQxQ; pose p u := (u.2, u.1).
rewrite -> !pair_big_dep, (reindex_onto (h:=p J I) (h':=p I J)) => [|[//]].
apply eq_big=> [] [j i] //=;try reflexivity; symmetry.
by rewrite eq_refl andbC; case: (@andP (P i)) => //= [[]]; exact: PQxQ.
Qed.

Lemma exchange_big :  forall (I J : finType) (P : pred I) (Q : pred J) F,
  \big[*%M/1]_(i | P i) \big[*%M/1]_(j | Q j) F i j ===
    \big[*%M/1]_(j | Q j) \big[*%M/1]_(i | P i) F i j.
Proof.
move=> I J P Q F; rewrite -> (exchange_big_dep (Q:=fun i j => Q j) (xQ:=Q))=> //.
by apply eq_bigr=> i /= Qi; apply eq_bigl=> j; rewrite [Q i]Qi andbT.
Qed.

Lemma exchange_big_dep_nat :
  forall m1 n1 m2 n2 (P : pred nat) (Q : rel nat) (xQ : pred nat) F,
    (forall i j, m1 <= i < n1 -> m2 <= j < n2 -> P i -> Q i j -> xQ j) ->
  \big[*%M/1]_(m1 <= i < n1 | P i) \big[*%M/1]_(m2 <= j < n2 | Q i j) F i j ===
    \big[*%M/1]_(m2 <= j < n2 | xQ j)
       \big[*%M/1]_(m1 <= i < n1 | P i && Q i j) F i j.
Proof.
move=> m1 n1 m2 n2 P Q xQ F PQxQ.
transitivity
  (\big[*%M/1]_(i < n1 - m1| P (i + m1))
    \big[*%M/1]_(j < n2 - m2 | Q (i + m1) (j + m2)) F (i + m1) (j + m2)).
- rewrite -{1}[m1]add0n; rewrite -> big_addn; rewrite -> big_mkord; apply eq_bigr=> i _.
  by rewrite -{1}[m2]add0n; rewrite -> big_addn; rewrite -> big_mkord; reflexivity.
rewrite -> (exchange_big_dep
                       (I:=ordinal_finType (n1 - m1))
                       (J:=ordinal_finType (n2 - m2))
                       (P:=fun i => P (i + m1))
                       (Q:=fun i j => Q (i + m1) (j + m2))
                       (xQ:=fun j: 'I__ => xQ (j + m2)))=> [|i j]; last first.
  by apply: PQxQ; rewrite leq_addl addnC -subn_gt0 -subn_sub subn_gt0 ltn_ord.
symmetry; rewrite -{1}[m2]add0n; rewrite -> big_addn; rewrite -> big_mkord; apply eq_bigr=> j _.
by rewrite -{1}[m1]add0n; rewrite -> big_addn; rewrite -> big_mkord; reflexivity.
Qed.

Lemma exchange_big_nat : forall m1 n1 m2 n2 (P Q : pred nat) F,
  \big[*%M/1]_(m1 <= i < n1 | P i) \big[*%M/1]_(m2 <= j < n2 | Q j) F i j ===
    \big[*%M/1]_(m2 <= j < n2 | Q j) \big[*%M/1]_(m1 <= i < n1 | P i) F i j.
Proof.
move=> m1 n1 m2 n2 P Q F.
rewrite -> (exchange_big_dep_nat (P:=P) (Q:=fun i j => Q j) (xQ:=Q))=> //.
by apply eq_bigr=> i /= Qi; apply eq_bigl=> j; rewrite [Q i]Qi andbT.
Qed.

End Abelian.

End MonoidProperties.

Section BigProp.

Context `{Equivalence R req} {Pb : R -> Prop}.
Context {idx : R} {op1 : binop R}.
Context {Pb_morph : Morphism (Equivalence.equiv==>Equivalence.equiv) Pb}.
Context {op1_morph : Morphism (req==>req==>req) op1}.
Hypothesis (Pb_idx : Pb idx)
           (Pb_op1 : forall x y, Pb x -> Pb y -> Pb (op1 x y)).

Lemma big_prop : forall I r (P : pred I) F,
  (forall i, P i -> Pb (F i)) -> Pb (\big[op1/idx]_(i <- r | P i) F i).
Proof. by move=> I r P F PbF; elim: r => //= i *; case Pi: (P i); auto. Qed.

Variable (op2 : binop R).
Context {op2_morph : Morphism (req==>req==>req) op2}.

Hypothesis (Pb_eq_op : forall x y, Pb x -> Pb y -> op1 x y === op2 x y).

Lemma big_prop_seq : forall (I : eqType) (r : seq I) (P : pred I) F,
  (forall i, P i && (i \in r) -> Pb (F i)) ->
   Pb (\big[op1/idx]_(i <- r | P i) F i).
Proof. by move=> I r P F; rewrite -> big_cond_seq; exact: big_prop. Qed.

Lemma eq_big_op :  forall I r (P : pred I) F,
   (forall i, P i -> Pb (F i)) ->
  \big[op1/idx]_(i <- r | P i) F i === \big[op2/idx]_(i <- r | P i) F i.
Proof.
have:= big_prop=> Pb_big I r P F Pb_F.
elim: r; try reflexivity; move=> i r //=; case Pi: (P i); move=> Heq; rewrite <- Heq; auto; reflexivity.
Qed.

Lemma eq_big_op_seq :  forall (I : eqType) r (P : pred I) F,
    (forall i, P i && (i \in r) -> Pb (F i)) ->
  \big[op1/idx]_(i <- r | P i) F i === \big[op2/idx]_(i <- r | P i) F i.
Proof.
move=> I r P F Pb_F; rewrite -> big_cond_seq.
by symmetry; rewrite -> big_cond_seq; symmetry; apply eq_big_op.
Qed.

End BigProp.

Section BigRel.
Context `{Equivalence R1 req1}.
Variables (idx1 : R1) (op1 : binop R1).
Context `{Equivalence R2 req2}.
Variable Pr : R1 -> R2 -> Prop.
Variables (idx2 : R2) (op2 : binop R2).
Context {Pr_morph : Morphism (Equivalence.equiv==>Equivalence.equiv==>Equivalence.equiv) Pr}.
Context {op1_morph : Morphism (Equivalence.equiv==>Equivalence.equiv==>Equivalence.equiv) op1}.
Context {op2_morph : Morphism (Equivalence.equiv==>Equivalence.equiv==>Equivalence.equiv) op2}.

Hypothesis Pr_idx : Pr idx1 idx2.
Hypothesis Pr_rel : forall x1 x2 y1 y2,
  Pr x1 x2 -> Pr y1 y2 -> Pr (op1 x1 y1) (op2 x2 y2).

Lemma big_rel : forall I r (P : pred I) F1 F2,
  (forall i, (P i) -> Pr (F1 i) (F2 i)) ->
  Pr (\big[op1/idx1]_(i <- r | P i) F1 i) (\big[op2/idx2]_(i <- r | P i) F2 i).
Proof.
move=> I r P F1 F2 PrF.
elim: r => //= i *; case Pi: (P i); auto.
Qed.

Lemma big_rel_seq : forall (I : eqType) (r : seq I) (P : pred I) F1 F2,
    (forall i, P i && (i \in r) -> Pr (F1 i) (F2 i)) ->
  Pr (\big[op1/idx1]_(i <- r | P i) F1 i) (\big[op2/idx2]_(i <- r | P i) F2 i).
Proof.
move=> I r P F1 F2 *; rewrite -> big_cond_seq.
by rewrite -> (big_cond_seq (idx:=idx2)); apply big_rel.
Qed.

End BigRel.

Section Morphism.

Context {R1 : Type} `{Equivalence R2 req2}.
Variables (idx1 : R1) (op1 : binop R1).
Variables (idx2 : R2) (op2 : binop R2).
Variable phi : R1 -> R2.
Hypothesis phiM : forall x y, req2 (phi (op1 x y)) (op2 (phi x) (phi y)).
Hypothesis phi_id : req2 (phi idx1) idx2.
Context {op2_morph : Morphism (Equivalence.equiv==>Equivalence.equiv==>Equivalence.equiv) op2}.

Lemma big_morph : forall I r (P : pred I) F,
  phi (\big[op1/idx1]_(i <- r | P i) F i) ===
     \big[op2/idx2]_(i <- r | P i) phi (F i).
Proof.
move=> I r P F; elim: r => [ //= | i r //= ].
case: (P i) => Heq; rewrite <- Heq; [apply phiM|reflexivity].
Qed.

End Morphism.

Section Distributivity.

Context `{Equivalence R req} {add mul : binop R} {zero : R}.
Notation Local "*%M" := mul (at level 0).
Notation Local "x * y" := (mul x y).
Notation Local "0" := zero.
Notation Local "+%M" := add (at level 0).
Notation Local "x + y" := (add x y).

Context {op_morph : Morphism (Equivalence.equiv==>Equivalence.equiv==>Equivalence.equiv) add}.
Context {mul_morph : Morphism (Equivalence.equiv==>Equivalence.equiv==>Equivalence.equiv) mul}.
Context {op_assoc : associative +%M}.
Context {op_comm : commutative +%M}.
Context {op_left_unit : left_unit +%M 0}.
Context {op_left_zero : left_absorbing *%M 0}.
Context {op_right_zero : right_absorbing *%M 0}.
Context {op_left_distr : left_distributive +%M *%M}.
Context {op_right_distr : right_distributive +%M *%M}.

Lemma big_distrl : forall I r a (P : pred I) F,
  \big[+%M/0]_(i <- r | P i) F i * a === \big[+%M/0]_(i <- r | P i) (F i * a).
Proof.
move=> I r a P F;  apply (big_morph (phi:=fun x => x * a)) => [ x y | | //= ].
  by apply left_dist.
by apply op_left_zero.
Qed.

Lemma big_distrr : forall I r a (P : pred I) F,
  a * \big[+%M/0]_(i <- r | P i) F i === \big[+%M/0]_(i <- r | P i) (a * F i).
Proof.
move=> I r a P F. apply (big_morph (phi:=fun x => a *x)) => [ x y || //= ].
  by apply op_right_distr.
by apply op_right_zero.
Qed.

Context {one : R}.
Notation Local "1" := one.

(* sinon ça marche pas...*)
Existing Instance mulC_id_l.

Lemma big_distr_big_dep :
  forall (I J : finType) j0 (P : pred I) (Q : I -> pred J) F,
  \big[*%M/1]_(i | P i) \big[+%M/0]_(j | Q i j) F i j ===
     \big[+%M/0]_(f | pfamily j0 P Q f) \big[*%M/1]_(i | P i) F i (f i).
Proof.
move=> I J j0 P Q F; rewrite <- big_filter; rewrite filter_index_enum; set r := enum P.
pose fIJ := {ffun I -> J}; pose Pf := pfamily j0 _ Q; symmetry.
transitivity (\big[+%M/0]_(f | Pf (mem r) f) \big[*%M/1]_(i <- r) F i (f i)).
  apply: eq_big=> f; auto; last by rewrite <- big_filter; rewrite filter_index_enum; reflexivity.
  by apply: eq_forallb => i; rewrite /= mem_enum.
have: uniq r by exact: enum_uniq.
elim: {P}r => [_|i r IHr].
  rewrite -> (big_pred1 (i:=[ffun => j0])); first by rewrite -> big_nil; reflexivity.
  move=> f //=; apply /familyP /eqP=> /= [Df |->{f} i]; last by rewrite ffunE.
  by apply/ffunP=> i; rewrite ffunE; exact/eqP.
case/andP=> nri; rewrite -> big_cons; move/IHr {IHr} => IHr; rewrite <- IHr; rewrite -> big_distrl.
rewrite -> (partition_big (P:=Pf (mem (i :: r))) (p:=fun f : fIJ => f i) (Q:=Q i)); last first.
  by move=> f; move/familyP; move/(_ i); rewrite /= inE /= eqxx.
pose seti j (f : fIJ) := [ffun k => if k == i then j else f k].
apply eq_bigr => j Qij; rewrite -> (reindex_onto (h:=seti j) (h':=seti j0)
  (P:=fun i0 => andb (Pf (mem (Cons I i r)) i0) (eq_op (i0 i) j))); last first.
  move=> f /=; case/andP; move/familyP=> eq_f; move/eqP=> fi.
  by apply/ffunP => k; rewrite !ffunE; case: eqP => // ->.
rewrite -> big_distrr; apply eq_big => [f | f eq_f]; last first.
  rewrite -> big_cons; rewrite ffunE eq_refl; apply mul_morph; [reflexivity|]; rewrite -> !(big_cond_seq r predT).
  by apply eq_bigr => k; rewrite ffunE; case: eqP; try reflexivity; move => ->; case/idPn.
rewrite !ffunE !eq_refl andbT; apply/andP/familyP=> [[Pjf fij0] k | Pff].
  have:= familyP _ _ Pjf k; rewrite /= ffunE in_cons; case: eqP => // -> _.
  by rewrite (negbTE nri) -(eqP fij0) !ffunE ?inE /= !eqxx.
split.
  apply/familyP=> k; move/(_ k): Pff; rewrite /= ffunE in_cons.
  by case: eqP => // ->.
apply/eqP; apply/ffunP=> k; have:= Pff k; rewrite !ffunE /=.
by case: eqP => // ->; rewrite (negbTE nri) /=; move/eqP.
Qed.

Lemma big_distr_big :
  forall (I J : finType) j0 (P : pred I) (Q : pred J) F,
  \big[*%M/1]_(i | P i) \big[+%M/0]_(j | Q j) F i j ===
     \big[+%M/0]_(f | pffun_on j0 P Q f) \big[*%M/1]_(i | P i) F i (f i).
Proof.
move=> I J j0 P Q F; rewrite -> (big_distr_big_dep j0); apply eq_bigl => f.
by apply/familyP/familyP=> Pf i; move/(_ i): Pf; case: (P i).
Qed.

Lemma bigA_distr_big_dep :
  forall (I J : finType) (Q : I -> pred J) F,
  \big[*%M/1]_i \big[+%M/0]_(j | Q i j) F i j
    === \big[+%M/0]_(f | family Q f) \big[*%M/1]_i F i (f i).
Proof.
move=> I J Q F; case: (pickP J) => [j0 _ | J0].
   exact: (big_distr_big_dep j0).
rewrite /index_enum -enumT; case: (enum I) (mem_enum I) => [I0 | i r _].
  have f0: I -> J by move=> i; have:= I0 i.
  rewrite -> (big_pred1 (i:=finfun f0)); first by rewrite -> big_nil; reflexivity.
  rewrite /mem // => x.
  by apply/familyP/eqP=> _; first apply/ffunP; move=> i; have:= I0 i.
have Q0: Q _ =1 pred0 by move=> ? j; have:= J0 j.
rewrite -> big_cons=> /=; rewrite -> big_pred0=> //; rewrite -> op_left_zero; rewrite -> big_pred0; first by reflexivity.
by move=> f; apply/familyP; move/(_ i); rewrite Q0.
Qed.

Lemma bigA_distr_big :
  forall (I J : finType) (Q : pred J) (F : I -> J -> R),
  \big[*%M/1]_i \big[+%M/0]_(j | Q j) F i j
    === \big[+%M/0]_(f | ffun_on Q f) \big[*%M/1]_i F i (f i).
Proof. move=> *; exact: bigA_distr_big_dep. Qed.

Lemma bigA_distr_bigA :
  forall (I J : finType) F,
  \big[*%M/1]_(i : I) \big[+%M/0]_(j : J) F i j
    === \big[+%M/0]_(f : {ffun I -> J}) \big[*%M/1]_i F i (f i).
Proof.
move=> *; rewrite -> bigA_distr_big; apply eq_bigl => ?; exact/familyP.
Qed.

End Distributivity.
