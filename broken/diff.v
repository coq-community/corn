(*
Require Import CPoly_Newton.
Require Import CRArith.
Require Import Unicode.Utf8
 Setoid Arith List Program Permutation metric2.Classified
 CSetoids CPoly_ApZero CRings CPoly_Degree
 CRArith Qmetric Qring CReals
 stdlib_omissions.Pair stdlib_omissions.Q
 list_separates SetoidPermutation.
Require ne_list.
Import ne_list.notations.

(* Require Import ProductMetric CompleteProduct.*)

(** Outline of the definition of the derivative using div diff.
Should lead to FTC.
Should also be the basis for Newton iteration. 
Becomes very sketchy at the end.
*)

Notation "'one' a":=(ne_list.one a) (at level 60).
Implicit Arguments ne_zip [A B].

Section divdiff.
Definition divdiff2 (f: Q-> CR) :=fun x:Q*Q => 
  let (p , q) := x in  let l:= (p ::: (one q)) in (divdiff (ne_zip l (ne_list.map f l) )).
End divdiff.

(*
Section extra.
Context {X Y : MetricSpace} (f: X → Complete Y) `{!UniformlyContinuous_mu f} `{!UniformlyContinuous f}.
Definition Cbind_slowC: UCFunction (Complete X) (Complete Y):=
   ucFunction (Cbind_slow (wrap_uc_fun' f)).
End extra.
Notation " x >>= f ":= (Cbind_slowC f x) (at level 50).
*)

Section derivative.
(* Notation Q:=Q_as_MetricSpace.*)
(** Definition of the derivative. The usual rules should follow from the ones for dd*)
Context (f:Q->CR) `{!UniformlyContinuous_mu f}
        `{!UniformlyContinuous f}.
Context `{!UniformlyContinuous_mu (divdiff2 f)}
        `{!UniformlyContinuous (divdiff2 f)}.
Definition der : UCFunction Q CR := ucFunction (compose (divdiff2 f) diagonal).
End derivative.

Section towardsLBC.
(** We work towards the Law of Bounded change *)
(* This is seq 1 (S n) *)
Fixpoint posnats (n: nat): ne_list nat:=
    match n with
    | O => one (S O)
    | S n' => (S (S n')) ::: (posnats n')
    end.

Eval compute in (posnats 2).

Notation QPoint := (Q * CR)%type.
Notation CRPoint := (CR * CR)%type.
Local Notation Σ := cm_Sum.

(* Unfortunately, this is not allowed:
Fixpoint interleave {A:Type} (l1 l2 : list A) {struct l1}: list A :=
match l1 with
   | nil => l2
   | a :: l1 => a :: (interleave l2 l1)
end.
*)

Fixpoint interleave {A:Type} (l1 l2 : ne_list A) {struct l1}: ne_list A :=
match l1 with
   | one a => a ::: l2
   | a ::: l1 => a ::: match l2 with | one b => b :::l1
                                                | b ::: l2 => b ::: (interleave l1 l2) end
end.

(*
Fixpoint ne_removelast {A:Set} (l:ne_list A) : ne_list A :=
  match l with
    | one a => one a
    | a ::: l => a ::: ne_removelast l
  end.
*)

Eval compute in (interleave ( 1 ::: (one 2#1)) (ne_list.map Qopp (ne_list.app (one 3#1) (one 0)))).

Definition diff_list (x y: Q) (m:nat) (f:Q->CR):=
let h:=(x-y)/(S m) in
let l:= (ne_list.map (λ x: Q * Q, fst x + snd x) 
   (ne_zip (ne_list.map (λ n:nat, h * n) (posnats m)) (ne_list.replicate_Sn x m))) in 
Σ  (ne_list.map (divdiff2 f) (ne_zip (x ::: l) (ne_list.app l (one 0)))).

(* (map (λ x0 : Q and Q, let (p, q) := x0 in (f p - f q )* ' (/p -q))%CR)*)

Check (diff_list 1 1 2 inject_Q_CR).

Section telescope.
(* 
This really holds for a group, but we do not want to use the group tactic plugin.
*)
(* Should be type classified *)
Context {R:CRing}.
Add Ring R: (CRing_Ring R)(preprocess [unfold cg_minus;simpl]).
Lemma telescope_sum : forall l:ne_list R, forall x y:R, 
   Σ (interleave (x ::: l) (ne_list.map cg_inv (ne_list.app l (one y)))) [=] x [-] y.
Proof with ring.
induction l.
unfold ne_list.last;simpl. intros... 
intros; simpl.
change (x [+] ([--] t [+] Σ (interleave (t ::: l) (ne_list.map cg_inv (ne_list.app l (one y))))) [=] x[-]y).
rewrite IHl...
Qed.
End telescope.

Require Import Morphisms.

(* We would like to use a Map2 for vectors. However, this only works for lists of a fixed length.
Define a general theory of applicative functors from a (strong) monad using type classes.
https://secure.wikimedia.org/wikibooks/en/wiki/Haskell/Applicative_Functors
Map2 should be for vectors
We need the rules:
f ^@> l <@> C a = fun x => (f x a) ^@> l
f ^@> C a <@> l = (f a) ^@> l
Or even f ^@> C a = C f a
*)

Definition dd_pointfree(f:Q->Q):=(compose (uncurry Qdiv) 
            (compose (map_pair (compose (uncurry Qminus) (map_pair f f)) 
            (uncurry Qminus)) (@diagonal (Q*Q)))).
(* This example seems to be too difficult for pointfree:
Require Export PointFree.
Definition test0: PointFree (@fst (unit*unit) unit) _ := _.
Check test0.
Definition test1: PointFree (λ x y: Q, (Qdiv x y)) _ := _.
Check test1.
Opaque Qdiv.
Definition test2: PointFree (uncurry (λ x y: Q, (Qdiv x y))) _ := _.
Check test2.
Definition test1: PointFree (λ x y: Q, (x-y)) _ := (uncurry Qminus (map_pair fst snd)).
*)

(* Sanity check: The derivative of 2x is 2*)
Eval compute  in  (dd_pointfree (fun x =>(2#1)*x) (1#1,0#1)).

Context (f:Q->CR).
Lemma dd_sum:forall x y:Q, forall m:nat,
   (('(S m))* (divdiff2 f (x, y)))%CR [=] diff_list x y m f.
intros.
pose h:=(x-y)/(S m).
transitivity ( ((f x) - (f y))*('(/h))%CR)%CR.
change divdiff2 with dd_pointfree.
unfold divdiff2. 
change ((' S m * ((f x - f y) * ' (/ (x - y))))%CR[=]
  ((f x - f y) * ' (/ h))%CR).
unfold h.
unfold Qdiv.
set ((f x) - (f y))%CR.
rewrite Qinv_mult_distr Qinv_involutive -CRmult_Qmult. 
set (/(x - y)). ring.
unfold diff_list. fold h. unfold divdiff2.
set l:= (ne_list.map (λ x: Q * Q, fst x + snd x) 
   (ne_zip (ne_list.map (λ n:nat, h * n) (posnats m)) (ne_list.replicate_Sn x m))).
set fl:= (ne_list.map f l).
transitivity (Σ (interleave (f x ::: fl) (ne_list.map cg_inv (ne_list.app fl (one f y))))*'(/h))%CR.
rewrite (telescope_sum fl); reflexivity.
(* setoid_rewrite divdiff_e. *)(* we need map to be a morphism *)
transitivity (Σ
  (ne_list.map
     (λ x0 : Q and Q,
      let (p, q) := x0 in
      ((f p [-] f q)%CR *'(/ (p -q))))%CR
     (ne_zip
        (x
         ::: l)  (ne_list.app l (one 0))))).
2:admit.
(* transitivity Σ
  (ne_list.map (fun x => (fst x *snd x)) 
     etc. 
     (λ x0 : Q and Q, let (p, q) := x0 in ((f p[-]f q) * ' (/ (p - q)))%CR)
     (ne_zip (x ::: l) (ne_list.app l (one 0))))

set (ne_list.map (λ x0 : Q and Q, fst x0 + snd x0)
           (ne_zip (ne_list.map (λ n : nat, h * n) (posnats m))
              (ne_list.replicate_Sn x m))).
*)
admit.
Qed.

Context (f:Q->CR) `{!UniformlyContinuous_mu f}
        `{!UniformlyContinuous f}.
Context `{!UniformlyContinuous_mu (divdiff2 f)}
        `{!UniformlyContinuous (divdiff2 f)}.

(* Use compare to avoid dependency on proofs of being in the interval *)
Lemma der_pos_dd_pos: (forall x:Q, (('0 <= (der f) x)%CR))
 -> forall x y, ('0<= (divdiff2 f (x, y)))%CR.
intros.
rewrite CRle_not_lt. intro.
contradict H.
(* definition of der is not correct *)
unfold der . simpl. unfold diagonal. simpl. unfold compose. simpl.
setoid_rewrite  divdiff_e. simpl.
SearchAbout [CRlt].

admit.
Qed.

End bla.
*)