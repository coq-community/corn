Require Import ARDyadics CRArith ARexp ARpi.

Definition answer (n:positive) (r : CR) : Z :=
 let m := (iter_pos n _ (Pmult 10) 1%positive) in
 let (a,b) := (approximate r (1#m)%Qpos)*m in
 Zdiv a b.

Let ARtest : CR := ARtoCR (2 * ARexp (ARexp (AQexp (1 : fastD)))).
Time Eval vm_compute in (answer 200 ARtest).

Let ARtest2 : CR := ARtoCR ('(ZtofastD 4) + AQexp (ZtofastD 10)).
Time Eval vm_compute in (answer 1500 ARtest2).

Let ARtest3 : CR := ARtoCR (ARpi : fastAR).
Time Eval vm_compute in (answer 1500 ARtest3).

Let ARtest4 : CR := ARtoCR (ARexp ARpi - ARpi : fastAR).
Time Eval vm_compute in (answer 350 ARtest4).

(*

Definition half : fastD := 1 $ (-1)%bigZ.
(*
Lemma yada2 : -(1) ≤ ('half : Q) ≤ 0.
Proof.
Admitted.

Let test := ARAlternatingSum.ARInfAltSum_length (ARexpSequence half)
   (zl:=CRexp.expSequence_zl (CRexp.Qle_ZO_flip yada2)).

Time Eval vm_compute in (test (-100)).

Time Eval vm_compute in (ARAlternatingSum.ARAltSum (CRseries.powers (-half)) (CRseries.factorials) 8 (-200)).
*)
Definition answer (n:positive) (r : CR) : Z :=
 let m := (iter_pos n _ (Pmult 10) 1%positive) in
 let (a,b) := (approximate r (1#m)%Qpos)*m in
 Zdiv a b.

Timeout 3 Let ARtest : CR := ARtoCR (ARexp (ARexp (AQexp (1 : fastD)))).
Timeout 3 Let ARtest2 : CR := ARtoCR (AQexp ('(10 : Z) : fastD)).

Let n : positive := 2000%positive.

Timeout 30 Time Eval vm_compute in (answer n ARtest2).

(*
Let CRtest : CR := CRexp.exp (Compress.compress (CRexp.exp (Compress.compress (CRexp.rational_exp (1#2))))).
Timeout 10 Time Eval vm_compute in (answer n CRtest).

Let ARtest2 : CR := ARtoCR (AQexp (1 $ 2 : fastD)).

Let boundQ (a : Q) := (3#1)^(Zdiv (Qnum (- a)) (Qden (- a))).

Timeout 10 Eval vm_compute in (boundQ 1).
Timeout 10 Eval vm_compute in (proj1_sig (AQexp_inv_pos_bound (1 : fastD))).
Let CRtest : CR := CRexp.rational_exp (4).

Let n : positive := 1000%positive.
Timeout 10 Time Eval vm_compute in (answer n ARtest2).
Time Eval vm_compute in (answer n CRtest).
*)
*)