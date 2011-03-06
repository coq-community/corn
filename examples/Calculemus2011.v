Require Import ARDyadics CRArith ARexp ARpi ARarctan.
Require Import CRArith Compress CRexp CRpi CRarctan.

Definition answer (n:positive) (r : CR) : Z :=
 let m := (iter_pos n _ (Pmult 10) 1%positive) in
 let (a,b) := (approximate r (1#m)%Qpos)*m in
 Zdiv a b.

Let ARtest1 : CR := ARtoCR (ARpi : fastAR).
Let CRtest1 : CR := CRpi.

Let ARtest2 : CR := ARtoCR (ARexp (ARcompress (ARexp (ARcompress (AQexp (1 ≪ (-1) : fastD)))))).
Let CRtest2 : CR := exp (compress (exp (compress (rational_exp (1#2))))).

Let ARtest3 : CR := ARtoCR (ARexp (ARcompress ARpi) - ARpi : fastAR).
Let CRtest3 : CR := exp (compress CRpi) - CRpi.

Let ARtest4 : CR := ARtoCR (ARarctan (ARcompress (ARpi : fastAR))).
Let CRtest4 : CR := arctan (compress CRpi).

Time Eval vm_compute in (answer 300 ARtest1).
Time Eval vm_compute in (answer 300 CRtest1).
Time Eval vm_compute in (answer 1750 ARtest1).

Time Eval vm_compute in (answer 25 ARtest2).
Time Eval vm_compute in (answer 25 CRtest2).
Time Eval vm_compute in (answer 450 ARtest2).

Time Eval vm_compute in (answer 25 ARtest3).
Time Eval vm_compute in (answer 25 CRtest3).
Time Eval vm_compute in (answer 425 ARtest3).

Time Eval vm_compute in (answer 25 ARtest4).
Time Eval vm_compute in (answer 25 CRtest4).
Time Eval vm_compute in (answer 85 ARtest4).

