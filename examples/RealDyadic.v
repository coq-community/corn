Require Import BigZ ARDyadics CRArith ARexp ARpi ARarctan ARroot.

Definition answer (n:positive) (r : fastAR) : bigZ :=
 let m := (iter_pos n _ (Pmult 10) 1%positive) in 
 let (a, b) := (approximate r (1#m)%Qpos : fastD) * 'Zpos m in 
 BigZ.shiftl a b.

Let ARtest : fastAR := 2 * ARexp (ARexp (AQexp 1)).
Time Eval vm_compute in (answer 150 ARtest).

Let ARtest2 : fastAR := '(4 : Z) + AQexp ('(10 : Z)).
Time Eval vm_compute in (answer 1250 ARtest2).

Let ARtest3 : fastAR := ARpi.
Time Eval vm_compute in (answer 750 ARtest3).

Let ARtest4 : fastAR := ARexp ARpi - ARpi.
Time Eval vm_compute in (answer 200 ARtest4).

Let ARtest5 : fastAR := ARarctan (ARcompress ARpi).
Time Eval vm_compute in (answer 35 ARtest5).

Let ARtest6 : fastAR := ARsqrt 2.
Time Eval vm_compute in (answer 1000 ARtest6).

Let ARtest7 : fastAR := ARsqrt (ARexp 1).
Time Eval vm_compute in (answer 500 ARtest7).

Let ARtest8 : fastAR := ARexp (ARsqrt 2).
Time Eval vm_compute in (answer 200 ARtest8).
