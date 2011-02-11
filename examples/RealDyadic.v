Require Import ARDyadics CRArith ARexp.

Definition answer (n:positive) (r : CR) : Z :=
 let m := (iter_pos n _ (Pmult 10) 1%positive) in
 let (a,b) := (approximate r (1#m)%Qpos)*m in
 Zdiv a b.

Let ARtest : CR := ARtoCR (2 * ARexp (ARexp (AQexp (1 : fastD)))).
Let ARtest2 : CR := ARtoCR ('(ZtofastD 4) + AQexp (ZtofastD 10)).

Time Eval vm_compute in (answer 200 ARtest).
Time Eval vm_compute in (answer 1500 ARtest2).