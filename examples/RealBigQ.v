Require Import BigQ BigZ CRArith ARbigQ ARtrans ARsign.

Definition answer (n:positive) (r : ARbigQ) : bigZ :=
 let m := iter_pos n _ (Pmult 10) 1%positive in 
 match (approximate r (1#m)%Qpos : bigQ) * 'Zpos m with
 | BigQ.Qz n => n
 | BigQ.Qq n d => BigZ.div n ('d)
 end.

(* Many of the following expressions are taken from the "Many Digits friendly competition" problem set *)

Definition P01 : ARbigQ := ARsin (ARsin (AQsin 1)).
Time Eval vm_compute in (answer 150 P01).

Definition P02 : ARbigQ := ARsqrt (ARcompress ARpi).
Time Eval vm_compute in (answer 250 P02).

Definition P03 : ARbigQ := ARsin (AQexp 1).
Time Eval vm_compute in (answer 200 P03).

Definition P04 : ARbigQ := ARexp (ARcompress (ARpi * AQsqrt ('163%Z))).
Time Eval vm_compute in (answer 175 P04).

Definition P05 : ARbigQ := ARexp (ARexp (AQexp 1)).
Time Eval vm_compute in (answer 150 P05).

Definition P07 : ARbigQ := AQexp ('1000%Z).
Time Eval vm_compute in (answer 500 P07).

Definition P08 : ARbigQ := AQcos ('(10^50)%Z).
Time Eval vm_compute in (answer 750 P08).

Definition C02_prf : ARapartT (ARpi : ARbigQ) (0 : ARbigQ).
Proof. AR_solve_apartT (-8)%Z. Defined.

Definition C02 : ARbigQ := ARsqrt (AQexp 1 * ARinvT ARpi C02_prf).
Time Eval vm_compute in (answer 150 C02).

Definition C03 : ARbigQ := ARsin (ARcompress ((AQexp 1 + 1) ^ (3:N))).
Time Eval vm_compute in (answer 200 C03).

Definition C04 : ARbigQ := ARexp (ARcompress (ARpi * AQsqrt ('2011%Z))).
Time Eval vm_compute in (answer 100 C04).

Definition C05 : ARbigQ := ARexp (ARexp (ARsqrt (AQexp 1))).
Time Eval vm_compute in (answer 150 C05).

Definition ARtest1 : ARbigQ := ARpi.
Time Eval vm_compute in (answer 750 ARtest1).

Definition ARtest2 : ARbigQ := ARarctan (ARcompress ARpi).
Time Eval vm_compute in (answer 35 ARtest2).

Definition ARtest3 : ARbigQ := ARsqrt 2.
Time Eval vm_compute in (answer 1000 ARtest3).

Definition ARtest4 : ARbigQ := ARsin ARpi.
Time Eval vm_compute in (answer 200 ARtest4).

Example xkcd217A : ARltT ARtest4 ('20%Z).
Proof. Time AR_solve_ltT (-8)%Z. Defined.
