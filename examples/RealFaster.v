Require Import Bignums.BigZ.BigZ CRArith model.totalorder.QposMinMax
        ARbigD ARbigQ ARQ ARtrans ARsign.

Definition myAR := ARbigD.

Definition answer (n : positive) (r : ARbigD) : bigZ :=
 let m := iter_pos _ (Pmult 10) 1%positive n in 
 let (a, b) := (approximate r (Qpos2QposInf (1#m)) : bigD) * 'Zpos m in 
 BigZ.shiftl a b.

(* To avoid timing the printing mechanism *)
Definition no_answer (n : positive) (r : myAR) :=
  let m := iter_pos _ (Pmult 10) 1%positive n in
  let _ := approximate r (Qpos2QposInf (1#m)) in
  tt.

(* xkcd.org/217 *)
Definition xkcd : myAR := (ARexp ARpi)-ARpi.

Time Eval vm_compute in (answer 10 xkcd).

Example xkcd217A : ARltT xkcd ('20%Z).
Proof. Time AR_solve_ltT (-8)%Z. Defined.

(* Many of the following expressions are taken from the "Many Digits friendly competition" problem set *)

(* Instance resolution takes 3s *)
Time Definition P01 : myAR := ARsin (ARsin (AQsin 1)).

Time Eval vm_compute in (answer 500 P01).
Time Eval vm_compute in (no_answer 500 P01).
Definition P02 : myAR := ARsqrt (ARcompress ARpi).
Time Eval vm_compute in (answer 500 P02).

Definition P03 : myAR := ARsin (AQexp 1).
Time Eval vm_compute in (answer 500 P03).

Definition P04 : myAR := ARexp (ARcompress (ARpi * AQsqrt ('163%Z))).
Time Eval vm_compute in (answer 500 P04).

Definition P05 : myAR := ARexp (ARexp (AQexp 1)).
Time Eval vm_compute in (answer 500 P05).

Definition P07 : myAR := AQexp ('1000%Z).
Time Eval vm_compute in (answer 2000 P07).

Definition P08 : myAR := AQcos ('(10^50)%Z).
Time Eval vm_compute in (answer 2000 P08).

Definition C02_prf : ARapartT (ARpi : myAR) (0 : myAR).
Proof. AR_solve_apartT (-8)%Z. Defined.

Definition C02 : myAR := ARsqrt (AQexp 1 * ARinvT ARpi C02_prf).
Time Eval vm_compute in (answer 250 C02).

Definition C03 : myAR := ARsin (ARcompress ((AQexp 1 + 1) ^ (3:N))).
Time Eval vm_compute in (answer 500 C03).

Definition C04 : myAR := ARexp (ARcompress (ARpi * AQsqrt ('2011%Z))).
Time Eval vm_compute in (answer 500 C04).

Definition C05 : myAR := ARexp (ARexp (ARsqrt (AQexp 1))).
Time Eval vm_compute in (answer 500 C05).

(* slow *) (*
Definition C07 : myAR := ARpi ^ 1000%N.
Time Eval vm_compute in (answer 50 C07).
*)
Definition ARtest1 : myAR := ARpi.
Time Eval vm_compute in (answer 1500 ARtest1).

Definition ARtest2 : myAR := ARarctan (ARcompress ARpi).
Time Eval vm_compute in (answer 100 ARtest2).

Definition ARtest3 : myAR := ARsqrt 2.
Time Eval vm_compute in (answer 1000 ARtest3).

Definition ARtest4 : myAR := ARsin ARpi.
Time Eval vm_compute in (answer 500 ARtest4).
