Require Import ARbigD CRArith ARexp ARpi ARarctan.
Require Import CRArith Compress CRexp CRpi CRarctan.

Definition eval (n:positive) (r : CR) : Q :=
 let m := iter_pos n _ (Pmult 10) 1%positive in approximate r (1#m)%Qpos.

Definition deval (n:positive) (r : ARbigD) : bigD :=
 let m := iter_pos n _ (Pmult 10) 1%positive in approximate r (1#m)%Qpos.

Let ARtest1 : ARbigD := ARpi.
Let CRtest1 : CR := CRpi.

Let ARtest2 : ARbigD := ARexp (ARcompress (ARexp (ARcompress (AQexp (1 ≪ (-1)))))).
Let CRtest2 : CR := exp (compress (exp (compress (rational_exp (1#2))))).

Let ARtest3 : ARbigD := ARexp (ARcompress ARpi) - ARpi.
Let CRtest3 : CR := exp (compress CRpi) - CRpi.

Let ARtest4 : ARbigD := ARarctan (ARcompress ARpi).
Let CRtest4 : CR := arctan (compress CRpi).
(*
Time Eval vm_compute in (deval 300 ARtest1).
Time Eval vm_compute in (eval 300 CRtest1).
Time Eval vm_compute in (deval 2000 ARtest1).

Time Eval vm_compute in (deval 25 ARtest2).
Time Eval vm_compute in (eval 25 CRtest2).
Time Eval vm_compute in (deval 450 ARtest2).

Time Eval vm_compute in (deval 25 ARtest3).
Time Eval vm_compute in (eval 25 CRtest3).
Time Eval vm_compute in (deval 425 ARtest3).

Time Eval vm_compute in (deval 25 ARtest4).
Time Eval vm_compute in (eval 25 CRtest4).
Time Eval vm_compute in (deval 85 ARtest4).
*)
(* Finally, we compare our sqrt with an implementation not using type classes *)
Require Import ARroot dyadics.

Let n := Eval compute in (10 * 10 * 10 * 10)%nat.
Let ARroot_test : nat -> bigD * bigD := AQsqrt_loop (a:=2).

Time Eval vm_compute in (
  (fun _ _ _ _ _ _ _ _ _ _ => true)
  (snd (ARroot_test n))
  (snd (ARroot_test n))
  (snd (ARroot_test n))
  (snd (ARroot_test n))
  (snd (ARroot_test n))
  (snd (ARroot_test n))
  (snd (ARroot_test n))
  (snd (ARroot_test n))
  (snd (ARroot_test n))
  (snd (ARroot_test n))).

Require Import BigZ.
Open Scope bigZ_scope.

Definition BigD_0 : bigD := (0 $ 0).
Definition BigD_1 : bigD := (1 $ 0).
Definition BigD_2 : bigD := (2 $ 0).
Definition BigD_4 : bigD := (4 $ 0).

Definition BigD_plus (x y : bigD) : bigD := 
  match BigZ.compare (expo x) (expo y) with
  | Gt => BigZ.shiftl (mant x) (expo x - expo y) + mant y $ BigZ.min (expo x) (expo y)
  | _ => mant x + BigZ.shiftl (mant y) (expo y - expo x) $ BigZ.min (expo x) (expo y)
  end.

Definition BigD_opp (x : bigD) : bigD := -mant x $ expo x.

Definition BigD_mult (x y : bigD) : bigD := mant x * mant y $ expo x + expo y.

Definition BigD_shiftl (x : bigD) (n : bigZ) : bigD := mant x $ expo x + n.

Definition BigD_compare (x y : bigD) : comparison := 
  match BigZ.compare (expo x) (expo y) with
  | Gt => BigZ.compare (BigZ.shiftl (mant x) (expo x - expo y)) (mant y)
  | _ => BigZ.compare (mant x) (BigZ.shiftl (mant y) (expo y - expo x))
  end.

Fixpoint root_loop_alt (x : bigD) (n : nat) : bigD * bigD :=
  match n with
  | O => (x, BigD_0)
  | S n => let (r, s) := root_loop_alt x n in
     match BigD_compare (BigD_plus s BigD_1) r with
     | Gt => (BigD_shiftl r 2, BigD_shiftl s 1)
     | _ => (BigD_shiftl (BigD_plus r (BigD_opp (BigD_plus s BigD_1))) 2, BigD_shiftl (BigD_plus s BigD_2) 1)
     end
  end.

Time Eval vm_compute in (
  (fun _ _ _ _ _ _ _ _ _ _ => true)
  (snd (root_loop_alt BigD_2 n))
  (snd (root_loop_alt BigD_2 n))
  (snd (root_loop_alt BigD_2 n))
  (snd (root_loop_alt BigD_2 n))
  (snd (root_loop_alt BigD_2 n))
  (snd (root_loop_alt BigD_2 n))
  (snd (root_loop_alt BigD_2 n))
  (snd (root_loop_alt BigD_2 n))
  (snd (root_loop_alt BigD_2 n))
  (snd (root_loop_alt BigD_2 n))).

(* As suggested by Laurent Théry, mult is more efficient than shiftl in case the size of bigN is 
    large enough. By increasing size in theories/Numbers/Natural/BigN/NMake_gen.ml to 12 
    the following is faster. *)
Fixpoint root_loop_alt_mult (x : bigD) (n : nat) : bigD * bigD :=
  match n with
  | O => (x, BigD_0)
  | S n => let (r, s) := root_loop_alt_mult x n in
     match BigD_compare (BigD_plus s BigD_1) r with
     | Gt => (BigD_mult BigD_4 r, BigD_mult BigD_2 s)
     | _ => (BigD_mult BigD_4 (BigD_plus r (BigD_opp (BigD_plus s BigD_1))), BigD_mult BigD_2 (BigD_plus s BigD_2))
     end
  end.

Time Eval vm_compute in (
  (fun _ _ _ _ _ _ _ _ _ _ => true)
  (snd (root_loop_alt_mult BigD_2 n))
  (snd (root_loop_alt_mult BigD_2 n))
  (snd (root_loop_alt_mult BigD_2 n))
  (snd (root_loop_alt_mult BigD_2 n))
  (snd (root_loop_alt_mult BigD_2 n))
  (snd (root_loop_alt_mult BigD_2 n))
  (snd (root_loop_alt_mult BigD_2 n))
  (snd (root_loop_alt_mult BigD_2 n))
  (snd (root_loop_alt_mult BigD_2 n))
  (snd (root_loop_alt_mult BigD_2 n))).
