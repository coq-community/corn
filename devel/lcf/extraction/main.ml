open All
open Big_int

(* [int] <-> [nat], for positive [int], tail recursive *)

let i2n = 
  let rec acc p = function 0 -> p | n -> acc (S p) (n-1)
  in acc O  

let n2i = 
  let rec acc p = function O -> p | S n -> acc (p+1) n
  in acc 0

(* [positive] -> [big_int] *)

let rec p2b = function 
 XH -> unit_big_int
| XO p -> (mult_int_big_int 2 (p2b p))
| XI p -> (succ_big_int (mult_int_big_int 2 (p2b p)))

(* [z] -> [big_int] *)

let z2b = function 
  Z0 -> zero_big_int
| Zpos p -> (p2b p)
| Zneg p -> (minus_big_int (p2b p))       

let tests = [
  "one_R", ("One in reals", fun _ -> one_R);
  "one_C", ("One in complex", fun _ -> c_Re_observer one_C); 
  "half", ("1/2 in reals", fun _ -> half0 Tt); 
  "sqrt2_old", ("sqrt(2), direct computation", fun _ -> sqrt_two Tt); 
  "sixteen", ("(x+1)^4 at x=1", fun _ -> sixteen_R Tt); 
  "e", ("exp(1), by series", fun _ -> e);
  "e_2", ("exp(1), by series, using Z", fun _ -> e_2);
  "e_3", ("exp(1), by series, using Z, linear version of pos_fact_ap_zero", fun _ -> e_3);
  "e_4", ("exp(1), by series, using Z, pos_fact_ap_zero in the model", fun _ -> e_4);
  "new_e", ("exp(1), by series, using directly Q", fun _ -> new_E);
  "Pi", ("Pi, first version", fun _ -> pi); 
  "one_fta", ("One as root of x-1", fun _ -> c_Re_observer (one_fta Tt)); 
  "sqrt2_fta", ("sqrt(2) as root of x^2-2", fun _ -> c_Re_observer (sqrt_two_fta Tt));
  "sqrt2", ("sqrt(2), second version",  fun _ -> sqrt_two_lcf Tt);
(*
  "pi", ("Pi, second version",  fun _ -> pi0);
  "cosone", ("cos(1)", fun _ -> cosone);
  "logtwo", ("log(2)", fun _ -> logtwo Tt); *)
]

let usage () = 
  print_string ("usage: fta-test <test> <n>\n"^  
		"where:\n" ^ 
		" <n> is the rank of the approximation\n" ^
		" <test> is one of the following tests:\n"); 
  List.iter (fun (s1,(s2,_)) -> Printf.printf "  %10s\t %s\n" s1 s2) tests; 
  print_newline (); 
  exit 1

let _ = 
  Sys.set_signal Sys.sigint (Sys.Signal_handle (fun _ -> exit 0)); 
  if Array.length Sys.argv <> 3 then usage (); 
  let test = Sys.argv.(1)
  and nb = int_of_string Sys.argv.(2) in 
  let def = try snd (List.assoc test tests) with Not_found -> usage ()
  in 
  let q = Obj.magic (r_observer (def ()) (i2n nb)) in
  Printf.printf "the %d-th approx of %s is :\n%s / %s\n" 
    nb test 
    (string_of_big_int (z2b q.num)) 
    (string_of_big_int (p2b q.den))
  
