
Require Import Test.
Require Import Qreduction.
(* Require Import RealsII. *)

Extract Constant IR => "cauchy_IR".
(* Extract Constant IR => "rR".*)

Extract Constant my_fact' => "my_fact".
Extract Constant my_fact_ap_zero' => "my_fact_ap_zero".

Extract Constant pos_fact_ap_zero__to_realize =>
 "fun n -> pring_ap_zero_opt_opt (pos_fact n)".

Extract Constant grows =>
"fun x w z0 h0 hw hz -> grows_opt x w z0 (r_observer w O) (r_observer z0 O) h0 hw hz".

Extract Constant lft_rht_concrete =>
"fun a b hab -> lft_rht_extract a b (r_observer a O) (r_observer b O) hab".

Extraction
 Inline ap_cotransitive ap_cotransitive_unfolded ap_symmetric
       ap_symmetric_unfolded CSetoid_is_CSetoid cs_proof
       COrdField_is_COrdField ap_wdl_unfolded un_op_strext
       un_op_strext_unfolded bin_op_strext bin_op_strext_unfolded Ccsr_strext.

Extraction NoInline less_imp_ap Greater_imp_ap.

(* for sqrt *)
Extraction Inline Cnested_intervals_zero.

(* Extraction Inline Sin_One_pos. *)

Cd "devel/lcf/extraction".

Extraction "all"
   Cauchy_IR.Cauchy_IR R_observer lft_rht_extract grows_opt
   pring_ap_zero_opt_opt my_fact my_fact_ap_zero Qplus' Qmult'  
   C_Re_observer C_Im_observer one_R one_C half sqrt_two sixteen_R
   Series.E E_2 E_3 E_4 new_E pi sqrt_two_lcf one_fta sqrt_two_fta 
   (* Pi.Pi cosone logtwo *).
