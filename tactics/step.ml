(* A tactic for chaining transitivity steps *)

open Tacticals
open Tactics
open Libnames
open Rawterm
open Summary
open Libobject
open Lib

let transitivity_right_table = ref []
let transitivity_left_table = ref []

(* for 7.4 
let step left x tac =
  let tac = Tacinterp.interp tac in
  let l =
    List.map (fun lem ->
      tclTHENLAST
      (apply_with_bindings (constr_of_reference lem, ImplicitBindings [x]))
        tac)
      !(if left then transitivity_left_table else transitivity_right_table)
  in
  tclFIRST l
*)

(* for CVS version *)
let step left x tac =
  let l =
    List.map (fun lem ->
      tclTHENLAST
      (apply_with_bindings (constr_of_reference lem, ImplicitBindings [x]))
        tac)
      !(if left then transitivity_left_table else transitivity_right_table)
  in
  tclFIRST l
(* *)

(* Main function to push lemmas in persistent environment *)

let cache_transitivity_lemma (_,(left,lem)) =
  if left then  
    transitivity_left_table  := lem :: !transitivity_left_table
  else
    transitivity_right_table := lem :: !transitivity_right_table
  
let subst_transitivity_lemma (_,subst,(b,ref)) = (b,subst_global subst ref)

let (inTransitivity,_) =
  declare_object {(default_object "TRANSITIVITY-STEPS") with
    cache_function = cache_transitivity_lemma;
    open_function = (fun i o -> if i=1 then cache_transitivity_lemma o);
    subst_function = subst_transitivity_lemma;
    classify_function = (fun (_,o) -> Substitute o);       
    export_function = (fun x -> Some x) }

(* Synchronisation with reset *)

let freeze () = !transitivity_left_table, !transitivity_right_table

let unfreeze (l,r) = 
  transitivity_left_table := l;
  transitivity_right_table := r

let init () = 
  transitivity_left_table := [];
  transitivity_right_table := []

let _ = 
  declare_summary "transitivity-steps"
    { freeze_function = freeze;
      unfreeze_function = unfreeze;
      init_function = init;
      survive_module = false; 
      survive_section = false }

(* Main entry points *)

let add_transitivity_lemma left ref =
  add_anonymous_leaf (inTransitivity (left,Nametab.global ref))

(* Vernacular syntax *)

(* for 7.4 
TACTIC EXTEND Stepl
| ["Stepl" constr(c) tactic(tac) ] -> [ step true c tac ]
END

TACTIC EXTEND Stepr
| ["Stepr" constr(c) tactic(tac) ] -> [ step false c tac ]
END
*)

(* for CVS version*)
TACTIC EXTEND Stepl
| ["Stepl" constr(c) tactic(tac) ] -> [ step true c (snd tac) ]
END

TACTIC EXTEND Stepr
| ["Stepr" constr(c) tactic(tac) ] -> [ step false c (snd tac) ]
END
(* *)

VERNAC COMMAND EXTEND AddStepl
| [ "Declare" "Left" "Step" global(id) ] ->
    [ add_transitivity_lemma true id ]
END

VERNAC COMMAND EXTEND AddStepr
| [ "Declare" "Right" "Step" global(id) ] ->
    [ add_transitivity_lemma false id ]
END
