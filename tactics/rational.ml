
open Util
open Pp
open Printer
open Term
open Names
open Nameops
open Libnames
open Closure
open Reductionops
open Tactics
open Tacmach
open Proof_trees
open Environ
open Declarations
open Inductiveops

let coq_modules = Coqlib.init_modules @ Coqlib.zarith_base_modules

let coq_constant s = 
   Coqlib.gen_constant_in_modules "CoRN" coq_modules s

let constant s = 
  try
	constr_of_reference (Nametab.absolute_reference (path_of_string s))
  with Not_found ->
    error (Printf.sprintf "constant %s" s)
    | Anomaly _ ->
	error (Printf.sprintf "constant %s" s)

let constant_algebra s = constant ("CoRN.algebra." ^ s)
let constant_tactics s = constant ("CoRN.tactics." ^ s)

type xexpr =
    X_var of int
  | X_unop of int * xexpr
  | X_binop of int * xexpr * xexpr
  | X_part of int * xexpr * constr
  | X_int of int
  | X_plus of xexpr * xexpr
  | X_mult of xexpr * xexpr
  | X_div of xexpr * xexpr * constr
  | X_zero
  | X_one
  | X_nat of int
  | X_inv of xexpr
  | X_minus of xexpr * xexpr
  | X_power of xexpr * int

let hd_app c = fst (destApplication c)

let args_app c = snd (destApplication c)

let first_arg c = (args_app c).(0)
let third_arg c = (args_app c).(2)
let sixth_arg c = (args_app c).(5)

let xinterp g c = sixth_arg (pf_type_of g c)

let mk_existential env = Evarutil.new_evar_in_sign env

let mk_lambda n t c = mkLambda (n,t,c)
let mk_cast c t = mkCast (c,t)
let mk_case ci a b c = mkCase (ci,a,b,c)

let pf_nf_betadeltaiota = pf_reduce nf_betadeltaiota
let pf_cbv_betadeltaiota = pf_reduce Tacred.cbv_betadeltaiota

let pf_whd_all_but sp =
  let flags =
    RedFlags.red_sub
      (RedFlags.red_add_transparent betadeltaiota (Conv_oracle.freeze()))
      (RedFlags.fCONST sp) in
  pf_reduce (clos_norm_flags flags) 

let xrational verbose g a =

  let cr_crr = constant_algebra "CRings.cr_crr"
  and cf_crr = constant_algebra "CFields.cf_crr" in

  let the_csetoid = a.(0) in
  let the_csemigroup = first_arg the_csetoid in
  let the_cmonoid = first_arg the_csemigroup in
  let the_cgroup = first_arg the_cmonoid in
  let the_cabgroup = first_arg the_cgroup in

  let the_cstructure,the_suffix,the_file =
    if isApp the_cabgroup && hd_app the_cabgroup = cr_crr then
      let the_cring = first_arg the_cabgroup in
	if isApp the_cring && hd_app the_cring = cf_crr then
	  let the_cfield = first_arg the_cring in
            the_cfield,"F","FieldReflection"
	else the_cring,"R","RingReflection"
    else the_cabgroup,"G","GroupReflection" in

  let nat_nat = coq_constant "nat"
  and nat_O = coq_constant "O"
  and nat_S = coq_constant "S"
  and refl_equal = coq_constant "refl_equal"
  and bool_bool = coq_constant "bool"
  and bool_true = coq_constant "true"
  and pos_xI = coq_constant "xI"
  and pos_xO = coq_constant "xO"
  and pos_xH = coq_constant "xH"
  and int_ZERO = coq_constant "ZERO"
  and int_POS = coq_constant "POS"
  and int_NEG = coq_constant "NEG"

  and cs_eq = constant_algebra "CSetoids.cs_eq" in

  let xexpr_constant s =
    try constant_tactics (the_file ^ ".xexpr" ^ the_suffix ^ "_" ^ s)
    with _ -> nat_O in
  let xexpr_var = xexpr_constant "var"
  and xexpr_unop = xexpr_constant "unop"
  and xexpr_binop = xexpr_constant "binop"
  and xexpr_part = xexpr_constant "part"
  and xexpr_int = xexpr_constant "int"
  and xexpr_plus = xexpr_constant "plus"
  and xexpr_mult = xexpr_constant "mult"
  and xexpr_div = xexpr_constant "div"
  and xexpr_zero = xexpr_constant "zero"
  and xexpr_one = xexpr_constant "one"
  and xexpr_nat = xexpr_constant "nat"
  and xexpr_inv = xexpr_constant "inv"
  and xexpr_minus = xexpr_constant "minus"
  and xexpr_power = xexpr_constant "power" in

  let the_file_constant s = constant_tactics
    (the_file ^ "." ^ s ^ the_suffix) in
  let xforget = the_file_constant "xforget"
  and tactic_lemma = the_file_constant "Tactic_lemma" in

  let norm = constant_tactics ("AlgReflection.Norm" ^ the_suffix) in

  let csf_fun = constant_algebra "CSetoids.csf_fun"
  and csbf_fun = constant_algebra "CSetoids.csbf_fun"
  and csg_unit = constant_algebra "CMonoids.cm_unit"
  and cr_one = constant_algebra "CRings.cr_one"
  and nring = constant_algebra "CRings.nring"
  and zring = constant_algebra "CRings.zring"
  and csg_op = constant_algebra "CSemiGroups.csg_op"
  and cg_inv = constant_algebra "CGroups.cg_inv"
  and cg_minus = constant_algebra "CGroups.cg_minus"
  and cr_mult = constant_algebra "CRings.cr_mult"
  and cf_div = constant_algebra "CFields.cf_div"
  and nexp_op = constant_algebra "CRings.nexp_op"
  and expr_minus = constant_tactics "AlgReflection.expr_minus"
  and pfpfun = constant_algebra "CSetoidFun.pfpfun"
  and id_un_op = constant_algebra "CSetoids.id_un_op"
  and cs_binproj1 = constant_algebra "CSetoidFun.cs_binproj1"
  and fid = constant_algebra "CSetoidFun.Fid"
  and csetoid_un_op = constant_algebra "CSetoids.CSetoid_un_op"
  and csetoid_bin_op = constant_algebra "CSetoids.CSetoid_bin_op"
  and partFunct = constant_algebra "CSetoidFun.PartFunct"

  in

  let ind_of_ref = function 
    | IndRef (kn,i) -> (kn,i)
    | _ -> anomaly "IndRef expected" in

  let nat_info = 
    let nat = ind_of_ref Coqlib.glob_nat in
    make_default_case_info (Global.env()) RegularStyle nat
  in
    
  let rec evalnat n =
    if eq_constr n nat_O then 0
    else if isApp n & eq_constr (hd_app n) nat_S then
      let a = args_app n in
	if Array.length a > 0 then (evalnat a.(0)) + 1
	else raise (Failure "evalnat")
    else raise (Failure "evalnat") in

  let rec evalpos n =
    if eq_constr n pos_xH then 1
    else if isApp n then
      let f = hd_app n
      and a = args_app n in
	if Array.length a > 0 then
	  if eq_constr f pos_xI then 2 * (evalpos a.(0)) + 1
	  else if eq_constr f pos_xO then 2 * (evalpos a.(0))
	  else raise (Failure "evalint")
	else raise (Failure "evalint")
    else raise (Failure "evalint") in

  let rec evalint n =
    if eq_constr n int_ZERO then 0
    else if isApp n then
      let f = hd_app n
      and a = args_app n in
	if Array.length a > 0 then
	  if eq_constr f int_POS then evalpos a.(0)
	  else if eq_constr f int_NEG then -(evalpos a.(0))
	  else raise (Failure "evalint")
	else raise (Failure "evalint")
    else raise (Failure "evalint") in
    
  let rec envindex : constr * constr list -> int * constr list =
    function (x,e) ->
      match e with
	  [] -> (0,[x])
	| y::f ->
	    if eq_constr x y then (0, e) else
	      let (i,g) = envindex (x,f) in
		(i + 1, y::g) in

  let liftV : constr * constr list * constr list * constr list * constr list -> xexpr * constr list * constr list * constr list * constr list =
    function (x,eV,eU,eB,eP) -> let (i,fV) = envindex (x,eV) in (X_var i, fV,eU,eB,eP) in

  let rec
    liftU : constr * constr * constr list * constr list * constr list * constr list -> xexpr * constr list * constr list * constr list * constr list =
    function (f,x,eV,eU,eB,eP) ->
      let (x',fV,fU,fB,fP) = lift (x,eV,eU,eB,eP) in
        let (i,gU) = envindex (f,fU) in (X_unop(i,x'),fV,gU,fB,fP) and

    liftB : constr * constr * constr * constr list * constr list * constr list * constr list -> xexpr * constr list * constr list * constr list * constr list =
    function (f,x,y,eV,eU,eB,eP) ->
      let (x',fV,fU,fB,fP) = lift (x,eV,eU,eB,eP) in
      let (y',gV,gU,gB,gP) = lift (y,fV,fU,fB,fP) in
        let (i,hB) = envindex (f,gB) in (X_binop(i,x',y'),gV,gU,hB,gP) and

    liftP : constr * constr * constr * constr list * constr list * constr list * constr list -> xexpr * constr list * constr list * constr list * constr list =
    function (x,y,h,eV,eU,eB,eP) -> let (z,fV,fU,fB,fP) = lift (y,eV,eU,eB,eP) in 
      let (i,gP) = envindex (x,fP) in (X_part(i,z,h), fV,fU,fB,gP) and

    lift : constr * constr list * constr list * constr list * constr list -> xexpr * constr list * constr list * constr list * constr list  =
    function (x0,eV,eU,eB,eP) ->
      let x = strip_outer_cast x0 in
      if isApp x then
	let f = hd_app x
	and a = args_app x in
	  if eq_constr f csg_unit then (X_zero, eV,eU,eB,eP)
	  else if eq_constr f cr_one then (X_one, eV,eU,eB,eP)
	  else if eq_constr f nring & Array.length a > 1 then
	    try (X_nat(evalnat a.(1)), eV,eU,eB,eP)
	    with Failure "evalnat" -> liftV (x,eV,eU,eB,eP)
	  else if eq_constr f zring & Array.length a > 1 then
	    try (X_int(evalint a.(1)), eV,eU,eB,eP)
	    with Failure "evalint" -> liftV (x,eV,eU,eB,eP)
          else if eq_constr f pfpfun & Array.length a > 3 then
            liftP(a.(1),a.(2),a.(3),eV,eU,eB,eP)
	  else if eq_constr f csbf_fun then
	    if Array.length a > 5 & eq_constr a.(0) a.(2) & eq_constr a.(1) a.(2)
	    then
              if isApp a.(3) then
                 let g = hd_app a.(3) in
                 if eq_constr g csg_op
		 then
		   let (t1,e1V,e1U,e1B,e1P) = lift (a.(4),eV,eU,eB,eP) in
		   let (t2,e2V,e2U,e2B,e2P) = lift (a.(5),e1V,e1U,e1B,e1P) in
		   (X_plus(t1,t2), e2V,e2U,e2B,e2P)
		 else
                 if eq_constr g cr_mult
	         then
		   let (t1,e1V,e1U,e1B,e1P) = lift (a.(4),eV,eU,eB,eP) in
		   let (t2,e2V,e2U,e2B,e2P) = lift (a.(5),e1V,e1U,e1B,e1P) in
		     (X_mult(t1,t2), e2V,e2U,e2B,e2P)
		 else liftB(a.(3),a.(4),a.(5),eV,eU,eB,eP)
              else liftB(a.(3),a.(4),a.(5),eV,eU,eB,eP)
            else liftV (x,eV,eU,eB,eP)
	  else if eq_constr f csf_fun then
	    if Array.length a > 3 & eq_constr a.(0) a.(1) then
              if isApp a.(2) then
		let g = hd_app a.(2) in
		let b = args_app a.(2) in
		  if eq_constr g cg_inv then
		    let (t1,e1V,e1U,e1B,e1P) = lift (a.(3),eV,eU,eB,eP) in
		      (X_inv(t1), e1V,e1U,e1B,e1P)
		  else
                  if eq_constr g nexp_op & Array.length b > 1 then
		    try
		      let n = evalnat b.(1) in
		      let (t1,e1V,e1U,e1B,e1P) = lift (a.(3),eV,eU,eB,eP) in
			(X_power(t1,n), e1V,e1U,e1B,e1P)
		    with Failure "evalnat" -> liftV (x,eV,eU,eB,eP)
		  else liftU (a.(2),a.(3),eV,eU,eB,eP)
	      else liftU (a.(2),a.(3),eV,eU,eB,eP)
	    else liftV (x,eV,eU,eB,eP)
	  else if eq_constr f cg_minus then
	    if Array.length a > 2 then
	      let (t1,e1V,e1U,e1B,e1P) = lift (a.(1),eV,eU,eB,eP) in
	      let (t2,e2V,e2U,e2B,e2P) = lift (a.(2),e1V,e1U,e1B,e1P) in
		(X_minus(t1,t2), e2V,e2U,e2B,e2P)
	    else liftV (x,eV,eU,eB,eP)
          else if eq_constr f cf_div then
            if Array.length a > 3 then
              let (t1,e1V,e1U,e1B,e1P) = lift (a.(1),eV,eU,eB,eP) in
              let (t2,e2V,e2U,e2B,e2P) = lift (a.(2),e1V,e1U,e1B,e1P) in
                (X_div(t1,t2,a.(3)), e2V,e2U,e2B,e2P)
            else liftV (x,eV,eU,eB,eP)
	  else if isApp f then
	    lift ((collapse_appl x), eV,eU,eB,eP)
	  else liftV (x,eV,eU,eB,eP)
      else liftV (x,eV,eU,eB,eP) in

  let rec natconstr i =
    if i > 0 then mkApp(nat_S, [| natconstr (i - 1) |]) else nat_O in

  let rec posconstr k =
    if k == 1 then pos_xH else
      let l = k mod 2 in
	mkApp((if l == 0 then pos_xO else pos_xI), [| posconstr (k / 2) |]) in

  let rec intconstr k =
    if k == 0 then int_ZERO else
    if k > 0 then mkApp(int_POS, [| posconstr k |]) else
      mkApp(int_NEG, [| posconstr (- k) |]) in
    
  let rec xexprconstr t rhoV rhoU rhoB rhoP =
    match t with
	X_var i -> mkApp(xexpr_var, [| the_cstructure; rhoV; rhoU; rhoB; rhoP; natconstr i |])
      | X_unop (i,t1) ->
          let c1 = xexprconstr t1 rhoV rhoU rhoB rhoP in
          mkApp(xexpr_unop, [| the_cstructure; rhoV; rhoU; rhoB; rhoP; xinterp g c1; natconstr i; c1 |])
      | X_binop (i,t1,t2) ->
          let c1 = xexprconstr t1 rhoV rhoU rhoB rhoP in
          let c2 = xexprconstr t2 rhoV rhoU rhoB rhoP in
          mkApp(xexpr_binop, [| the_cstructure; rhoV; rhoU; rhoB; rhoP; xinterp g c1; xinterp g c2; natconstr i; c1; c2 |])
      | X_part (i,t,h) -> 
          let c = xexprconstr t rhoV rhoU rhoB rhoP in
          mkApp(xexpr_part, [| the_cstructure; rhoV; rhoU; rhoB; rhoP; xinterp g c; natconstr i; c; h |])
      | X_int i -> mkApp(xexpr_int, [| the_cstructure; rhoV; rhoU; rhoB; rhoP; intconstr i |])
      | X_plus (t1,t2) ->
	  let c1 = xexprconstr t1 rhoV rhoU rhoB rhoP
	  and c2 = xexprconstr t2 rhoV rhoU rhoB rhoP in
	  mkApp(xexpr_plus, [| the_cstructure; rhoV; rhoU; rhoB; rhoP;
	                       xinterp g c1; xinterp g c2; c1; c2 |])
      | X_mult (t1,t2) ->
	  let c1 = xexprconstr t1 rhoV rhoU rhoB rhoP
	  and c2 = xexprconstr t2 rhoV rhoU rhoB rhoP in
	  mkApp(xexpr_mult, [| the_cstructure; rhoV; rhoU; rhoB; rhoP;
		               xinterp g c1; xinterp g c2; c1; c2 |])
      | X_div (t1,t2,nz) ->
	  let c1 = xexprconstr t1 rhoV rhoU rhoB rhoP
	  and c2 = xexprconstr t2 rhoV rhoU rhoB rhoP in
	  mkApp(xexpr_div, [| the_cstructure; rhoV; rhoU; rhoB; rhoP;
		              xinterp g c1; xinterp g c2; c1; c2; nz |])
      | X_zero ->
	  mkApp(xexpr_zero, [| the_cstructure; rhoV; rhoU; rhoB; rhoP |])
      | X_one ->
	  mkApp(xexpr_one, [| the_cstructure; rhoV; rhoU; rhoB; rhoP |])
      | X_nat i ->
	  mkApp(xexpr_nat, [| the_cstructure; rhoV; rhoU; rhoB; rhoP; natconstr i |])
      | X_inv (t1) ->
	  let c1 = xexprconstr t1 rhoV rhoU rhoB rhoP in
	  mkApp(xexpr_inv, [| the_cstructure; rhoV; rhoU; rhoB; rhoP; xinterp g c1; c1 |])
      | X_minus (t1,t2) ->
	  let c1 = xexprconstr t1 rhoV rhoU rhoB rhoP
	  and c2 = xexprconstr t2 rhoV rhoU rhoB rhoP in
	  mkApp(xexpr_minus, [| the_cstructure; rhoV; rhoU; rhoB; rhoP;
		                xinterp g c1; xinterp g c2; c1; c2 |])
      | X_power (t1,n) ->
	  let c1 = xexprconstr t1 rhoV rhoU rhoB rhoP in
	  mkApp(xexpr_power, [| the_cstructure; rhoV; rhoU; rhoB; rhoP;
		                xinterp g c1; c1; natconstr n |]) in
    
  let rec valconstr e ta =
    match e with
	[] -> mk_lambda Anonymous nat_nat
	    (mk_cast (mkApp(csg_unit, [|the_cmonoid |])) ta)
      | [c] -> mk_lambda Anonymous nat_nat c
      | c::f -> mk_lambda (Name (id_of_string "n")) nat_nat
	    (mk_case nat_info ta (mkRel 1) [| c; valconstr f ta |]) in
    
  let rec unconstr e ta =
    match e with
	[] -> mk_lambda Anonymous nat_nat
	    (mk_cast (mkApp(id_un_op, [|the_csetoid |])) ta)
      | [c] -> mk_lambda Anonymous nat_nat c
      | c::f -> mk_lambda (Name (id_of_string "n")) nat_nat
	    (mk_case nat_info ta (mkRel 1) [| c; unconstr f ta |]) in
    
  let rec binconstr e ta =
    match e with
	[] -> mk_lambda Anonymous nat_nat
	    (mk_cast (mkApp(cs_binproj1, [|the_csetoid |])) ta)
      | [c] -> mk_lambda Anonymous nat_nat c
      | c::f -> mk_lambda (Name (id_of_string "n")) nat_nat
	    (mk_case nat_info ta (mkRel 1) [| c; binconstr f ta |]) in
    
  let rec funconstr e ta =
    match e with
	[] -> mk_lambda Anonymous nat_nat
	    (mk_cast (mkApp(fid, [|the_csetoid |])) ta)
      | [c] -> mk_lambda Anonymous nat_nat c
      | c::f -> mk_lambda (Name (id_of_string "n")) nat_nat
	    (mk_case nat_info ta (mkRel 1) [| c; funconstr f ta |]) in

  let rec printval i e =
    match e with
	[] -> ()
      | c::f ->
	  msgnl (str "(" ++ int i ++ str ") -> " ++ prterm c);
	  printval (i + 1) f in

  let report g fV fU fB fP a xleft xright rhoV rhoU rhoB rhoP =
    (let left =
       pf_nf_betadeltaiota g
	 (mkApp(xforget, [| the_cstructure; rhoV; rhoU; rhoB; rhoP; xinterp g xleft; xleft |]))
     and right =
       pf_nf_betadeltaiota g
	 (mkApp(xforget, [| the_cstructure; rhoV; rhoU; rhoB; rhoP; xinterp g xright; xright |]))
     in
     let nleft = 
       pf_cbv_betadeltaiota g (mkApp(norm, [| left |]))
     and nright = 
       pf_cbv_betadeltaiota g (mkApp(norm, [| right |]))
     in
       msgnl (mt ()); printval 0 fV; msgnl (mt ());
       msgnl (mt ()); printval 0 fU; msgnl (mt ());
       msgnl (mt ()); printval 0 fB; msgnl (mt ());
       msgnl (mt ()); printval 0 fP; msgnl (mt ());
       msgnl (prterm a.(1));
       msgnl ( prterm left );
       msgnl ( prterm nleft ++ fnl ());
       msgnl ( prterm a.(2) );
       msgnl ( prterm right );
       msgnl ( prterm nright ++ fnl ());
       if the_suffix = "F" then
	 let difference =
	   (pf_cbv_betadeltaiota g
	      (mkApp(norm, [| mkApp(expr_minus, [| left; right |]) |]))) in
	   msgnl ( prterm difference ++ fnl ())
       else ())
  in
 
  let ta = pf_type_of g a.(1) in
  let fleft = a.(1) and fright = a.(2) in
  let (l,eV,eU,eB,eP) = lift (fleft,[],[],[],[]) in
  let (r,fV,fU,fB,fP) = lift (fright,eV,eU,eB,eP) in
  let rhoV = valconstr fV ta in
  let rhoU = unconstr fU (mkApp(csetoid_un_op, [|the_csetoid|])) in
  let rhoB = binconstr fB (mkApp(csetoid_bin_op, [|the_csetoid|])) in
  let rhoP = funconstr fP (mkApp(partFunct, [|the_csetoid|])) in
  let xleft = xexprconstr l rhoV rhoU rhoB rhoP
  and xright = xexprconstr r rhoV rhoU rhoB rhoP in
    if verbose then
      report g fV fU fB fP a xleft xright rhoV rhoU rhoB rhoP;
    let term =
      mkApp(tactic_lemma,
        [| the_cstructure; rhoV; rhoU; rhoB; rhoP; fleft; fright; xleft; xright;
           mkApp(refl_equal, [| bool_bool; bool_true |]) |])
    in
	let result = 
	  try 
	    exact_check term g 
	  with e when Logic.catchable_exception e -> error "cannot establish equality"
	in
	if verbose then msgnl (str "end Rational");
	result

	    
let hrational verbose g =

  let cs_eq = constant_algebra "CSetoids.cs_eq" in

  let c = strip_outer_cast (pf_concl g) in
    if isApp c & eq_constr (hd_app c) cs_eq then
      let a = args_app c in
	if Array.length a > 2 then
	  xrational verbose g a
	else error "not an [=] equation"
    else error "not an [=] equation"
      
let hrational1 verbose g =
  if verbose then msgnl (str "begin Rational");
  hrational verbose g
      
TACTIC EXTEND Rational
| ["Rational"] -> [ hrational1 false ]
END

TACTIC EXTEND RationalVerbose
| ["Rational" "Verbose"] -> [ hrational1 true ]
END
