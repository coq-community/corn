(*i camlp4use: "pa_extend.cmo" i*)
(*i camlp4deps: "parsing/grammar.cma" i*)

open Names
open Pp
open Pcoq
open Genarg
open Term
open Topconstr
open Libnames
open Tactics
open Tacticals
open Termops
open Namegen
open Recordops
open Tacmach
open Coqlib
open Glob_term
open Util
open Evd
open Extend
open Goptions
open Tacexpr
open Tacinterp
open Pretyping.Default
open Constr
open Tactic
open Extraargs
open Ppconstr
open Printer

let mydump t = 
  let env = Global.env () in
  prerr_endline "dumping to plot.pgm";
  let buf = Buffer.create 100000 in
  let fmt = Format.formatter_of_buffer buf in
  let c = constr_of_global (Constrintern.intern_reference t) in
  ppnl_with fmt (pr_constr (Reductionops.nf_betadeltaiota env Evd.empty c));
  pp_flush_with fmt ();
  let str = Buffer.contents buf in 
  let str = Str.global_replace (Str.regexp "(") "P2\n" str in
  let str = Str.global_replace (Str.regexp "[),#]") " " str in
  let oc = open_out "plot.pgm" in
  output_string oc str;
  close_out oc
;;

VERNAC COMMAND EXTEND DumpArray
[ "Dump" global(a) ] -> [ mydump a ]
END
