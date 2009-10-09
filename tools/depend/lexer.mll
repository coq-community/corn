(* A lexer for Coq files dependencies
 *
 * Copyright © 2004-2007 Lionel Elie Mamane <lionel@mamane.lu>
 *
 * To the maximum extent permitted by law, I abandon all my copyrights
 * on the interface (.mli) file generated from this file by the OCaml
 * ocamllex / compiler chain.
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 *
 *)

{
  open Parser;;
  open Types;;
  exception Eof;;
  let seen_eof = ref(false);;
  let lex_debug = false;;
  let lex_debug_print x = if lex_debug then print_string x;;
  let rmnewsuffix x = Filename.chop_suffix x ".new";;
}

let whitespace = [ ' ' '\t' ]
let separator = ':'
let basename = [ ^ ' ' '\t' ':' '\n' ]+
let eol = '\n'
let coqSource = basename ".v" as name
let coqBinary = (basename ".vo") as name ( ".new" ? )
let coqGlob   = (basename ".glob") as name ( ".new" ? )
let ocamlBinary =  basename ".cmo" as name

rule token = parse
  | whitespace+         { lex_debug_print "WS"; token lexbuf }
  | eol                 { lex_debug_print "EOL"; EOL }
  | separator+          { lex_debug_print "SEP"; Separator }
  | ocamlBinary         { lex_debug_print "OBIN: "; lex_debug_print name; Binary (OCamlBinaryFile name) }
  | coqBinary           { lex_debug_print "CBIN: "; lex_debug_print name; Binary (CoqBinaryFile name) }
  | coqGlob             { lex_debug_print "CGLB: "; lex_debug_print name; Binary (CoqGlobalFile name) }
  | coqSource           { lex_debug_print "CSRC: "; lex_debug_print name; Source (CoqSourceFile name) }
  | eof                 { lex_debug_print "EOF"; if !seen_eof then raise Eof
                                                            else (seen_eof := true; EOL ) }

