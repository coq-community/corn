(* Common code for my for Coq files dependencies utilities
 * 
 * Copyright © 2004 Lionel Elie Mamane <lionel@mamane.lu>
 * 
 * To the maximum extent permitted by law, I abandon all my copyrights
 * on the interface (.mli) file generated from this file by the OCaml
 * compiler.
 * 
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
 * 02111-1307, USA.
 * 
 *)

let table = (Hashtbl.create 120);;

(* Read the dependencies file *)
let read_depends input = 
  try
    let lexbuf = Lexing.from_channel input in
      while true do
	match Parser.dep_spec Lexer.token lexbuf with
	  | None -> ()
	  | Some (file, dep) -> Hashtbl.replace table file dep
      done
  with Lexer.Eof ->
    ();;
