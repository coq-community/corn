(* full_depend: Computes the full (direct and indirect) dependencies
 *              of a binary from partial dependencies (direct only)
 *
 * Copyright © 2004 Lionel Elie Mamane <lionel@mamane.lu>
 *
 * To the maximum extent permitted by law, I abandon all my copyrights
 * on the interface (.mli) file generated from this file by the OCaml
 * compiler.
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

open Types;;
open Common;;

if (Array.length Sys.argv) < 3 then
  begin
    print_string "full_depend - Computes the full dependency list of a binary"; print_newline();
    print_string "Copyright 2004, Lionel Elie Mamane <lionel@mamane.lu>"; print_newline();
    print_string "full_depend comes with ABSOLUTELY NO WARRANTY.\n";
    print_string "This is free software, and you are welcome to redistribute it\n";
    print_string "under certain conditions. See the file COPYING for details.\n";
    print_newline();
    print_string "Usage: "; print_string Sys.argv.(0); print_string " depend_file binary"; print_newline();
    print_newline();
    print_string "depend_file is the file containing the dependencies. Use \"-\" for stdin."; print_newline();
    print_string "binary is the file you want to compute the full dependencies off"; print_newline();
    exit 0;
  end;;


let file = if Sys.argv.(1) = "-" then stdin else (open_in Sys.argv.(1)) in
  read_depends file;
  close_in file;;

(* Similar to List.merge
 * Assumes that l1 l2 are sorted and don't contain duplicates
 * Then, merges l1 and l2 into a sorted list without duplicate
 *)
let rec unique_merge cmp =
  let rec aux l1 l2 = match l1, l2 with
    | _, [] -> l1
    | [], _ -> l2
    | h1::t1, h2::t2 -> let ord = (cmp h1 h2) in
	if (ord < 0) then h1::(aux t1 l2)
	else if ord > 0 then h2::(aux l1 t2)
	else (* ord = 0 *) h1::(aux t1 t2)
  in aux;;

let umerge = unique_merge compare;;

let rec full_depend filename =
  List.fold_left
    (fun l fname ->
       umerge l (match fname with
		   | CoqSourceFile n -> [n]
		   | CoqBinaryFile n -> full_depend n
		   | OCamlBinaryFile n -> [(Filename.chop_extension n) ^ ".ml"]))
    []
    (Hashtbl.find table filename);;

List.fold_left
  (fun x y -> print_string y; print_newline())
  ()
  (Array.fold_left
     (fun x y -> umerge x (full_depend y))
     []
     (Array.sub Sys.argv 2 ((-) (Array.length Sys.argv) 2)));;
