(* Types for my parser / lexer for Coq files dependencies
 *
 * It is my opinion that this file is too short and trivial for any
 * copyright to hold on it. However, if you or your lawyer think
 * different, then:
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

type file = | OCamlBinaryFile of string
	    | CoqSourceFile of string
	    | CoqBinaryFile of string;;

exception Wrong_file_type of file;;

let fileName = function
  | OCamlBinaryFile n -> n
  | CoqSourceFile n -> n
  | CoqBinaryFile n -> n;;

let coqBinaryName = function
  | CoqBinaryFile name -> name
  | f -> raise (Wrong_file_type f);;

let coqSourceName = function
  | CoqSourceFile name -> name
  | f -> raise (Wrong_file_type f);;
