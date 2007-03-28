/* A parser for Coq files dependencies
 *
 * Copyright © 2004 Lionel Elie Mamane <lionel@mamane.lu>
 *
 * To the maximum extent permitted by law, I abandon all my copyrights
 * on the interface (.mli) file generated from this file by the OCaml
 * yacc / compiler chain.
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
 */

%{
  open Types
%}
  %token <Types.file> Source
  %token <Types.file> Binary
  %token Separator
  %token EOL
  %start dep_spec
  %type <(string * Types.file list) option> dep_spec
  %start filename
  %type <Types.file> filename
%%
  dep_spec:
      BinarySequence Separator FilenameSequence EOL     { Some (coqBinaryName $1, $3) }
    | EOL                                               { None }
  ;

  BinarySequence:
      Binary                                            { $1 }
    | Binary BinarySequence                             { $1 }

  FilenameSequence:
                                                        { [] }
    | filename FilenameSequence                         { $1 :: $2 }
  ;

  filename:
      Source                                            { $1 }
    | Binary                                            { $1 }
  ;
