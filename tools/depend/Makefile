#  Makefile for my Coq files dependencies utilities
#
#  It is my opinion that this file is too trivial for any copyright to
#  hold on it. However, if you or your lawyer think different, then:
#
#  Copyright © 2004 Lionel Elie Mamane <lionel@mamane.lu>
#
#  This program is free software; you can redistribute it and/or
#  modify it under the terms of the GNU General Public License
#  as published by the Free Software Foundation; either version 2
#  of the License, or (at your option) any later version.
#
#  This program is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with this program; if not, write to the Free Software
#  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.

OCAMLFLAGS := -dtypes

all: full_depend

%.cmi: %.mli
	ocamlc $(OCAMLFLAGS) -c $<

%.cmx %.cmi: %.ml
	ocamlopt $(OCAMLFLAGS) -c $<

%.cmo %.cmi: %.ml
	ocamlc $(OCAMLFLAGS) -c $<

%.ml %.mli: %.mly
	ocamlyacc $<

%.ml %.mli: %.mll
	ocamllex $<

parser.cmi: types.cmi

parser.cmo: types.cmi

parser.cmx: types.cmi

common.cmi: types.cmi

common.cmo: types.cmi

common.cmx: types.cmi

lexer.cmo: parser.cmi types.cmi

lexer.cmx: parser.cmi types.cmi

full_depend.cmo: parser.cmi lexer.cmi types.cmi common.cmi

full_depend.cmx: parser.cmi lexer.cmi types.cmi common.cmi

full_depend.byte: types.cmo lexer.cmo parser.cmo common.cmo full_depend.cmo
	ocamlc $(OCAMLFLAGS) -o $@ $^

full_depend: types.cmx lexer.cmx parser.cmx common.cmx full_depend.cmx
	ocamlopt $(OCAMLFLAGS) -o $@ $^

clean:
	rm -f full_depend *.cm[oix] *.o {parser,lexer}.ml{i,} types.mli *.annot common.mli full_depend.mli *~ full_depend.byte
