#!/usr/bin/env sh

# Produce files Make and Makefile

cp -f Make.in Make

DIRECTORIES="algebra complex coq_reals fta ftc liouville logic metrics model raster reals tactics transc order metric2 stdlib_omissions util classes ode write_image"

find $DIRECTORIES -name "*.v" >>Make

${COQBIN}coq_makefile -f Make -o Makefile
