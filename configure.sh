#!/usr/bin/env sh
cp -f Make.in Make
find algebra complex coq_reals fta ftc logic metrics model raster reals tactics transc order metric2 stdlib_omissions util classes ode -name "*.v" |grep -v tactics/Opaque_algebra.v >>Make
${COQBIN}coq_makefile -f Make -o Makefile
