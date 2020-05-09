#!/usr/bin/env sh

# Produce files Make and Makefile

cp -f Make.in Make

COQ_VERSION_LINE=$(coqc --version | head -1)
COQ_VERSION=`echo $COQ_VERSION_LINE | sed 's/The Coq Proof Assistant, version 8\.\([^ +]*\).*/\1/'`
DIRECTORIES="algebra complex coq_reals fta ftc liouville logic metrics model raster reals tactics transc order metric2 stdlib_omissions util classes ode"

# Include constructive measure theory on version 8.12 and after
if [ $COQ_VERSION -gt 12 ] ;
then
    find $DIRECTORIES -name "*.v" >>Make
else
    find $DIRECTORIES -name "*.v" | grep -v "stdlib/" >>Make
fi

${COQBIN}coq_makefile -f Make -o Makefile
