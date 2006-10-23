TEXFILES=\
	CSetoids.tex \
	CGroups.tex \
	CRings.tex \
	CIntDomains.tex \
	CFields.tex \
	CVectorSpace.tex \
	LinearAlgebra.tex \
	CReals.tex \
	CPolynomials.tex \
	IVT.tex \
	CComplex.tex \
	NRootCC.tex \
	FTAreg.tex \
	FTA.tex \
	header.tex bibliography.tex skel.tex

ps: skel.ps
dvi: skel.dvi

skel.dvi: ${TEXFILES} skel.aux
	latex skel.tex

skel.aux:
	latex skel.tex

skel.ps: skel.dvi
	dvips -f < skel.dvi > skel.ps

clean:
	rm -f skel.aux skel.log skel.dvi skel.ps
