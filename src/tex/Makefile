# -*- tab-width:4 ; indent-tabs-mode:t -*-

def:
	@echo "please use:"
	@echo "  make manual      to compile the user manual"
	@echo "  make devguide    to compile the developers guide"


manual_sources=fibonacci-all.pvl


manual: Makefile $(manual_sources)
	TEXINPUTS=$(TEXINPUTS):../../examples// pdflatex manual
#	bibtex manual
	TEXINPUTS=$(TEXINPUTS):../../examples// pdflatex manual

devguide:
	TEXINPUTS=$(TEXINPUTS):../../examples// pdflatex devguide
	TEXINPUTS=$(TEXINPUTS):../../examples// pdflatex devguide


fibonacci_pvl=../../examples/manual/fibonacci.pvl



fibonacci-%.pvl: extract $(fibonacci_pvl)
	echo $* $@
	./extract -v fragment=$* $(fibonacci_pvl) > $@

clean::
	rm -f fibonacci-*.pvl


