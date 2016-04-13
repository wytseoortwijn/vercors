# -*- tab-width:4 ; indent-tabs-mode:t -*-

def:
	@echo "please use:"
	@echo "  make manual      to compile the user manual"
	@echo "  make devguide    to compile the developers guide"

manual:
	TEXINPUTS=$(TEXINPUTS):../../examples// pdflatex manual
#	bibtex manual
	TEXINPUTS=$(TEXINPUTS):../../examples// pdflatex manual

devguide:
	TEXINPUTS=$(TEXINPUTS):../../examples// pdflatex devguide
	TEXINPUTS=$(TEXINPUTS):../../examples// pdflatex devguide


