html:
	raco make tutorial.scrbl
	scribble \
	  ++xref-in setup/xref load-collections-xref \
	  --redirect-main http://docs.racket-lang.org/ \
	  --dest out/ \
	  +m tutorial.scrbl

pdf:
	raco make tutorial.scrbl
	scribble \
	  ++xref-in setup/xref load-collections-xref \
	  --redirect-main http://docs.racket-lang.org/ \
	  --dest out/ \
	  --pdf \
	  +m tutorial.scrbl

