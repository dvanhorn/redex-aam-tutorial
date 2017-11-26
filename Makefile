html:
	raco make tutorial.scrbl
	scribble \
	  ++xref-in setup/xref load-collections-xref \
	  --redirect-main http://docs.racket-lang.org/ \
	  --dest out/ \
	  --dest-name index \
	  +m tutorial.scrbl

pdf:
	raco make tutorial.scrbl
	scribble \
	  ++xref-in setup/xref load-collections-xref \
	  --redirect-main http://docs.racket-lang.org/ \
	  --dest out/ \
	  --xelatex \
	  +m tutorial.scrbl

test:
	raco test -c redex-aam-tutorial

test-ci:
	raco test --drdr --timeout +inf.0 -j 4 --package redex-aam-tutorial

install:
	raco pkg install ../redex-aam-tutorial
