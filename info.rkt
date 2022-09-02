#lang info
(define deps (list "base" "redex-lib" "scheme-lib" "scribble-lib"))
(define build-deps (list "racket-doc"
                         "redex-doc"
                         "redex-gui-lib" "sandbox-lib"))
(define scribblings (list (list "tutorial.scrbl")))
