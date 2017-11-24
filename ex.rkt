#lang racket/base

(require scribble/manual
         scribble/core
         scribble/decode
         "counter.rkt")

(provide exercise Exref exref eop)

(define eop "■")

(define (exercise tag . content)
  (nested-flow
    (make-style #f '()) ;; #f ==> blockquote? 
    (decode-flow
      (append
	(list (exercise-target tag) ". ")
	content
	(list " " eop)))))

(define exercises (new-counter "exercise"))

(define (exercise-target tag)
  (counter-target exercises tag (bold "Exercise")))

(define (Exref tag)
  (make-element #f (list (counter-ref exercises tag "Exercise"))))

(define (exref tag [loud #f])
  (if loud
      (make-element #f (list (silent-counter-ref exercises tag loud)))
      (make-element #f (list (counter-ref exercises tag "exercise")))))
