#lang racket

(require scribble/manual
         scribble/core
         scribble/decode
	 2htdp/image
         "counter.rkt")

(provide exercise Exref exref eop)

(define eop (rectangle 3 10 'solid 'black)#;(image/plain "Images/qed.png"))

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
