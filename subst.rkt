#lang racket
(require redex/reduction-semantics)
(provide (all-defined-out))
(define-language L
  (T num)
  (X (variable-except λ μ if0 : num)))
  
(define-metafunction L
  subst : (X any) ... any -> any 
  [(subst (X_1 any_1) (X_2 any_2) ... any_3)
   (subst-1 X_1 any_1 (subst (X_2 any_2) ... any_3))]
  [(subst any_3) any_3])

(define-metafunction L
  subst-1 : X any any -> any 
  ;; 1. x_1 bound, so don't continue in λ body 
  [(subst-1 X_1 any_1 (λ ([X_2 : T_2] ... [X_1 : T_1] [X_3 : T_3] ...) any_2))
   (λ ([X_2 : T_2] ... [X_1 : T_1] [X_3 : T_3] ...) any_2)
   (side-condition (not (member (term X_1) (term (X_2 ...)))))]
  ;; or μ
  [(subst-1 X any_1 (μ (X : T) any_2))
   (μ (X : T) any_2)]
  
  ;; 2. general purpose capture avoiding case 
  [(subst-1 X_1 any_1 (λ ([X_2 : T_2] ...) any_2)) 
   (λ ([X_new : T_2] ...) (subst-1 X_1 any_1 (subst-vars (X_2 X_new) ... any_2)))
   (where (X_new ...) ,(variables-not-in (term (X_1 any_1 any_2)) (term (X_2 ...))))]
  ;; and μ
  [(subst-1 X_1 any_1 (μ (X_2 : T) any_2))
   (μ (X_new : T) (subst-1 X_1 any_1 (subst-vars (X_2 X_new) any_2)))
   (where (X_new) ,(variables-not-in (term (X_1 any_1 any_2)) (term (X_2))))]
   
  ;; 3. replace x_1 with e_1 
  [(subst-1 X_1 any_1 X_1) any_1]
  ;; 4. x_1 and x_2 are different, so don't replace [(subst x_1 any_1 x_2) x_2] 
  ;; the last cases cover all other expressions
  [(subst-1 X_1 any_1 (any_2 ...)) ((subst-1 X_1 any_1 any_2) ...)] 
  [(subst-1 X_1 any_1 any_2) any_2])

(define-metafunction L 
  subst-vars : (X any) ... any -> any
  [(subst-vars (X_1 any_1) X_1) any_1] 
  [(subst-vars (X_1 any_1) (any_2 ...)) ((subst-vars (X_1 any_1) any_2) ...)]
  [(subst-vars (X_1 any_1) any_2) any_2]
  [(subst-vars (X_1 any_1) (X_2 any_2) ... any_3) (subst-vars (X_1 any_1) (subst-vars (X_2 any_2) ... any_3))] 
  [(subst-vars any) any])
  

(define-metafunction L
  lookup : (any ...) any -> any
  [(lookup ((any_k any_v) any ...) any_k) any_v]
  [(lookup (any_0 any ...) any_k)
   (lookup (any ...) any_k)])

(define-metafunction L
  :: : (any ...) any ... -> any
  [(:: (any_1 ...) any_0 ...)
   (any_0 ... any_1 ...)])

   