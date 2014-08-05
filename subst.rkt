#lang racket
(require redex/reduction-semantics)
(provide (all-defined-out))

(define-language L
  (T any)
  (M any)
  (X (variable-except λ μ if0 : num)))
  
(define-metafunction L
  subst : (X M) ... M -> M
  [(subst (X_1 M_1) (X_2 M_2) ... M_3)
   (subst-1 X_1 M_1 (subst (X_2 M_2) ... M_3))]
  [(subst M_3) M_3])

(define-metafunction L
  subst-1 : X M M -> M
  ;; 1. X_1 bound, so don't continue in λ body
  [(subst-1 X_1 M_1 (λ ([X_2 : T_2] ... [X_1 : T_1] [X_3 : T_3] ...) M_2))
   (λ ([X_2 : T_2] ... [X_1 : T_1] [X_3 : T_3] ...) M_2)
   (side-condition (not (member (term X_1) (term (X_2 ...)))))]
  ;; or μ
  [(subst-1 X M_1 (μ (X : T) M_2))
   (μ (X : T) M_2)]
  
  ;; 2. general purpose capture avoiding case
  [(subst-1 X_1 M_1 (λ ([X_2 : T_2] ...) M_2)) 
   (λ ([X_new : T_2] ...) (subst-1 X_1 M_1 (subst-vars (X_2 X_new) ... M_2)))
   (where (X_new ...) ,(variables-not-in (term (X_1 M_1 M_2)) (term (X_2 ...))))]
  ;; and μ
  [(subst-1 X_1 M_1 (μ (X_2 : T) M_2))
   (μ (X_new : T) (subst-1 X_1 M_1 (subst-vars (X_2 X_new) M_2)))
   (where (X_new) ,(variables-not-in (term (X_1 M_1 M_2)) (term (X_2))))]
   
  ;; 3. replace X_1 with M_1
  [(subst-1 X_1 M_1 X_1) M_1]
  ;; 4. X_1 and X_2 are different, so don't replace
  [(subst-1 X_1 M_1 X_2) X_2]
  ;; the last cases cover all other expressions
  [(subst-1 X_1 M_1 (M_2 ...)) ((subst-1 X_1 M_1 M_2) ...)] 
  [(subst-1 X_1 M_1 M_2) M_2])

(define-metafunction L 
  subst-vars : (X M) ... M -> M
  [(subst-vars (X_1 M_1) X_1) M_1] 
  [(subst-vars (X_1 M_1) (M_2 ...)) 
   ((subst-vars (X_1 M_1) M_2) ...)]
  [(subst-vars (X_1 M_1) M_2) M_2]
  [(subst-vars (X_1 M_1) (X_2 M_2) ... M_3) 
   (subst-vars (X_1 M_1) (subst-vars (X_2 M_2) ... M_3))]
  [(subst-vars M) M])
  
   