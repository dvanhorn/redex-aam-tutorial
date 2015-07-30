#lang racket
(require redex/reduction-semantics)
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Generic utilities

;; Shorthands to help keep code narrow.
(define-syntax-rule
  (test-#t e)
  (test-equal e #t))

(define-syntax-rule
  (test-#f e)
  (test-equal e #f))

(define-language REDEX)

;; Set heaps
;; =========

;; Set heaps model a map : A ↦ P(B)

;; The empty set heap
(define-term Σ∅ ,(hash))

;; ext-Σ : extend a set heap with given associations
;; (ext-Σ Σ (k v) ...) = Σ[k ↦ {v} ∪ Σ(k), ...]
(module+ test
  (test-equal (term (ext-Σ Σ∅ (x 1)))
              (hash 'x (set 1)))
  (test-equal (term (ext-Σ (ext-Σ Σ∅ (x 1)) (x 2)))
              (hash 'x (set 1 2)))
  (test-equal (term (ext-Σ Σ∅ (x 1) (y 2)))
              (hash 'x (set 1) 'y (set 2))))
              
(define-metafunction REDEX
  ext-Σ : any (any any) ... -> any
  [(ext-Σ any_r) any_r]
  [(ext-Σ any_r any_kv0 any_kv1 ...)
   (ext-Σ (ext-Σ1 any_r any_kv0) any_kv1 ...)])

;; lookup-Σ : Look up member of set heap
;; (lookup-Σ Σ k v) iff v ∈ Σ(k)
(module+ test
  (test-#t
   (judgment-holds (lookup-Σ (ext-Σ Σ∅ (x 1)) x 1)))
  (test-#f
   (judgment-holds (lookup-Σ Σ∅ x 1))))

(define-judgment-form REDEX
  #:mode (lookup-Σ I I O)
  #:contract (lookup-Σ any_r any_k any_v)
  [(lookup-Σ any_r any_k any_v)
   (where (_ ... any_v _ ...)
	  ,(set->list
	    (hash-ref (term any_r)
		      (term any_k)
                      '())))])

;; ext-Σ1 : extend with one new binding
;; (ext-Σ1 Σ (k v)) = Σ[k ↦ {v} ∪ Σ(k)]
(module+ test
  (test-equal (term (ext-Σ1 Σ∅ (x 1)))
              (hash 'x (set 1)))
  (test-equal (term (ext-Σ1 (ext-Σ1 Σ∅ (x 1)) (x 2)))
              (hash 'x (set 1 2))))

(define-metafunction REDEX
  ext-Σ1 : any (any any) -> any
  [(ext-Σ1 any_r (any_k any_v))
   ,(hash-set (term any_r)
	      (term any_k)
	      (set-add
               (hash-ref (term any_r) (term any_k) (set))
               (term any_v)))])


;; Associations
;; ============

;; Associations model a map : A ↦ B

(module+ test
  (test-#t
   (judgment-holds (lookup ((x 1) (y 2) (x 3)) x 1)))
  (test-#f
   (judgment-holds (lookup ((x 1) (y 2) (x 3)) x 2)))
  (test-#t
   (judgment-holds (lookup ((x 1) (y 2) (x 3)) x 3))))

(define-judgment-form REDEX
  #:mode (lookup I I O)
  #:contract (lookup ((any any) ...) any any)
  [(lookup (_ ... (any any_0) _ ...) any any_0)])

;; for when the range is a list and you want to
;; choose non-deterministally.
(define-judgment-form REDEX
  #:mode (lookup* I I O)
  [(lookup* any_assoc (any_k ...) (any_v ...))
   (lookup any_assoc any_k any_v)
   ...])

(define-metafunction REDEX
  ext : ((any any) ...) (any any) ... -> ((any any) ...)
  [(ext any) any]
  [(ext any any_0 any_1 ...)
   (ext1 (ext any any_1 ...) any_0)])

(define-metafunction REDEX
  ext1 : ((any any) ...) (any any) -> ((any any) ...)
  [(ext1 (any_0 ... (any_k _) any_1 ...) (any_k any_v1))
   (any_0 ... (any_k any_v1) any_1 ...)]
  [(ext1 (any_0 ...) (any_k any_v1))
   ((any_k any_v1) any_0 ...)])


;; unique
;; ======

;; unique : determine if a list consists of unique elements
(module+ test
  (test-equal (term (unique)) #t)
  (test-equal (term (unique 1)) #t)
  (test-equal (term (unique 1 2 3 2)) #f))

(define-relation REDEX
  unique ⊆ any × ...
  [(unique any_!_1 ...)])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Substitution

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
  
   