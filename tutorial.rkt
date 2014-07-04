#lang racket
(require redex)
(require "subst.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Syntax

(define-language PCF
  (M ::= 
     N O X L 
     (μ (X : T) L)
     (M M ...) 
     (if0 M M M))
  (X ::= variable-not-otherwise-mentioned)
  (L ::= (λ ([X : T] ...) M))
  (V ::= N O L)
  (N ::= number)
  (O ::= O1 O2)
  (O1 ::= add1 sub1)
  (O2 ::= + *)
  (T ::= num (T ... -> T))
  (Γ ::= ((X T) ...)))


(define-term fact-5
  ((μ (fact : (num -> num))
      (λ ([n : num])
        (if0 n
             1
             (* n (fact (sub1 n))))))
   5))

(test-equal (redex-match? PCF M (term fact-5)) true)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Reduction semantics

(define r
  (reduction-relation 
   PCF #:domain M
   (--> (μ (X : T) M) 
        (subst (X (μ (X : T) M)) M) 
        μ)
   
   (--> ((λ ([X : T] [X_1 : T_1]) M_0) M M)
        (subst (X M) (X_1 M) M_0)
        β2)
   
   (--> ((λ ([X : T] ...) M_0) M ...)
        (subst (X M) ... M_0)
        β)
   
   (--> (O V ...) (δ O V ...) δ)
   
   (--> (if0 0 M_1 M_2) M_1 if-t)
   (--> (if0 N M_1 M_2) M_2
        (side-condition (not (zero? (term N))))
        if-f)))

(define -->r
  (compatible-closure r PCF M))
   
(define-metafunction PCF
  δ : O V ... -> V
  [(δ + N_0 N_1) ,(+ (term N_0) (term N_1))]
  [(δ * N_0 N_1) ,(* (term N_0) (term N_1))]
  [(δ sub1 N) ,(sub1 (term N))]
  [(δ add1 N) ,(add1 (term N))])

;(render-reduction-relation r)
;(render-metafunction δ)

(test-->>∃ -->r (term fact-5) 120)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Typing relation

(define-judgment-form PCF
  #:mode (⊢ I I I O)
  #:contract (⊢ Γ M : T)
  
  [(where T (lookup Γ X))
   ---------------------- var
   (⊢ Γ X : T)]
  
  [------------- num
   (⊢ Γ N : num)]
  
  [----------------------- op1
   (⊢ Γ O1 : (num -> num))]
  
  [--------------------------- op2
   (⊢ Γ O2 : (num num -> num))]
  
  [(⊢ Γ M_1 : num)
   (⊢ Γ M_2 : T)
   (⊢ Γ M_3 : T)
   --------------------------- if0
   (⊢ Γ (if0 M_1 M_2 M_3) : T)]
  
  [(⊢ (:: Γ (X T)) L : T)
   ----------------------- μ
   (⊢ Γ (μ (X : T) L) : T)]
  
  [(⊢ Γ M_0 : (T_1 ..._1 -> T))
   (⊢ Γ M_1 : T_1) ...  
   ----------------------- app
   (⊢ Γ (M_0 M_1 ..._1) : T)]
  
  [(⊢ (:: Γ (X T) ...) M : T_n)
   ------------------------------------------ λ
   (⊢ Γ (λ ([X : T] ...) M) : (T ... -> T_n))])
   
; (render-judgment-form ⊢)

(test-equal (judgment-holds (⊢ () fact-5 : T) T)
            (term (num)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Evaluation relation

(define-extended-language PCF⇓ PCF
  (V ::= N O (L ρ) ((μ (X : T) L) ρ))
  (ρ ::= ((X V) ...)))

(define-judgment-form PCF⇓
  #:mode (⇓ I I I O)
  #:contract (⇓ M ρ : V)
  
  [(⇓ N ρ : N)]  
  [(⇓ O ρ : O)]  
  [(⇓ L ρ : (L ρ))]  
  [(⇓ (μ (X_f : T_f) L) ρ : ((μ (X_f : T_f) L) ρ))]
  
  [(where V (lookup ρ X))
   ----------------------
   (⇓ X ρ : V)]

  [(⇓ M_0 ρ : N)
   (where M ,(if (zero? (term N)) (term M_1) (term M_2)))
   (⇓ M ρ : V)
   ---------------------------
   (⇓ (if0 M_0 M_1 M_2) ρ : V)]
    
  [(⇓ M_0 ρ : O)
   (⇓ M_1 ρ : V_1)
   ...
   (where V (δ O V_1 ...))
   -----------------------
   (⇓ (M_0 M_1 ...) ρ : V)]
    
  [(⇓ M_0 ρ : ((λ ([X_1 : T] ...) M) ρ_1))
   (⇓ M_1 ρ : V_1)
   ...
   (⇓ M (:: ρ_1 (X_1 V_1) ...) : V)
   --------------------------------
   (⇓ (M_0 M_1 ...) ρ : V)]
  
  [(⇓ M_0 ρ : (name f ((μ (X_f : T_f) (λ ([X_1 : T] ...) M)) ρ_1)))
   (⇓ M_1 ρ : V_1)
   ...
   (⇓ M (:: ρ_1 (X_f f) (X_1 V_1) ...) : V)
   ----------------------------------------
   (⇓ (M_0 M_1 ...) ρ : V)])

; (render-judgment-form ⇓)

(test-equal (judgment-holds (⇓ fact-5 () : V) V) (term (120)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Call-by-value PCF reduction semantics

(define-extended-language PCFv PCF
  (E ::= hole (V ... E M ...) (if0 E M M)))

(define rv
  (extend-reduction-relation 
   r PCFv #:domain M
   (--> ((λ ([X : T] ...) M_0) V ...)
        (subst (X V) ... M_0)
        β)))

(define -->rv
  (context-closure rv PCFv E))

(define -->rv0
  (compatible-closure rv PCFv M))

(test-->> -->rv (term fact-5) 120)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Explicit substitution reduction semantics

(define-extended-language PCFρ PCFv
  (V ::= N O ((L M) ρ) ((μ (X : T) L) ρ))
  (ρ ::= ((X V) ...))
  (C ::= V (M ρ) (if0 C C C) (C C ...))
  (E ::= hole (V ... E C ...) (if0 E C C)))

(define rρ
  (reduction-relation 
   PCFρ #:domain C
   (--> ((if0 M ...) ρ) (if0 (M ρ) ...) ρ-if)
   (--> ((M ...) ρ) ((M ρ) ...) ρ-app)
   (--> (O ρ) O ρ-op)
   (--> (N ρ) N ρ-num)        
   (--> (X ρ) (lookup ρ X) ρ-x)
   
   (--> (((λ ([X : T] ...) M) ρ) V ...)
        (M (:: ρ (X V) ...))        
        β)
   
   (--> ((name f ((μ (X_f : T_f) (λ ([X : T] ...) M)) ρ)) V ...)
        (M (:: ρ (X_f f) (X V) ...))
        rec-β)
   
   (--> (O V ...) (δ O V ...) δ)
   
   (--> (if0 0 C_1 C_2) C_1 if-t)
   (--> (if0 N C_1 C_2) C_2
        (side-condition (not (zero? (term N))))
        if-f)))

(define -->rρ
  (context-closure rρ PCFρ E))

(test-->> -->rρ (term (fact-5 ())) 120)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Eval/Continue machine

(define-extended-language PCFς PCFρ
  (E ::= (V ... hole C ...) (if0 hole C C))
  (K ::= (E ...))
  (S ::= ; why so serious?
     (side-condition C_1 (not (redex-match PCFς V (term C_1)))))
  (ς ::= (C K) V))

(define -->rς
  (reduction-relation 
   PCFς
   #:domain ς
   
   ;; Eval  
   (--> (C K) (C_1 K)
        (where ((any_0 C_0) ... (any_1 C_1) (any_2 C_2) ...)
               ,(apply-reduction-relation/tag-with-names rρ (term C)))
        (computed-name (term any_1)))
   
   (--> ((if0 S_0 C_1 C_2) (E ...))
        (S_0 ((if0 hole C_1 C_2) E ...)) 
        ev-if)
   
   (--> ((V ... S C ...) (E ...))
        (S ((V ... hole C ...) E ...))
        ev-app)
   
   ;; Continue
   (--> (V ()) V halt)
   
   (--> (V ((if0 hole C_1 C_2) E ...))
        ((if0 V C_1 C_2) (E ...)) co-if)
   
   (--> (V ((V_0 ... hole C_0 ...) E ...))
        ((V_0 ... V C_0 ...) (E ...))
        co-app)))


;(traces -->rς (term ((fact-5 ()) ())))
(test-->> -->rς (term ((fact-5 ()) ())) 120)

   
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Eval/Continue machine with heap

(define-extended-language PCFσ PCFς
  (ρ ::= ((X A) ...))
  (A ::= any)
  (σ ::= ((A V) ...))  
  (ς ::= (C K σ) V))

(define rσ
  (reduction-relation 
   PCFσ #:domain (C σ)
   (--> (((if0 M ...) ρ) σ) ((if0 (M ρ) ...) σ) ρ-if)
   (--> (((M ...) ρ) σ) (((M ρ) ...) σ) ρ-app)
   (--> ((O ρ) σ) (O σ) ρ-op)
   (--> ((N ρ) σ) (N σ) ρ-num)        
   (--> ((X ρ) σ) ((lookup σ (lookup ρ X)) σ) ρ-x)
   
   (--> (name ς ((((λ ([X : T] ...) M) ρ) V ...) σ))
        ((M (:: ρ (X A) ...)) (:: σ (A V) ...))
        (where (A ...) (alloc ς))
        β)
   
   (--> (name ς (((name f ((μ (X_f : T_f) (λ ([X : T] ...) M)) ρ)) V ...) σ))
        ((M (:: ρ (X_f A_f) (X A) ...)) (:: σ (A_f f) (A V) ...))
        (where (A_f A ...) (alloc ς))
        rec-β)
   
   (--> ((O V ...) σ) ((δ O V ...) σ) δ)
   
   (--> ((if0 0 C_1 C_2) σ) (C_1 σ) if-t)
   (--> ((if0 N C_1 C_2) σ) (C_2 σ)
        (side-condition (not (zero? (term N))))
        if-f)))

(define-metafunction PCFσ
  alloc : (C any_σ) -> (A ...)
  [(alloc ((((λ ([X : T] ...) M) ρ) V ...) any_σ))
   ,(map (λ (x) (gensym x)) (term (X ...)))]
  [(alloc ((((μ (X_f : T_f) (λ ([X : T] ...) M)) ρ) V ...) any_σ))
   ,(map (λ (x) (gensym x)) (term (X_f X ...)))])
   

(define -->rσ
  (reduction-relation 
   PCFσ
   #:domain ς
   
   ;; Eval  
   (--> (C K σ) (C_1 K σ_1)
        (where ((any_0 (C_0 σ_0)) ... (any_1 (C_1 σ_1)) (any_2 (C_2 σ_2)) ...)
               ,(apply-reduction-relation/tag-with-names rσ (term (C σ))))
        step
        #;(computed-name (term any_1)))
   
   (--> ((if0 S_0 C_1 C_2) (E ...) σ)
        (S_0 ((if0 hole C_1 C_2) E ...) σ) 
        ev-if)
   
   (--> ((V ... S C ...) (E ...) σ)
        (S ((V ... hole C ...) E ...) σ)
        ev-app)
   
   ;; Continue
   (--> (V () σ) V halt)
   
   (--> (V ((if0 hole C_1 C_2) E ...) σ)
        ((if0 V C_1 C_2) (E ...) σ) co-if)
   
   (--> (V ((V_0 ... hole C_0 ...) E ...) σ)
        ((V_0 ... V C_0 ...) (E ...) σ)
        co-app)))

(test-->> -->rσ (term ((fact-5 ()) () ())) 120)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Eval/Continue machine with set-based heap

(define-extended-language PCFσs PCFσ
  (σ ::= ((A (V ...)) ...)))

(define rσs
  (extend-reduction-relation 
   rσ PCFσs #:domain (C σ)
   (--> ((X ρ) σ) (V σ) 
        (where (V_0 ... V V_1 ...) (lookup σ (lookup ρ X)))        
        ρ-x)
   
   (--> (name ς ((((λ ([X : T] ...) M) ρ) V ...) σ))
        ((M (:: ρ (X A) ...)) (⊔ σ (A V) ...))
        (where (A ...) (alloc ς))
        β)
   
   (--> (name ς (((name f ((μ (X_f : T_f) (λ ([X : T] ...) M)) ρ)) V ...) σ))
        ((M (:: ρ (X_f A_f) (X A) ...)) (⊔ σ (A_f f) (A V) ...))
        (where (A_f A ...) (alloc ς))
        rec-β)))

(define -->rσs
  (extend-reduction-relation 
   -->rσ PCFσs
   #:domain ς 
   (--> (C K σ) (C_1 K σ_1)
        (where ((any_0 (C_0 σ_0)) ... (any_1 (C_1 σ_1)) (any_2 (C_2 σ_2)) ...)
               ,(apply-reduction-relation/tag-with-names rσs (term (C σ))))
        step)))

(define-metafunction PCFσs
  ⊔ : σ (A V) ... -> σ
  [(⊔ σ) σ]
  [(⊔ σ (A V) (A_0 V_0) ...)
   (⊔ (⊔1 σ A V) (A_0 V_0) ...)])

(define-metafunction PCFσs
  ⊔1 : σ A V -> σ
  [(⊔1 ((A_0 (V_0 ...)) ... (A (V_1 ...)) (A_2 (V_2 ...)) ...) A V)
   ((A_0 (V_0 ...)) ... (A (V V_1 ...)) (A_2 (V_2 ...)) ...)]
  [(⊔1 ((A_0 (V_0 ...)) ...) A V)
   ((A (V)) (A_0 (V_0 ...)) ...)])

(test-->> -->rσs (term ((fact-5 ()) () ())) 120)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Pushdown flow analysis

(define rσs^
  (extend-reduction-relation 
   rσs PCFσs #:domain (C σ)
   (--> (name ς ((((λ ([X : T] ...) M) ρ) V ...) σ))
        ((M (:: ρ (X A) ...)) (⊔ σ (A V) ...))
        (where (A ...) (alloc^ ς))
        β)
   
   (--> (name ς (((name f ((μ (X_f : T_f) (λ ([X : T] ...) M)) ρ)) V ...) σ))
        ((M (:: ρ (X_f A_f) (X A) ...)) (⊔ σ (A_f f) (A V) ...))
        (where (A_f A ...) (alloc^ ς))
        rec-β)))

(define-metafunction PCFσs
  alloc^ : (C any_σ) -> (A ...)
  [(alloc^ ((((λ ([X : T] ...) M) ρ) V ...) any_σ))
   (X ...)]
  [(alloc^ ((((μ (X_f : T_f) (λ ([X : T] ...) M)) ρ) V ...) any_σ))
   (X_f X ...)])

(define -->rσs^
  (extend-reduction-relation 
   -->rσs PCFσs
   #:domain ς 
   (--> (C K σ) (C_1 K σ_1)
        (where ((any_0 (C_0 σ_0)) ... (any_1 (C_1 σ_1)) (any_2 (C_2 σ_2)) ...)
               ,(apply-reduction-relation/tag-with-names rσs^ (term (C σ))))
        step)))



        