#lang racket

(define-syntax-rule (tstruct name params)
  (struct name params #:transparent))


;; NF
(tstruct S0 ())
(tstruct S1 (e1))
(tstruct S2 (e1 e2))
(tstruct K0 ())
(tstruct K1 (e1))
(tstruct I0 ())

(define (normApp e1 e2)
  (match e1
    [(S0) (S1 e2)]
    [(S1 a) (S2 a e2)]
    [(K0) (K1 e2)]
    [(K1 a) a] ;; K a e2 = a
    [(S2 a b);; S a b e2 = (a e2) (b e2)
     (normApp (normApp a e2) (normApp b e2))]
    [(I0) e2])) ;; I e2 = e2

;; EXP
(tstruct S ())
(tstruct K ())
(tstruct I ())
(tstruct App (e1 e2))

(tstruct varr (x))

;; takes a function x -> EXP, and makes it into a term. Doesn't do any normalization.
(define (fromLam e1)
  (define x (gensym))
  (define (impl e) ;; this can be seen as "bracket abstraction" from https://en.wikipedia.org/wiki/Combinatory_logic#Reduction_in_combinatory_logic
    (match e
      [(varr name) #:when (eq? name x) (I)] ;; treat as lambda x . x
      [(App e1 e2) ;; treat as lambda x . e1 e2
       (App (App (S) (impl e1)) (impl e2))]
      [e (App (K) e)] ;; e = S, K, I, (varr x)
      ))
  (impl (e1 (varr x))))

;; EXP -> racket value
(define (eval e)
  (match e
    [(App e1 e2) ((eval e1) (eval e2))]
    [(S) (lambda (x) (lambda (y) (lambda (z) ((x z) (y z)))))]
    [(K) (lambda (x) (lambda (y) x))]
    [(I) (lambda (x) x)]))

(define-syntax-rule (lam x e)
  (fromLam (lambda (x) e)))
  
      
    