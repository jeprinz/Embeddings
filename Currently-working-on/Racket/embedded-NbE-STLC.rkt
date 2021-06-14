#lang racket

;; Before I try dep thy, I will try STLC

(define (lam x e) (list 'lam x e))
(define (var x) (list 'var x))
(define (app e1 e2) (list 'app e1 e2))
(define (num n) (list 'num n))

(define base (cons (lambda (e) e) (lambda (e) e)))
(define (to A B)
  (cons
   (lambda (e)
     (let [(x (gensym))]
       (list 'lam x ((car B) (e ((cdr A) (var x)))))))
   (lambda (e)
     (lambda (x) ((cdr B) (list 'app e ((car A) x)))))))

;; In what way is this an improvement? Sure, it doesn't require a datatype for types.
;; But does it actually get the invariances that I want, like beta-equivalence?

(define (reify T e)
  ((car T) e))

(define nat
  (to (to base base) (to base base)))

;; nat
(define Z
  (lambda (f)
    (lambda (x) x)))

;; (to nat nat)
(define S
  (lambda (n)
    (lambda (f)
      (lambda (x)
        (f ((n f) x))))))

;; (to nat (to nat nat))
(define add ;; can't define it like this in STLC
  (lambda (a)
    (lambda (b)
      (((a nat) S) b))))