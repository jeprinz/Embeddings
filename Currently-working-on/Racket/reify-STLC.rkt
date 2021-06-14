#lang racket

(define (lam x e) (list 'lam x e))
(define (var x) (list 'var x))
(define (app e1 e2) (list 'app e1 e2))
(define (num n) (list 'num n))

(define (eval-j e)
  (define (evalImpl e ctx)
    (match e
      [(list 'lam var e) (lambda (x) (evalImpl e (hash-set ctx var x)))]
      [(list 'app e1 e2) ((evalImpl e1 ctx) (evalImpl e2 ctx))]
      [(list 'var x) (hash-ref ctx x)]
      [(list 'num n) n]))
  (evalImpl e (hash)))

(define (to A B) (list 'to A B))
(define base (list 'base))

(define (nApp T e)
  (match T
    [(list 'base) e]
    [(list 'to A B)
     (lambda (x) (nApp B (list 'app e (reify A x))))]))

(define (reify T e)
  (match T
    [(list 'base) e]
    [(list 'to A B)
     (let [(x (gensym))]
         (list 'lam x (reify B (e (nApp A (var x))))))]))
;; Really, we should want Pi to have variable and B refers to the variable.
;;

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





































  
            