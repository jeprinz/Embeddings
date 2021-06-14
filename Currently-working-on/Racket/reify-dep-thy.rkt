#lang racket

(define (lam x e) (list 'lambda x e))
(define (var x) (list 'var x))
(define (app e1 e2) (list 'app e1 e2))

(define type (list 'type))
;; SPECIAL dependent functions.
;; B is a FUNCTION which inputs a, and then outputs a TYPE.
(define (Pi A B) (list 'Pi A B))
(define (to A B) (list 'Pi A (lambda (x) B)))
;; SAME VARS AS EXPRESSIONS (define (var X) (list 'var X))

(define (nApp T e)
  (match T
    [(list 'type) e]
    [(list 'var X) e]
    [(list 'app e1 e2) e]
    [(list 'Pi A B)
     (lambda (x) (nApp (B x) (list 'app e (reify A x))))]))

(define (reify T e)
  (match T
    [(list 'type) e] ;; maybe shouldn't do exactly the same thing on type as var?
    [(list 'var X) e] ;; free var is like base from STLC
    [(list 'app e1 e2) e] ;; I think this case should be same as var, because is neutral form?
    [(list 'Pi A B)
     (let [(x (gensym))]
       (let [(napp (nApp A (var x)))]
         (list 'lambda x (reify (B napp) (e napp)))))]))
;; Really, we should want Pi to have variable and B refers to the variable.
;;

(define nat
  (Pi type
      (lambda (X)
        (to (to X X) (to X X)))))

;; nat
(define Z
  (lambda (X)
    (lambda (f)
      (lambda (x) x))))

;; (to nat nat)
(define S
  (lambda (n)
    (lambda (X)
      (lambda (f)
        (lambda (x)
          (f (((n X) f) x)))))))

;; (to nat (to nat nat))
(define add ;; can't define it like this in STLC
  (lambda (a)
    (lambda (b)
      (((a nat) S) b))))

;; An example of reification where term has a type in it which ends up gettings
;; passed into reify

(define type1
  (to
   (Pi type (lambda (X) (to X X)))
   type))

(define term1
  (lambda (id)
    ((id type) type)))

;; lam id . id T t     where T and t are a specific term and type

;; Another thing to think about is types with terms in them
(define type2
  (Pi
   (to nat type)
   (lambda (P)
     (to
      (Pi nat
          (lambda (n) (to (P n) (P (S n)))))
      (to
       (P Z)
       (P (S (S Z))))))))

(define term2
  (lambda (P)
    (lambda (PS)
      (lambda (PZ)
        ((PS (S Z)) ((PS Z) PZ))))))

(define type3
  (Pi
   (to type type)
   (lambda (P)
     (to (P type) (P type)))))

(define term3
  (lambda (P)
    (lambda (Ptype) Ptype)))


#|

The big question that I need to try to answer is:
How should types be stored in values?

In NbE, we have "source" and "values". Reify converts a value into source.

When reifying a function, can do so by plugging in arguments.
But nothing can be done with a type in Agda (and doesn't exist in Racket).

So, if we want to be able to store source types, then values must include source types.
But, types can have values in them and vice versa. So needs to be a different source.





So, Sem must have data-type types in it. But, these types can have values in them, which
must be stored as actual functions, AND the typechecking can depend on these types.
NO- just focus on Racket and computation and figure out typechecking afterwards.

|#


































  
            