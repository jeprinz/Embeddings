#lang racket
;; like reify-dep-thy, except it should reify under types and work with nonempty context
;; So, Sem (Pi ....) is stored as function value as always, while
;;     Sem type is stored in a special datatype!


;; Syntactic domain (Exp)
(struct lam (e) #:transparent)
(struct app (e1 e2) #:transparent)
(struct varr (i) #:transparent) ;; apparently var is a keyword in racket?
(struct type () #:transparent)
(struct Pi (A B) #:transparent)

;; Semantic domain (but functions are just stored as functions...
(struct Stype () #:transparent)
(struct SPi (A B) #:transparent) ;; A is Sem, B is GSem -> Sem
(define (Sto A B) (SPi A (lambda (a) B)))
;; should I add (struct value (e) #:transparent)

;; Ren is nat -> nat
;; Sub is nat -> Sem
;; GSem is Ren -> Sem

(define idRen (lambda (i) i))
(define forget1Ren
  (lambda (ren)
    (lambda (i)
      (ren (+ i 1)))))


;; e.g.
; (reify (Pi 'X type (Pi (var 'X) (var 'X))) (lambda (X) (lambda (x) x)))
; =
; (lam 'X (lam 'x (var 'x)))

(define (index l i)
  (if (= i 0)
      (car l)
      (index (cdr l) (- i 1))))

;; returns ctx -> Sem
(define (eval e)
  (match e
    [(lam e)
     (lambda (ctx)
       (lambda (x) ((eval e) (cons x ctx))))]
    [(app e1 e2)
     (lambda (ctx)
       (((eval e1) ctx) ((eval e2) ctx)))]
    [(varr i)
     (lambda (ctx)
       (index ctx i))]
    [(Pi A B)
     (lambda (ctx)
       (SPi ((eval A) ctx)
          (lambda (a)
            ((eval B) (cons a ctx)))))]
    [(type)
     (lambda (ctx) (Stype))]
    ))

#|
Each type in the context actually must be a function which inputs previous stuff
in context. So the context really has to be a list, because the order is necessary.
|#

;; Ctx is List (ctx -> Sem)
;; T is ctx -> Sem
;; e is ctx -> Sem
(define (nAppC Ctx T e)
  "hole")
;; T and e are elements of Sem
(define (nApp T e)
  "hole")

;; TODO: make a better name for this function.
;; What it does is give a ctx element of a Ctx filled with variables
(define (ctxNApp Ctx)
  (match Ctx
    [(cons T Ctx)
     (let ([rest (ctxNApp Ctx)])
       (cons
        (nApp (T rest) (varr 0))
        rest))]
    [null
     null]))
(define (reifyC Ctx T e)
  (match Ctx
    [(cons T Ctx)
     "hole1"]
    [null
     "hole2"]))

(define (reify T e)
  "hole")

;; Question: When are Exps stored in Sems? I don't think they ever are here!
;; Although, Exps need to be inputted as arugments to elements of Sem.
;; So this is just a shallow embedding?!? No, not quite. It stores types as data.

#|

(define (nApp T e)
  (match T
    [(Stype)
     (match e
       [(Stype) (type)]
       [(SPi A B)
        (let [(x (gensym))]
          (Pi x (reify (Stype) A)
              (reify (Stype) (B (nApp A (varr x))))))]
       [any e])]
    [(SPi A B)
     (lambda (x) (nApp (B x) (app e (reify A x))))]
    [any (println "here1") (println T) e]))

;; both T and e come from Semantic domain!

(define (reify T e)
  (match T
    [(Stype)
     (match e
       [(Stype) (type)]
       [(SPi A B)
        (let [(x (gensym))]
          (Pi x (reify (Stype) A)
              (reify (Stype) (B (nApp A (varr x))))))]
       [any e])]
    [(SPi A B)
     (let [(x (gensym))]
       (let [(napp (nApp A (varr x)))]
         (lam x (reify (B napp) (e napp)))))]
    [any (println "here2") (println T) e]))

|#