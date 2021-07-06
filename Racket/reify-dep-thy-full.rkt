#lang racket
;; like reify-dep-thy, except it should reify under types and work with nonempty context
;; So, Sem (Pi ....) is stored as function value as always, while
;;     Sem type is stored in a special datatype!


;; Syntactic domain (Exp)
(struct lam (x e) #:transparent)
(struct app (e1 e2) #:transparent)
(struct varr (x) #:transparent) ;; apparently var is a keyword in racket?
(struct type () #:transparent)
(struct Pi (x A B) #:transparent)

;; Semantic domain (but functions are just stored as functions...
(struct Stype () #:transparent)
(struct SPi (A B) #:transparent)
(define (Sto A B) (SPi A (lambda (a) B)))
;; should I add (struct value (e) #:transparent)


;; e.g.
; (reify (Pi 'X type (Pi (var 'X) (var 'X))) (lambda (X) (lambda (x) x)))
; =
; (lam 'X (lam 'x (var 'x)))

;; ctx is hashmap whose values are Sems
(define (evalImpl ctx e)
  (match e
    [(lam name e)
     (lambda (x) (evalImpl (hash-set ctx name x) e))]
    [(app e1 e2)
     ((evalImpl ctx e1) (evalImpl ctx e2))]
    [(varr name)
     (hash-ref ctx name)]
    [(Pi x A B)
     (SPi (evalImpl ctx A)
          (lambda (a)
            (evalImpl (hash-set ctx x a) B)))]
    [(type)
     (Stype)]
    ))

(define (eval e)
  (evalImpl (hash) e))

(define (nApp T e)
  (match T
    [(Stype) e]
    [(SPi A B)
     (lambda (x) (nApp (B x) (app e (reify A x))))]
    [any e]))

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
    [any e]))

;; TODO: figure out non-empty contexts.

;; for each example, try (reify (eval typen) (eval termn))

(define type1
  (Pi 'X (type) (type)))
(define term1
  (lam 'X (app (lam 'x (varr 'x)) (varr 'X))))

(define type2 (type))
(define term2
  (Pi 'P (Pi '_ (type) (type))
      (app (varr 'P)
           (app (lam 'x (varr 'x))
                (type)))))

(define type3
  (Pi 'T (type)
      (Pi '_ (varr 'T) (varr 'T))))
(define term3
  (lam 'T (lam 't (varr 't))))

(define type4
  (Pi 'P (Pi '_ (type) (type))
      (Pi 'T (type)
          (Pi '_
              (app (varr 'P) (varr 'T))
              (app (varr 'P) (varr 'T))))))
(define term4
  (lam 'P (lam 'T (lam 'x (varr 'x)))))

(define type5
  (Pi '_ (type) (type)))
(define term5
  (lam 'x (varr 'x)))
