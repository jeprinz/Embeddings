#lang racket

;; Not finished, working on reification with debruin indices instead of named variables.

;; Syntactic domain (Exp)
(struct lam (e) #:transparent)
(struct app (e1 e2) #:transparent)
(struct varr (i) #:transparent) ;; apparently var is a keyword in racket?
(struct type () #:transparent)
(struct Pi (A B) #:transparent)

;; Semantic domain (but functions are just stored as functions...
(struct Stype () #:transparent)
(struct SPi (A B) #:transparent)
(define (Sto A B) (SPi A (lambda (a) B)))
(struct SNe (e) #:transparent) ;; stores neutral forms of Exp.

;; comparing to agda, "ctx" is like "sub" argument. Essentially it stores the same info as data instead of function, mapping from vars in G1 to Exps in G2
;; for some ways of building subs, list is as good as function. For others, function makes computation easier.
;; Syn -> Sem
(define (evalImpl ctx e)
  (match e
    [(lam e)
     (lambda (x) (evalImpl (cons x ctx) e))]
    [(app e1 e2)
     ((evalImpl ctx e1) (evalImpl ctx e2))]
    [(varr i)
     (list-ref ctx i)]
    [(Pi A B)
     (SPi (evalImpl ctx A)
          (lambda (a)
            (evalImpl (cons a ctx) B)))]
    [(type)
     (Stype)]
    ))

(define (eval e)
  (evalImpl (list) e)) ;; (list) is like a Sub nil nil

;; need to define renamings, either as data or as functions, and use in nApp and reify

;; Sem -> Exp(neutral) -> Sem
(define (nApp T e)
  (match T
    [(Stype) e]
    [(SNe e) e] ;; ?
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
        (Pi (reify (Stype) A)
            (reify (Stype) (B (nApp A (varr 0)))))]
       [any e])]
    [(SPi A B)
     (let [(napp (nApp A (varr 0)))]
       (lam (reify (B napp) (e napp))))]
    [any e]))

;; Current problem: doesn't do any sort of renaming, so all variables are 0.
;; Needs to take into account going under lam and Pi in those two cases.

(define type1
  (Pi (type) (Pi (varr 0) (varr 1))))
(define term1
  (lam (lam (varr 0))))

(define type2
  (Pi (type) (Pi (varr 0) (Pi (varr 1) (varr 2)))))
(define term2
  (lam (lam (lam (varr 1)))))

(define type3
  (Pi (Pi (type) (type)) (Pi (type) (type))))
(define term3
  (lam (lam (app (varr 1) (varr 0)))))