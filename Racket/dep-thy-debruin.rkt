#lang racket

;; Not finished, working on reification with debruin indices instead of named variables.
;; If I can successfully code this, but translating to an Agda implementation STILL involves proving
;; sub and ren stuff, then this maybe proves that ANY Agda implementation really would have to prove that stuff.

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

;; Sem means elements of semantic domain above. GSem means function (ren -> Sem).
;; Ren is a list of indices, which represents a mapping (Var G1 T -> Var G2 ?T).
;; Sub is a list of GSem, which represents a mapping (Var G1 T -> GSem G2 ?T).to

;; Syn -> Sem
(define (evalImpl sub e)
  (match e
    [(lam e)
     (lambda (x) (evalImpl (cons x sub) e))]
    [(app e1 e2)
     ((evalImpl sub e1) (evalImpl sub e2))]
    [(varr i)
     (list-ref sub i)]
    [(Pi A B)
     (SPi (evalImpl sub A)
          (lambda (a)
            (evalImpl (cons a sub) B)))]
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