#lang racket

;; going to work out what the deal is with renamings, how they fit into
;; the algorithm.

;; There will likely be multiple possible options for implementation. I will try to use
;; the one which which is the "most general" or "most parametric", in other words the one
;; which doesns't tie down Sem to any particular implementation of Exp.

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
;; should I add (struct value (e) #:transparent)

(define (evalImpl ctx e)
  (match e
    [(lam e)
     (lambda (x) (evalImpl (cons ctx x) e))]
    [(app e1 e2)
     ((evalImpl ctx e1) (evalImpl ctx e2))]
    [(varr i)
     (list-ref ctx i)]
    [(Pi A B)
     (SPi (evalImpl ctx A)
          (lambda (a))
            (evalImpl (cons ctx a) B)))]
    [(type)
     (Stype)]
    ))

(define (eval e)
  (evalImpl (hash) e))