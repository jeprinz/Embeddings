#lang racket

(struct varr (i) #:transparent)
(struct app (e1 e2) #:transparent)
(struct lam (e) #:transparent)

(define (n-app e n)
  (if (eq? n 0)
      e
      ;"yeetus")) ; I could have sworn that I finished this file, but maybe my progress didn't get saved.
      (lambda (x) (n-app (app e (x 0 (id-ren 100))) (- n 1)))))

;; ren is a list of debruin indices

;; sub is a list of values, one for each free variable
;; each of the values is a function (n -> ren -> Exp)

;; ctx is a number
;; Ren G1 G2 -> Ren G1 (G2 , T)     ;; should rename this.
(define (append1ren ren)
  (match ren
    ['() '()]
    [(cons x ren) (cons (+ x 1) (append1ren ren))]))

;; Ren (G1 , T) G2 -> Ren G1 G2
;; forget1ren = tail

;; Sub G1 G2 -> GExp G2 T -> Sub (G1 , T) G2
;; append1sub = cons

;; Ren G (G , T)
(define (weaken1ren ctx)
  (if (= ctx 0)
      '()
      (cons 1 (append1ren (weaken1ren (- ctx 1))))))

;; liftSub : Sub G1 G2 -> Sub (G1 , T) (G2 , T)
(define (liftSub sub)
  (cons (lambda (n ren) (n-app (varr (list-ref ren 0)) n))
        (transSR sub (weaken1ren (length sub)))))

;; Ren G G
(define (id-ren ctx)
  (if (= ctx 0)
      (list)
      (cons 0 (append1ren (id-ren (- ctx 1))))))

;; Ren G1 G2 -> Var G1 -> Exp G2
;; applyRen = list-ref

;; transRR : Ren G1 G2 -> Ren G2 G3 -> Ren G1 G3
(define (transRR ren1 ren2)
  (match ren1
    ['() '()]
     [(cons i ren1) (cons (list-ref ren2 i) (transRR ren1 ren2))]))

;; transSR : Sub G1 G2 -> Ren G2 G3 -> Sub G1 G3
(define (transSR sub ren)
  (match sub
    ['() '()]
    ;; here, e : n -> ren -> Exp
    [(cons e sub) (cons (lambda (n ren2) (e n (transRR ren ren2))) (transSR sub ren))]))

;; Note that e : Exp,  but the terms in sub are not Exp, rather are (n -> ren -> Exp)
(define (unquote-n sub n e)
  (match e
    [(varr i)
     ((list-ref sub i) n (id-ren 100)) ;; values in sub are functions, not merely terms
     ]
    [(app e1 e2)
     ((unquote-n sub (+ n 1) e1)
      (lambda (n ren) (unquote-n (transSR sub ren) n e2)))]
    [(lam e)
     (if (= n 0)
         (lam (unquote-n (liftSub sub) 0 e))
         (lambda (x) (unquote-n (cons x sub) (- n 1) e)))]))

(define (norm e) (unquote-n (list) 0 e))

;; Just like the fromLam in SKI.rkt, doesn't do any normalization. Merely makes a lambda expression.
;; QUESTION: what kind of thing is e? can't merely be an Exp Empty, because
;; e is a function from Exp Empty A -> Exp Empty (B a). fromLam then returns (Exp Empty ((a : A) -> B a))
(define (fromLam e)
  "hole")

;; taking hint from SKI.rkt, can do fromLam first and work from there.

#|

There are various ways to represent substitutions and renamings, and Sem and GSem.

I am looking to see if there is a way with the following properties:
1) All of the operations necessary to do on Rens and Subs can be done straightforwardly with
    them as lists, and don't need to think of them as functions or map over the lists
2) No separate renaming/weakening function on terms necessary. Only unquote-n exists.
3) Sems don't have a renaming at top level, so that SemT can be pattern matched on.

|#


;; TESTS

;;(unquote-n (list (lambda (n ren) (n-app (varr (list-ref ren 0)) n))) 0 (lam (varr 1)))

;;(norm (lam (app (lam (lam (varr 1))) (varr 0))))
;;(norm (lam (app (lam (lam (app (varr 1) (varr 1)))) (varr 0))))

(define (print-sub sub)
  (match sub
    ['() '()]
    [(cons e sub)
     (cons (e 0 (id-ren 20)) (print-sub sub))]))
