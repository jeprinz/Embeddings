#lang racket

;; The concept of this file is to do the same thing as reify-dep-thy, except that
;; there is no "reify" and "nApp", and instead Pi and type are directly defined
;; as what would be "reify Pi" and "reify type".

;; The goal is to eventually implement the idea that I asked Alex about in Agda.
;; Namely, having a shallow embedding whose model is a semantic domain which
;; evaluates terms and outputs normalized terms in another model.


;; There are some big remaining questions about how to do this (even in Racket)
;; For example, what about when types have app, lam, and var in them?