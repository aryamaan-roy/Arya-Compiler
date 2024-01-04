#! /usr/bin/env racket
#lang racket

(require "utilities.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp-Cif.rkt")

(require "interp.rkt")
(require "interp-Lif.rkt")
(require "interp-Lfun.rkt")
(require "interp-Cfun.rkt")

(require "compiler.rkt")

(require "type-check-Lif.rkt")
(require "type-check-Lfun.rkt")
(require "type-check-Cfun.rkt")

(debug-level 1)
;; (AST-output-syntax 'concrete-syntax)

;; all the files in the tests/ directory with extension ".rkt".
(define all-tests
  (map (lambda (p) (car (string-split (path->string p) ".")))
       (filter (lambda (p)
                 (string=? (cadr (string-split (path->string p) ".")) "rkt"))
               (directory-list (build-path (current-directory) "tests")))))

(define (tests-for r)
  (map (lambda (p)
         (caddr (string-split p "_")))
       (filter
        (lambda (p)
          (string=? r (car (string-split p "_"))))
        all-tests)))

;; only for Lvar
;(interp-tests "var" #f compiler-passes interp-Lvar "var_test" (tests-for "var"))

;; only for ex 4.1
;(interp-tests "cond" #f compiler-passes type-check-Lif "cond_test" (tests-for "cond"))

;; only for Lif
;(interp-tests "cond" #f compiler-passes interp-Lif "cond_test" (tests-for "cond"))

;; For Lfun
(interp-tests "functions" #f compiler-passes interp-Lfun "functions_test" (tests-for "functions"))


;; Uncomment the following when all the passes are complete to
;; test the final x86 code.
;(compiler-tests "var" #f compiler-passes "var_test" (tests-for "var"))
;(compiler-tests "cond" #f compiler-passes "cond_test" (tests-for "cond"))
;(compiler-tests "functions" #f compiler-passes "functions_test" (tests-for "functions"))

