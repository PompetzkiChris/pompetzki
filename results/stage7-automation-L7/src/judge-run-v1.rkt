#lang racket/base
;; judge-run-v1.rkt -- lane L7: both judges on the given .jdg files, one row each (sigma1.rkt's cmd-judge, for a file list).
;; Usage: racket judge-run-v1.rkt RESULTS.txt FILE.jdg ...
(require "l7core-v1.rkt" racket/list racket/match racket/string)
(define args (vector->list (current-command-line-arguments)))
(define results (car args))
(define files (cdr args))
(define o (open-output-file results #:exists 'error))
(for ([f files])
  (define full (path->string (path->complete-path f)))
  (match-define (list e1 t1 o1) (run-cmd JUDGE-DIR PMP (list "judge-v3.pmp" full)))
  (match-define (list e2 t2 o2) (run-cmd JUDGE-DIR RACKET (list "racket/judge.rkt" full)))
  (define row (format "~a | pmp ~a exit ~a ~a ms | racket ~a exit ~a ~a ms | pmp: ~a | racket: ~a"
                      f (verdict o1) e1 t1 (verdict o2) e2 t2 (one-line o1) (one-line o2)))
  (displayln row o) (flush-output o)
  (printf "~a\n" row) (flush-output))
(close-output-port o)
